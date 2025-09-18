/* Tests for System V IPC semaphores - by D.C. van Moolenbroek */
/* This test must be run as root, as it includes permission checking tests. */
#include <stdlib.h>
#include <limits.h>
#include <pwd.h>
#include <grp.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <sys/wait.h>
#include <sys/mman.h>
#include <sys/sysctl.h>
#include <signal.h>

#include "common.h"

#define ITERATIONS	3

#define WAIT_USECS	100000		/* time for processes to get ready */

#define KEY_A		0x73570001
#define KEY_B		(KEY_A + 1)
#define KEY_C		(KEY_A + 2)

#define ROOT_USER	"root"		/* name of root */
#define ROOT_GROUP	"wheel"		/* name of root's group */
#define NONROOT_USER	"bin"		/* name of any unprivileged user */
#define NONROOT_GROUP	"bin"		/* name of any unprivileged group */

enum {
	DROP_NONE,
	DROP_USER,
	DROP_ALL,
};

enum {
	SUGID_NONE,
	SUGID_ROOT_USER,
	SUGID_NONROOT_USER,
	SUGID_ROOT_GROUP,
	SUGID_NONROOT_GROUP,
};

struct link {
	pid_t pid;
	int sndfd;
	int rcvfd;
};

/*
 * Test semaphore properties.  This is a macro, so that it prints useful line
 * information if an error occurs.
 */
#define TEST_SEM(id, num, val, pid, ncnt, zcnt) do { \
	if (semctl(id, num, GETVAL) != val) e(0); \
	if (pid != -1 && semctl(id, num, GETPID) != pid) e(1); \
	if (ncnt != -1 && semctl(id, num, GETNCNT) != ncnt) e(2); \
	if (zcnt != -1 && semctl(id, num, GETZCNT) != zcnt) e(3); \
} while (0);

static int nr_signals = 0;

static size_t page_size;
static char *page_ptr;
static void *bad_ptr;

/*
 * Spawn a child process, with a pair of pipes to talk to it bidirectionally.
 * Drop user and group privileges in the child process if requested.
 */
static void flush_standard_streams(void)
{
	fflush(stdout);
	fflush(stderr);
}

static void create_pipes(int up[2], int dn[2])
{
	if (pipe(up) != 0) e(0);
	if (pipe(dn) != 0) e(0);
}

static void setup_child_pipes(struct link *link, int up[2], int dn[2])
{
	close(up[1]);
	close(dn[0]);
	
	link->pid = getppid();
	link->rcvfd = up[0];
	link->sndfd = dn[1];
}

static void setup_parent_pipes(struct link *link, int up[2], int dn[2])
{
	close(up[0]);
	close(dn[1]);
	
	link->sndfd = up[1];
	link->rcvfd = dn[0];
}

static void drop_group_privileges(void)
{
	struct group *gr;
	
	if (setgroups(0, NULL) != 0) e(0);
	
	if ((gr = getgrnam(NONROOT_GROUP)) == NULL) e(0);
	
	if (setgid(gr->gr_gid) != 0) e(0);
	if (setegid(gr->gr_gid) != 0) e(0);
}

static void drop_user_privileges(void)
{
	struct passwd *pw;
	
	if ((pw = getpwnam(NONROOT_USER)) == NULL) e(0);
	
	if (setuid(pw->pw_uid) != 0) e(0);
}

static void apply_privilege_drop(int drop)
{
	switch (drop) {
	case DROP_ALL:
		drop_group_privileges();
		drop_user_privileges();
		break;
	case DROP_USER:
		drop_user_privileges();
		break;
	}
}

static void handle_child_process(struct link *link, void (*proc)(struct link *), int drop, int up[2], int dn[2])
{
	setup_child_pipes(link, up, dn);
	
	errct = 0;
	
	apply_privilege_drop(drop);
	
	proc(link);
	
	exit(errct);
}

static void spawn(struct link *link, void (*proc)(struct link *), int drop)
{
	int up[2], dn[2];
	
	flush_standard_streams();
	create_pipes(up, dn);
	
	link->pid = fork();
	
	switch (link->pid) {
	case 0:
		handle_child_process(link, proc, drop, up, dn);
		break;
	case -1:
		e(0);
		break;
	default:
		setup_parent_pipes(link, up, dn);
		break;
	}
}

/*
 * Wait for a child process to terminate, and clean up.
 */
static void
collect(struct link * link)
{
	int status;

	close(link->sndfd);
	close(link->rcvfd);

	if (waitpid(link->pid, &status, 0) != link->pid) {
		e(0);
		return;
	}

	if (!WIFEXITED(status)) {
		e(0);
		return;
	}
	
	errct += WEXITSTATUS(status);
}

/*
 * Forcibly terminate a child process, and clean up.
 */
static void close_link_fds(struct link *link)
{
    close(link->sndfd);
    close(link->rcvfd);
}

static void kill_link_process(struct link *link)
{
    if (kill(link->pid, SIGKILL) != 0) e(0);
}

static void wait_for_process(struct link *link)
{
    int status;
    
    if (waitpid(link->pid, &status, 0) <= 0) e(0);
    
    if (WIFSIGNALED(status)) {
        if (WTERMSIG(status) != SIGKILL) e(0);
        return;
    }
    
    if (!WIFEXITED(status)) {
        e(0);
        return;
    }
    
    errct += WEXITSTATUS(status);
}

static void terminate(struct link *link)
{
    kill_link_process(link);
    close_link_fds(link);
    wait_for_process(link);
}

/*
 * Send an integer value to the child or parent.
 */
static void
snd(struct link * link, int val)
{
	const size_t val_size = sizeof(val);
	if (write(link->sndfd, (void *)&val, val_size) != val_size) e(0);
}

/*
 * Receive an integer value from the child or parent, or -1 on EOF.
 */
static int
rcv(struct link * link)
{
	int r, val;

	if ((r = read(link->rcvfd, (void *)&val, sizeof(val))) == 0)
		return -1;

	if (r != sizeof(val)) e(0);

	return val;
}

/*
 * Child procedure that creates semaphore sets.
 */
static int create_semaphore(int key, int mask) {
    return semget(key, 3, IPC_CREAT | IPC_EXCL | mask);
}

static void get_user_uid(int sugid_type, uid_t *uid) {
    struct passwd *pw;
    const char *username = (sugid_type == SUGID_ROOT_USER) ? ROOT_USER : NONROOT_USER;
    
    if ((pw = getpwnam(username)) == NULL) e(0);
    *uid = pw->pw_uid;
}

static void get_group_gid(int sugid_type, gid_t *gid) {
    struct group *gr;
    const char *groupname = (sugid_type == SUGID_ROOT_GROUP) ? ROOT_GROUP : NONROOT_GROUP;
    
    if ((gr = getgrnam(groupname)) == NULL) e(0);
    *gid = gr->gr_gid;
}

static void update_uid_gid(int sugid, uid_t *uid, gid_t *gid) {
    switch (sugid) {
    case SUGID_ROOT_USER:
    case SUGID_NONROOT_USER:
        get_user_uid(sugid, uid);
        break;
    case SUGID_ROOT_GROUP:
    case SUGID_NONROOT_GROUP:
        get_group_gid(sugid, gid);
        break;
    }
}

static void set_semaphore_permissions(int id, uid_t uid, gid_t gid, int mode) {
    struct semid_ds semds;
    
    semds.sem_perm.uid = uid;
    semds.sem_perm.gid = gid;
    semds.sem_perm.mode = mode;
    
    if (semctl(id, 0, IPC_SET, &semds) != 0) e(0);
}

static void configure_semaphore_permissions(int *id, int mask, int rmask, int sugid) {
    uid_t uid = geteuid();
    gid_t gid = getegid();
    
    if (sugid == SUGID_NONE) return;
    
    update_uid_gid(sugid, &uid, &gid);
    
    set_semaphore_permissions(id[0], uid, gid, mask);
    set_semaphore_permissions(id[1], uid, gid, mask | rmask);
    set_semaphore_permissions(id[2], uid, gid, rmask);
}

static void verify_permissions(int id, int mask, uid_t uid, gid_t gid) {
    struct semid_ds semds;
    
    if (!(mask & IPC_R)) return;
    
    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_perm.mode != (SEM_ALLOC | mask)) e(0);
    if (semds.sem_perm.uid != uid) e(0);
    if (semds.sem_perm.gid != gid) e(0);
    if (semds.sem_perm.cuid != geteuid()) e(0);
    if (semds.sem_perm.cgid != getegid()) e(0);
}

static void cleanup_semaphores(int *id) {
    (void)semctl(id[0], 0, IPC_RMID);
    (void)semctl(id[1], 0, IPC_RMID);
    (void)semctl(id[2], 0, IPC_RMID);
}

static void create_semaphores(int *id, int mask, int rmask, int sugid) {
    int initial_mask = (sugid == SUGID_NONE) ? mask : 0;
    
    if ((id[0] = create_semaphore(KEY_A, initial_mask)) == -1) e(0);
    if ((id[1] = create_semaphore(KEY_B, mask | rmask)) == -1) e(0);
    if ((id[2] = create_semaphore(KEY_C, rmask)) == -1) e(0);
}

static void send_ids_to_parent(struct link *parent, int *id) {
    snd(parent, id[0]);
    snd(parent, id[1]);
    snd(parent, id[2]);
}

static void test_perm_child(struct link *parent) {
    int mask, rmask, sugid, id[3];
    uid_t uid;
    gid_t gid;
    
    while ((mask = rcv(parent)) != -1) {
        rmask = rcv(parent);
        sugid = rcv(parent);
        
        create_semaphores(id, mask, rmask, sugid);
        
        uid = geteuid();
        gid = getegid();
        
        if (sugid != SUGID_NONE) {
            update_uid_gid(sugid, &uid, &gid);
        }
        
        configure_semaphore_permissions(id, mask, rmask, sugid);
        verify_permissions(id[0], mask, uid, gid);
        send_ids_to_parent(parent, id);
        
        if (rcv(parent) != 0) e(0);
        
        cleanup_semaphores(id);
    }
}

/*
 * Perform a permission test.  The given procedure will be called for various
 * access masks, which it can use to determine whether operations on three
 * created semaphore sets should succeed or fail.  The first two semaphore sets
 * are created with appropriate privileges, the third one is not.  If the
 * 'owner_test' variable is set, the test will change slightly so as to allow
 * testing of operations that require a matching uid/cuid.
 */
#define SHIFT_USER 6
#define SHIFT_GROUP 3
#define SHIFT_OTHER 0
#define PERMISSION_MASK 0777
#define PERMISSION_BITS 7
#define TEST_CASES 7
#define TERMINATION_SIGNAL -1

typedef struct {
    int shift;
    int drop1;
    int drop2;
    int sugid;
} TestConfiguration;

static TestConfiguration get_test_configuration(int n) {
    TestConfiguration config;
    
    switch (n) {
    case 0:
        config.shift = SHIFT_USER;
        config.drop1 = DROP_ALL;
        config.drop2 = DROP_ALL;
        config.sugid = SUGID_NONE;
        break;
    case 1:
        config.shift = SHIFT_USER;
        config.drop1 = DROP_NONE;
        config.drop2 = DROP_ALL;
        config.sugid = SUGID_NONROOT_USER;
        break;
    case 2:
        config.shift = SHIFT_USER;
        config.drop1 = DROP_USER;
        config.drop2 = DROP_ALL;
        config.sugid = SUGID_ROOT_USER;
        break;
    case 3:
        config.shift = SHIFT_GROUP;
        config.drop1 = DROP_NONE;
        config.drop2 = DROP_USER;
        config.sugid = SUGID_NONE;
        break;
    case 4:
        config.shift = SHIFT_GROUP;
        config.drop1 = DROP_NONE;
        config.drop2 = DROP_ALL;
        config.sugid = SUGID_NONROOT_GROUP;
        break;
    case 5:
        config.shift = SHIFT_GROUP;
        config.drop1 = DROP_NONE;
        config.drop2 = DROP_USER;
        config.sugid = SUGID_NONROOT_GROUP;
        break;
    case 6:
        config.shift = SHIFT_OTHER;
        config.drop1 = DROP_NONE;
        config.drop2 = DROP_ALL;
        config.sugid = SUGID_NONE;
        break;
    }
    
    return config;
}

static void send_child1_configuration(struct link *child1, int mask, int rmask, int sugid) {
    snd(child1, mask);
    snd(child1, rmask);
    snd(child1, sugid);
}

static void receive_ids(struct link *child1, int *id) {
    id[0] = rcv(child1);
    id[1] = rcv(child1);
    id[2] = rcv(child1);
}

static void send_child2_configuration(struct link *child2, int owner_test, int shift, int bit, int *id) {
    snd(child2, owner_test ? shift : bit);
    snd(child2, id[0]);
    snd(child2, id[1]);
    snd(child2, id[2]);
}

static void process_permission_bit(struct link *child1, struct link *child2, 
                                  int bit, int shift, int sugid, int owner_test) {
    int mask = bit << shift;
    int rmask = PERMISSION_MASK & ~(PERMISSION_BITS << shift);
    int id[3];
    
    send_child1_configuration(child1, mask, rmask, sugid);
    receive_ids(child1, id);
    send_child2_configuration(child2, owner_test, shift, bit, id);
    
    if (rcv(child2) != 0) e(0);
    
    snd(child1, 0);
}

static void run_test_case(void (* proc)(struct link *), int owner_test, TestConfiguration config) {
    struct link child1, child2;
    int bit;
    
    spawn(&child1, test_perm_child, config.drop1);
    spawn(&child2, proc, config.drop2);
    
    for (bit = 0; bit <= PERMISSION_BITS; bit++) {
        process_permission_bit(&child1, &child2, bit, config.shift, config.sugid, owner_test);
    }
    
    snd(&child1, TERMINATION_SIGNAL);
    snd(&child2, TERMINATION_SIGNAL);
    
    collect(&child1);
    collect(&child2);
}

static void test_perm(void (* proc)(struct link *), int owner_test) {
    int n;
    
    for (n = 0; n < TEST_CASES; n++) {
        TestConfiguration config = get_test_configuration(n);
        run_test_case(proc, owner_test, config);
    }
}

/*
 * Test semget(2) permission checks.  Please note that the checks are advisory:
 * nothing keeps a process from opening a semaphore set with fewer privileges
 * than required by the operations the process subsequently issues on the set.
 */
static int check_semget_result(int result, int expected_errno) {
    return (result < 0 && (result != -1 || errno != expected_errno));
}

static int should_succeed(int bit, int tbit) {
    return (bit != 0 && (bit & tbit) == bit);
}

static void validate_semget_result(int result, int bit, int tbit, int expected_id) {
    if (check_semget_result(result, EACCES)) e(0);
    if (should_succeed(bit, tbit) != (result != -1)) e(0);
    if (result != -1 && result != expected_id) e(0);
}

static void test_semaphore_permissions(int tbit, int id[3], struct link *parent) {
    int r, bit, mask;
    
    for (bit = 0; bit <= 7; bit++) {
        mask = bit << 6;
        
        r = semget(KEY_A, 0, mask);
        validate_semget_result(r, bit, tbit, id[0]);
        
        r = semget(KEY_B, 0, mask);
        validate_semget_result(r, bit, tbit, id[1]);
        
        if (semget(KEY_C, 0, mask) != -1) e(0);
        if (errno != EACCES) e(0);
    }
    
    snd(parent, 0);
}

static void test88a_perm(struct link *parent) {
    int tbit, id[3];
    
    while ((tbit = rcv(parent)) != -1) {
        id[0] = rcv(parent);
        id[1] = rcv(parent);
        id[2] = rcv(parent);
        
        test_semaphore_permissions(tbit, id, parent);
    }
}

/*
 * Test the basic semget(2) functionality.
 */
#define KEY_A 0x12345678
#define KEY_B 0x87654321
#define SEM_ALLOC 01000
#define TEST_SEM(id, num, val, pid, ncnt, zcnt) do { \
    if (semctl((id), (num), GETVAL) != (val)) e(0); \
    if (semctl((id), (num), GETPID) != (pid)) e(0); \
    if (semctl((id), (num), GETNCNT) != (ncnt)) e(0); \
    if (semctl((id), (num), GETZCNT) != (zcnt)) e(0); \
} while(0)

static int create_semaphore(key_t key, int nsems, int flags)
{
    return semget(key, nsems, flags);
}

static int remove_semaphore(int id)
{
    return semctl(id, 0, IPC_RMID);
}

static void remove_leftover_semaphore(key_t key)
{
    int id = semget(key, 0, 0600);
    if (id >= 0 && remove_semaphore(id) == -1)
        e(0);
}

static void verify_unique_ids(int id1, int id2, int id3)
{
    if (id1 == id2) e(0);
    if (id2 == id3) e(0);
    if (id1 == id3) e(0);
}

static void test_private_keys(void)
{
    int id[3];
    
    if ((id[0] = create_semaphore(IPC_PRIVATE, 1, IPC_CREAT | 0600)) < 0) e(0);
    if ((id[1] = create_semaphore(IPC_PRIVATE, 1, IPC_CREAT | IPC_EXCL | 0600)) < 0) e(0);
    if ((id[2] = create_semaphore(IPC_PRIVATE, 1, 0600)) < 0) e(0);
    
    verify_unique_ids(id[0], id[1], id[2]);
    
    if (remove_semaphore(id[0]) != 0) e(0);
    if (remove_semaphore(id[1]) != 0) e(0);
    if (remove_semaphore(id[2]) != 0) e(0);
}

static void test_non_private_keys(void)
{
    int id[3];
    
    if (semget(KEY_A, 1, 0600) != -1) e(0);
    if (errno != ENOENT) e(0);
    
    if ((id[0] = create_semaphore(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0600)) < 0) e(0);
    
    if (semget(KEY_B, 1, 0600) != -1) e(0);
    if (errno != ENOENT) e(0);
    
    if ((id[1] = create_semaphore(KEY_B, 1, IPC_CREAT | 0600)) < 0) e(0);
    
    if (id[0] == id[1]) e(0);
    
    if ((id[2] = semget(KEY_A, 1, 0600)) < 0) e(0);
    if (id[2] != id[0]) e(0);
    
    if ((id[2] = create_semaphore(KEY_B, 1, IPC_CREAT | 0600)) < 0) e(0);
    if (id[2] != id[1]) e(0);
    
    if (create_semaphore(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0600) != -1) e(0);
    if (errno != EEXIST) e(0);
    
    if (remove_semaphore(id[0]) != 0) e(0);
    if (remove_semaphore(id[1]) != 0) e(0);
}

static void verify_no_id_collisions(int *idp, unsigned int count, int new_id)
{
    unsigned int j;
    for (j = 0; j < count; j++)
        if (new_id == idp[j]) e(0);
}

static void test_semaphore_limit(struct seminfo *seminfo)
{
    int *idp;
    unsigned int i;
    
    if (seminfo->semmni < 3 || seminfo->semmni > USHRT_MAX) e(0);
    
    if ((idp = malloc(sizeof(int) * (seminfo->semmni + 1))) == NULL) e(0);
    
    for (i = 0; i < seminfo->semmni + 1; i++) {
        if ((idp[i] = create_semaphore(KEY_A + i, 1, IPC_CREAT | 0600)) < 0)
            break;
        verify_no_id_collisions(idp, i, idp[i]);
    }
    
    if (errno != ENOSPC) e(0);
    if (i < 3) e(0);
    if (i == seminfo->semmni + 1) e(0);
    
    while (i-- > 0)
        if (remove_semaphore(idp[i]) != 0) e(0);
    
    free(idp);
}

static void test_semaphore_bounds(struct seminfo *seminfo)
{
    int id[2];
    
    if (create_semaphore(KEY_A, -1, IPC_CREAT | 0600) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (create_semaphore(KEY_A, 0, IPC_CREAT | 0600) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (seminfo->semmsl < 3 || seminfo->semmsl > USHRT_MAX) e(0);
    if (create_semaphore(KEY_A, seminfo->semmsl + 1, IPC_CREAT | 0600) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if ((id[0] = create_semaphore(KEY_A, seminfo->semmsl, IPC_CREAT | 0600)) < 0) e(0);
    if (remove_semaphore(id[0]) != 0) e(0);
    
    if ((id[0] = create_semaphore(KEY_A, 2, IPC_CREAT | 0600)) < 0) e(0);
    
    if ((id[1] = semget(KEY_A, 0, 0600)) < 0) e(0);
    if (id[0] != id[1]) e(0);
    
    if ((id[1] = semget(KEY_A, 1, 0600)) < 0) e(0);
    if (id[0] != id[1]) e(0);
    
    if ((id[1] = semget(KEY_A, 2, 0600)) < 0) e(0);
    if (id[0] != id[1]) e(0);
    
    if (semget(KEY_A, 3, 0600) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (semget(KEY_A, seminfo->semmsl + 1, 0600) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (remove_semaphore(id[0]) != 0) e(0);
}

static void verify_semds_permissions(struct semid_ds *semds, key_t expected_key, int expected_mode)
{
    if (semds->sem_perm.uid != geteuid()) e(0);
    if (semds->sem_perm.gid != getegid()) e(0);
    if (semds->sem_perm.cuid != geteuid()) e(0);
    if (semds->sem_perm.cgid != getegid()) e(0);
    if (semds->sem_perm.mode != (SEM_ALLOC | expected_mode)) e(0);
    if (semds->sem_perm._key != expected_key) e(0);
}

static void verify_semaphore_values(int id, struct semid_ds *semds)
{
    unsigned int i;
    for (i = 0; i < semds->sem_nsems; i++)
        TEST_SEM(id, i, 0, 0, 0, 0);
}

static void test_initial_values(struct seminfo *seminfo)
{
    struct semid_ds semds;
    time_t now;
    int id[2];
    
    time(&now);
    if (seminfo->semmns < 3 + seminfo->semmsl) e(0);
    
    if ((id[0] = create_semaphore(IPC_PRIVATE, 3, IPC_CREAT | IPC_EXCL | 0642)) < 0) e(0);
    if ((id[1] = create_semaphore(KEY_A, seminfo->semmsl, IPC_CREAT | 0613)) < 0) e(0);
    
    if (semctl(id[0], 0, IPC_STAT, &semds) != 0) e(0);
    verify_semds_permissions(&semds, IPC_PRIVATE, 0642);
    if (semds.sem_nsems != 3) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);
    verify_semaphore_values(id[0], &semds);
    
    if (semctl(id[1], 0, IPC_STAT, &semds) != 0) e(0);
    verify_semds_permissions(&semds, KEY_A, 0613);
    if (semds.sem_nsems != seminfo->semmsl) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);
    verify_semaphore_values(id[1], &semds);
    
    if (remove_semaphore(id[1]) != 0) e(0);
    if (remove_semaphore(id[0]) != 0) e(0);
}

static void test_superuser_permissions(void)
{
    int id[2];
    
    if ((id[0] = create_semaphore(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0000)) < 0) e(0);
    
    if ((id[1] = semget(KEY_A, 0, 0600)) < 0) e(0);
    if (id[0] != id[1]) e(0);
    
    if ((id[1] = semget(KEY_A, 0, 0000)) < 0) e(0);
    if (id[0] != id[1]) e(0);
    
    if (remove_semaphore(id[0]) != 0) e(0);
}

static void test88a(void)
{
    struct seminfo seminfo;
    
    subtest = 0;
    
    test_private_keys();
    
    remove_leftover_semaphore(KEY_A);
    remove_leftover_semaphore(KEY_B);
    
    test_non_private_keys();
    
    if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
    
    test_semaphore_limit(&seminfo);
    test_semaphore_bounds(&seminfo);
    test_initial_values(&seminfo);
    test_superuser_permissions();
    
    test_perm(test88a_perm, 0);
}

/*
 * Test semop(2) permission checks.
 */
static void init_sops_case(struct sembuf *sops, size_t *nsops, int *bit, int case_num) {
	memset(sops, 0, sizeof(struct sembuf) * 2);
	
	switch (case_num) {
	case 0:
		*nsops = 1;
		*bit = 4;
		break;
	case 1:
		sops[0].sem_op = 1;
		*nsops = 1;
		*bit = 2;
		break;
	case 2:
		sops[0].sem_op = -1;
		*nsops = 1;
		*bit = 2;
		break;
	case 3:
		sops[1].sem_op = 1;
		*nsops = 2;
		*bit = 6;
		break;
	case 4:
		sops[0].sem_num = 1;
		sops[1].sem_op = -1;
		*nsops = 2;
		*bit = 6;
		break;
	case 5:
		sops[1].sem_num = 1;
		*nsops = 2;
		*bit = 4;
		break;
	case 6:
		sops[0].sem_op = 1;
		sops[1].sem_op = -1;
		*nsops = 2;
		*bit = 2;
		break;
	case 7:
		sops[0].sem_num = USHRT_MAX;
		*nsops = 2;
		*bit = 4;
		break;
	}
}

static int adjust_result_for_case7(int result, int case_num) {
	if (case_num == 7 && result == -1 && errno == EFBIG) {
		return 0;
	}
	return result;
}

static void verify_semop_result(int result, int bit, int tbit) {
	if (result < 0 && (result != -1 || errno != EACCES)) {
		e(0);
	}
	if (((bit & tbit) == bit) != (result != -1)) {
		e(0);
	}
}

static void verify_semop_eacces(int result) {
	if (result != -1) {
		e(0);
	}
	if (errno != EACCES) {
		e(0);
	}
}

static void test_semop_with_id(int id, struct sembuf *sops, size_t nsops, int bit, int tbit, int case_num) {
	int r = semop(id, sops, nsops);
	r = adjust_result_for_case7(r, case_num);
	verify_semop_result(r, bit, tbit);
}

static void test88b_perm(struct link *parent) {
	struct sembuf sops[2];
	size_t nsops;
	int i, tbit, bit, id[3];
	
	while ((tbit = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);
		
		for (i = 0; i < 8; i++) {
			init_sops_case(sops, &nsops, &bit, i);
			
			test_semop_with_id(id[0], sops, nsops, bit, tbit, i);
			test_semop_with_id(id[1], sops, nsops, bit, tbit, i);
			
			verify_semop_eacces(semop(id[2], sops, nsops));
		}
		
		snd(parent, 0);
	}
}

/*
 * Signal handler.
 */
static void
got_signal(int sig)
{
    if (sig != SIGHUP) {
        e(0);
    }
    if (nr_signals != 0) {
        e(0);
    }
    nr_signals++;
}

/*
 * Child process for semop(2) tests, mainly testing blocking operations.
 */
static void setup_sops(struct sembuf *sops, int num, int op, int flg) {
    sops->sem_num = num;
    sops->sem_op = op;
    sops->sem_flg = flg;
}

static void perform_semop(int id, struct sembuf *sops, int count) {
    if (semop(id, sops, count) != 0) e(0);
}

static void perform_semop_fail(int id, struct sembuf *sops, int count, int expected_errno) {
    if (semop(id, sops, count) != -1) e(0);
    if (errno != expected_errno) e(0);
}

static void verify_parent_message(struct link *parent, int expected) {
    if (rcv(parent) != expected) e(0);
}

static void setup_signal_handler(void) {
    struct sigaction act;
    memset(&act, 0, sizeof(act));
    act.sa_handler = got_signal;
    sigfillset(&act.sa_mask);
    if (sigaction(SIGHUP, &act, NULL) != 0) e(0);
}

static void test_case_1(int id, struct link *parent) {
    struct sembuf sops[1];
    memset(sops, 0, sizeof(sops));
    perform_semop(id, sops, 1);
    verify_parent_message(parent, 1);
    sops[0].sem_op = -3;
    perform_semop(id, sops, 1);
}

static void test_case_2(int id, struct link *parent) {
    struct sembuf sops[3];
    verify_parent_message(parent, 2);
    setup_sops(&sops[0], 2, 2, 0);
    setup_sops(&sops[1], 1, -1, 0);
    setup_sops(&sops[2], 0, 1, 0);
    perform_semop(id, sops, 3);
}

static void test_case_3(int id, struct link *parent) {
    struct sembuf sops[5];
    verify_parent_message(parent, 3);
    setup_sops(&sops[0], 1, 0, 0);
    setup_sops(&sops[1], 1, 1, 0);
    setup_sops(&sops[2], 0, 0, 0);
    setup_sops(&sops[3], 2, 0, 0);
    setup_sops(&sops[4], 2, 1, 0);
    perform_semop(id, sops, 5);
}

static void test_case_4(int id, struct link *parent) {
    struct sembuf sops[2];
    verify_parent_message(parent, 4);
    setup_sops(&sops[0], 1, -2, 0);
    setup_sops(&sops[1], 2, 0, 0);
    perform_semop(id, sops, 2);
}

static void test_case_5(int id, struct link *parent) {
    struct sembuf sops[2];
    verify_parent_message(parent, 5);
    setup_sops(&sops[0], 0, -1, 0);
    setup_sops(&sops[1], 1, -1, IPC_NOWAIT);
    perform_semop(id, sops, 2);
}

static void test_case_6(int id, struct link *parent) {
    struct sembuf sops[2];
    verify_parent_message(parent, 6);
    setup_sops(&sops[0], 1, 0, 0);
    setup_sops(&sops[1], 0, 0, IPC_NOWAIT);
    perform_semop_fail(id, sops, 2, EAGAIN);
}

static void test_case_7(int id, struct link *parent) {
    struct sembuf sops[2];
    verify_parent_message(parent, 7);
    setup_sops(&sops[0], 0, 0, 0);
    setup_sops(&sops[1], 1, 1, 0);
    perform_semop(id, sops, 2);
}

static void test_case_8(int id, struct link *parent) {
    struct sembuf sops[2];
    verify_parent_message(parent, 8);
    setup_sops(&sops[0], 0, -1, 0);
    setup_sops(&sops[1], 1, 2, 0);
    perform_semop_fail(id, sops, 2, ERANGE);
}

static void test_case_9(int id, struct link *parent) {
    struct sembuf sops[3];
    setup_signal_handler();
    verify_parent_message(parent, 9);
    memset(sops, 0, sizeof(sops));
    setup_sops(&sops[0], 0, 0, 0);
    setup_sops(&sops[1], 0, 1, 0);
    setup_sops(&sops[2], 1, 0, 0);
    if (semop(id, sops, 3) != -1)
    if (errno != EINTR) e(0);
    if (nr_signals != 1) e(0);
    TEST_SEM(id, 0, 0, parent->pid, 0, 0);
    TEST_SEM(id, 1, 1, parent->pid, 0, 0);
}

static void test_case_10(int id, struct link *parent) {
    struct sembuf sops[1];
    verify_parent_message(parent, 10);
    memset(sops, 0, sizeof(sops));
    sops[0].sem_op = -3;
    perform_semop_fail(id, sops, 1, EIDRM);
}

static void test_case_11(int id, struct link *parent) {
    struct sembuf sops[2];
    id = rcv(parent);
    setup_sops(&sops[0], 0, -1, 0);
    setup_sops(&sops[1], 1, 1, 0);
    perform_semop_fail(id, sops, 2, ERANGE);
    verify_parent_message(parent, 11);
    setup_sops(&sops[0], 1, 0, 0);
    setup_sops(&sops[1], 0, -1, 0);
    perform_semop(id, sops, 2);
}

static void test_case_12(int id, struct link *parent) {
    struct sembuf sops[2];
    id = rcv(parent);
    setup_sops(&sops[0], 0, -1, 0);
    setup_sops(&sops[1], 1, 0, 0);
    perform_semop(id, sops, 2);
    snd(parent, errct);
    verify_parent_message(parent, 12);
    setup_sops(&sops[0], 1, -1, 0);
    setup_sops(&sops[1], 0, 3, 0);
    (void)semop(id, sops, 2);
    e(0);
}

static void test88b_child(struct link *parent) {
    int id = rcv(parent);
    test_case_1(id, parent);
    test_case_2(id, parent);
    test_case_3(id, parent);
    test_case_4(id, parent);
    test_case_5(id, parent);
    test_case_6(id, parent);
    test_case_7(id, parent);
    test_case_8(id, parent);
    test_case_9(id, parent);
    test_case_10(id, parent);
    test_case_11(id, parent);
    test_case_12(id, parent);
}

/*
 * Test the basic semop(2) functionality.
 */
#define WAIT_USECS 250000
#define SEMOPM_OFFSET 1
#define INVALID_SEMNUM_1 1
#define INVALID_SEMNUM_MAX USHRT_MAX
#define SEMOP_TEST_2 2
#define SEMOP_TEST_3 3
#define SEMOP_TEST_4 4
#define SEMOP_TEST_5 5
#define SEMOP_TEST_6 6
#define SEMOP_TEST_7 7
#define SEMOP_TEST_8 8
#define SEMOP_TEST_9 9
#define SEMOP_TEST_10 10
#define SEMOP_TEST_11 11
#define SEMOP_TEST_12 12
#define SEMMNI_SEQ_OFFSET 10

static int allocate_sembuf(struct sembuf **sops, struct seminfo *seminfo)
{
	size_t size;
	
	if (semctl(0, 0, IPC_INFO, seminfo) == -1) return -1;
	if (seminfo->semopm < 3 || seminfo->semopm > USHRT_MAX) return -1;
	
	size = sizeof((*sops)[0]) * (seminfo->semopm + SEMOPM_OFFSET);
	if ((*sops = malloc(size)) == NULL) return -1;
	memset(*sops, 0, size);
	return 0;
}

static void test_null_operations(int id)
{
	struct sembuf *sops2;
	
	if (semop(id, NULL, 0) != 0) e(0);
	if (semop(id, NULL, 1) != -1) e(0);
	if (errno != EFAULT) e(0);
	if (semop(id, bad_ptr, 1) != -1) e(0);
	if (errno != EFAULT) e(0);
	
	memset(page_ptr, 0, page_size);
	sops2 = ((struct sembuf *)bad_ptr) - 1;
	sops2->sem_op = 1;
	if (semop(id, sops2, 2) != -1) e(0);
	if (errno != EFAULT) e(0);
}

static void test_operation_limits(int id, struct sembuf *sops, struct seminfo *seminfo)
{
	if (semop(id, sops, seminfo->semopm) != 0) e(0);
	if (semop(id, sops, seminfo->semopm + 1) != -1) e(0);
	if (errno != E2BIG) e(0);
	if (semop(id, sops, SIZE_MAX) != -1) e(0);
	if (errno != E2BIG) e(0);
}

static void test_semaphore_range(int id, struct sembuf *sops)
{
	sops[1].sem_num = INVALID_SEMNUM_1;
	if (semop(id, sops, 2) != -1) e(0);
	if (errno != EFBIG) e(0);
	
	sops[1].sem_num = INVALID_SEMNUM_MAX;
	if (semop(id, sops, 2) != -1) e(0);
	if (errno != EFBIG) e(0);
}

static void test_value_limits(int id, struct sembuf *sops, struct seminfo *seminfo)
{
	sops[0].sem_flg = IPC_NOWAIT;
	
	if (seminfo->semvmx < SHRT_MAX) {
		sops[0].sem_op = seminfo->semvmx + 1;
		if (semop(id, sops, 1) != -1) e(0);
		if (errno != ERANGE) e(0);
		if (semctl(id, 0, GETVAL) != 0) e(0);
	}
	
	sops[0].sem_op = seminfo->semvmx;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != seminfo->semvmx) e(0);
	
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != -1) e(0);
	if (errno != ERANGE) e(0);
	if (semctl(id, 0, GETVAL) != seminfo->semvmx) e(0);
	
	sops[0].sem_op = seminfo->semvmx;
	if (semop(id, sops, 1) != -1) e(0);
	if (errno != ERANGE) e(0);
	if (semctl(id, 0, GETVAL) != seminfo->semvmx) e(0);
	
	sops[0].sem_op = SHRT_MAX;
	if (semop(id, sops, 1) != -1) e(0);
	if (errno != ERANGE) e(0);
	if (semctl(id, 0, GETVAL) != seminfo->semvmx) e(0);
	
	if (seminfo->semvmx < -(int)SHRT_MIN) {
		sops[0].sem_op = -seminfo->semvmx - 1;
		if (semop(id, sops, 1) != -1) e(0);
		if (errno != EAGAIN) e(0);
		if (semctl(id, 0, GETVAL) != seminfo->semvmx) e(0);
	}
	
	sops[0].sem_op = -seminfo->semvmx;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != 0) e(0);
}

static void test_basic_nonblocking(int id, struct sembuf *sops)
{
	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != 0) e(0);
	
	sops[0].sem_op = 2;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != 2) e(0);
	
	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != -1) e(0);
	if (errno != EAGAIN) e(0);
	
	sops[0].sem_op = -3;
	if (semop(id, sops, 1) != -1) e(0);
	if (errno != EAGAIN) e(0);
	
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != 3) e(0);
	
	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != 2) e(0);
	
	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != -1) e(0);
	if (errno != EAGAIN) e(0);
	
	sops[0].sem_op = -2;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != 0) e(0);
	
	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != 0) e(0);
}

static void test_invalid_ids(struct seminfo *seminfo)
{
	struct semid_ds semds;
	int id;
	
	if (semop(-1, NULL, 0) != -1) e(0);
	if (errno != EINVAL) e(0);
	
	if (semop(INT_MIN, NULL, 0) != -1) e(0);
	if (errno != EINVAL) e(0);
	
	memset(&semds, 0, sizeof(semds));
	id = IXSEQ_TO_IPCID(seminfo->semmni, semds.sem_perm);
	if (semop(id, NULL, 0) != -1) e(0);
	if (errno != EINVAL) e(0);
}

static void verify_initial_state(int id, time_t now)
{
	struct semid_ds semds;
	
	TEST_SEM(id, 0, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);
}

static void verify_otime_update(int id, time_t now)
{
	struct semid_ds semds;
	
	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime < now || semds.sem_otime >= now + SEMMNI_SEQ_OFFSET) e(0);
}

static void perform_blocking_test_1(int id, struct sembuf *sops, struct link *child)
{
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);
	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	
	snd(child, id);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 1, getpid(), 0, 1);
	
	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) e(0);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, child->pid, 0, 0);
	
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);
	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	
	snd(child, 1);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 1, getpid(), 1, 0);
	
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 2, getpid(), 1, 0);
	
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, child->pid, 0, 0);
}

static void perform_blocking_test_2(int id, struct sembuf *sops, struct link *child)
{
	if (semop(id, sops, 1) != 0) e(0);
	
	snd(child, SEMOP_TEST_2);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, 0, 1, 0);
	TEST_SEM(id, 2, 0, 0, 0, 0);
	
	sops[0].sem_num = 1;
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 1, child->pid, 0, 0);
	TEST_SEM(id, 1, 0, child->pid, 0, 0);
	TEST_SEM(id, 2, 2, child->pid, 0, 0);
}

static void perform_blocking_test_3(int id, struct sembuf *sops, struct link *child)
{
	snd(child, SEMOP_TEST_3);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 1, child->pid, 0, 1);
	TEST_SEM(id, 1, 0, child->pid, 0, 0);
	TEST_SEM(id, 2, 2, child->pid, 0, 0);
	
	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 2;
	sops[1].sem_op = -2;
	if (semop(id, sops, 2) != 0) e(0);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, child->pid, 0, 0);
	TEST_SEM(id, 1, 1, child->pid, 0, 0);
	TEST_SEM(id, 2, 1, child->pid, 0, 0);
}

static void perform_blocking_test_4(int id, struct sembuf *sops, struct link *child)
{
	snd(child, SEMOP_TEST_4);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, child->pid, 0, 0);
	TEST_SEM(id, 1, 1, child->pid, 1, 0);
	TEST_SEM(id, 2, 1, child->pid, 0, 0);
	
	sops[0].sem_num = 1;
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, child->pid, 0, 0);
	TEST_SEM(id, 1, 2, getpid(), 0, 0);
	TEST_SEM(id, 2, 1, child->pid, 0, 1);
	
	sops[0].sem_num = 2;
	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) e(0);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, child->pid, 0, 0);
	TEST_SEM(id, 1, 0, child->pid, 0, 0);
	TEST_SEM(id, 2, 0, child->pid, 0, 0);
}

static void perform_blocking_test_5(int id, struct sembuf *sops, struct link *child)
{
	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 1;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != 0) e(0);
	
	snd(child, SEMOP_TEST_5);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, getpid(), 1, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);
	
	sops[0].sem_num = 0;
	sops[0].sem_op = 1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) e(0);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, child->pid, 0, 0);
	TEST_SEM(id, 1, 0, child->pid, 0, 0);
}

static void perform_blocking_test_6(int id, struct sembuf *sops, struct link *child)
{
	sops[0].sem_num = 0;
	sops[0].sem_op = 1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) e(0);
	
	snd(child, SEMOP_TEST_6);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	TEST_SEM(id, 1, 1, getpid(), 0, 1);
	
	sops[0].sem_num = 1;
	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) e(0);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);
}

static void test_invalid_semnum(int id, struct sembuf *sops)
{
	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 4;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != -1) e(0);
	if (errno != EFBIG) e(0);
}

static void perform_overflow_test_7(int id, struct sembuf *sops, struct link *child, struct seminfo *seminfo)
{
	sops[0].sem_num = 1;
	sops[0].sem_op = seminfo->semvmx;
	if (semop(id, sops, 1) != 0) e(0);
	
	snd(child, SEMOP_TEST_7);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 1, getpid(), 0, 1);
	TEST_SEM(id, 1, seminfo->semvmx, getpid(), 0, 0);
	
	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = -1;
	if (semop(id, sops, 2) != 0) e(0);
	TEST_SEM(id, 0, 0, child->pid, 0, 0);
	TEST_SEM(id, 1, seminfo->semvmx, child->pid, 0, 0);
	
	sops[0].sem_num = 1;
	sops[0].sem_op = -2;
	if (semop(id, sops, 1) != 0) e(0);
}

static void perform_overflow_test_8(int id, struct sembuf *sops, struct link *child, struct seminfo *seminfo)
{
	snd(child, SEMOP_TEST_8);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, child->pid, 1, 0);
	TEST_SEM(id, 1, seminfo->semvmx - 2, getpid(), 0, 0);
	
	sops[0].sem_num = 0;
	sops[0].sem_op = 1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) e(0);
	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	TEST_SEM(id, 1, seminfo->semvmx - 1, getpid(), 0, 0);
	
	sops[0].sem_num = 0;
	sops[0].sem_op = seminfo->semvmx - 1;
	sops[1].sem_num = 0;
	sops[1].sem_op = seminfo->semvmx - 1;
	sops[2].sem_num = 0;
	sops[2].sem_op = 2;
	if (semop(id, sops, 3) != -1) e(0);
	if (errno != ERANGE) e(0);
	TEST_SEM(id, 0, 1, getpid(), 0, 0);
}

static void test_signal_interrupt(int id, struct sembuf *sops, struct link *child)
{
	if (semctl(id, 1, SETVAL, 0) != 0) e(0);
	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) e(0);
	
	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 1, getpid(), 0, 0);
	
	snd(child, SEMOP_TEST_9);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 1, getpid(), 0, 1);
	
	kill(child->pid, SIGHUP);
}

static void test_eidrm(int id, struct link *child)
{
	snd(child, SEMOP_TEST_10);
	usleep(WAIT_USECS);
	if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

static void test_setval_wakeup(struct link *child, struct seminfo *seminfo)
{
	struct semid_ds semds;
	time_t now;
	int id;
	
	if ((id = semget(IPC_PRIVATE, 2, 0600)) == -1) e(0);
	
	snd(child, id);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);
	
	if (semctl(id, 1, SETVAL, seminfo->semvmx) != 0) e(0);
	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, seminfo->semvmx, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);
	
	if (semctl(id, 0, SETVAL, 1) != 0) e(0);
	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, seminfo->semvmx, 0, 0, 0);
	
	if (semctl(id, 0, SETVAL, 0) != 0) e(0);
	
	snd(child, SEMOP_TEST_11);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, seminfo->semvmx, 0, 0, 1);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);
	
	if (semctl(id, 1, SETVAL, 0) != 0) e(0);
	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);
	
	time(&now);
	if (semctl(id, 0, SETVAL, 2) != 0) e(0);
	TEST_SEM(id, 0, 1, child->pid, 0, 0);
	TEST_SEM(id, 1, 0, child->pid, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime < now || semds.sem_otime >= now + SEMMNI_SEQ_OFFSET) e(0);
	
	if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

static void test_setall_wakeup(struct link *child)
{
	struct semid_ds semds;
	unsigned short val[2];
	time_t now;
	int id;
	
	if ((id = semget(IPC_PRIVATE, 2, 0600)) == -1) e(0);
	
	snd(child, id);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	
	val[0] = 1;
	val[1] = 1;
	if (semctl(id, 0, SETALL, val) != 0) e(0);
	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, 1, 0, 0, 1);
	
	val[0] = 0;
	val[1] = 1;
	if (semctl(id, 0, SETALL, val) != 0) e(0);
	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 1, 0, 0, 0);
	
	val[0] = 1;
	val[1] = 1;
	if (semctl(id, 0, SETALL, val) != 0) e(0);
	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, 1, 0, 0, 1);
	
	val[0] = 0;
	val[1] = 0;
	if (semctl(id, 0, SETALL, val) != 0) e(0);
	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);
	
	time(&now);
	val[0] = 1;
	val[1] = 0;
	if (semctl(id, 0, SETALL, val) != 0) e(0);
	TEST_SEM(id, 0, 0, child->pid, 0, 0);
	TEST_SEM(id, 1, 0, child->pid, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime < now || semds.sem_otime >= now + SEMMNI_SEQ_OFFSET) e(0);
}

static void test_child_termination(int id, struct sembuf *sops, struct link *child)
{
	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 1;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != 0) e(0);
	
	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);
	
	if (rcv(child) != 0) e(0);
	
	snd(child, SEMOP_TEST_12);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 1, 0);
	
	terminate(child);
	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);
	
	if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

static void test88b(void)
{
	struct seminfo seminfo;
	struct semid_ds semds;
	struct sembuf *sops, *sops2;
	struct link child;
	time_t now;
	int id;

	subtest = 1;

	if (allocate_sembuf(&sops, &seminfo) != 0) e(0);
	
	if ((id = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600)) == -1) e(0);
	
	test_null_operations(id);
	
	verify_initial_state(id, 0);
	
	time(&now);
	if (semop(id, sops, 1) != 0) e(0);
	
	verify_otime_update(id, now);
	
	test_operation_limits(id, sops, &seminfo);
	test_semaphore_range(id, sops);
	
	if (seminfo.semvmx < 3 || seminfo.semvmx > SHRT_MAX) e(0);
	
	test_value_limits(id, sops, &seminfo);
	test_basic_nonblocking(id, sops);
	
	sops2 = ((struct sembuf *)bad_ptr) - 1;
	

/*
 * Test semctl(2) permission checks, part 1: regular commands.
 */
#define READ_PERMISSION_BIT 4
#define WRITE_PERMISSION_BIT 2
#define EXPECTED_ERROR_NOT_FOUND -1

static int check_semctl_result(int result, int expected_bit, int test_bit)
{
	if (result < 0 && (result != EXPECTED_ERROR_NOT_FOUND || errno != EACCES)) 
		e(0);
	if (((expected_bit & test_bit) == expected_bit) != (result != EXPECTED_ERROR_NOT_FOUND)) 
		e(0);
	return result;
}

static void check_semctl_denied(int id, int semnum, int cmd, void *arg)
{
	int result = (arg == NULL) ? semctl(id, semnum, cmd) : semctl(id, semnum, cmd, arg);
	if (result != EXPECTED_ERROR_NOT_FOUND) 
		e(0);
	if (errno != EACCES) 
		e(0);
}

static void test_read_only_commands(int *id, int tbit)
{
	static const int cmds[] = { GETVAL, GETPID, GETNCNT, GETZCNT };
	int i;
	
	for (i = 0; i < __arraycount(cmds); i++) {
		check_semctl_result(semctl(id[0], 0, cmds[i]), READ_PERMISSION_BIT, tbit);
		check_semctl_result(semctl(id[1], 0, cmds[i]), READ_PERMISSION_BIT, tbit);
		check_semctl_denied(id[2], 0, cmds[i], NULL);
	}
}

static void test_setval_command(int *id, int tbit)
{
	check_semctl_result(semctl(id[0], 0, SETVAL, 0), WRITE_PERMISSION_BIT, tbit);
	check_semctl_result(semctl(id[1], 0, SETVAL, 0), WRITE_PERMISSION_BIT, tbit);
	check_semctl_denied(id[2], 0, SETVAL, (void *)0);
}

static void test_pointer_command(int *id, int tbit, int cmd, void *ptr, int required_bit)
{
	check_semctl_result(semctl(id[0], 0, cmd, ptr), required_bit, tbit);
	check_semctl_result(semctl(id[1], 0, cmd, ptr), required_bit, tbit);
	check_semctl_denied(id[2], 0, cmd, ptr);
}

static void test_pointer_commands(int *id, int tbit)
{
	struct semid_ds semds;
	unsigned short val[3];
	
	memset(val, 0, sizeof(val));
	
	test_pointer_command(id, tbit, GETALL, val, READ_PERMISSION_BIT);
	test_pointer_command(id, tbit, SETALL, val, WRITE_PERMISSION_BIT);
	test_pointer_command(id, tbit, IPC_STAT, &semds, READ_PERMISSION_BIT);
}

#ifndef IPCID_TO_IX
#define IPCID_TO_IX(id)		((id) & 0xffff)
#endif

static void test_sem_stat_command(int *id, int tbit)
{
	struct semid_ds semds;
	
	check_semctl_result(semctl(IPCID_TO_IX(id[0]), 0, SEM_STAT, &semds), 
			    READ_PERMISSION_BIT, tbit);
	check_semctl_result(semctl(IPCID_TO_IX(id[1]), 0, SEM_STAT, &semds), 
			    READ_PERMISSION_BIT, tbit);
	check_semctl_denied(IPCID_TO_IX(id[2]), 0, SEM_STAT, &semds);
}

static void test_info_commands(void)
{
	struct seminfo seminfo;
	
	if (semctl(0, 0, IPC_INFO, &seminfo) == EXPECTED_ERROR_NOT_FOUND) 
		e(0);
	if (semctl(0, 0, SEM_INFO, &seminfo) == EXPECTED_ERROR_NOT_FOUND) 
		e(0);
}

static void test88c_perm1(struct link * parent)
{
	int tbit, id[3];

	while ((tbit = rcv(parent)) != EXPECTED_ERROR_NOT_FOUND) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		test_read_only_commands(id, tbit);
		test_setval_command(id, tbit);
		test_pointer_commands(id, tbit);
		test_sem_stat_command(id, tbit);
		test_info_commands();

		snd(parent, 0);
	}
}

/*
 * Test semctl(2) permission checks, part 2: the IPC_SET command.
 */
static int check_semctl_result(int result, int expected_shift)
{
	if (result < 0 && (result != -1 || errno != EPERM)) e(0);
	if ((expected_shift == 6) != (result != -1)) e(0);
	return result;
}

static void perform_ipc_set(int id, int shift)
{
	struct semid_ds semds;
	int r;
	
	memset(&semds, 0, sizeof(semds));
	r = semctl(id, 0, IPC_SET, &semds);
	check_semctl_result(r, shift);
}

static void
test88c_perm2(struct link * parent)
{
	int shift, id[3];
	
	while ((shift = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);
		
		perform_ipc_set(id[0], shift);
		perform_ipc_set(id[1], shift);
		perform_ipc_set(id[2], shift);
		
		snd(parent, 0);
	}
}

/*
 * Test semctl(2) permission checks, part 3: the IPC_RMID command.
 */
static int receive_id(struct link *parent)
{
    return rcv(parent);
}

static void receive_three_ids(struct link *parent, int *id)
{
    id[0] = receive_id(parent);
    id[1] = receive_id(parent);
    id[2] = receive_id(parent);
}

static int is_valid_semctl_result(int result)
{
    return !(result < 0 && (result != -1 || errno != EPERM));
}

static void verify_semctl_permission(int id, int shift)
{
    int result = semctl(id, 0, IPC_RMID);
    
    if (!is_valid_semctl_result(result)) {
        e(0);
    }
    
    const int expected_success = (shift == 6);
    const int actual_success = (result != -1);
    
    if (expected_success != actual_success) {
        e(0);
    }
}

static void test88c_perm3(struct link *parent)
{
    int shift, id[3];
    
    while ((shift = receive_id(parent)) != -1) {
        receive_three_ids(parent, id);
        
        verify_semctl_permission(id[0], shift);
        verify_semctl_permission(id[1], shift);
        verify_semctl_permission(id[2], shift);
        
        snd(parent, 0);
    }
}

/*
 * Test the basic semctl(2) functionality.
 */
#define CMD_GETVAL 0
#define CMD_GETPID 1
#define CMD_GETNCNT 2
#define CMD_GETZCNT 3

#define INITIAL_VAL_MARKER 0x5a
#define VAL_MARKER 0x5b
#define DEFAULT_PERMS 0600
#define TEST_PERMS 0642
#define ALT_PERMS 0712

static int create_and_remove_semaphore(void) {
    int id = semget(IPC_PRIVATE, 1, DEFAULT_PERMS);
    if (id < 0) e(0);
    if (semctl(id, 0, IPC_RMID) != 0) e(0);
    return id;
}

static int create_invalid_id(struct seminfo *seminfo) {
    struct semid_ds semds;
    memset(&semds, 0, sizeof(semds));
    return IXSEQ_TO_IPCID(seminfo->semmni, semds.sem_perm);
}

static void wait_for_time_change(time_t current) {
    time_t now;
    while (time(&now) == current)
        usleep(250000);
}

static void test_invalid_id_command(int badid1, int badid2, int cmd) {
    if (semctl(badid1, 0, cmd) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (semctl(badid2, 0, cmd) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (semctl(-1, 0, cmd) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (semctl(INT_MIN, 0, cmd) != -1) e(0);
    if (errno != EINVAL) e(0);
}

static void test_get_commands(int id, int badid1, int badid2, time_t now) {
    static const int cmds[] = { GETVAL, GETPID, GETNCNT, GETZCNT };
    struct semid_ds semds;
    unsigned int i, j;
    
    for (i = 0; i < __arraycount(cmds); i++) {
        for (j = 0; j < 3; j++)
            if (semctl(id, j, cmds[i]) != 0) e(0);
        
        test_invalid_id_command(badid1, badid2, cmds[i]);
        
        if (semctl(id, -1, cmds[i]) != -1) e(0);
        if (errno != EINVAL) e(0);
        
        if (semctl(id, 3, cmds[i]) != -1) e(0);
        if (errno != EINVAL) e(0);
        
        if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
        if (semds.sem_otime != 0) e(0);
        if (semds.sem_ctime >= now) e(0);
    }
}

static void test_getall_command(int id, int badid1, int badid2) {
    unsigned short val[4];
    unsigned int i, j;
    
    for (j = 0; j < 5; j++) {
        for (i = 0; i < __arraycount(val); i++)
            val[i] = USHRT_MAX;
        
        if (semctl(id, (int)j - 1, GETALL, val) != 0) e(0);
        for (i = 0; i < 3; i++)
            if (val[i] != 0) e(0);
        if (val[i] != USHRT_MAX) e(0);
    }
    
    for (i = 0; i < __arraycount(val); i++)
        val[i] = USHRT_MAX;
    
    test_invalid_id_command(badid1, badid2, GETALL);
    
    for (i = 0; i < __arraycount(val); i++)
        if (val[i] != USHRT_MAX) e(0);
    
    if (semctl(id, 0, GETALL, NULL) != -1) e(0);
    if (errno != EFAULT) e(0);
    
    if (semctl(id, 0, GETALL, bad_ptr) != -1) e(0);
    if (errno != EFAULT) e(0);
    
    if (semctl(id, 0, GETALL, ((unsigned short *)bad_ptr) - 2) != -1) e(0);
    if (errno != EFAULT) e(0);
    
    if (semctl(id, 0, GETALL, ((unsigned short *)bad_ptr) - 3) != 0) e(0);
}

static void test_ipc_stat_errors(int badid1, int badid2, char *statbuf) {
    test_invalid_id_command(badid1, badid2, IPC_STAT);
    
    for (unsigned int i = 0; i < sizeof(struct semid_ds) + 1; i++)
        if (statbuf[i] != INITIAL_VAL_MARKER) e(0);
}

static void test_ipc_stat_command(int id, int badid1, int badid2, time_t now) {
    char statbuf[sizeof(struct semid_ds) + 1];
    struct semid_ds semds;
    
    memset(statbuf, INITIAL_VAL_MARKER, sizeof(statbuf));
    
    test_ipc_stat_errors(badid1, badid2, statbuf);
    
    if (semctl(id, 0, IPC_STAT, statbuf) != 0) e(0);
    
    if (statbuf[sizeof(statbuf) - 1] != INITIAL_VAL_MARKER) e(0);
    
    if (semctl(id, 0, IPC_STAT, NULL) != -1) e(0);
    if (errno != EFAULT) e(0);
    
    if (semctl(id, 0, IPC_STAT, bad_ptr) != -1) e(0);
    if (errno != EFAULT) e(0);
    
    if (semctl(id, 0, IPC_STAT, ((struct semid_ds *)bad_ptr) - 1) != 0) e(0);
    
    if (semctl(id, -1, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime >= now) e(0);
}

static void verify_sem_stat_result(int r, int i, int id, int id2, 
                                  struct semid_ds *semds, unsigned short *seen,
                                  struct seminfo *seminfo) {
    if (r < 0) e(0);
    if (!(semds->sem_perm.mode & SEM_ALLOC)) e(0);
    if (semds->sem_ctime == 0) e(0);
    if (IXSEQ_TO_IPCID(i, semds->sem_perm) != r) e(0);
    
    if (r == id) {
        seen[0]++;
        if (semds->sem_perm.mode != (SEM_ALLOC | DEFAULT_PERMS)) e(0);
        if (semds->sem_perm.uid != geteuid()) e(0);
        if (semds->sem_perm.gid != getegid()) e(0);
        if (semds->sem_perm.cuid != semds->sem_perm.uid) e(0);
        if (semds->sem_perm.cgid != semds->sem_perm.gid) e(0);
        if (semds->sem_perm._key != IPC_PRIVATE) e(0);
        if (semds->sem_nsems != 3) e(0);
        if (semds->sem_otime != 0) e(0);
        
        if (semctl(i, 0, SEM_STAT, NULL) != -1) e(0);
        if (errno != EFAULT) e(0);
        
        if (semctl(i, 0, SEM_STAT, bad_ptr) != -1) e(0);
        if (errno != EFAULT) e(0);
    } else if (r == id2) {
        seen[1]++;
        if (semds->sem_perm.mode != (SEM_ALLOC | TEST_PERMS)) e(0);
        if (semds->sem_perm.uid != geteuid()) e(0);
        if (semds->sem_perm.gid != getegid()) e(0);
        if (semds->sem_perm.cuid != semds->sem_perm.uid) e(0);
        if (semds->sem_perm.cgid != semds->sem_perm.gid) e(0);
        if (semds->sem_perm._key != KEY_A) e(0);
        if (semds->sem_nsems != seminfo->semmsl) e(0);
    }
}

static void test_sem_stat(int id, int id2, struct seminfo *seminfo, time_t now) {
    char statbuf[sizeof(struct semid_ds) + 1];
    struct semid_ds semds;
    unsigned short seen[2];
    unsigned int i;
    int r;
    
    memset(statbuf, INITIAL_VAL_MARKER, sizeof(statbuf));
    
    if (semctl(-1, 0, SEM_STAT, statbuf) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (semctl(seminfo->semmni, 0, SEM_STAT, statbuf) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    for (i = 0; i < sizeof(statbuf); i++)
        if (statbuf[i] != INITIAL_VAL_MARKER) e(0);
    
    memset(seen, 0, sizeof(seen));
    
    for (i = 0; i < seminfo->semmni; i++) {
        errno = 0;
        if ((r = semctl(i, i / 2 - 1, SEM_STAT, statbuf)) == -1) {
            if (errno != EINVAL) e(0);
            continue;
        }
        memcpy(&semds, statbuf, sizeof(semds));
        verify_sem_stat_result(r, i, id, id2, &semds, seen, seminfo);
    }
    
    if (seen[0] != 1) e(0);
    if (seen[1] != 1) e(0);
    
    if (statbuf[sizeof(statbuf) - 1] != INITIAL_VAL_MARKER) e(0);
    
    if (semctl(id, 5, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime >= now) e(0);
}

static void test_setval_errors(int id, int badid1, int badid2, 
                              struct seminfo *seminfo) {
    test_invalid_id_command(badid1, badid2, SETVAL);
    
    if (semctl(id, -1, SETVAL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (semctl(id, 3, SETVAL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (semctl(id, 0, SETVAL, -1) != -1) e(0);
    if (errno != ERANGE) e(0);
    
    if (semctl(id, 0, SETVAL, seminfo->semvmx + 1) != -1) e(0);
    if (errno != ERANGE) e(0);
}

static void test_setval_command(int id, int badid1, int badid2, 
                               struct seminfo *seminfo, time_t now) {
    struct semid_ds semds;
    unsigned short val[4];
    
    test_setval_errors(id, badid1, badid2, seminfo);
    
    TEST_SEM(id, 0, 0, 0, 0, 0);
    
    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime >= now) e(0);
    
    if (semctl(id, 1, SETVAL, 0) != 0) e(0);
    
    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);
    
    TEST_SEM(id, 1, 0, 0, 0, 0);
    
    if (semctl(id, 2, SETVAL, seminfo->semvmx) != 0) e(0);
    
    TEST_SEM(id, 2, seminfo->semvmx, 0, 0, 0);
    
    if (semctl(id, 0, SETVAL, 1) != 0) e(0);
    
    TEST_SEM(id, 0, 1, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, seminfo->semvmx, 0, 0, 0);
    
    if (semctl(id, 0, GETALL, val) != 0) e(0);
    if (val[0] != 1) e(0);
    if (val[1] != 0) e(0);
    if (val[2] != seminfo->semvmx) e(0);
}

static void test_setall_errors(int id, int badid1, int badid2, 
                              struct seminfo *seminfo) {
    unsigned short val[3];
    
    test_invalid_id_command(badid1, badid2, SETALL);
    
    val[0] = seminfo->semvmx + 1;
    val[1] = 0;
    val[2] = 0;
    if (semctl(id, 0, SETALL, val) != -1) e(0);
    if (errno != ERANGE) e(0);
    
    val[0] = 0;
    val[1] = 1;
    val[2] = seminfo->semvmx + 1;
    if (semctl(id, 0, SETALL, val) != -1) e(0);
    if (errno != ERANGE) e(0);
    
    if (semctl(id, 0, SETALL, NULL) != -1) e(0);
    if (errno != EFAULT) e(0);
    
    if (semctl(id, 0, SETALL, bad_ptr) != -1) e(0);
    if (errno != EFAULT) e(0);
    
    if (semctl(id, 0, SETALL, ((unsigned short *)bad_ptr) - 2) != -1) e(0);
    if (errno != EFAULT) e(0);
}

static void test_setall_command(int id, int badid1, int badid2,
                               struct seminfo *seminfo, time_t now) {
    struct semid_ds semds;
    unsigned short val[3];
    
    test_setall_errors(id, badid1, badid2, seminfo);
    
    TEST_SEM(id, 0, 1, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, seminfo->semvmx, 0, 0, 0);
    
    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime >= now) e(0);
    
    val[0] = seminfo->semvmx;
    val[1] = 0;
    val[2] = 0;
    if (semctl(id, 0, SETALL, val) != 0) e(0);
    
    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);
    
    TEST_SEM(id, 0, seminfo->semvmx, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, 0, 0, 0, 0);
    
    val[0] = 0;
    val[1] = 1;
    val[2] = seminfo->semvmx;
    if (semctl(id, INT_MAX, SETALL, val) != 0) e(0);
    
    TEST_SEM(id, 0, 0, 0, 0, 0);
    TEST_SEM(id, 1, 1, 0, 0, 0);
    TEST_SEM(id, 2, seminfo->semvmx, 0, 0, 0);
    
    memset(page_ptr, 0, page_size);
    if (semctl(id, 0, SETALL, ((unsigned short *)bad_ptr) - 3) != 0) e(0);
    
    TEST_SEM(id, 0, 0, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, 0, 0, 0, 0);
}

static void test_ipc_set_errors(int badid1, int badid2, struct semid_ds *semds) {
    test_invalid_id_command(badid1, badid2, IPC_SET);
    
    if (semctl(0, 0, IPC_SET, NULL) != -1) e(0);
    if (errno != EFAULT) e(0);
    
    if (semctl(0, 0, IPC_SET, bad_ptr) != -1) e(0);
    if (errno != EFAULT) e(0);
}

static void test_ipc_set_mode(int id, struct semid_ds *semds,
                             struct semid_ds *osemds) {
    unsigned int i;
    
    semds->sem_perm.uid = osemds->sem_perm.uid;
    semds->sem_perm.gid = osemds->sem_perm.gid;
    
    for (i = 0; i < 0777; i++) {
        semds->sem_perm.mode = i;
        if (semctl(id, i / 2 - 1, IPC_SET, semds) != 0) e(0);
        
        if (semctl(id, i / 2 - 2, IPC_STAT, semds) != 0) e(0);
        if (semds->sem_perm.mode != (SEM_ALLOC | i)) e(0);
        
        semds->sem_perm.mode = ~0777 | i;
        if (semctl(id, i / 2 - 3, IPC_SET, semds) != 0) e(0);
        
        if (semctl(id, i / 2 - 4, IPC_STAT, semds) != 0) e(0);
        if (semds->sem_perm.mode != (SEM_ALLOC | i)) e(0);
    }
    
    if (semds->sem_perm.uid != osemds->sem_perm.uid) e(0);
    if (semds->sem_perm.gid != osemds->sem_perm.gid) e(0);
}

static void test_ipc_set_command(int id, int badid1, int badid2, time_t now) {
    struct semid_ds semds, osemds;
    
    if (semctl(id, 0, IPC_STAT, &osemds) != 0) e(0);
    if (osemds.sem_otime != 0) e(0);
    if (osemds.sem_ctime >= now) e(0);
    
    test_ipc_set_errors(badid1, badid2, &semds);
    
    memset(&semds, VAL_MARKER, sizeof(semds));
    semds.sem_perm.mode = ALT_PERMS;
    semds.sem_perm.uid = UID_MAX;
    semds.sem_perm.gid = GID_MAX - 1;
    
    if (semctl(id, 0, IPC_SET, &semds) != 0) e(0);
    
    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_perm.mode != (SEM_ALLOC | ALT_PERMS)) e(0);
    if (semds.sem_perm.uid != UID_MAX) e(0);
    if (semds.sem_perm.gid != GID_MAX - 1) e(0);
    if (semds.sem_perm.cuid != osemds.sem_perm.cuid) e(0);
    if (semds.sem_perm.cgid != osemds.sem_perm.cgid) e(0);
    if (semds.sem_perm._seq != osemds.sem_perm._seq) e(0);
    if (semds.sem_perm._key != osemds.sem_perm._key) e(0);
    if (semds.sem_nsems != osemds.sem_nsems) e(0);
    if (semds.sem_otime != osemds.sem_otime) e(0);
    if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);
    
    test_ipc_set_mode(id, &semds, &osemds);
    
    if (semctl(id, 0, IPC_SET, ((struct semid_ds *)bad_ptr) - 1) != 0) e(0);
}

static void test_ipc_rmid(int badid1, int badid2, int id, int id2) {
    struct semid_ds semds;
    
    test_invalid_id_command(badid1, badid2, IPC_RMID);
    
    if (semctl(id, 0, IPC_RMID) != 0) e(0);
    
    if (semctl(id, 0, IPC_RMID) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (semctl(id, 0, IPC_STAT, &semds) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (semctl(id2, 1, IPC_RMID) != 0) e(0);
    
    if (semctl(id2, 1, IPC_RMID) != -1) e(0);
    if (errno != EINVAL) e(0);
}

static void verify_seminfo(struct seminfo *seminfo, int cmd, int r) {
    if (r < 1 || r >= seminfo->semmni) e(0);
    
    if (seminfo->semmap < 0) e(0);
    if (seminfo->semmni < 3 || seminfo->semmni > USHRT_MAX) e(0);
    if (seminfo->semmns < 3 || seminfo->semmns > USHRT_MAX) e(0);
    if (seminfo->semmnu < 0) e(0);
    if (seminfo->semmsl < 3 || seminfo->semmsl > USHRT_MAX) e(0);
    if (seminfo->semopm < 3 || seminfo->semopm > USHRT_MAX) e(0);
    if (seminfo->semume < 0) e(0);
    
    if (cmd == SEM_INFO) {
        if (seminfo->semusz < 2) e(0);
        if (seminfo->semaem < 4) e(0);
    } else {
        if (seminfo->semusz < 0) e(0);
        if (seminfo->semaem < 0) e(0);
    }
    
    if (seminfo->semvmx < 3 || seminfo->semvmx > SHRT_MAX) e(0);
}

static void test_info_command(int cmd) {
    struct seminfo seminfo;
    int r;
    
    memset(&seminfo, 0xff, sizeof(seminfo));
    
    if ((r = semctl(0, 0, cmd, &seminfo)) == -1) e(0);
    
    verify_seminfo(&seminfo, cmd, r);
    
    if (semctl(INT_MAX, -1, cmd, &seminfo) == -1) e(0);
    if (semctl(-1, INT_MAX, cmd, &seminfo) == -1) e(0);
    
    if (semctl(0, 0, cmd, NULL) != -1) e(0);
    if (errno != EFAULT) e(0);
    
    if (semctl(0, 0, cmd, bad_ptr) != -1) e(0);
    if (errno != EFAULT) e(0);
    
    if (semctl(0, 0, cmd, ((struct seminfo *)bad_ptr) - 1) == -1) e(0);
}

static void test_invalid_commands(int id) {
    if (semctl(id, 0, INT_MIN) != -1) e(0);
    if (errno != EINVAL) e(0);
    
    if (semctl(id, 0, INT_MAX) != -1) e(0);
    if (errno != EINVAL) e(0);
}

static void test88c(void) {
    struct seminfo seminfo;
    struct semid_ds semds;
    time_t now;
    int id, id2, badid1, badid2;
    
    subtest = 2;
    
    if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
    
    test_perm(test88c_perm1, 0);
    test_perm(test88c_perm2, 1);
    test_perm(test88c_perm3, 1);
    
    badid1 = create_and_remove_semaphore();
    badid2 = create_invalid_id(&seminfo);
    
    if ((id = semget(IPC_PRIVATE, 3, IPC_CREAT | DEFAULT_PERMS)) < 0) e(0);
    
    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime == 0) e(0);
    
    wait_for_time_change(semds.sem_ctime);
    time(&now);
    
    test_get_commands(id, badid1, badid2, now);
    test_getall_command(id, badid1, badid2);
    
    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime >= now) e(0);
    
    test_ipc_stat_command(id, badid1, badid2, now);
    
    if ((id2 = semget(KEY_A, seminfo.semmsl, IPC_CREAT | TEST_PERMS)) < 0) e(0);
    
    test_sem_stat(id, id2, &seminfo, now);
    test_setval_command(id, badid1, badid2, &seminfo, now);
    
    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    
    wait_for_time_change(semds.sem_ctime);
    time(&now);
    
    test_setall_command(id, badid1, badid2, &seminfo, now);
    
    wait_for_time_change(semds.sem_ctime);
    time(&now);
    
    test_ipc_set_command(id, badid1, badid2, now);
    test_ipc_rmid(badid1, badid2, id, id2);
    
    if ((id = semget(IPC_PRIVATE, 3, DEFAULT_PERMS)) == -1) e(0);
    if ((id2 = semget(IPC_PRIVATE, 1, DEFAULT_PERMS)) == -1) e(0);
    
    test_info_command(IPC_INFO);
    test_info_command(SEM_INFO);
    
    if (semctl(id2, 0, IPC_RMID) != 0) e(0);
    
    test_invalid_commands(id);
    
    if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

/*
 * Test SEM_UNDO support.  Right now this functionality is missing altogether.
 * For now, we test that any attempt to use SEM_UNDO fails.
 */
static void test88d(void)
{
    const int SEM_PERMISSIONS = 0600;
    const int EXPECTED_ERROR = EINVAL;
    const int SINGLE_SEMAPHORE = 1;
    
    struct sembuf sop;
    int id;
    
    subtest = 3;
    
    id = semget(IPC_PRIVATE, SINGLE_SEMAPHORE, SEM_PERMISSIONS);
    if (id == -1) e(0);
    
    if (!(SHRT_MAX & SEM_UNDO)) e(0);
    
    sop.sem_num = 0;
    sop.sem_op = 1;
    sop.sem_flg = SHRT_MAX;
    
    if (semop(id, &sop, SINGLE_SEMAPHORE) != -1) e(0);
    if (errno != EXPECTED_ERROR) e(0);
    
    if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

enum {
	RESUME_SEMOP,	/* use semop() to resume blocked parties */
	RESUME_SETVAL,	/* use semctl(SETVAL) to resume blocked parties */
	RESUME_SETALL,	/* use semctl(SETALL) to resume blocked parties */
	NR_RESUMES
};

enum {
	MATCH_FIRST,	/* first match completes, blocks second match */
	MATCH_SECOND,	/* first match does not complete, second match does */
	MATCH_KILL,	/* second match completes after first is aborted */
	MATCH_BOTH,	/* first and second match both complete */
	MATCH_CASCADE,	/* completed match in turn causes another match */
	MATCH_ALL,	/* a combination of the last two */
	NR_MATCHES
};

/*
 * Auxiliary child procedure.  The auxiliary children will deadlock until the
 * semaphore set is removed.
 */
static void setup_semop_for_child1(struct sembuf *sops, int num)
{
    sops[0].sem_num = num;
    sops[0].sem_op = 1;
    sops[1].sem_num = num;
    sops[1].sem_op = 0;
    sops[2].sem_num = 0;
    sops[2].sem_op = 1;
}

static void setup_semop_for_child2(struct sembuf *sops, int num)
{
    struct seminfo seminfo;
    if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
    
    sops[0].sem_num = num;
    sops[0].sem_op = -seminfo.semvmx;
    sops[1].sem_num = num;
    sops[1].sem_op = -seminfo.semvmx;
    sops[2].sem_num = 0;
    sops[2].sem_op = 1;
}

static void setup_semop_operations(struct sembuf *sops, int child, int num)
{
    memset(sops, 0, sizeof(struct sembuf) * 3);
    
    if (child == 1) {
        setup_semop_for_child1(sops, num);
    } else if (child == 2) {
        setup_semop_for_child2(sops, num);
    } else {
        e(0);
    }
}

static void verify_semop_failure(int id, struct sembuf *sops)
{
    if (semop(id, sops, 3) != -1) e(0);
    if (errno != EIDRM) e(0);
}

static void
test88e_childaux(struct link * parent)
{
    struct sembuf sops[3];
    int child, id, num;

    child = rcv(parent);
    id = rcv(parent);
    num = rcv(parent);

    setup_semop_operations(sops, child, num);
    
    snd(parent, 0);
    
    verify_semop_failure(id, sops);
}

/*
 * First child procedure.
 */
static void initialize_sembuf(struct sembuf *sops) {
    memset(sops, 0, sizeof(struct sembuf) * 3);
    sops[0].sem_num = 2;
    sops[0].sem_op = -1;
}

static void setup_match_first(struct sembuf *sops) {
    sops[1].sem_num = 3;
    sops[1].sem_op = 1;
}

static void setup_match_second(struct sembuf *sops) {
    sops[1].sem_num = 3;
    sops[1].sem_op = -1;
    sops[2].sem_num = 0;
    sops[2].sem_op = 1;
}

static void setup_match_kill(struct sembuf *sops) {
    sops[1].sem_num = 0;
    sops[1].sem_op = 1;
}

static void setup_match_default(struct sembuf *sops) {
    sops[1].sem_num = 3;
    sops[1].sem_op = 1;
}

static void configure_semops(int match, struct sembuf *sops, size_t *nsops, int *expect) {
    *nsops = 2;
    *expect = 0;
    
    switch (match) {
    case MATCH_FIRST:
        setup_match_first(sops);
        break;
    case MATCH_SECOND:
        setup_match_second(sops);
        *nsops = 3;
        *expect = -1;
        break;
    case MATCH_KILL:
        setup_match_kill(sops);
        *expect = INT_MIN;
        break;
    case MATCH_BOTH:
    case MATCH_CASCADE:
    case MATCH_ALL:
        setup_match_default(sops);
        break;
    default:
        e(0);
    }
}

static void verify_semop_result(int result, int expected) {
    if (result != expected) e(0);
    if (expected == -1 && errno != EIDRM) e(0);
}

static void test88e_child1(struct link *parent) {
    struct sembuf sops[3];
    size_t nsops;
    int match, id, expect;

    match = rcv(parent);
    id = rcv(parent);

    initialize_sembuf(sops);
    configure_semops(match, sops, &nsops, &expect);

    snd(parent, 0);

    int result = semop(id, sops, nsops);
    verify_semop_result(result, expect);
}

/*
 * Second child procedure.
 */
static void initialize_sembuf(struct sembuf *sops) {
    memset(sops, 0, sizeof(struct sembuf) * 2);
    sops[0].sem_num = 2;
    sops[0].sem_op = -1;
}

static void configure_match_first(struct sembuf *sops) {
    sops[1].sem_num = 0;
    sops[1].sem_op = 1;
}

static void configure_match_both_or_all(struct sembuf *sops) {
    sops[1].sem_num = 3;
    sops[1].sem_op = 1;
}

static void configure_match_cascade(struct sembuf *sops) {
    sops[0].sem_num = 3;
}

static void configure_sembuf_by_match(int match, struct sembuf *sops, size_t *nsops, int *expect) {
    *nsops = 2;
    *expect = 0;
    
    if (match == MATCH_FIRST) {
        configure_match_first(sops);
        *expect = -1;
        return;
    }
    
    if (match == MATCH_SECOND || match == MATCH_KILL) {
        *nsops = 1;
        return;
    }
    
    if (match == MATCH_BOTH || match == MATCH_ALL) {
        configure_match_both_or_all(sops);
        return;
    }
    
    if (match == MATCH_CASCADE) {
        configure_match_cascade(sops);
        *nsops = 1;
        return;
    }
    
    e(0);
}

static void verify_semop_result(int result, int expect) {
    if (result != expect) e(0);
    if (expect == -1 && errno != EIDRM) e(0);
}

static void test88e_child2(struct link *parent) {
    struct sembuf sops[2];
    size_t nsops;
    int match, id, expect;
    
    match = rcv(parent);
    id = rcv(parent);
    
    initialize_sembuf(sops);
    configure_sembuf_by_match(match, sops, &nsops, &expect);
    
    snd(parent, 0);
    
    verify_semop_result(semop(id, sops, nsops), expect);
}

/*
 * Third child procedure.
 */
static void
test88e_child3(struct link * parent)
{
	struct sembuf sops[1];
	int match, id;

	match = rcv(parent);
	id = rcv(parent);

	memset(sops, 0, sizeof(sops));
	
	if (match != MATCH_ALL) {
		e(0);
	}
	
	sops[0].sem_num = 3;
	sops[0].sem_op = -2;

	snd(parent, 0);

	if (semop(id, sops, 1) != 0) {
		e(0);
	}
}

/*
 * Perform one test for operations affecting multiple processes.
 */
static void spawn_auxiliary_child(struct link *aux, int aux_num, int id, int sem_num, int *counter, int aux_flag)
{
	spawn(aux, test88e_childaux, (aux_num == 1) ? DROP_ALL : DROP_NONE);
	snd(aux, aux_num);
	snd(aux, id);
	snd(aux, sem_num);
	if (rcv(aux) != 0) e(0);
	if (aux_flag & 4) (*counter)++;
}

static void spawn_main_children(struct link *child1, struct link *child2, struct link *child3, int match, int id)
{
	spawn(child1, test88e_child1, DROP_ALL);
	snd(child1, match);
	snd(child1, id);
	if (rcv(child1) != 0) e(0);

	if (match == MATCH_FIRST || match == MATCH_SECOND || match == MATCH_KILL)
		usleep(WAIT_USECS);

	spawn(child2, test88e_child2, DROP_NONE);
	snd(child2, match);
	snd(child2, id);
	if (rcv(child2) != 0) e(0);

	if (match == MATCH_ALL) {
		spawn(child3, test88e_child3, DROP_USER);
		snd(child3, match);
		snd(child3, id);
		if (rcv(child3) != 0) e(0);
	}
}

static int get_increment_value(int match)
{
	if (match == MATCH_BOTH || match == MATCH_ALL)
		return 2;
	return 1;
}

static void test_semaphore_values_for_match_first(int id, int aux_ncnt, int aux_zcnt)
{
	TEST_SEM(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
	TEST_SEM(id, 3, 0, 0, 0, 0);
}

static void test_semaphore_values_for_match_kill(int id, struct link *child1, int aux_ncnt, int aux_zcnt)
{
	TEST_SEM(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
	terminate(child1);
	usleep(WAIT_USECS);
	TEST_SEM(id, 2, 0, 0, 1 + aux_ncnt, aux_zcnt);
	TEST_SEM(id, 3, 0, 0, 0, 0);
}

static void test_semaphore_values_for_match_cascade(int id, int aux_ncnt, int aux_zcnt)
{
	TEST_SEM(id, 2, 0, 0, 1 + aux_ncnt, aux_zcnt);
	TEST_SEM(id, 3, 0, 0, 1, 0);
}

static void test_semaphore_values_for_match_all(int id, int aux_ncnt, int aux_zcnt)
{
	TEST_SEM(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
	TEST_SEM(id, 3, 0, 0, 1, 0);
}

static int test_and_get_increment(int match, int id, struct link *child1, int aux_ncnt, int aux_zcnt)
{
	if (match == MATCH_FIRST || match == MATCH_SECOND) {
		test_semaphore_values_for_match_first(id, aux_ncnt, aux_zcnt);
	} else if (match == MATCH_KILL) {
		test_semaphore_values_for_match_kill(id, child1, aux_ncnt, aux_zcnt);
	} else if (match == MATCH_BOTH) {
		test_semaphore_values_for_match_first(id, aux_ncnt, aux_zcnt);
	} else if (match == MATCH_CASCADE) {
		test_semaphore_values_for_match_cascade(id, aux_ncnt, aux_zcnt);
	} else if (match == MATCH_ALL) {
		test_semaphore_values_for_match_all(id, aux_ncnt, aux_zcnt);
	} else {
		e(0);
	}

	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, -1, -1);

	return get_increment_value(match);
}

static void resume_children(int resume, int id, int inc)
{
	struct sembuf sop;
	unsigned short val[4];

	if (resume == RESUME_SEMOP) {
		memset(&sop, 0, sizeof(sop));
		sop.sem_num = 2;
		sop.sem_op = inc;
		if (semop(id, &sop, 1) != 0) e(0);
	} else if (resume == RESUME_SETVAL) {
		if (semctl(id, 2, SETVAL, inc) != 0) e(0);
	} else if (resume == RESUME_SETALL) {
		memset(val, 0, sizeof(val));
		val[2] = inc;
		if (semctl(id, 0, SETALL, val) != 0) e(0);
	} else {
		e(0);
	}
}

static void verify_and_collect_for_match_first(int id, struct link *child1, struct link *child2, int aux_ncnt, int aux_zcnt)
{
	TEST_SEM(id, 2, 0, child1->pid, 1 + aux_ncnt, aux_zcnt);
	TEST_SEM(id, 3, 1, child1->pid, 0, 0);
	collect(child1);
}

static void verify_and_collect_for_match_second(int id, struct link *child2, int aux_ncnt, int aux_zcnt)
{
	TEST_SEM(id, 2, 0, child2->pid, 1 + aux_ncnt, aux_zcnt);
	TEST_SEM(id, 3, 0, 0, 0, 0);
	collect(child2);
}

static void verify_and_collect_for_match_kill(int id, struct link *child2, int aux_ncnt, int aux_zcnt)
{
	TEST_SEM(id, 2, 0, child2->pid, aux_ncnt, aux_zcnt);
	TEST_SEM(id, 3, 0, 0, 0, 0);
	collect(child2);
}

static void verify_and_collect_for_match_both(int id, struct link *child1, struct link *child2, int aux_ncnt, int aux_zcnt)
{
	TEST_SEM(id, 2, 0, -1, aux_ncnt, aux_zcnt);
	TEST_SEM(id, 3, 2, -1, 0, 0);
	collect(child1);
	collect(child2);
}

static void verify_and_collect_for_match_cascade(int id, struct link *child1, struct link *child2, int aux_ncnt, int aux_zcnt)
{
	TEST_SEM(id, 2, 0, child1->pid, aux_ncnt, aux_zcnt);
	TEST_SEM(id, 3, 0, child2->pid, 0, 0);
	collect(child1);
	collect(child2);
}

static void verify_and_collect_for_match_all(int id, struct link *child1, struct link *child2, struct link *child3, int aux_ncnt, int aux_zcnt)
{
	TEST_SEM(id, 2, 0, -1, aux_ncnt, aux_zcnt);
	TEST_SEM(id, 3, 0, child3->pid, 0, 0);
	collect(child1);
	collect(child2);
	collect(child3);
}

static void verify_and_collect_resumed(int match, int id, struct link *child1, struct link *child2, struct link *child3, int aux_ncnt, int aux_zcnt)
{
	if (match == MATCH_FIRST) {
		verify_and_collect_for_match_first(id, child1, child2, aux_ncnt, aux_zcnt);
	} else if (match == MATCH_SECOND) {
		verify_and_collect_for_match_second(id, child2, aux_ncnt, aux_zcnt);
	} else if (match == MATCH_KILL) {
		verify_and_collect_for_match_kill(id, child2, aux_ncnt, aux_zcnt);
	} else if (match == MATCH_BOTH) {
		verify_and_collect_for_match_both(id, child1, child2, aux_ncnt, aux_zcnt);
	} else if (match == MATCH_CASCADE) {
		verify_and_collect_for_match_cascade(id, child1, child2, aux_ncnt, aux_zcnt);
	} else if (match == MATCH_ALL) {
		verify_and_collect_for_match_all(id, child1, child2, child3, aux_ncnt, aux_zcnt);
	} else {
		e(0);
	}

	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, -1, -1);
}

static void collect_unresumed_children(int match, struct link *child1, struct link *child2)
{
	if (match == MATCH_FIRST) {
		collect(child2);
	} else if (match == MATCH_SECOND) {
		collect(child1);
	}
}

static void sub88e(unsigned int match, unsigned int resume, unsigned int aux)
{
	struct link aux1, aux2, child1, child2, child3;
	unsigned short val[4];
	int id, inc, aux_zcnt, aux_ncnt;

	if ((id = semget(IPC_PRIVATE, __arraycount(val), 0666)) == -1) e(0);

	aux_zcnt = aux_ncnt = 0;

	if (aux & 1) {
		spawn_auxiliary_child(&aux1, 1, id, (aux & 4) ? 2 : 1, (aux & 4) ? &aux_zcnt : &aux_ncnt, aux);
	}

	spawn_main_children(&child1, &child2, &child3, match, id);

	if (aux & 2) {
		spawn_auxiliary_child(&aux2, 2, id, (aux & 4) ? 2 : 1, (aux & 4) ? &aux_ncnt : &aux_ncnt, aux);
	}

	usleep(WAIT_USECS);

	inc = test_and_get_increment(match, id, &child1, aux_ncnt, aux_zcnt);

	resume_children(resume, id, inc);

	verify_and_collect_resumed(match, id, &child1, &child2, &child3, aux_ncnt, aux_zcnt);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);

	collect_unresumed_children(match, &child1, &child2);

	if (aux & 1) collect(&aux1);
	if (aux & 2) collect(&aux2);
}

/*
 * Test operations affecting multiple processes, ensuring the following points:
 * 1) an operation resumes all possible waiters; 2) a resumed operation in turn
 * correctly resumes other now-unblocked operations; 3) a basic level of FIFO
 * fairness is provided between blocked parties; 4) all the previous points are
 * unaffected by additional waiters that are not being resumed; 5) identifier
 * removal properly resumes all affected waiters.
 */
static void
test88e(void)
{
	unsigned int resume, match, aux;

	subtest = 4;

	for (match = 0; match < NR_MATCHES; match++)
		for (resume = 0; resume < NR_RESUMES; resume++)
			for (aux = 1; aux <= 8; aux++)
				sub88e(match, resume, aux);
}

/*
 * Verify that non-root processes can use sysctl(2) to see semaphore sets
 * created by root.
 */
static const int KERN_SYSVIPC_SEM_INFO_MIB[] = { 
    CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_INFO, KERN_SYSVIPC_SEM_INFO 
};

static const int EXPECTED_SEEN_COUNT = 1;
static const int ID_COUNT = 2;

static struct sem_sysctl_info* get_sem_sysctl_info(size_t *len)
{
    if (sysctl(KERN_SYSVIPC_SEM_INFO_MIB, __arraycount(KERN_SYSVIPC_SEM_INFO_MIB), 
               NULL, len, NULL, 0) != 0) 
        e(0);

    struct sem_sysctl_info *semsi = malloc(*len);
    if (semsi == NULL) 
        e(0);

    if (sysctl(KERN_SYSVIPC_SEM_INFO_MIB, __arraycount(KERN_SYSVIPC_SEM_INFO_MIB), 
               semsi, len, NULL, 0) != 0) 
        e(0);

    return semsi;
}

static int is_allocated_semaphore(struct semid_ds *semid)
{
    return (semid->sem_perm.mode & SEM_ALLOC) != 0;
}

static void count_matching_semaphores(struct sem_sysctl_info *semsi, int *ids, int *seen)
{
    for (int32_t i = 0; i < semsi->seminfo.semmni; i++) {
        if (!is_allocated_semaphore(&semsi->semids[i]))
            continue;

        int id = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
        
        for (int j = 0; j < ID_COUNT; j++) {
            if (id == ids[j]) {
                seen[j]++;
                break;
            }
        }
    }
}

static void verify_seen_counts(int *seen)
{
    for (int i = 0; i < ID_COUNT; i++) {
        if (seen[i] != EXPECTED_SEEN_COUNT) 
            e(0);
    }
}

static void test88f_child(struct link *parent)
{
    int ids[ID_COUNT];
    int seen[ID_COUNT] = {0};
    size_t len;

    for (int i = 0; i < ID_COUNT; i++) {
        ids[i] = rcv(parent);
    }

    struct sem_sysctl_info *semsi = get_sem_sysctl_info(&len);
    count_matching_semaphores(semsi, ids, seen);
    free(semsi);
    
    verify_seen_counts(seen);
}

/*
 * Test sysctl(2) based information retrieval.  This test aims to ensure that
 * in particular ipcs(1) and ipcrm(1) will be able to do their jobs.
 */
static void verify_seminfo_only(const int *mib, struct seminfo *seminfo)
{
	size_t len = sizeof(*seminfo);
	if (sysctl(mib, __arraycount(mib), seminfo, &len, NULL, 0) != 0) e(0);
	if (len != sizeof(*seminfo)) e(0);
}

static void verify_seminfo_match(const struct seminfo *seminfo)
{
	struct seminfo seminfo2;
	if (semctl(0, 0, IPC_INFO, &seminfo2) == -1) e(0);
	if (memcmp(seminfo, &seminfo2, sizeof(*seminfo)) != 0) e(0);
}

static size_t calculate_semsi_size(const struct seminfo *seminfo)
{
	if (seminfo->semmni <= 0) e(0);
	if (seminfo->semmni > SHRT_MAX) e(0);
	
	return sizeof(struct sem_sysctl_info) +
	    sizeof(((struct sem_sysctl_info *)0)->semids[0]) * (seminfo->semmni - 1);
}

static void verify_size_estimation(const int *mib, size_t expected_size)
{
	size_t len = 0;
	if (sysctl(mib, __arraycount(mib), NULL, &len, NULL, 0) != 0) e(0);
	if (len != expected_size) e(0);
}

static struct sem_sysctl_info *retrieve_semaphore_array(const int *mib, size_t size)
{
	struct sem_sysctl_info *semsi = malloc(size);
	if (semsi == NULL) e(0);
	
	size_t len = size;
	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0) e(0);
	if (len != size) e(0);
	
	return semsi;
}

static void find_semaphore_slots(const struct sem_sysctl_info *semsi, 
                                 const struct seminfo *seminfo,
                                 const int *id, int32_t *slot)
{
	slot[0] = slot[1] = -1;
	
	for (int32_t i = 0; i < seminfo->semmni; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
			continue;
		
		int id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
		if (id2 == id[0]) {
			if (slot[0] != -1) e(0);
			slot[0] = i;
		} else if (id2 == id[1]) {
			if (slot[1] != -1) e(0);
			slot[1] = i;
		}
	}
	
	if (slot[0] < 0) e(0);
	if (slot[1] < 0) e(0);
}

static void verify_semaphore_properties(const struct semid_ds_sysctl *semds,
                                       key_t expected_key, int expected_mode,
                                       int expected_nsems)
{
	if (semds->sem_perm.uid != geteuid()) e(0);
	if (semds->sem_perm.gid != getegid()) e(0);
	if (semds->sem_perm.cuid != geteuid()) e(0);
	if (semds->sem_perm.cgid != getegid()) e(0);
	if (semds->sem_perm.mode != (SEM_ALLOC | expected_mode)) e(0);
	if (semds->sem_perm._key != expected_key) e(0);
	if (semds->sem_nsems != expected_nsems) e(0);
	if (semds->sem_otime != 0) e(0);
	if (semds->sem_ctime == 0) e(0);
}

static void verify_sets_not_in_listing(const int *mib, size_t size,
                                       const struct seminfo *seminfo,
                                       const int *id)
{
	struct sem_sysctl_info *semsi = retrieve_semaphore_array(mib, size);
	
	for (int32_t i = 0; i < seminfo->semmni; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
			continue;
		
		int id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
		if (id2 == id[0]) e(0);
		if (id2 == id[1]) e(0);
	}
	
	free(semsi);
}

static void test88f(void)
{
	static const int mib[] = { CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_INFO,
	    KERN_SYSVIPC_SEM_INFO };
	struct seminfo seminfo;
	struct sem_sysctl_info *semsi;
	struct link child;
	size_t size;
	int id[2];
	int32_t slot[2];
	
	verify_seminfo_only(mib, &seminfo);
	verify_seminfo_match(&seminfo);
	
	size = calculate_semsi_size(&seminfo);
	verify_size_estimation(mib, size);
	
	if ((id[0] = semget(KEY_A, 5, IPC_CREAT | 0612)) < 0) e(0);
	if ((id[1] = semget(IPC_PRIVATE, 3, 0650)) < 0) e(0);
	
	semsi = retrieve_semaphore_array(mib, size);
	
	if (sizeof(semsi->seminfo) != sizeof(seminfo)) e(0);
	if (memcmp(&semsi->seminfo, &seminfo, sizeof(semsi->seminfo)) != 0) e(0);
	
	find_semaphore_slots(semsi, &seminfo, id, slot);
	
	verify_semaphore_properties(&semsi->semids[slot[0]], KEY_A, 0612, 5);
	verify_semaphore_properties(&semsi->semids[slot[1]], IPC_PRIVATE, 0650, 3);
	
	spawn(&child, test88f_child, DROP_ALL);
	snd(&child, id[0]);
	snd(&child, id[1]);
	collect(&child);
	
	if (semctl(id[0], 0, IPC_RMID) != 0) e(0);
	if (semctl(id[1], 0, IPC_RMID) != 0) e(0);
	
	verify_sets_not_in_listing(mib, size, &seminfo, id);
	
	free(semsi);
}

/*
 * Initialize the test.
 */
static const int MIB_KERN_SYSVIPC_SEM[] = { CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_SEM };

static void set_root_privileges(void)
{
	struct group *gr;
	
	setuid(geteuid());
	
	if ((gr = getgrnam(ROOT_GROUP)) == NULL) e(0);
	
	setgid(gr->gr_gid);
	setegid(gr->gr_gid);
}

static int is_ipc_service_running(void)
{
	size_t len;
	int value;
	
	len = sizeof(value);
	if (sysctl(MIB_KERN_SYSVIPC_SEM, __arraycount(MIB_KERN_SYSVIPC_SEM), 
	           &value, &len, NULL, 0) != 0) e(0);
	if (len != sizeof(value)) e(0);
	
	return value;
}

static void skip_test_if_no_ipc(void)
{
	if (is_ipc_service_running() == 0) {
		printf("skipped\n");
		cleanup();
		exit(0);
	}
}

static void setup_test_memory(void)
{
	page_size = getpagesize();
	page_ptr = mmap(NULL, page_size * 2, PROT_READ | PROT_WRITE,
	                MAP_ANON | MAP_PRIVATE, -1, 0);
	if (page_ptr == MAP_FAILED) e(0);
	
	bad_ptr = page_ptr + page_size;
	if (munmap(bad_ptr, page_size) != 0) e(0);
}

static void
test88_init(void)
{
	set_root_privileges();
	skip_test_if_no_ipc();
	setup_test_memory();
}

/*
 * Test program for SysV IPC semaphores.
 */
int parse_test_mask(int argc, char **argv)
{
    const int DEFAULT_MASK = 0xFF;
    return (argc == 2) ? atoi(argv[1]) : DEFAULT_MASK;
}

void run_test_if_enabled(int mask, int bit, void (*test_function)(void))
{
    if (mask & bit) {
        test_function();
    }
}

void run_test_suite(int test_mask)
{
    run_test_if_enabled(test_mask, 0x01, test88a);
    run_test_if_enabled(test_mask, 0x02, test88b);
    run_test_if_enabled(test_mask, 0x04, test88c);
    run_test_if_enabled(test_mask, 0x08, test88d);
    run_test_if_enabled(test_mask, 0x10, test88e);
    run_test_if_enabled(test_mask, 0x20, test88f);
}

int main(int argc, char **argv)
{
    const int TEST_NUMBER = 88;
    int test_mask;
    int i;

    start(TEST_NUMBER);
    test88_init();
    
    test_mask = parse_test_mask(argc, argv);

    for (i = 0; i < ITERATIONS; i++) {
        run_test_suite(test_mask);
    }

    quit();
}
