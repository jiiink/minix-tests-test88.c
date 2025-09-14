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
static void
child_main(struct link *link, void (*proc)(struct link *), int drop, int rcvfd, int sndfd)
{
	struct passwd *pw;
	struct group *gr;

	link->pid = getppid();
	link->rcvfd = rcvfd;
	link->sndfd = sndfd;

	errct = 0;

	switch (drop) {
	case DROP_ALL:
		if (setgroups(0, NULL) != 0) {
			perror("setgroups");
			exit(EXIT_FAILURE);
		}

		gr = getgrnam(NONROOT_GROUP);
		if (gr == NULL) {
			perror("getgrnam");
			exit(EXIT_FAILURE);
		}

		if (setgid(gr->gr_gid) != 0) {
			perror("setgid");
			exit(EXIT_FAILURE);
		}
		if (setegid(gr->gr_gid) != 0) {
			perror("setegid");
			exit(EXIT_FAILURE);
		}

		/* FALLTHROUGH */
	case DROP_USER:
		pw = getpwnam(NONROOT_USER);
		if (pw == NULL) {
			perror("getpwnam");
			exit(EXIT_FAILURE);
		}

		if (setuid(pw->pw_uid) != 0) {
			perror("setuid");
			exit(EXIT_FAILURE);
		}
		break;
	}

	proc(link);

	exit(errct);
}

static void
spawn(struct link *link, void (*proc)(struct link *), int drop)
{
	int up[2], dn[2];
	pid_t pid;

	fflush(stdout);
	fflush(stderr);

	if (pipe(up) != 0) {
		perror("pipe");
		exit(EXIT_FAILURE);
	}
	if (pipe(dn) != 0) {
		perror("pipe");
		close(up[0]);
		close(up[1]);
		exit(EXIT_FAILURE);
	}

	pid = fork();
	if (pid < 0) {
		perror("fork");
		close(up[0]);
		close(up[1]);
		close(dn[0]);
		close(dn[1]);
		exit(EXIT_FAILURE);
	}

	if (pid == 0) {
		close(up[1]);
		close(dn[0]);
		child_main(link, proc, drop, up[0], dn[1]);
	}

	link->pid = pid;
	close(up[0]);
	close(dn[1]);
	link->sndfd = up[1];
	link->rcvfd = dn[0];
}

/*
 * Wait for a child process to terminate, and clean up.
 */
static void
collect(struct link * link)
{
	int status = 0;

	if (close(link->sndfd) == -1) {
		e(0);
	}
	if (close(link->rcvfd) == -1) {
		e(0);
	}

	if (waitpid(link->pid, &status, 0) != link->pid) {
		e(0);
	}

	if (WIFEXITED(status)) {
		errct += WEXITSTATUS(status);
	} else {
		e(0);
	}
}

/*
 * Forcibly terminate a child process, and clean up.
 */
static void
terminate(struct link *link)
{
	int status;
	pid_t wait_result;

	if (kill(link->pid, SIGKILL) != 0) {
		perror("terminate: failed to send SIGKILL");
		close(link->sndfd);
		close(link->rcvfd);
		exit(EXIT_FAILURE);
	}

	close(link->sndfd);
	close(link->rcvfd);

	do {
		wait_result = waitpid(link->pid, &status, 0);
	} while (wait_result == -1 && errno == EINTR);

	if (wait_result < 0) {
		perror("terminate: waitpid failed");
		exit(EXIT_FAILURE);
	}

	if (WIFSIGNALED(status)) {
		if (WTERMSIG(status) != SIGKILL) {
			fprintf(stderr, "terminate: child killed by unexpected signal %d\n",
				WTERMSIG(status));
			exit(EXIT_FAILURE);
		}
	} else if (WIFEXITED(status)) {
		errct += WEXITSTATUS(status);
	} else {
		fprintf(stderr, "terminate: child in unexpected state after wait\n");
		exit(EXIT_FAILURE);
	}
}

/*
 * Send an integer value to the child or parent.
 */
static void
snd(struct link *link, int val)
{
    const char *buffer = (const char *)&val;
    size_t size = sizeof(val);
    size_t written = 0;

    while (written < size) {
        ssize_t result = write(link->sndfd, buffer + written, size - written);

        if (result < 0) {
            if (errno == EINTR) {
                continue;
            }
            perror("write");
            exit(EXIT_FAILURE);
        }
        written += (size_t)result;
    }
}

/*
 * Receive an integer value from the child or parent, or -1 on EOF.
 */
static int
rcv(struct link *link)
{
    int val;
    ssize_t bytes_read;

    if (link == NULL) {
        return -1;
    }

    bytes_read = read(link->rcvfd, &val, sizeof(val));

    if (bytes_read != sizeof(val)) {
        /* Handles read error, EOF, or a short read. */
        return -1;
    }

    return val;
}

/*
 * Child procedure that creates semaphore sets.
 */
static int
create_semaphore(key_t key, int flags)
{
	int id = semget(key, 3, IPC_CREAT | IPC_EXCL | flags);
	if (id == -1) {
		e(0);
	}
	return id;
}

static void
resolve_sugid(int sugid, uid_t *uid_ptr, gid_t *gid_ptr)
{
	const char *user_name = NULL;
	const char *group_name = NULL;

	switch (sugid) {
	case SUGID_ROOT_USER:
		user_name = ROOT_USER;
		break;
	case SUGID_NONROOT_USER:
		user_name = NONROOT_USER;
		break;
	case SUGID_ROOT_GROUP:
		group_name = ROOT_GROUP;
		break;
	case SUGID_NONROOT_GROUP:
		group_name = NONROOT_GROUP;
		break;
	default:
		return;
	}

	if (user_name != NULL) {
		struct passwd *pw = getpwnam(user_name);
		if (pw == NULL) {
			e(0);
		}
		*uid_ptr = pw->pw_uid;
	} else if (group_name != NULL) {
		struct group *gr = getgrnam(group_name);
		if (gr == NULL) {
			e(0);
		}
		*gid_ptr = gr->gr_gid;
	}
}

static void
set_semaphore_permissions(int id, uid_t uid, gid_t gid, int mode)
{
	struct semid_ds semds;
	semds.sem_perm.uid = uid;
	semds.sem_perm.gid = gid;
	semds.sem_perm.mode = mode;
	if (semctl(id, 0, IPC_SET, &semds) != 0) {
		e(0);
	}
}

static void
verify_semaphore_permissions(int id, int mask, uid_t uid, gid_t gid)
{
	struct semid_ds semds;
	if (semctl(id, 0, IPC_STAT, &semds) != 0) {
		e(0);
	}
	if (semds.sem_perm.mode != (SEM_ALLOC | mask)) e(0);
	if (semds.sem_perm.uid != uid) e(0);
	if (semds.sem_perm.gid != gid) e(0);
	if (semds.sem_perm.cuid != geteuid()) e(0);
	if (semds.sem_perm.cgid != getegid()) e(0);
}

static void
test_perm_child(struct link * parent)
{
	int mask;
	int id[3];

	while ((mask = rcv(parent)) != -1) {
		int rmask = rcv(parent);
		int sugid = rcv(parent);

		int sem_a_flags = (sugid == SUGID_NONE) ? mask : 0;
		id[0] = create_semaphore(KEY_A, sem_a_flags);
		id[1] = create_semaphore(KEY_B, mask | rmask);
		id[2] = create_semaphore(KEY_C, rmask);

		uid_t uid = geteuid();
		gid_t gid = getegid();

		if (sugid != SUGID_NONE) {
			resolve_sugid(sugid, &uid, &gid);
			set_semaphore_permissions(id[0], uid, gid, mask);
			set_semaphore_permissions(id[1], uid, gid, mask | rmask);
			set_semaphore_permissions(id[2], uid, gid, rmask);
		}

		if (mask & IPC_R) {
			verify_semaphore_permissions(id[0], mask, uid, gid);
		}

		snd(parent, id[0]);
		snd(parent, id[1]);
		snd(parent, id[2]);

		if (rcv(parent) != 0) {
			e(0);
		}

		(void)semctl(id[0], 0, IPC_RMID);
		(void)semctl(id[1], 0, IPC_RMID);
		(void)semctl(id[2], 0, IPC_RMID);
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
struct perm_test_case {
	int shift;
	int drop1;
	int drop2;
	int sugid;
};

static const struct perm_test_case PERM_TEST_CASES[] = {
	{6, DROP_ALL,  DROP_ALL,  SUGID_NONE},
	{6, DROP_NONE, DROP_ALL,  SUGID_NONROOT_USER},
	{6, DROP_USER, DROP_ALL,  SUGID_ROOT_USER},
	{3, DROP_NONE, DROP_USER, SUGID_NONE},
	{3, DROP_NONE, DROP_ALL,  SUGID_NONROOT_GROUP},
	{3, DROP_NONE, DROP_USER, SUGID_NONROOT_GROUP},
	{0, DROP_NONE, DROP_ALL,  SUGID_NONE},
};

static void
test_perm(void (* proc)(struct link *), int owner_test)
{
	struct link child1, child2;
	int id[3];
	const int TERMINATE_SIGNAL = -1;

	for (size_t i = 0; i < sizeof(PERM_TEST_CASES) / sizeof(PERM_TEST_CASES[0]); ++i) {
		const struct perm_test_case * const tc = &PERM_TEST_CASES[i];

		spawn(&child1, test_perm_child, tc->drop1);
		spawn(&child2, proc, tc->drop2);

		for (int bit = 0; bit <= 7; bit++) {
			const int mask = bit << tc->shift;
			const int rmask = 0777 & ~(7 << tc->shift);

			snd(&child1, mask);
			snd(&child1, rmask);
			snd(&child1, tc->sugid);
			id[0] = rcv(&child1);
			id[1] = rcv(&child1);
			id[2] = rcv(&child1);

			snd(&child2, (owner_test) ? tc->shift : bit);
			snd(&child2, id[0]);
			snd(&child2, id[1]);
			snd(&child2, id[2]);
			if (rcv(&child2) != 0) {
				e(0);
			}

			snd(&child1, 0);
		}

		snd(&child1, TERMINATE_SIGNAL);
		snd(&child2, TERMINATE_SIGNAL);

		collect(&child1);
		collect(&child2);
	}
}

/*
 * Test semget(2) permission checks.  Please note that the checks are advisory:
 * nothing keeps a process from opening a semaphore set with fewer privileges
 * than required by the operations the process subsequently issues on the set.
 */
#define MAX_PERM_VAL 7
#define USER_PERM_SHIFT 6

static void
check_sem_access(key_t key, int expected_id, int creation_perms,
                 int test_perm_val)
{
	const int mask = test_perm_val << USER_PERM_SHIFT;
	const int r = semget(key, 0, mask);

	const _Bool did_succeed = (r != -1);
	const _Bool should_succeed = (test_perm_val != 0) &&
	                             ((test_perm_val & creation_perms) == test_perm_val);

	if (did_succeed) {
		if (r != expected_id) {
			e(0);
		}
	} else {
		if (errno != EACCES) {
			e(0);
		}
	}

	if (did_succeed != should_succeed) {
		e(0);
	}
}

static void
check_sem_no_access(key_t key, int test_perm_val)
{
	const int mask = test_perm_val << USER_PERM_SHIFT;
	if (semget(key, 0, mask) != -1) {
		e(0);
	}
	if (errno != EACCES) {
		e(0);
	}
}

static void
test88a_perm(struct link * parent)
{
	int tbit;
	int id[3];

	while ((tbit = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		for (int bit = 0; bit <= MAX_PERM_VAL; bit++) {
			check_sem_access(KEY_A, id[0], tbit, bit);
			check_sem_access(KEY_B, id[1], tbit, bit);
			check_sem_no_access(KEY_C, bit);
		}

		snd(parent, 0);
	}
}

/*
 * Test the basic semget(2) functionality.
 */
static void
check_true(int condition)
{
	if (!condition) {
		e(0);
	}
}

static int
check_syscall(int result)
{
	if (result < 0) {
		e(0);
	}
	return result;
}

static void
check_fail(int result, int expected_errno)
{
	check_true(result == -1);
	check_true(errno == expected_errno);
}

static void
cleanup_sem(key_t key)
{
	int semid = semget(key, 0, 0600);
	if (semid >= 0) {
		check_syscall(semctl(semid, 0, IPC_RMID));
	}
}

static void
test_ipc_private_semantics(void)
{
	int id[3];

	id[0] = check_syscall(semget(IPC_PRIVATE, 1, IPC_CREAT | 0600));
	id[1] = check_syscall(
	    semget(IPC_PRIVATE, 1, IPC_CREAT | IPC_EXCL | 0600));
	id[2] = check_syscall(semget(IPC_PRIVATE, 1, 0600));

	check_true(id[0] != id[1]);
	check_true(id[1] != id[2]);
	check_true(id[0] != id[2]);

	check_syscall(semctl(id[0], 0, IPC_RMID));
	check_syscall(semctl(id[1], 0, IPC_RMID));
	check_syscall(semctl(id[2], 0, IPC_RMID));
}

static void
test_key_semantics(void)
{
	int id_key_a, id_key_b, id_temp;

	check_fail(semget(KEY_A, 1, 0600), ENOENT);
	id_key_a =
	    check_syscall(semget(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0600));

	check_fail(semget(KEY_B, 1, 0600), ENOENT);
	id_key_b = check_syscall(semget(KEY_B, 1, IPC_CREAT | 0600));

	check_true(id_key_a != id_key_b);

	id_temp = check_syscall(semget(KEY_A, 1, 0600));
	check_true(id_temp == id_key_a);

	id_temp = check_syscall(semget(KEY_B, 1, IPC_CREAT | 0600));
	check_true(id_temp == id_key_b);

	check_fail(semget(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0600), EEXIST);

	check_syscall(semctl(id_key_a, 0, IPC_RMID));
	check_syscall(semctl(id_key_b, 0, IPC_RMID));
}

static void
test_semmni_limit(const struct seminfo *seminfo)
{
	unsigned int i, j;
	int *idp;

	check_true(seminfo->semmni >= 3 && seminfo->semmni <= USHRT_MAX);

	idp = malloc(sizeof(int) * (seminfo->semmni + 1));
	check_true(idp != NULL);

	for (i = 0; i < seminfo->semmni + 1; i++) {
		idp[i] = semget(KEY_A + i, 1, IPC_CREAT | 0600);
		if (idp[i] < 0) {
			break;
		}

		for (j = 0; j < i; j++) {
			check_true(idp[i] != idp[j]);
		}
	}

	check_true(errno == ENOSPC);
	check_true(i >= 3);
	check_true(i < seminfo->semmni + 1);

	while (i-- > 0) {
		check_syscall(semctl(idp[i], 0, IPC_RMID));
	}

	free(idp);
}

static void
test_nsems_limits(const struct seminfo *seminfo)
{
	int id_a, id_b;

	check_fail(semget(KEY_A, -1, IPC_CREAT | 0600), EINVAL);
	check_fail(semget(KEY_A, 0, IPC_CREAT | 0600), EINVAL);

	check_true(seminfo->semmsl >= 3 && seminfo->semmsl <= USHRT_MAX);
	check_fail(semget(KEY_A, seminfo->semmsl + 1, IPC_CREAT | 0600),
	    EINVAL);

	id_a = check_syscall(semget(KEY_A, seminfo->semmsl, IPC_CREAT | 0600));
	check_syscall(semctl(id_a, 0, IPC_RMID));

	id_a = check_syscall(semget(KEY_A, 2, IPC_CREAT | 0600));

	id_b = check_syscall(semget(KEY_A, 0, 0600));
	check_true(id_a == id_b);
	id_b = check_syscall(semget(KEY_A, 1, 0600));
	check_true(id_a == id_b);
	id_b = check_syscall(semget(KEY_A, 2, 0600));
	check_true(id_a == id_b);

	check_fail(semget(KEY_A, 3, 0600), EINVAL);
	check_fail(semget(KEY_A, seminfo->semmsl + 1, 0600), EINVAL);

	check_syscall(semctl(id_a, 0, IPC_RMID));
}

static void
verify_semds_initial_state(int semid, key_t key, int nsems, mode_t mode,
    time_t now)
{
	struct semid_ds semds;
	unsigned int i;

	check_syscall(semctl(semid, 0, IPC_STAT, &semds));
	check_true(semds.sem_perm.uid == geteuid());
	check_true(semds.sem_perm.gid == getegid());
	check_true(semds.sem_perm.cuid == geteuid());
	check_true(semds.sem_perm.cgid == getegid());
	check_true(semds.sem_perm.mode == (SEM_ALLOC | mode));
	check_true(semds.sem_perm._key == key);
	check_true(semds.sem_nsems == nsems);
	check_true(semds.sem_otime == 0);
	check_true(semds.sem_ctime >= now && semds.sem_ctime < now + 10);

	for (i = 0; i < semds.sem_nsems; i++) {
		TEST_SEM(semid, i, 0, 0, 0, 0);
	}
}

static void
test_initial_values(const struct seminfo *seminfo)
{
	time_t now;
	int id_private, id_key_a;

	time(&now);
	check_true(seminfo->semmns >= 3 + seminfo->semmsl);

	id_private =
	    check_syscall(semget(IPC_PRIVATE, 3, IPC_CREAT | IPC_EXCL | 0642));
	id_key_a = check_syscall(
	    semget(KEY_A, seminfo->semmsl, IPC_CREAT | 0613));

	verify_semds_initial_state(id_private, IPC_PRIVATE, 3, 0642, now);
	verify_semds_initial_state(
	    id_key_a, KEY_A, seminfo->semmsl, 0613, now);

	check_syscall(semctl(id_key_a, 0, IPC_RMID));
	check_syscall(semctl(id_private, 0, IPC_RMID));
}

static void
test_permissions(void)
{
	int id_created, id_retrieved;

	id_created =
	    check_syscall(semget(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0000));

	id_retrieved = check_syscall(semget(KEY_A, 0, 0600));
	check_true(id_created == id_retrieved);

	id_retrieved = check_syscall(semget(KEY_A, 0, 0000));
	check_true(id_created == id_retrieved);

	check_syscall(semctl(id_created, 0, IPC_RMID));

	test_perm(test88a_perm, 0);
}

static void
test88a(void)
{
	struct seminfo seminfo;

	subtest = 0;

	test_ipc_private_semantics();

	cleanup_sem(KEY_A);
	cleanup_sem(KEY_B);

	test_key_semantics();

	check_syscall(semctl(0, 0, IPC_INFO, &seminfo));
	test_semmni_limit(&seminfo);
	test_nsems_limits(&seminfo);
	test_initial_values(&seminfo);
	test_permissions();
}

/*
 * Test semop(2) permission checks.
 */
struct semop_test_case {
	size_t nsops;
	int bit;
	int is_efbig_test;
	struct sembuf sops[2];
};

static const struct semop_test_case test_cases[] = {
	{1, 4, 0, {{0, 0, 0}, {0, 0, 0}}},
	{1, 2, 0, {{0, 1, 0}, {0, 0, 0}}},
	{1, 2, 0, {{0, -1, 0}, {0, 0, 0}}},
	{2, 6, 0, {{0, 0, 0}, {0, 1, 0}}},
	{2, 6, 0, {{1, 0, 0}, {0, -1, 0}}},
	{2, 4, 0, {{0, 0, 0}, {1, 0, 0}}},
	{2, 2, 0, {{0, 1, 0}, {0, -1, 0}}},
	{2, 4, 1, {{USHRT_MAX, 0, 0}, {0, 0, 0}}},
};

static void
check_authorized_semop(int semid, const struct sembuf *sops, size_t nsops,
    int tbit, int bit, int is_efbig_test)
{
	int r = semop(semid, sops, nsops);

	if (is_efbig_test && r == -1 && errno == EFBIG) {
		r = 0;
	}

	if (r == -1 && errno != EACCES) {
		e(0);
	}

	const int has_permission = ((tbit & bit) == bit);
	const int call_succeeded = (r != -1);

	if (has_permission != call_succeeded) {
		e(0);
	}
}

static void
check_unauthorized_semop(int semid, const struct sembuf *sops, size_t nsops)
{
	if (semop(semid, sops, nsops) != -1 || errno != EACCES) {
		e(0);
	}
}

static void
test88b_perm(struct link * parent)
{
	int tbit;
	int id[3];
	const size_t num_tests = sizeof(test_cases) / sizeof(test_cases[0]);

	while ((tbit = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		for (size_t i = 0; i < num_tests; i++) {
			const struct semop_test_case *tc = &test_cases[i];

			check_authorized_semop(id[0], tc->sops, tc->nsops, tbit,
			    tc->bit, tc->is_efbig_test);
			check_authorized_semop(id[1], tc->sops, tc->nsops, tbit,
			    tc->bit, tc->is_efbig_test);
			check_unauthorized_semop(id[2], tc->sops, tc->nsops);
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
	if (sig != SIGHUP || nr_signals != 0) {
		terminate_flag = 1;
		return;
	}
	nr_signals = 1;
}

/*
 * Child process for semop(2) tests, mainly testing blocking operations.
 */
static void
expect_rcv(struct link *parent, int expected_val)
{
	if (rcv(parent) != expected_val) {
		e(0);
	}
}

static void
checked_semop(int semid, struct sembuf *sops, size_t nsops)
{
	if (semop(semid, sops, nsops) != 0) {
		e(0);
	}
}

static void
checked_semop_err(int semid, struct sembuf *sops, size_t nsops, int expected_errno)
{
	if (semop(semid, sops, nsops) != -1) {
		e(0);
	}
	if (errno != expected_errno) {
		e(0);
	}
}

static void
setup_sighup_handler(void)
{
	struct sigaction act;
	memset(&act, 0, sizeof(act));
	act.sa_handler = got_signal;
	sigfillset(&act.sa_mask);
	if (sigaction(SIGHUP, &act, NULL) != 0) {
		e(0);
	}
}

static void
test88b_child(struct link *parent)
{
	int id = rcv(parent);

	{
		struct sembuf sops[] = { {.sem_op = 0} };
		checked_semop(id, sops, 1);
	}

	expect_rcv(parent, 1);
	{
		struct sembuf sops[] = { {.sem_op = -3} };
		checked_semop(id, sops, 1);
	}

	expect_rcv(parent, 2);
	{
		struct sembuf sops[] = {
			{.sem_num = 2, .sem_op = 2},
			{.sem_num = 1, .sem_op = -1},
			{.sem_num = 0, .sem_op = 1}
		};
		checked_semop(id, sops, 3);
	}

	expect_rcv(parent, 3);
	{
		struct sembuf sops[] = {
			{.sem_num = 1, .sem_op = 0},
			{.sem_num = 1, .sem_op = 1},
			{.sem_num = 0, .sem_op = 0},
			{.sem_num = 2, .sem_op = 0},
			{.sem_num = 2, .sem_op = 1}
		};
		checked_semop(id, sops, 5);
	}

	expect_rcv(parent, 4);
	{
		struct sembuf sops[] = {
			{.sem_num = 1, .sem_op = -2},
			{.sem_num = 2, .sem_op = 0}
		};
		checked_semop(id, sops, 2);
	}

	expect_rcv(parent, 5);
	{
		struct sembuf sops[] = {
			{.sem_num = 0, .sem_op = -1},
			{.sem_num = 1, .sem_op = -1, .sem_flg = IPC_NOWAIT}
		};
		checked_semop(id, sops, 2);
	}

	expect_rcv(parent, 6);
	{
		struct sembuf sops[] = {
			{.sem_num = 1, .sem_op = 0},
			{.sem_num = 0, .sem_op = 0, .sem_flg = IPC_NOWAIT}
		};
		checked_semop_err(id, sops, 2, EAGAIN);
	}

	expect_rcv(parent, 7);
	{
		struct sembuf sops[] = {
			{.sem_num = 0, .sem_op = 0},
			{.sem_num = 1, .sem_op = 1}
		};
		checked_semop(id, sops, 2);
	}

	expect_rcv(parent, 8);
	{
		struct sembuf sops[] = {
			{.sem_num = 0, .sem_op = -1},
			{.sem_num = 1, .sem_op = 2}
		};
		checked_semop_err(id, sops, 2, ERANGE);
	}

	expect_rcv(parent, 9);
	setup_sighup_handler();
	{
		struct sembuf sops[] = {
			{.sem_num = 0, .sem_op = 0},
			{.sem_num = 0, .sem_op = 1},
			{.sem_num = 1, .sem_op = 0}
		};
		checked_semop_err(id, sops, 3, EINTR);
	}
	if (nr_signals != 1) {
		e(0);
	}

	TEST_SEM(id, 0, 0, parent->pid, 0, 0);
	TEST_SEM(id, 1, 1, parent->pid, 0, 0);

	expect_rcv(parent, 10);
	{
		struct sembuf sops[] = { {.sem_op = -3} };
		checked_semop_err(id, sops, 1, EIDRM);
	}

	id = rcv(parent);
	{
		struct sembuf sops[] = {
			{.sem_num = 0, .sem_op = -1},
			{.sem_num = 1, .sem_op = 1}
		};
		checked_semop_err(id, sops, 2, ERANGE);
	}

	expect_rcv(parent, 11);
	{
		struct sembuf sops[] = {
			{.sem_num = 1, .sem_op = 0},
			{.sem_num = 0, .sem_op = -1}
		};
		checked_semop(id, sops, 2);
	}

	id = rcv(parent);
	{
		struct sembuf sops[] = {
			{.sem_num = 0, .sem_op = -1},
			{.sem_num = 1, .sem_op = 0}
		};
		checked_semop(id, sops, 2);
	}

	snd(parent, errct);
	expect_rcv(parent, 12);

	{
		struct sembuf sops[] = {
			{.sem_num = 1, .sem_op = -1},
			{.sem_num = 0, .sem_op = 3}
		};
		(void)semop(id, sops, 2);
	}

	e(0);
}

/*
 * Test the basic semop(2) functionality.
 */
static void
run_semop_setup_tests(struct sembuf *sops, const struct seminfo *info)
{
	struct semid_ds semds;
	struct sembuf *sops2;
	time_t now;
	int id;

	if ((id = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600)) == -1) e(0);

	if (semop(id, NULL, 0) != 0) e(0);

	if (semop(id, NULL, 1) != -1 || errno != EFAULT) e(0);
	if (semop(id, bad_ptr, 1) != -1 || errno != EFAULT) e(0);

	memset(page_ptr, 0, page_size);
	sops2 = ((struct sembuf *)bad_ptr) - 1;
	sops2->sem_op = 1;
	if (semop(id, sops2, 2) != -1 || errno != EFAULT) e(0);

	TEST_SEM(id, 0, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);

	time(&now);
	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[0].sem_flg = 0;
	if (semop(id, sops, 1) != 0) e(0);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime < now || semds.sem_otime >= now + 10) e(0);

	if (semop(id, sops, info->semopm) != 0) e(0);
	if (semop(id, sops, info->semopm + 1) != -1 || errno != E2BIG) e(0);
	if (semop(id, sops, SIZE_MAX) != -1 || errno != E2BIG) e(0);

	sops[1].sem_num = 1;
	if (semop(id, sops, 2) != -1 || errno != EFBIG) e(0);

	sops[1].sem_num = USHRT_MAX;
	if (semop(id, sops, 2) != -1 || errno != EFBIG) e(0);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

static void
run_semop_nowait_tests(struct sembuf *sops, const struct seminfo *info)
{
	struct sembuf *sops2;
	int id;

	if ((id = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600)) == -1) e(0);

	sops[0].sem_num = 0;
	sops[0].sem_flg = IPC_NOWAIT;

	if (info->semvmx < SHRT_MAX) {
		sops[0].sem_op = info->semvmx + 1;
		if (semop(id, sops, 1) != -1 || errno != ERANGE) e(0);
		if (semctl(id, 0, GETVAL) != 0) e(0);
	}

	sops[0].sem_op = info->semvmx;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != info->semvmx) e(0);

	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != -1 || errno != ERANGE) e(0);
	if (semctl(id, 0, GETVAL) != info->semvmx) e(0);

	sops[0].sem_op = info->semvmx;
	if (semop(id, sops, 1) != -1 || errno != ERANGE) e(0);
	if (semctl(id, 0, GETVAL) != info->semvmx) e(0);

	sops[0].sem_op = SHRT_MAX;
	if (semop(id, sops, 1) != -1 || errno != ERANGE) e(0);
	if (semctl(id, 0, GETVAL) != info->semvmx) e(0);

	if (info->semvmx < -(int)SHRT_MIN) {
		sops[0].sem_op = -info->semvmx - 1;
		if (semop(id, sops, 1) != -1 || errno != EAGAIN) e(0);
		if (semctl(id, 0, GETVAL) != info->semvmx) e(0);
	}

	sops[0].sem_op = -info->semvmx;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != 0) e(0);

	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != 0) e(0);
	sops[0].sem_op = 2;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != 2) e(0);
	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != -1 || errno != EAGAIN) e(0);
	sops[0].sem_op = -3;
	if (semop(id, sops, 1) != -1 || errno != EAGAIN) e(0);
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != 3) e(0);
	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != 2) e(0);
	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != -1 || errno != EAGAIN) e(0);
	sops[0].sem_op = -2;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != 0) e(0);
	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != 0) e(0);

	sops2 = ((struct sembuf *)bad_ptr) - 1;
	sops2->sem_op = 0;
	sops2--;
	if (semop(id, sops2, 2) != 0) e(0);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

static void
run_semop_invalid_id_tests(const struct seminfo *info)
{
	struct semid_ds semds;
	int id;
	int temp_id;

	if ((temp_id = semget(IPC_PRIVATE, 1, 0600)) == -1) e(0);
	if (semctl(temp_id, 0, IPC_RMID) != 0) e(0);

	if (semop(temp_id, NULL, 0) != -1 || errno != EINVAL) e(0);
	if (semop(-1, NULL, 0) != -1 || errno != EINVAL) e(0);
	if (semop(INT_MIN, NULL, 0) != -1 || errno != EINVAL) e(0);

	memset(&semds, 0, sizeof(semds));
	id = IXSEQ_TO_IPCID(info->semmni, semds.sem_perm);
	if (semop(id, NULL, 0) != -1 || errno != EINVAL) e(0);
}

static void
run_blocking_single_op_test(int id, struct sembuf *sops, struct link *child)
{
	memset(sops, 0, sizeof(sops[0]));
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

static void
run_blocking_multi_op_test(int id, struct sembuf *sops, struct link *child)
{
	memset(sops, 0, sizeof(sops[0]) * 2);
	if (semop(id, sops, 1) != 0) e(0);

	snd(child, 2);
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

	snd(child, 3);
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

	snd(child, 4);
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

	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 1;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != 0) e(0);

	snd(child, 5);
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

	sops[0].sem_num = 0;
	sops[0].sem_op = 1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) e(0);

	snd(child, 6);
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

static void
run_blocking_error_checks(int id, struct sembuf *sops, struct link *child,
    const struct seminfo *info)
{
	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 4;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != -1 || errno != EFBIG) e(0);

	sops[0].sem_num = 1;
	sops[0].sem_op = info->semvmx;
	if (semop(id, sops, 1) != 0) e(0);

	snd(child, 7);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 1, getpid(), 0, 1);
	TEST_SEM(id, 1, info->semvmx, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = -1;
	if (semop(id, sops, 2) != 0) e(0);
	TEST_SEM(id, 0, 0, child->pid, 0, 0);
	TEST_SEM(id, 1, info->semvmx, child->pid, 0, 0);

	sops[0].sem_num = 1;
	sops[0].sem_op = -2;
	if (semop(id, sops, 1) != 0) e(0);

	snd(child, 8);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, child->pid, 1, 0);
	TEST_SEM(id, 1, info->semvmx - 2, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) e(0);
	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	TEST_SEM(id, 1, info->semvmx - 1, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = info->semvmx - 1;
	sops[1].sem_num = 0;
	sops[1].sem_op = info->semvmx - 1;
	sops[2].sem_num = 0;
	sops[2].sem_op = 2;
	if (semop(id, sops, 3) != -1 || errno != ERANGE) e(0);
	TEST_SEM(id, 0, 1, getpid(), 0, 0);
}

static void
run_blocking_interrupts(int id, struct sembuf *sops, struct link *child)
{
	if (semctl(id, 1, SETVAL, 0) != 0) e(0);
	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) e(0);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 1, getpid(), 0, 0);

	snd(child, 9);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 1, getpid(), 0, 1);

	kill(child->pid, SIGHUP);

	snd(child, 10);
	usleep(WAIT_USECS);
	if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

static void
run_semctl_wakeup(struct link *child, const struct seminfo *info)
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
	if (semctl(id, 0, IPC_STAT, &semds) != 0 || semds.sem_otime != 0) e(0);

	if (semctl(id, 1, SETVAL, info->semvmx) != 0) e(0);
	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, info->semvmx, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0 || semds.sem_otime != 0) e(0);

	if (semctl(id, 0, SETVAL, 1) != 0) e(0);
	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, info->semvmx, 0, 0, 0);
	if (semctl(id, 0, SETVAL, 0) != 0) e(0);

	snd(child, 11);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, info->semvmx, 0, 0, 1);
	if (semctl(id, 0, IPC_STAT, &semds) != 0 || semds.sem_otime != 0) e(0);

	if (semctl(id, 1, SETVAL, 0) != 0) e(0);
	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0 || semds.sem_otime != 0) e(0);

	time(&now);
	if (semctl(id, 0, SETVAL, 2) != 0) e(0);
	TEST_SEM(id, 0, 1, child->pid, 0, 0);
	TEST_SEM(id, 1, 0, child->pid, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime < now || semds.sem_otime >= now + 10) e(0);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);

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
	if (semctl(id, 0, SETALL, val) != 0) e(0);
	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 1, 0, 0, 0);

	val[0] = 1;
	if (semctl(id, 0, SETALL, val) != 0) e(0);
	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, 1, 0, 0, 1);

	val[0] = 0;
	val[1] = 0;
	if (semctl(id, 0, SETALL, val) != 0) e(0);
	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0 || semds.sem_otime != 0) e(0);

	time(&now);
	val[0] = 1;
	if (semctl(id, 0, SETALL, val) != 0) e(0);
	TEST_SEM(id, 0, 0, child->pid, 0, 0);
	TEST_SEM(id, 1, 0, child->pid, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime < now || semds.sem_otime >= now + 10) e(0);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

static void
run_blocking_on_child_death(struct sembuf *sops, struct link *child)
{
	int id;

	if ((id = semget(IPC_PRIVATE, 2, 0600)) == -1) e(0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 1;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != 0) e(0);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);

	if (rcv(child) != 0) e(0);

	snd(child, 12);
	usleep(WAIT_USECS);
	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 1, 0);

	terminate(child);
	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

static void
run_all_blocking_tests(struct sembuf *sops, const struct seminfo *info)
{
	struct link child;
	int id;

	if ((id = semget(IPC_PRIVATE, 3, 0600)) == -1) e(0);

	spawn(&child, test88b_child, DROP_NONE);

	run_blocking_single_op_test(id, sops, &child);
	run_blocking_multi_op_test(id, sops, &child);
	run_blocking_error_checks(id, sops, &child, info);
	run_blocking_interrupts(id, sops, &child);

	run_semctl_wakeup(&child, info);
	run_blocking_on_child_death(sops, &child);
}

static void
test88b(void)
{
	struct seminfo seminfo;
	struct sembuf *sops;
	size_t size;

	subtest = 1;

	if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
	if (seminfo.semopm < 3 || seminfo.semopm > USHRT_MAX) e(0);
	if (seminfo.semvmx < 3 || seminfo.semvmx > SHRT_MAX) e(0);

	size = sizeof(sops[0]) * (seminfo.semopm + 3);
	sops = malloc(size);
	if (sops == NULL) e(0);
	memset(sops, 0, size);

	run_semop_setup_tests(sops, &seminfo);
	run_semop_nowait_tests(sops, &seminfo);
	run_semop_invalid_id_tests(&seminfo);
	test_perm(test88b_perm, 0);
	run_all_blocking_tests(sops, &seminfo);

	free(sops);
}

/*
 * Test semctl(2) permission checks, part 1: regular commands.
 */
static void
check_semctl_success(int r, int tbit, int perm_bit)
{
	if (r == -1 && errno != EACCES) {
		e(0);
	}

	const int should_succeed = ((tbit & perm_bit) == perm_bit);
	const int did_succeed = (r != -1);

	if (should_succeed != did_succeed) {
		e(0);
	}
}

static void
check_semctl_failure(int r)
{
	if (r != -1 || errno != EACCES) {
		e(0);
	}
}

static void
test_simple_read_cmds(int tbit, const int *id)
{
	static const int cmds[] = { GETVAL, GETPID, GETNCNT, GETZCNT };
	size_t i, j;

	for (i = 0; i < __arraycount(cmds); i++) {
		for (j = 0; j < 2; j++) {
			check_semctl_success(semctl(id[j], 0, cmds[i]), tbit,
			    4);
		}
		check_semctl_failure(semctl(id[2], 0, cmds[i]));
	}
}

static void
test_setval_cmd(int tbit, const int *id)
{
	size_t i;

	for (i = 0; i < 2; i++) {
		check_semctl_success(semctl(id[i], 0, SETVAL, 0), tbit, 2);
	}
	check_semctl_failure(semctl(id[2], 0, SETVAL, 0));
}

static void
test_ptr_cmds(int tbit, const int *id)
{
	struct semid_ds semds;
	unsigned short val[3];
	size_t i, j;

	struct ptr_cmd_test {
		int cmd;
		void *ptr;
		int perm_bit;
	};

	const struct ptr_cmd_test tests[] = {
		{ GETALL,   val,    4  },
		{ SETALL,   val,    2  },
		{ IPC_STAT, &semds, 4  }
	};

	memset(val, 0, sizeof(val));

	for (i = 0; i < __arraycount(tests); i++) {
		const struct ptr_cmd_test *t = &tests[i];
		for (j = 0; j < 2; j++) {
			check_semctl_success(semctl(id[j], 0, t->cmd, t->ptr),
			    tbit, t->perm_bit);
		}
		check_semctl_failure(semctl(id[2], 0, t->cmd, t->ptr));
	}
}

#ifndef IPCID_TO_IX
#define IPCID_TO_IX(id)		((id) & 0xffff)
#endif

static void
test_sem_stat_cmd(int tbit, const int *id)
{
	struct semid_ds semds;
	size_t i;

	for (i = 0; i < 2; i++) {
		check_semctl_success(semctl(IPCID_TO_IX(id[i]), 0, SEM_STAT,
		    &semds), tbit, 4);
	}
	check_semctl_failure(semctl(IPCID_TO_IX(id[2]), 0, SEM_STAT, &semds));
}

static void
test_info_cmds(void)
{
	struct seminfo seminfo;

	if (semctl(0, 0, IPC_INFO, &seminfo) == -1) {
		e(0);
	}
	if (semctl(0, 0, SEM_INFO, &seminfo) == -1) {
		e(0);
	}
}

static void
test88c_perm1(struct link * parent)
{
	int tbit;
	int id[3];

	while ((tbit = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		test_simple_read_cmds(tbit, id);
		test_setval_cmd(tbit, id);
		test_ptr_cmds(tbit, id);
		test_sem_stat_cmd(tbit, id);
		test_info_cmds();

		snd(parent, 0);
	}
}

/*
 * Test semctl(2) permission checks, part 2: the IPC_SET command.
 */
static void
test88c_perm2(struct link *parent)
{
	struct semid_ds semds;
	int shift;
	int id[3];

	while ((shift = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		memset(&semds, 0, sizeof(semds));

		const int should_succeed = (shift == 6);

		for (size_t i = 0; i < sizeof(id) / sizeof(id[0]); i++) {
			int r = semctl(id[i], 0, IPC_SET, &semds);

			if (r == -1 && errno != EPERM) {
				e(0);
			}

			const int succeeded = (r != -1);
			if (succeeded != should_succeed) {
				e(0);
			}
		}

		snd(parent, 0);
	}
}

/*
 * Test semctl(2) permission checks, part 3: the IPC_RMID command.
 */
static void
remove_semaphore_with_check(int sem_id, bool expect_success)
{
    const int result = semctl(sem_id, 0, IPC_RMID);
    const bool success = (result != -1);

    if (!success && errno != EPERM) {
        e(0);
    }

    if (success != expect_success) {
        e(0);
    }
}

static void
test88c_perm3(struct link * parent)
{
    int shift;
    while ((shift = rcv(parent)) != -1) {
        const bool expect_success = (shift == 6);
        const int ids_to_process = 3;

        for (int i = 0; i < ids_to_process; ++i) {
            const int sem_id = rcv(parent);
            remove_semaphore_with_check(sem_id, expect_success);
        }

        snd(parent, 0);
    }
}

/*
 * Test the basic semctl(2) functionality.
 */
static void
expect_semctl_fail(int semid, int semnum, int cmd, void *arg, int expected_errno)
{
	if (semctl(semid, semnum, cmd, arg) != -1)
		e(0);
	if (errno != expected_errno)
		e(0);
}

static int
expect_semctl_ok(int semid, int semnum, int cmd, void *arg)
{
	int r = semctl(semid, semnum, cmd, arg);
	if (r == -1)
		e(0);
	return r;
}

static void
wait_for_new_timestamp(time_t base_time)
{
	time_t now;
	while (time(&now) == base_time) {
		usleep(250000);
	}
}

static void
test_get_cmds(int id, int badid1, int badid2, time_t ctime_before)
{
	static const int cmds[] = { GETVAL, GETPID, GETNCNT, GETZCNT };
	struct semid_ds semds;

	for (size_t i = 0; i < __arraycount(cmds); i++) {
		for (int j = 0; j < 3; j++) {
			expect_semctl_ok(id, j, cmds[i], NULL);
		}

		expect_semctl_fail(badid1, 0, cmds[i], NULL, EINVAL);
		expect_semctl_fail(badid2, 0, cmds[i], NULL, EINVAL);
		expect_semctl_fail(-1, 0, cmds[i], NULL, EINVAL);
		expect_semctl_fail(INT_MIN, 0, cmds[i], NULL, EINVAL);

		expect_semctl_fail(id, -1, cmds[i], NULL, EINVAL);
		expect_semctl_fail(id, 3, cmds[i], NULL, EINVAL);

		expect_semctl_ok(id, 0, IPC_STAT, &semds);
		if (semds.sem_otime != 0) e(0);
		if (semds.sem_ctime != ctime_before) e(0);
	}
}

static void
test_getall_cmd(int id, int badid1, int badid2, time_t ctime_before)
{
	unsigned short val[4];
	struct semid_ds semds;

	for (int j = 0; j < 5; j++) {
		for (size_t i = 0; i < __arraycount(val); i++) val[i] = USHRT_MAX;
		expect_semctl_ok(id, j - 1, GETALL, val);
		for (int i = 0; i < 3; i++)
			if (val[i] != 0) e(0);
		if (val[3] != USHRT_MAX) e(0);
	}

	for (size_t i = 0; i < __arraycount(val); i++) val[i] = USHRT_MAX;
	expect_semctl_fail(badid1, 0, GETALL, val, EINVAL);
	expect_semctl_fail(badid2, 0, GETALL, val, EINVAL);
	expect_semctl_fail(-1, 0, GETALL, val, EINVAL);
	expect_semctl_fail(INT_MIN, 0, GETALL, val, EINVAL);
	for (size_t i = 0; i < __arraycount(val); i++)
		if (val[i] != USHRT_MAX) e(0);

	expect_semctl_fail(id, 0, GETALL, NULL, EFAULT);
	expect_semctl_fail(id, 0, GETALL, bad_ptr, EFAULT);
	expect_semctl_fail(id, 0, GETALL, ((unsigned short *)bad_ptr) - 2, EFAULT);
	expect_semctl_ok(id, 0, GETALL, ((unsigned short *)bad_ptr) - 3);

	expect_semctl_ok(id, 0, IPC_STAT, &semds);
	if (semds.sem_otime != 0) e(0);
	if (semds.sem_ctime != ctime_before) e(0);
}

static void
test_ipc_stat_cmd(int id, int badid1, int badid2, time_t ctime_before)
{
	char statbuf[sizeof(struct semid_ds) + 1];
	struct semid_ds semds;

	memset(statbuf, 0x5a, sizeof(statbuf));

	expect_semctl_fail(badid1, 0, IPC_STAT, statbuf, EINVAL);
	expect_semctl_fail(badid2, 0, IPC_STAT, statbuf, EINVAL);
	expect_semctl_fail(-1, 0, IPC_STAT, statbuf, EINVAL);
	expect_semctl_fail(INT_MIN, 0, IPC_STAT, statbuf, EINVAL);

	for (size_t i = 0; i < sizeof(statbuf); i++)
		if ((unsigned char)statbuf[i] != 0x5a) e(0);

	expect_semctl_ok(id, 0, IPC_STAT, statbuf);
	if ((unsigned char)statbuf[sizeof(statbuf) - 1] != 0x5a) e(0);

	expect_semctl_fail(id, 0, IPC_STAT, NULL, EFAULT);
	expect_semctl_fail(id, 0, IPC_STAT, bad_ptr, EFAULT);
	expect_semctl_ok(id, 0, IPC_STAT, ((struct semid_ds *)bad_ptr) - 1);

	expect_semctl_ok(id, -1, IPC_STAT, &semds);
	if (semds.sem_otime != 0) e(0);
	if (semds.sem_ctime != ctime_before) e(0);
}

static void
test_sem_stat_cmd(int id, int id2, const struct seminfo *info)
{
	char statbuf[sizeof(struct semid_ds) + 1];
	unsigned short seen[2] = {0, 0};

	expect_semctl_fail(-1, 0, SEM_STAT, statbuf, EINVAL);
	expect_semctl_fail(info->semmni, 0, SEM_STAT, statbuf, EINVAL);

	memset(statbuf, 0x5a, sizeof(statbuf));
	for (unsigned int i = 0; i < sizeof(statbuf); i++)
		if ((unsigned char)statbuf[i] != 0x5a) e(0);

	for (int i = 0; i < info->semmni; i++) {
		errno = 0;
		int r = semctl(i, i / 2 - 1, SEM_STAT, statbuf);
		if (r == -1) {
			if (errno != EINVAL) e(0);
			continue;
		}

		if (r < 0) e(0);
		struct semid_ds semds;
		memcpy(&semds, statbuf, sizeof(semds));

		if (!(semds.sem_perm.mode & SEM_ALLOC)) e(0);
		if (semds.sem_ctime == 0) e(0);
		if (IXSEQ_TO_IPCID(i, semds.sem_perm) != r) e(0);
		if (r == id) {
			seen[0]++;
			expect_semctl_fail(i, 0, SEM_STAT, NULL, EFAULT);
			expect_semctl_fail(i, 0, SEM_STAT, bad_ptr, EFAULT);
		} else if (r == id2) {
			seen[1]++;
		}
	}

	if (seen[0] != 1) e(0);
	if (seen[1] != 1) e(0);
	if ((unsigned char)statbuf[sizeof(statbuf) - 1] != 0x5a) e(0);
}

static void
test_setval_cmd(int id, int badid1, int badid2, const struct seminfo *info,
    time_t ctime_before)
{
	struct semid_ds semds;
	time_t now;

	expect_semctl_fail(badid1, 0, SETVAL, 1, EINVAL);
	expect_semctl_fail(badid2, 0, SETVAL, 1, EINVAL);
	expect_semctl_fail(-1, 0, SETVAL, 1, EINVAL);
	expect_semctl_fail(INT_MIN, 0, SETVAL, 1, EINVAL);
	expect_semctl_fail(id, -1, SETVAL, 1, EINVAL);
	expect_semctl_fail(id, 3, SETVAL, 1, EINVAL);
	expect_semctl_fail(id, 0, SETVAL, -1, ERANGE);
	expect_semctl_fail(id, 0, SETVAL, info->semvmx + 1, ERANGE);

	TEST_SEM(id, 0, 0, 0, 0, 0);
	expect_semctl_ok(id, 0, IPC_STAT, &semds);
	if (semds.sem_otime != 0) e(0);
	if (semds.sem_ctime != ctime_before) e(0);

	expect_semctl_ok(id, 1, SETVAL, 0);
	expect_semctl_ok(id, 0, IPC_STAT, &semds);
	if (semds.sem_otime != 0) e(0);
	time(&now);
	if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);
	TEST_SEM(id, 1, 0, 0, 0, 0);

	expect_semctl_ok(id, 2, SETVAL, info->semvmx);
	TEST_SEM(id, 2, info->semvmx, 0, 0, 0);

	expect_semctl_ok(id, 0, SETVAL, 1);
	TEST_SEM(id, 0, 1, 0, 0, 0);
}

static void
test_setall_cmd(int id, int badid1, int badid2, const struct seminfo *info)
{
	unsigned short val[4];
	struct semid_ds semds;
	time_t ctime_before, now;

	expect_semctl_ok(id, 0, IPC_STAT, &semds);
	ctime_before = semds.sem_ctime;
	wait_for_new_timestamp(ctime_before);
	time(&now);

	expect_semctl_fail(badid1, 0, SETALL, val, EINVAL);
	expect_semctl_fail(badid2, 0, SETALL, val, EINVAL);
	expect_semctl_fail(-1, 0, SETALL, val, EINVAL);
	expect_semctl_fail(INT_MIN, 0, SETALL, val, EINVAL);

	val[0] = info->semvmx + 1; val[1] = 0; val[2] = 0;
	expect_semctl_fail(id, 0, SETALL, val, ERANGE);

	val[0] = 0; val[1] = 1; val[2] = info->semvmx + 1;
	expect_semctl_fail(id, 0, SETALL, val, ERANGE);

	expect_semctl_fail(id, 0, SETALL, NULL, EFAULT);
	expect_semctl_fail(id, 0, SETALL, bad_ptr, EFAULT);
	expect_semctl_fail(id, 0, SETALL, ((unsigned short *)bad_ptr) - 2, EFAULT);

	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	TEST_SEM(id, 2, info->semvmx, 0, 0, 0);

	expect_semctl_ok(id, 0, IPC_STAT, &semds);
	if (semds.sem_otime != 0) e(0);
	if (semds.sem_ctime != ctime_before) e(0);

	val[0] = info->semvmx; val[1] = 0; val[2] = 0;
	expect_semctl_ok(id, 0, SETALL, val);

	expect_semctl_ok(id, 0, IPC_STAT, &semds);
	if (semds.sem_otime != 0) e(0);
	time(&now);
	if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);
	TEST_SEM(id, 0, info->semvmx, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	TEST_SEM(id, 2, 0, 0, 0, 0);

	val[0] = 0; val[1] = 1; val[2] = info->semvmx;
	expect_semctl_ok(id, INT_MAX, SETALL, val);
	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, 1, 0, 0, 0);
	TEST_SEM(id, 2, info->semvmx, 0, 0, 0);

	memset(page_ptr, 0, page_size);
	expect_semctl_ok(id, 0, SETALL, ((unsigned short *)bad_ptr) - 3);
	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	TEST_SEM(id, 2, 0, 0, 0, 0);
}

static void
test_ipc_set_cmd(int id, int badid1, int badid2)
{
	struct semid_ds semds, osemds;
	time_t ctime_before, now;

	expect_semctl_ok(id, 0, IPC_STAT, &semds);
	ctime_before = semds.sem_ctime;
	wait_for_new_timestamp(ctime_before);
	time(&now);

	expect_semctl_fail(badid1, 0, IPC_SET, &semds, EINVAL);
	expect_semctl_fail(badid2, 0, IPC_SET, &semds, EINVAL);
	expect_semctl_fail(-1, 0, IPC_SET, &semds, EINVAL);
	expect_semctl_fail(INT_MIN, 0, IPC_SET, &semds, EINVAL);
	expect_semctl_fail(id, 0, IPC_SET, NULL, EFAULT);
	expect_semctl_fail(id, 0, IPC_SET, bad_ptr, EFAULT);

	expect_semctl_ok(id, 0, IPC_STAT, &osemds);
	if (osemds.sem_otime != 0) e(0);
	if (osemds.sem_ctime != ctime_before) e(0);

	memset(&semds, 0x5b, sizeof(semds));
	semds.sem_perm.mode = 0712;
	semds.sem_perm.uid = UID_MAX;
	semds.sem_perm.gid = GID_MAX - 1;
	expect_semctl_ok(id, 0, IPC_SET, &semds);

	expect_semctl_ok(id, 0, IPC_STAT, &semds);
	if (semds.sem_perm.mode != (SEM_ALLOC | 0712)) e(0);
	if (semds.sem_perm.uid != UID_MAX) e(0);
	if (semds.sem_perm.gid != GID_MAX - 1) e(0);
	if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);

	semds.sem_perm.uid = osemds.sem_perm.uid;
	semds.sem_perm.gid = osemds.sem_perm.gid;
	for (unsigned int i = 0; i < 0777; i++) {
		semds.sem_perm.mode = i;
		expect_semctl_ok(id, i / 2 - 1, IPC_SET, &semds);
		struct semid_ds new_semds;
		expect_semctl_ok(id, i / 2 - 2, IPC_STAT, &new_semds);
		if (new_semds.sem_perm.mode != (SEM_ALLOC | i)) e(0);
	}
	expect_semctl_ok(id, 0, IPC_SET, ((struct semid_ds *)bad_ptr) - 1);
}

static void
test_ipc_rmid_cmd(int id, int id2, int badid1, int badid2)
{
	struct semid_ds semds;
	expect_semctl_fail(badid1, 0, IPC_RMID, NULL, EINVAL);
	expect_semctl_fail(badid2, 0, IPC_RMID, NULL, EINVAL);
	expect_semctl_fail(-1, 0, IPC_RMID, NULL, EINVAL);
	expect_semctl_fail(INT_MIN, 0, IPC_RMID, NULL, EINVAL);

	expect_semctl_ok(id, 0, IPC_RMID, NULL);
	expect_semctl_fail(id, 0, IPC_RMID, NULL, EINVAL);
	expect_semctl_fail(id, 0, IPC_STAT, &semds, EINVAL);

	expect_semctl_ok(id2, 1, IPC_RMID, NULL);
	expect_semctl_fail(id2, 1, IPC_RMID, NULL, EINVAL);
}

static void
test_info_cmds(void)
{
	const int cmds[] = { IPC_INFO, SEM_INFO };
	for (size_t i = 0; i < __arraycount(cmds); i++) {
		int cmd = cmds[i];
		struct seminfo info;
		memset(&info, 0xff, sizeof(info));

		int r = expect_semctl_ok(0, 0, cmd, &info);
		if (r < 1 || r >= info.semmni) e(0);

		if (info.semmni < 3 || info.semmni > USHRT_MAX) e(0);
		if (info.semmsl < 3 || info.semmsl > USHRT_MAX) e(0);
		if (info.semopm < 3 || info.semopm > USHRT_MAX) e(0);
		if (info.semvmx < 3 || info.semvmx > SHRT_MAX) e(0);

		expect_semctl_ok(INT_MAX, -1, cmd, &info);
		expect_semctl_ok(-1, INT_MAX, cmd, &info);

		expect_semctl_fail(0, 0, cmd, NULL, EFAULT);
		expect_semctl_fail(0, 0, cmd, bad_ptr, EFAULT);
		expect_semctl_ok(0, 0, cmd, ((struct seminfo *)bad_ptr) - 1);
	}
}

static void
test88c(void)
{
	struct seminfo seminfo;
	struct semid_ds semds;
	int id, id2, badid1, badid2;
	time_t ctime_before;

	subtest = 2;
	expect_semctl_ok(0, 0, IPC_INFO, &seminfo);

	test_perm(test88c_perm1, 0);
	test_perm(test88c_perm2, 1);
	test_perm(test88c_perm3, 1);

	badid1 = expect_semctl_ok(IPC_PRIVATE, 1, 0600, NULL);
	expect_semctl_ok(badid1, 0, IPC_RMID, NULL);

	memset(&semds, 0, sizeof(semds));
	badid2 = IXSEQ_TO_IPCID(seminfo.semmni, semds.sem_perm);

	id = expect_semctl_ok(IPC_PRIVATE, 3, IPC_CREAT | 0600, NULL);
	expect_semctl_ok(id, 0, IPC_STAT, &semds);
	if (semds.sem_otime != 0) e(0);
	if (semds.sem_ctime == 0) e(0);

	ctime_before = semds.sem_ctime;
	wait_for_new_timestamp(ctime_before);

	test_get_cmds(id, badid1, badid2, ctime_before);
	test_getall_cmd(id, badid1, badid2, ctime_before);
	test_ipc_stat_cmd(id, badid1, badid2, ctime_before);

	id2 = expect_semctl_ok(KEY_A, seminfo.semmsl, IPC_CREAT | 0642, NULL);
	test_sem_stat_cmd(id, id2, &seminfo);

	test_setval_cmd(id, badid1, badid2, &seminfo, ctime_before);
	test_setall_cmd(id, badid1, badid2, &seminfo);
	test_ipc_set_cmd(id, badid1, badid2);
	test_ipc_rmid_cmd(id, id2, badid1, badid2);

	id = expect_semctl_ok(IPC_PRIVATE, 3, 0600, NULL);
	id2 = expect_semctl_ok(IPC_PRIVATE, 1, 0600, NULL);

	test_info_cmds();

	expect_semctl_ok(id2, 0, IPC_RMID, NULL);
	expect_semctl_fail(id, 0, INT_MIN, NULL, EINVAL);
	expect_semctl_fail(id, 0, INT_MAX, NULL, EINVAL);
	expect_semctl_ok(id, 0, IPC_RMID, NULL);
}

/*
 * Test SEM_UNDO support.  Right now this functionality is missing altogether.
 * For now, we test that any attempt to use SEM_UNDO fails.
 */
static void
test88d(void)
{
	const int sem_permissions = 0600;
	const int num_semaphores = 1;
	const size_t num_operations = 1;

	subtest = 3;

	int id = semget(IPC_PRIVATE, num_semaphores, sem_permissions);
	if (id == -1) {
		e(0);
	}

	if (!(SHRT_MAX & SEM_UNDO)) {
		e(0);
	}

	struct sembuf sop = {
		.sem_num = 0,
		.sem_op = 1,
		.sem_flg = SHRT_MAX
	};

	if (semop(id, &sop, num_operations) != -1) {
		e(0);
	}

	if (errno != EINVAL) {
		e(0);
	}

	if (semctl(id, 0, IPC_RMID, NULL) != 0) {
		e(0);
	}
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
static void
test88e_childaux(struct link * parent)
{
	const int child = rcv(parent);
	const int id = rcv(parent);
	const int num = rcv(parent);
	const size_t num_sops = 3;
	struct sembuf sops[num_sops] = { {0} };

	switch (child) {
	case 1:
		sops[0].sem_num = num;
		sops[0].sem_op = 1;
		sops[1].sem_num = num;
		sops[1].sem_op = 0;
		sops[2].sem_num = 0;
		sops[2].sem_op = 1;
		break;
	case 2: {
		struct seminfo seminfo;
		if (semctl(0, 0, IPC_INFO, &seminfo) == -1) {
			e(0);
		}
		const short op_val = -seminfo.semvmx;
		sops[0].sem_num = num;
		sops[0].sem_op = op_val;
		sops[1].sem_num = num;
		sops[1].sem_op = op_val;
		sops[2].sem_num = 0;
		sops[2].sem_op = 1;
		break;
	}
	default:
		e(0);
		break;
	}

	snd(parent, 0);

	if (semop(id, sops, num_sops) == 0 || errno != EIDRM) {
		e(0);
	}
}

/*
 * First child procedure.
 */
static void
test88e_child1(struct link * parent)
{
	struct sembuf sops[3] = {{ .sem_num = 2, .sem_op = -1 }};
	size_t nsops;
	int expect;

	const int match = rcv(parent);
	const int id = rcv(parent);

	switch (match) {
	case MATCH_FIRST:
	case MATCH_BOTH:
	case MATCH_CASCADE:
	case MATCH_ALL:
		sops[1].sem_num = 3;
		sops[1].sem_op = 1;
		nsops = 2;
		expect = 0;
		break;
	case MATCH_SECOND:
		sops[1].sem_num = 3;
		sops[1].sem_op = -1;
		sops[2].sem_num = 0;
		sops[2].sem_op = 1;
		nsops = 3;
		expect = -1;
		break;
	case MATCH_KILL:
		sops[1].sem_num = 0;
		sops[1].sem_op = 1;
		nsops = 2;
		expect = INT_MIN;
		break;
	default:
		e(0);
		return;
	}

	snd(parent, 0);

	if (semop(id, sops, nsops) != expect || (expect == -1 && errno != EIDRM)) {
		e(0);
	}
}

/*
 * Second child procedure.
 */
static void
test88e_child2(struct link * parent)
{
	struct sembuf sops[2];
	size_t nsops;
	int sem_id;
	int expected_rc;

	const int match_type = rcv(parent);
	sem_id = rcv(parent);

	memset(sops, 0, sizeof(sops));
	sops[0].sem_num = 2;
	sops[0].sem_op = -1;
	nsops = 2;
	expected_rc = 0;

	switch (match_type) {
	case MATCH_FIRST:
		sops[1].sem_op = 1;
		expected_rc = -1;
		break;
	case MATCH_SECOND:
	case MATCH_KILL:
		nsops = 1;
		break;
	case MATCH_BOTH:
	case MATCH_ALL:
		sops[1].sem_num = 3;
		sops[1].sem_op = 1;
		break;
	case MATCH_CASCADE:
		sops[0].sem_num = 3;
		nsops = 1;
		break;
	default:
		e(0);
	}

	snd(parent, 0);

	const int semop_rc = semop(sem_id, sops, nsops);

	if (semop_rc != expected_rc) {
		e(0);
	}
	if (expected_rc == -1 && errno != EIDRM) {
		e(0);
	}
}

/*
 * Third child procedure.
 */
static void
test88e_child3(struct link * parent)
{
	const int match = rcv(parent);
	const int id = rcv(parent);

	if (match != MATCH_ALL) {
		e(0);
	}

	struct sembuf sops[1] = {
		{
			.sem_num = 3,
			.sem_op = -2,
			.sem_flg = 0
		}
	};

	snd(parent, 0);

	if (semop(id, sops, 1) != 0) {
		e(0);
	}
}

/*
 * Perform one test for operations affecting multiple processes.
 */
#define SPAWN_AUX_FIRST (1U << 0)
#define SPAWN_AUX_SECOND (1U << 1)
#define AUX_BLOCK_ON_MAIN_SEM (1U << 2)

#define SEM_FAILURE_FLAG 0
#define SEM_AUX_BLOCK 1
#define SEM_MAIN_OP 2
#define SEM_EXTRA_OP 3
#define NUM_SEMS 4

struct sub88e_state {
	struct link aux1, aux2, child1, child2, child3;
	int id;
	unsigned int match;
	unsigned int resume;
	unsigned int aux;
	int aux_zcnt;
	int aux_ncnt;
};

static void
spawn_main_child(struct link *child, void (*entry)(void), int drop_flags,
    unsigned int match, int sem_id)
{
	spawn(child, entry, drop_flags);
	snd(child, match);
	snd(child, sem_id);
	if (rcv(child) != 0)
		e(0);
}

static void
spawn_aux_child(struct link *child, int child_num, int drop_flags,
    int sem_id, int sem_idx)
{
	spawn(child, test88e_childaux, drop_flags);
	snd(child, child_num);
	snd(child, sem_id);
	snd(child, sem_idx);
	if (rcv(child) != 0)
		e(0);
}

static void
setup_and_spawn_children(struct sub88e_state *st)
{
	st->id = semget(IPC_PRIVATE, NUM_SEMS, 0666);
	if (st->id == -1)
		e(0);

	st->aux_zcnt = 0;
	st->aux_ncnt = 0;

	if (st->aux & SPAWN_AUX_FIRST) {
		int sem_idx = (st->aux & AUX_BLOCK_ON_MAIN_SEM) ?
		    SEM_MAIN_OP : SEM_AUX_BLOCK;
		spawn_aux_child(&st->aux1, 1, DROP_ALL, st->id, sem_idx);
		if (st->aux & AUX_BLOCK_ON_MAIN_SEM)
			st->aux_zcnt++;
	}

	spawn_main_child(&st->child1, test88e_child1, DROP_ALL, st->match,
	    st->id);

	switch (st->match) {
	case MATCH_FIRST:
	case MATCH_SECOND:
	case MATCH_KILL:
		usleep(WAIT_USECS);
		break;
	}

	spawn_main_child(&st->child2, test88e_child2, DROP_NONE, st->match,
	    st->id);

	if (st->match == MATCH_ALL) {
		spawn_main_child(&st->child3, test88e_child3, DROP_USER,
		    st->match, st->id);
	}

	if (st->aux & SPAWN_AUX_SECOND) {
		int sem_idx = (st->aux & AUX_BLOCK_ON_MAIN_SEM) ?
		    SEM_MAIN_OP : SEM_AUX_BLOCK;
		spawn_aux_child(&st->aux2, 2, DROP_NONE, st->id, sem_idx);
		if (st->aux & AUX_BLOCK_ON_MAIN_SEM)
			st->aux_ncnt++;
	}

	usleep(WAIT_USECS);
}

static int
run_pre_resume_tests(struct sub88e_state *st)
{
	int inc = 1;

	switch (st->match) {
	case MATCH_FIRST:
	case MATCH_SECOND:
		TEST_SEM(st->id, SEM_MAIN_OP, 0, 0, 2 + st->aux_ncnt, st->aux_zcnt);
		TEST_SEM(st->id, SEM_EXTRA_OP, 0, 0, 0, 0);
		break;
	case MATCH_KILL:
		TEST_SEM(st->id, SEM_MAIN_OP, 0, 0, 2 + st->aux_ncnt, st->aux_zcnt);
		terminate(&st->child1);
		usleep(WAIT_USECS);
		TEST_SEM(st->id, SEM_MAIN_OP, 0, 0, 1 + st->aux_ncnt, st->aux_zcnt);
		TEST_SEM(st->id, SEM_EXTRA_OP, 0, 0, 0, 0);
		break;
	case MATCH_BOTH:
		TEST_SEM(st->id, SEM_MAIN_OP, 0, 0, 2 + st->aux_ncnt, st->aux_zcnt);
		TEST_SEM(st->id, SEM_EXTRA_OP, 0, 0, 0, 0);
		inc = 2;
		break;
	case MATCH_CASCADE:
		TEST_SEM(st->id, SEM_MAIN_OP, 0, 0, 1 + st->aux_ncnt, st->aux_zcnt);
		TEST_SEM(st->id, SEM_EXTRA_OP, 0, 0, 1, 0);
		break;
	case MATCH_ALL:
		TEST_SEM(st->id, SEM_MAIN_OP, 0, 0, 2 + st->aux_ncnt, st->aux_zcnt);
		TEST_SEM(st->id, SEM_EXTRA_OP, 0, 0, 1, 0);
		inc = 2;
		break;
	default:
		e(0);
	}

	TEST_SEM(st->id, SEM_FAILURE_FLAG, 0, 0, 0, 0);
	TEST_SEM(st->id, SEM_AUX_BLOCK, 0, 0, -1, -1);
	return inc;
}

static void
resume_children(struct sub88e_state *st, int inc)
{
	switch (st->resume) {
	case RESUME_SEMOP: {
		struct sembuf sop = {
			.sem_num = SEM_MAIN_OP, .sem_op = inc, .sem_flg = 0
		};
		if (semop(st->id, &sop, 1) != 0)
			e(0);
		break;
	}
	case RESUME_SETVAL:
		if (semctl(st->id, SEM_MAIN_OP, SETVAL, inc) != 0)
			e(0);
		break;
	case RESUME_SETALL: {
		unsigned short val[NUM_SEMS] = {0};
		val[SEM_MAIN_OP] = inc;
		if (semctl(st->id, 0, SETALL, val) != 0)
			e(0);
		break;
	}
	default:
		e(0);
	}
}

static void
run_post_resume_tests_and_cleanup(struct sub88e_state *st)
{
	switch (st->match) {
	case MATCH_FIRST:
		TEST_SEM(st->id, SEM_MAIN_OP, 0, st->child1.pid, 1 + st->aux_ncnt,
		    st->aux_zcnt);
		TEST_SEM(st->id, SEM_EXTRA_OP, 1, st->child1.pid, 0, 0);
		collect(&st->child1);
		break;
	case MATCH_SECOND:
		TEST_SEM(st->id, SEM_MAIN_OP, 0, st->child2.pid, 1 + st->aux_ncnt,
		    st->aux_zcnt);
		TEST_SEM(st->id, SEM_EXTRA_OP, 0, 0, 0, 0);
		collect(&st->child2);
		break;
	case MATCH_KILL:
		TEST_SEM(st->id, SEM_MAIN_OP, 0, st->child2.pid, st->aux_ncnt,
		    st->aux_zcnt);
		TEST_SEM(st->id, SEM_EXTRA_OP, 0, 0, 0, 0);
		collect(&st->child2);
		break;
	case MATCH_BOTH:
		TEST_SEM(st->id, SEM_MAIN_OP, 0, -1, st->aux_ncnt, st->aux_zcnt);
		TEST_SEM(st->id, SEM_EXTRA_OP, 2, -1, 0, 0);
		collect(&st->child1);
		collect(&st->child2);
		break;
	case MATCH_CASCADE:
		TEST_SEM(st->id, SEM_MAIN_OP, 0, st->child1.pid, st->aux_ncnt,
		    st->aux_zcnt);
		TEST_SEM(st->id, SEM_EXTRA_OP, 0, st->child2.pid, 0, 0);
		collect(&st->child1);
		collect(&st->child2);
		break;
	case MATCH_ALL:
		TEST_SEM(st->id, SEM_MAIN_OP, 0, -1, st->aux_ncnt, st->aux_zcnt);
		TEST_SEM(st->id, SEM_EXTRA_OP, 0, st->child3.pid, 0, 0);
		collect(&st->child1);
		collect(&st->child2);
		collect(&st->child3);
		break;
	default:
		e(0);
	}

	TEST_SEM(st->id, SEM_FAILURE_FLAG, 0, 0, 0, 0);
	TEST_SEM(st->id, SEM_AUX_BLOCK, 0, 0, -1, -1);

	if (semctl(st->id, 0, IPC_RMID) != 0)
		e(0);

	switch (st->match) {
	case MATCH_FIRST:
		collect(&st->child2);
		break;
	case MATCH_SECOND:
		collect(&st->child1);
		break;
	case MATCH_KILL:
	case MATCH_BOTH:
	case MATCH_CASCADE:
	case MATCH_ALL:
		break;
	default:
		e(0);
	}

	if (st->aux & SPAWN_AUX_FIRST)
		collect(&st->aux1);
	if (st->aux & SPAWN_AUX_SECOND)
		collect(&st->aux2);
}

static void
sub88e(unsigned int match, unsigned int resume, unsigned int aux)
{
	struct sub88e_state st = { .match = match, .resume = resume, .aux = aux };
	int inc;

	setup_and_spawn_children(&st);
	inc = run_pre_resume_tests(&st);
	resume_children(&st, inc);
	run_post_resume_tests_and_cleanup(&st);
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
	enum {
		SUBTEST_ID = 4,
		AUX_LOOP_START = 1,
		AUX_LOOP_END = 8
	};

	subtest = SUBTEST_ID;

	for (unsigned int match = 0; match < NR_MATCHES; match++) {
		for (unsigned int resume = 0; resume < NR_RESUMES; resume++) {
			for (unsigned int aux = AUX_LOOP_START; aux <= AUX_LOOP_END; aux++) {
				sub88e(match, resume, aux);
			}
		}
	}
}

/*
 * Verify that non-root processes can use sysctl(2) to see semaphore sets
 * created by root.
 */
static void
test88f_child(struct link * parent)
{
	static const int mib[] = { CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_INFO,
	    KERN_SYSVIPC_SEM_INFO };
	const unsigned int mib_count = sizeof(mib) / sizeof(mib[0]);
	struct sem_sysctl_info *semsi = NULL;
	size_t len;
	int id[2];
	int id2;
	int seen[2] = {0, 0};
	int i;

	id[0] = rcv(parent);
	id[1] = rcv(parent);

	if (sysctl(mib, mib_count, NULL, &len, NULL, 0) != 0) {
		e(0);
	}

	semsi = malloc(len);
	if (semsi == NULL) {
		e(0);
	}

	if (sysctl(mib, mib_count, semsi, &len, NULL, 0) != 0) {
		free(semsi);
		e(0);
	}

	for (i = 0; i < semsi->seminfo.semmni; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC)) {
			continue;
		}

		id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
		if (id2 == id[0]) {
			seen[0]++;
		} else if (id2 == id[1]) {
			seen[1]++;
		}
	}

	free(semsi);

	if (seen[0] != 1 || seen[1] != 1) {
		e(0);
	}
}

/*
 * Test sysctl(2) based information retrieval.  This test aims to ensure that
 * in particular ipcs(1) and ipcrm(1) will be able to do their jobs.
 */
static bool
verify_sem_properties(const struct semid_ds_sysctl *semds, key_t key,
    unsigned short nsems, mode_t mode)
{
	const uid_t euid = geteuid();
	const gid_t egid = getegid();

	return semds->sem_perm.uid == euid &&
	    semds->sem_perm.gid == egid &&
	    semds->sem_perm.cuid == euid &&
	    semds->sem_perm.cgid == egid &&
	    semds->sem_perm.mode == (SEM_ALLOC | mode) &&
	    semds->sem_perm._key == key &&
	    semds->sem_nsems == nsems &&
	    semds->sem_otime == 0 &&
	    semds->sem_ctime != 0;
}

static bool
find_sem_slots(const struct sem_sysctl_info *semsi, int sem_count,
    const int ids[2], int32_t slots[2])
{
	slots[0] = -1;
	slots[1] = -1;

	for (int32_t i = 0; i < sem_count; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC)) {
			continue;
		}

		const int current_id = IXSEQ_TO_IPCID(i,
		    semsi->semids[i].sem_perm);
		if (current_id == ids[0]) {
			if (slots[0] != -1) return false;
			slots[0] = i;
		} else if (current_id == ids[1]) {
			if (slots[1] != -1) return false;
			slots[1] = i;
		}
	}
	return slots[0] != -1 && slots[1] != -1;
}

static bool
verify_sems_removed(const struct sem_sysctl_info *semsi, int sem_count,
    const int ids[2])
{
	for (int32_t i = 0; i < sem_count; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC)) {
			continue;
		}
		const int current_id = IXSEQ_TO_IPCID(i,
		    semsi->semids[i].sem_perm);
		if (current_id == ids[0] || current_id == ids[1]) {
			return false;
		}
	}
	return true;
}

static void
test88f(void)
{
	static const int mib[] = { CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_INFO,
	    KERN_SYSVIPC_SEM_INFO };
	enum { SEM_A_NSEMS = 5, SEM_B_NSEMS = 3 };
	static const mode_t SEM_A_MODE = 0612;
	static const mode_t SEM_B_MODE = 0650;

	struct sem_sysctl_info *semsi = NULL;
	int sem_ids[2] = { -1, -1 };
	bool ok = false;

	struct seminfo seminfo;
	size_t len = sizeof(seminfo);
	if (sysctl(mib, __arraycount(mib), &seminfo, &len, NULL, 0) != 0 ||
	    len != sizeof(seminfo)) {
		goto cleanup;
	}

	struct seminfo seminfo2;
	if (semctl(0, 0, IPC_INFO, &seminfo2) == -1 ||
	    memcmp(&seminfo, &seminfo2, sizeof(seminfo)) != 0) {
		goto cleanup;
	}

	if (seminfo.semmni <= 0 || seminfo.semmni > SHRT_MAX) {
		goto cleanup;
	}

	const size_t expected_size = sizeof(*semsi) +
	    sizeof(semsi->semids[0]) * ((size_t)seminfo.semmni - 1);

	len = 0;
	if (sysctl(mib, __arraycount(mib), NULL, &len, NULL, 0) != 0 ||
	    len != expected_size) {
		goto cleanup;
	}

	sem_ids[0] = semget(KEY_A, SEM_A_NSEMS, IPC_CREAT | SEM_A_MODE);
	if (sem_ids[0] < 0) {
		goto cleanup;
	}
	sem_ids[1] = semget(IPC_PRIVATE, SEM_B_NSEMS, SEM_B_MODE);
	if (sem_ids[1] < 0) {
		goto cleanup;
	}

	semsi = malloc(expected_size);
	if (semsi == NULL) {
		goto cleanup;
	}

	len = expected_size;
	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0 ||
	    len != expected_size ||
	    memcmp(&semsi->seminfo, &seminfo, sizeof(seminfo)) != 0) {
		goto cleanup;
	}

	int32_t slots[2];
	if (!find_sem_slots(semsi, seminfo.semmni, sem_ids, slots) ||
	    !verify_sem_properties(&semsi->semids[slots[0]], KEY_A,
		SEM_A_NSEMS, SEM_A_MODE) ||
	    !verify_sem_properties(&semsi->semids[slots[1]], IPC_PRIVATE,
		SEM_B_NSEMS, SEM_B_MODE)) {
		goto cleanup;
	}

	struct link child;
	spawn(&child, test88f_child, DROP_ALL);
	snd(&child, sem_ids[0]);
	snd(&child, sem_ids[1]);
	collect(&child);

	const int original_sem_ids[2] = { sem_ids[0], sem_ids[1] };
	if (semctl(sem_ids[0], 0, IPC_RMID) != 0) {
		goto cleanup;
	}
	sem_ids[0] = -1;

	if (semctl(sem_ids[1], 0, IPC_RMID) != 0) {
		goto cleanup;
	}
	sem_ids[1] = -1;

	len = expected_size;
	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0 ||
	    len != expected_size) {
		goto cleanup;
	}

	if (!verify_sems_removed(semsi, seminfo.semmni, original_sem_ids)) {
		goto cleanup;
	}

	ok = true;

cleanup:
	free(semsi);
	if (sem_ids[0] != -1) {
		(void)semctl(sem_ids[0], 0, IPC_RMID);
	}
	if (sem_ids[1] != -1) {
		(void)semctl(sem_ids[1], 0, IPC_RMID);
	}

	if (!ok) {
		e(0);
	}
}

/*
 * Initialize the test.
 */
static void
test88_init(void)
{
	static const int mib[] = { CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_SEM };

	if (setuid(geteuid()) != 0) {
		perror("setuid failed");
		exit(EXIT_FAILURE);
	}

	const struct group *gr = getgrnam(ROOT_GROUP);
	if (gr == NULL) {
		fprintf(stderr, "Group '%s' not found\n", ROOT_GROUP);
		exit(EXIT_FAILURE);
	}

	if (setgid(gr->gr_gid) != 0) {
		perror("setgid failed");
		exit(EXIT_FAILURE);
	}
	if (setegid(gr->gr_gid) != 0) {
		perror("setegid failed");
		exit(EXIT_FAILURE);
	}

	int ipc_enabled;
	size_t len = sizeof(ipc_enabled);
	if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), &ipc_enabled, &len, NULL, 0) != 0) {
		perror("sysctl for KERN_SYSVIPC_SEM failed");
		exit(EXIT_FAILURE);
	}
	if (len != sizeof(ipc_enabled)) {
		fprintf(stderr, "sysctl returned an unexpected size\n");
		exit(EXIT_FAILURE);
	}

	if (ipc_enabled == 0) {
		printf("skipped\n");
		cleanup();
		exit(0);
	}

	page_size = getpagesize();
	size_t map_size = page_size * 2;
	page_ptr = mmap(NULL, map_size, PROT_READ | PROT_WRITE,
	    MAP_ANON | MAP_PRIVATE, -1, 0);
	if (page_ptr == MAP_FAILED) {
		perror("mmap failed");
		exit(EXIT_FAILURE);
	}

	bad_ptr = (char *)page_ptr + page_size;
	if (munmap(bad_ptr, page_size) != 0) {
		perror("munmap of second page failed");
		munmap(page_ptr, page_size);
		exit(EXIT_FAILURE);
	}
}

/*
 * Test program for SysV IPC semaphores.
 */
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <limits.h>

#define ITERATIONS 100
#define START_VALUE 88

void start(int arg);
void test88_init(void);
void test88a(void);
void test88b(void);
void test88c(void);
void test88d(void);
void test88e(void);
void test88f(void);
void quit(void);

enum TestMask {
    TEST_A = 1 << 0,
    TEST_B = 1 << 1,
    TEST_C = 1 << 2,
    TEST_D = 1 << 3,
    TEST_E = 1 << 4,
    TEST_F = 1 << 5,
    DEFAULT_MASK = 0xFF
};

typedef void (*TestFunction)(void);

typedef struct {
    int mask;
    TestFunction function;
} TestCase;

static const TestCase test_cases[] = {
    { TEST_A, test88a },
    { TEST_B, test88b },
    { TEST_C, test88c },
    { TEST_D, test88d },
    { TEST_E, test88e },
    { TEST_F, test88f }
};

#define NUM_TESTS (sizeof(test_cases) / sizeof(test_cases[0]))

static int parse_test_mask(int argc, char *argv[])
{
    if (argc < 2) {
        return DEFAULT_MASK;
    }

    char *endptr;
    errno = 0;
    long value = strtol(argv[1], &endptr, 0);

    if (errno != 0 || endptr == argv[1] || *endptr != '\0' || value < 0 || value > INT_MAX) {
        fprintf(stderr, "Error: Invalid or out-of-range value for test mask: %s\n", argv[1]);
        return -1;
    }

    return (int)value;
}

int main(int argc, char **argv)
{
    int mask = parse_test_mask(argc, argv);
    if (mask < 0) {
        return EXIT_FAILURE;
    }

    start(START_VALUE);
    test88_init();

    for (int i = 0; i < ITERATIONS; i++) {
        for (size_t j = 0; j < NUM_TESTS; j++) {
            if (mask & test_cases[j].mask) {
                test_cases[j].function();
            }
        }
    }

    quit();
    return EXIT_SUCCESS;
}
