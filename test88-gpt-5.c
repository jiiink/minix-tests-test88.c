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
spawn(struct link *link, void (*proc)(struct link *), int drop)
{
	struct passwd *pw = NULL;
	struct group *gr = NULL;
	int up[2] = { -1, -1 }, dn[2] = { -1, -1 };

	if (link == NULL || proc == NULL) {
		e(0);
		return;
	}

	(void)fflush(stdout);
	(void)fflush(stderr);

	if (pipe(up) != 0) {
		e(0);
		return;
	}
	if (pipe(dn) != 0) {
		close(up[0]);
		close(up[1]);
		e(0);
		return;
	}

	link->pid = fork();
	if (link->pid == -1) {
		close(up[0]);
		close(up[1]);
		close(dn[0]);
		close(dn[1]);
		e(0);
		return;
	}

	if (link->pid == 0) {
		close(up[1]);
		close(dn[0]);

		link->pid = getppid();
		link->rcvfd = up[0];
		link->sndfd = dn[1];

		errct = 0;

		switch (drop) {
		case DROP_ALL:
			if (setgroups(0, NULL) != 0) e(0);
			gr = getgrnam(NONROOT_GROUP);
			if (gr == NULL) e(0);
			if (setgid(gr->gr_gid) != 0) e(0);
			if (setegid(gr->gr_gid) != 0) e(0);
			/* fall through */
		case DROP_USER:
			pw = getpwnam(NONROOT_USER);
			if (pw == NULL) e(0);
			if (setuid(pw->pw_uid) != 0) e(0);
			break;
		default:
			break;
		}

		proc(link);
		_exit(errct);
	}

	close(up[0]);
	close(dn[1]);

	link->sndfd = up[1];
	link->rcvfd = dn[0];
}

/*
 * Wait for a child process to terminate, and clean up.
 */
static void
collect(struct link *lnk)
{
	int status;
	pid_t r;

	close(lnk->sndfd);
	close(lnk->rcvfd);

	do {
		r = waitpid(lnk->pid, &status, 0);
	} while (r == -1 && errno == EINTR);

	if (r == -1) {
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
static void
terminate(struct link *link)
{
	int status = 0;
	pid_t ret;

	if (kill(link->pid, SIGKILL) != 0) e(0);

	(void)close(link->sndfd);
	(void)close(link->rcvfd);

	do {
		ret = waitpid(link->pid, &status, 0);
	} while (ret == -1 && errno == EINTR);

	if (ret <= 0) {
		e(0);
		return;
	}

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

/*
 * Send an integer value to the child or parent.
 */
#include <errno.h>
#include <unistd.h>
#include <stddef.h>

static void
snd(struct link * link, int val)
{
	size_t total = 0;
	const unsigned char *buf = (const unsigned char *)&val;
	const size_t len = sizeof(val);

	if (link == NULL) {
		e(0);
		return;
	}

	while (total < len) {
		ssize_t n = write(link->sndfd, buf + total, len - total);
		if (n < 0) {
			if (errno == EINTR) {
				continue;
			}
			e(0);
			return;
		}
		if (n == 0) {
			e(0);
			return;
		}
		total += (size_t)n;
	}
}

/*
 * Receive an integer value from the child or parent, or -1 on EOF.
 */
static int
rcv(struct link *link)
{
    ssize_t r;
    int val;

    if (link == NULL || link->rcvfd < 0) e(0);

    do {
        r = read(link->rcvfd, &val, sizeof(val));
    } while (r < 0 && errno == EINTR);

    if (r == 0) return -1;
    if (r != (ssize_t)sizeof(val)) e(0);

    return val;
}

/*
 * Child procedure that creates semaphore sets.
 */
static void
test_perm_child(struct link *parent)
{
	struct passwd *pw;
	struct group *gr;
	struct semid_ds semds;
	uid_t uid;
	gid_t gid;
	int mask, rmask, sugid, id[3];
	const key_t keys[3] = { KEY_A, KEY_B, KEY_C };
	const int numsems = 3;

	while ((mask = rcv(parent)) != -1) {
		int flags[3];
		int modes[3];
		int i;

		rmask = rcv(parent);
		sugid = rcv(parent);

		flags[0] = IPC_CREAT | IPC_EXCL | ((sugid == SUGID_NONE) ? mask : 0);
		flags[1] = IPC_CREAT | IPC_EXCL | mask | rmask;
		flags[2] = IPC_CREAT | IPC_EXCL | rmask;

		for (i = 0; i < 3; i++) {
			id[i] = semget(keys[i], numsems, flags[i]);
			if (id[i] == -1) e(0);
		}

		uid = geteuid();
		gid = getegid();
		if (sugid != SUGID_NONE) {
			switch (sugid) {
			case SUGID_ROOT_USER:
				if ((pw = getpwnam(ROOT_USER)) == NULL) e(0);
				uid = pw->pw_uid;
				break;
			case SUGID_NONROOT_USER:
				if ((pw = getpwnam(NONROOT_USER)) == NULL) e(0);
				uid = pw->pw_uid;
				break;
			case SUGID_ROOT_GROUP:
				if ((gr = getgrnam(ROOT_GROUP)) == NULL) e(0);
				gid = gr->gr_gid;
				break;
			case SUGID_NONROOT_GROUP:
				if ((gr = getgrnam(NONROOT_GROUP)) == NULL) e(0);
				gid = gr->gr_gid;
				break;
			default:
				e(0);
			}

			modes[0] = mask;
			modes[1] = mask | rmask;
			modes[2] = rmask;

			semds.sem_perm.uid = uid;
			semds.sem_perm.gid = gid;

			for (i = 0; i < 3; i++) {
				semds.sem_perm.mode = modes[i];
				if (semctl(id[i], 0, IPC_SET, &semds) != 0) e(0);
			}
		}

		if (mask & IPC_R) {
			if (semctl(id[0], 0, IPC_STAT, &semds) != 0) e(0);
			if (semds.sem_perm.mode != (SEM_ALLOC | mask)) e(0);
			if (semds.sem_perm.uid != uid) e(0);
			if (semds.sem_perm.gid != gid) e(0);
			if (semds.sem_perm.cuid != geteuid()) e(0);
			if (semds.sem_perm.cgid != getegid()) e(0);
		}

		snd(parent, id[0]);
		snd(parent, id[1]);
		snd(parent, id[2]);

		if (rcv(parent) != 0) e(0);

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
static void
test_perm(void (*proc)(struct link *), int owner_test)
{
	struct link child1, child2;
	int id[3];
	int n, bit;

	const struct {
		int shift;
		int drop1;
		int drop2;
		int sugid;
	} scenarios[] = {
		{6, DROP_ALL,  DROP_ALL,  SUGID_NONE},
		{6, DROP_NONE, DROP_ALL,  SUGID_NONROOT_USER},
		{6, DROP_USER, DROP_ALL,  SUGID_ROOT_USER},
		{3, DROP_NONE, DROP_USER, SUGID_NONE},
		{3, DROP_NONE, DROP_ALL,  SUGID_NONROOT_GROUP},
		{3, DROP_NONE, DROP_USER, SUGID_NONROOT_GROUP},
		{0, DROP_NONE, DROP_ALL,  SUGID_NONE}
	};

	int scenario_count = (int)(sizeof(scenarios) / sizeof(scenarios[0]));

	for (n = 0; n < scenario_count; n++) {
		int shift = scenarios[n].shift;
		int rmask = 0777 & ~(7 << shift);

		spawn(&child1, test_perm_child, scenarios[n].drop1);
		spawn(&child2, proc, scenarios[n].drop2);

		for (bit = 0; bit < 8; bit++) {
			int mask = bit << shift;

			snd(&child1, mask);
			snd(&child1, rmask);
			snd(&child1, scenarios[n].sugid);
			id[0] = rcv(&child1);
			id[1] = rcv(&child1);
			id[2] = rcv(&child1);

			snd(&child2, owner_test ? shift : bit);
			snd(&child2, id[0]);
			snd(&child2, id[1]);
			snd(&child2, id[2]);
			if (rcv(&child2) != 0) e(0);

			snd(&child1, 0);
		}

		snd(&child1, -1);
		snd(&child2, -1);

		collect(&child1);
		collect(&child2);
	}
}

/*
 * Test semget(2) permission checks.  Please note that the checks are advisory:
 * nothing keeps a process from opening a semaphore set with fewer privileges
 * than required by the operations the process subsequently issues on the set.
 */
static void check_sem_open(int key, int mask, int expected_id, int expected_success)
{
	int r = semget(key, 0, mask);
	if (r == -1 && errno != EACCES) e(0);
	if ((r != -1) != expected_success) e(0);
	if (r != -1 && r != expected_id) e(0);
}

static void
test88a_perm(struct link * parent)
{
	int tbit;

	while ((tbit = rcv(parent)) != -1) {
		int idA = rcv(parent);
		int idB = rcv(parent);
		int idC = rcv(parent);
		int bit;

		for (bit = 0; bit <= 7; bit++) {
			int mask = bit << 6;
			int expected = (bit != 0) && ((bit & tbit) == bit);

			check_sem_open(KEY_A, mask, idA, expected);
			check_sem_open(KEY_B, mask, idB, expected);
			check_sem_open(KEY_C, mask, idC, 0);
		}

		snd(parent, 0);
	}
}

/*
 * Test the basic semget(2) functionality.
 */
static void remove_sem(int id)
{
	if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

static void
test88a(void)
{
	struct seminfo seminfo;
	struct semid_ds semds;
	time_t now;
	unsigned int i, j;
	int id[3], *idp;

	subtest = 0;

	if ((id[0] = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600)) < 0) e(0);
	if ((id[1] = semget(IPC_PRIVATE, 1, IPC_CREAT | IPC_EXCL | 0600)) < 0) e(0);
	if ((id[2] = semget(IPC_PRIVATE, 1, 0600)) < 0) e(0);

	if (id[0] == id[1]) e(0);
	if (id[1] == id[2]) e(0);
	if (id[0] == id[2]) e(0);

	remove_sem(id[0]);
	remove_sem(id[1]);
	remove_sem(id[2]);

	if ((id[0] = semget(KEY_A, 0, 0600)) >= 0 && semctl(id[0], 0, IPC_RMID) == -1) e(0);
	if ((id[0] = semget(KEY_B, 0, 0600)) >= 0 && semctl(id[0], 0, IPC_RMID) == -1) e(0);

	if (semget(KEY_A, 1, 0600) != -1) e(0);
	if (errno != ENOENT) e(0);

	if ((id[0] = semget(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0600)) < 0) e(0);

	if (semget(KEY_B, 1, 0600) != -1) e(0);
	if (errno != ENOENT) e(0);

	if ((id[1] = semget(KEY_B, 1, IPC_CREAT | 0600)) < 0) e(0);

	if (id[0] == id[1]) e(0);

	if ((id[2] = semget(KEY_A, 1, 0600)) < 0) e(0);
	if (id[2] != id[0]) e(0);

	if ((id[2] = semget(KEY_B, 1, IPC_CREAT | 0600)) < 0) e(0);
	if (id[2] != id[1]) e(0);

	if (semget(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0600) != -1) e(0);
	if (errno != EEXIST) e(0);

	remove_sem(id[0]);
	remove_sem(id[1]);

	if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
	if (seminfo.semmni < 3 || seminfo.semmni > USHRT_MAX) e(0);

	{
		size_t count = (size_t)seminfo.semmni + 1U;
		if (count == 0 || count > SIZE_MAX / sizeof(*idp)) e(0);
		idp = malloc(count * sizeof(*idp));
		if (idp == NULL) e(0);
	}

	for (i = 0; i < seminfo.semmni + 1; i++) {
		if ((idp[i] = semget(KEY_A + i, 1, IPC_CREAT | 0600)) < 0) {
			break;
		}
		for (j = 0; j < i; j++) {
			if (idp[i] == idp[j]) e(0);
		}
	}

	if (errno != ENOSPC) e(0);
	if (i < 3) e(0);
	if (i == seminfo.semmni + 1) e(0);

	while (i-- > 0) {
		remove_sem(idp[i]);
	}

	free(idp);

	if (semget(KEY_A, -1, IPC_CREAT | 0600) != -1) e(0);
	if (errno != EINVAL) e(0);

	if (semget(KEY_A, 0, IPC_CREAT | 0600) != -1) e(0);
	if (errno != EINVAL) e(0);

	if (seminfo.semmsl < 3 || seminfo.semmsl > USHRT_MAX) e(0);
	if (semget(KEY_A, seminfo.semmsl + 1, IPC_CREAT | 0600) != -1) e(0);
	if (errno != EINVAL) e(0);

	if ((id[0] = semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0600)) < 0) e(0);
	remove_sem(id[0]);

	if ((id[0] = semget(KEY_A, 2, IPC_CREAT | 0600)) < 0) e(0);

	if ((id[1] = semget(KEY_A, 0, 0600)) < 0) e(0);
	if (id[0] != id[1]) e(0);

	if ((id[1] = semget(KEY_A, 1, 0600)) < 0) e(0);
	if (id[0] != id[1]) e(0);

	if ((id[1] = semget(KEY_A, 2, 0600)) < 0) e(0);
	if (id[0] != id[1]) e(0);

	if ((id[1] = semget(KEY_A, 3, 0600)) != -1) e(0);
	if (errno != EINVAL) e(0);

	if ((id[1] = semget(KEY_A, seminfo.semmsl + 1, 0600)) != -1) e(0);
	if (errno != EINVAL) e(0);

	remove_sem(id[0]);

	if (time(&now) == (time_t)-1) e(0);
	if (seminfo.semmns < 3 + seminfo.semmsl) e(0);
	if ((id[0] = semget(IPC_PRIVATE, 3, IPC_CREAT | IPC_EXCL | 0642)) < 0) e(0);
	if ((id[1] = semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0613)) < 0) e(0);

	if (semctl(id[0], 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_perm.uid != geteuid()) e(0);
	if (semds.sem_perm.gid != getegid()) e(0);
	if (semds.sem_perm.cuid != geteuid()) e(0);
	if (semds.sem_perm.cgid != getegid()) e(0);
	if (semds.sem_perm.mode != (SEM_ALLOC | 0642)) e(0);
	if (semds.sem_perm._key != IPC_PRIVATE) e(0);
	if (semds.sem_nsems != 3) e(0);
	if (semds.sem_otime != 0) e(0);
	if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);

	for (i = 0; i < semds.sem_nsems; i++) {
		TEST_SEM(id[0], i, 0, 0, 0, 0);
	}

	if (semctl(id[1], 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_perm.uid != geteuid()) e(0);
	if (semds.sem_perm.gid != getegid()) e(0);
	if (semds.sem_perm.cuid != geteuid()) e(0);
	if (semds.sem_perm.cgid != getegid()) e(0);
	if (semds.sem_perm.mode != (SEM_ALLOC | 0613)) e(0);
	if (semds.sem_perm._key != KEY_A) e(0);
	if (semds.sem_nsems != seminfo.semmsl) e(0);
	if (semds.sem_otime != 0) e(0);
	if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);

	for (i = 0; i < semds.sem_nsems; i++) {
		TEST_SEM(id[1], i, 0, 0, 0, 0);
	}

	remove_sem(id[1]);
	remove_sem(id[0]);

	if ((id[0] = semget(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0000)) < 0) e(0);

	if ((id[1] = semget(KEY_A, 0, 0600)) < 0) e(0);
	if (id[0] != id[1]) e(0);

	if ((id[1] = semget(KEY_A, 0, 0000)) < 0) e(0);
	if (id[0] != id[1]) e(0);

	remove_sem(id[0]);

	test_perm(test88a_perm, 0);
}

/*
 * Test semop(2) permission checks.
 */
static int semop_check_or_e(int semid, struct sembuf *sops, size_t nsops, int adjust_efbig, int tbit, int bit)
{
	int r = semop(semid, sops, nsops);
	if (adjust_efbig && r == -1 && errno == EFBIG) r = 0;
	if (r < 0 && errno != EACCES) e(0);
	if (((bit & tbit) == bit) != (r != -1)) e(0);
	return r;
}

static void expect_eacces(int semid, struct sembuf *sops, size_t nsops)
{
	int r = semop(semid, sops, nsops);
	if (r != -1) e(0);
	if (errno != EACCES) e(0);
}

static void
test88b_perm(struct link * parent)
{
	struct sembuf sops[2];
	size_t nsops;
	int i, tbit, bit, id[3];

	typedef struct {
		size_t nsops;
		unsigned short sem_num[2];
		short sem_op[2];
		int bit;
		int adjust_efbig;
	} sop_case;

	static const sop_case cases[8] = {
		{1, {0, 0}, { 0,  0}, 4, 0},
		{1, {0, 0}, { 1,  0}, 2, 0},
		{1, {0, 0}, {-1,  0}, 2, 0},
		{2, {0, 0}, { 0,  1}, 6, 0},
		{2, {1, 0}, { 0, -1}, 6, 0},
		{2, {0, 1}, { 0,  0}, 4, 0},
		{2, {0, 0}, { 1, -1}, 2, 0},
		{2, {USHRT_MAX, 0}, { 0,  0}, 4, 1}
	};

	while ((tbit = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		for (i = 0; i < 8; i++) {
			const sop_case *c = &cases[i];

			sops[0].sem_num = c->sem_num[0];
			sops[0].sem_op  = c->sem_op[0];
			sops[0].sem_flg = 0;

			sops[1].sem_num = c->sem_num[1];
			sops[1].sem_op  = c->sem_op[1];
			sops[1].sem_flg = 0;

			nsops = c->nsops;
			bit = c->bit;

			semop_check_or_e(id[0], sops, nsops, c->adjust_efbig, tbit, bit);
			semop_check_or_e(id[1], sops, nsops, c->adjust_efbig, tbit, bit);
			expect_eacces(id[2], sops, nsops);
		}

		snd(parent, 0);
	}
}

/*
 * Signal handler.
 */
static void got_signal(int sig)
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
static inline void expect_rcv(struct link *parent, int expected) { if (rcv(parent) != expected) e(0); }
static inline void expect_semop_ret(int id, struct sembuf *sops, size_t nsops, int expected_ret) { if (semop(id, sops, nsops) != expected_ret) e(0); }
static inline void expect_semop_err(int id, struct sembuf *sops, size_t nsops, int expected_errno) { errno = 0; if (semop(id, sops, nsops) != -1) e(0); if (errno != expected_errno) e(0); }
static inline void set_sop(struct sembuf *s, unsigned short num, short op, short flg) { s->sem_num = num; s->sem_op = op; s->sem_flg = flg; }
static inline void expect_sigaction(int sig, const struct sigaction *a) { if (sigaction(sig, a, NULL) != 0) e(0); }

static void
test88b_child(struct link * parent)
{
	struct sembuf sops[5];
	struct sigaction act;
	int id;

	id = rcv(parent);

	memset(sops, 0, sizeof(sops));
	expect_semop_ret(id, sops, 1, 0);

	expect_rcv(parent, 1);

	set_sop(&sops[0], 0, -3, 0);
	expect_semop_ret(id, sops, 1, 0);

	expect_rcv(parent, 2);

	set_sop(&sops[0], 2, 2, 0);
	set_sop(&sops[1], 1, -1, 0);
	set_sop(&sops[2], 0, 1, 0);
	expect_semop_ret(id, sops, 3, 0);

	expect_rcv(parent, 3);

	set_sop(&sops[0], 1, 0, 0);
	set_sop(&sops[1], 1, 1, 0);
	set_sop(&sops[2], 0, 0, 0);
	set_sop(&sops[3], 2, 0, 0);
	set_sop(&sops[4], 2, 1, 0);
	expect_semop_ret(id, sops, 5, 0);

	expect_rcv(parent, 4);

	set_sop(&sops[0], 1, -2, 0);
	set_sop(&sops[1], 2, 0, 0);
	expect_semop_ret(id, sops, 2, 0);

	expect_rcv(parent, 5);

	set_sop(&sops[0], 0, -1, 0);
	set_sop(&sops[1], 1, -1, IPC_NOWAIT);
	expect_semop_ret(id, sops, 2, 0);

	expect_rcv(parent, 6);

	set_sop(&sops[0], 1, 0, 0);
	set_sop(&sops[1], 0, 0, IPC_NOWAIT);
	expect_semop_err(id, sops, 2, EAGAIN);

	expect_rcv(parent, 7);

	set_sop(&sops[0], 0, 0, 0);
	set_sop(&sops[1], 1, 1, 0);
	expect_semop_ret(id, sops, 2, 0);

	expect_rcv(parent, 8);

	set_sop(&sops[0], 0, -1, 0);
	set_sop(&sops[1], 1, 2, 0);
	expect_semop_err(id, sops, 2, ERANGE);

	memset(&act, 0, sizeof(act));
	act.sa_handler = got_signal;
	sigfillset(&act.sa_mask);
	expect_sigaction(SIGHUP, &act);

	expect_rcv(parent, 9);

	memset(sops, 0, sizeof(sops));
	set_sop(&sops[0], 0, 0, 0);
	set_sop(&sops[1], 0, 1, 0);
	set_sop(&sops[2], 1, 0, 0);
	expect_semop_err(id, sops, 3, EINTR);
	if (nr_signals != 1) e(0);

	TEST_SEM(id, 0, 0, parent->pid, 0, 0);
	TEST_SEM(id, 1, 1, parent->pid, 0, 0);

	expect_rcv(parent, 10);

	memset(sops, 0, sizeof(sops));
	set_sop(&sops[0], 0, -3, 0);
	expect_semop_err(id, sops, 1, EIDRM);

	id = rcv(parent);

	set_sop(&sops[0], 0, -1, 0);
	set_sop(&sops[1], 1, 1, 0);
	expect_semop_err(id, sops, 2, ERANGE);

	expect_rcv(parent, 11);

	set_sop(&sops[0], 1, 0, 0);
	set_sop(&sops[1], 0, -1, 0);
	expect_semop_ret(id, sops, 2, 0);

	id = rcv(parent);

	set_sop(&sops[0], 0, -1, 0);
	set_sop(&sops[1], 1, 0, 0);
	expect_semop_ret(id, sops, 2, 0);

	snd(parent, errct);
	expect_rcv(parent, 12);

	set_sop(&sops[0], 1, -1, 0);
	set_sop(&sops[1], 0, 3, 0);
	(void)semop(id, sops, 2);

	e(0);
}

/*
 * Test the basic semop(2) functionality.
 */
static void
test88b(void)
{
	struct seminfo seminfo;
	struct semid_ds semds;
	struct sembuf *sops = NULL, *sops2 = NULL;
	size_t size;
	struct link child;
	time_t now = 0;
	unsigned short val[2] = {0, 0};
	int id = -1;

	subtest = 1;

	if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);

	if (seminfo.semopm < 3 || seminfo.semopm > USHRT_MAX) e(0);

	if (seminfo.semopm > SIZE_MAX / sizeof(*sops) - 1) e(0);
	size = (seminfo.semopm + 1) * sizeof(*sops);
	sops = calloc(seminfo.semopm + 1, sizeof(*sops));
	if (sops == NULL) e(0);

	if ((id = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600)) == -1) e(0);

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

	TEST_SEM(id, 0, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);

	time(&now);
	if (semop(id, sops, 1) != 0) e(0);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime < now || semds.sem_otime >= now + 10) e(0);

	if (semop(id, sops, seminfo.semopm) != 0) e(0);

	if (semop(id, sops, seminfo.semopm + 1) != -1) e(0);
	if (errno != E2BIG) e(0);

	if (semop(id, sops, SIZE_MAX) != -1) e(0);
	if (errno != E2BIG) e(0);

	sops[1].sem_num = 1;
	if (semop(id, sops, 2) != -1) e(0);
	if (errno != EFBIG) e(0);

	sops[1].sem_num = USHRT_MAX;
	if (semop(id, sops, 2) != -1) e(0);
	if (errno != EFBIG) e(0);

	if (seminfo.semvmx < 3 || seminfo.semvmx > SHRT_MAX) e(0);

	sops[0].sem_flg = IPC_NOWAIT;

	if (seminfo.semvmx < SHRT_MAX) {
		sops[0].sem_op = seminfo.semvmx + 1;
		if (semop(id, sops, 1) != -1) e(0);
		if (errno != ERANGE) e(0);
		if (semctl(id, 0, GETVAL) != 0) e(0);
	}

	sops[0].sem_op = seminfo.semvmx;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != seminfo.semvmx) e(0);

	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != -1) e(0);
	if (errno != ERANGE) e(0);
	if (semctl(id, 0, GETVAL) != seminfo.semvmx) e(0);

	sops[0].sem_op = seminfo.semvmx;
	if (semop(id, sops, 1) != -1) e(0);
	if (errno != ERANGE) e(0);
	if (semctl(id, 0, GETVAL) != seminfo.semvmx) e(0);

	sops[0].sem_op = SHRT_MAX;
	if (semop(id, sops, 1) != -1) e(0);
	if (errno != ERANGE) e(0);
	if (semctl(id, 0, GETVAL) != seminfo.semvmx) e(0);

	if (seminfo.semvmx < -(int)SHRT_MIN) {
		sops[0].sem_op = -seminfo.semvmx - 1;
		if (semop(id, sops, 1) != -1) e(0);
		if (errno != EAGAIN) e(0);
		if (semctl(id, 0, GETVAL) != seminfo.semvmx) e(0);
	}

	sops[0].sem_op = -seminfo.semvmx;
	if (semop(id, sops, 1) != 0) e(0);
	if (semctl(id, 0, GETVAL) != 0) e(0);

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

	sops2->sem_op = 0;
	sops2--;
	if (semop(id, sops2, 2) != 0) e(0);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);

	if (semop(id, NULL, 0) != -1) e(0);
	if (errno != EINVAL) e(0);

	if (semop(-1, NULL, 0) != -1) e(0);
	if (errno != EINVAL) e(0);

	if (semop(INT_MIN, NULL, 0) != -1) e(0);
	if (errno != EINVAL) e(0);

	memset(&semds, 0, sizeof(semds));
	id = IXSEQ_TO_IPCID(seminfo.semmni, semds.sem_perm);
	if (semop(id, NULL, 0) != -1) e(0);
	if (errno != EINVAL) e(0);

	test_perm(test88b_perm, 0);

	if ((id = semget(IPC_PRIVATE, 3, 0600)) == -1) e(0);

	memset(sops, 0, sizeof(*sops));
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);

	TEST_SEM(id, 0, 1, getpid(), 0, 0);

	spawn(&child, test88b_child, DROP_NONE);

	snd(&child, id);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, getpid(), 0, 1);

	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) e(0);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);

	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);

	TEST_SEM(id, 0, 1, getpid(), 0, 0);

	snd(&child, 1);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, getpid(), 1, 0);

	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 2, getpid(), 1, 0);

	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);

	memset(sops, 0, sizeof(*sops) * 2);
	if (semop(id, sops, 1) != 0) e(0);

	snd(&child, 2);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, 0, 1, 0);
	TEST_SEM(id, 2, 0, 0, 0, 0);

	sops[0].sem_num = 1;
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, child.pid, 0, 0);
	TEST_SEM(id, 1, 0, child.pid, 0, 0);
	TEST_SEM(id, 2, 2, child.pid, 0, 0);

	snd(&child, 3);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, child.pid, 0, 1);
	TEST_SEM(id, 1, 0, child.pid, 0, 0);
	TEST_SEM(id, 2, 2, child.pid, 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 2;
	sops[1].sem_op = -2;
	if (semop(id, sops, 2) != 0) e(0);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, 1, child.pid, 0, 0);
	TEST_SEM(id, 2, 1, child.pid, 0, 0);

	snd(&child, 4);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, 1, child.pid, 1, 0);
	TEST_SEM(id, 2, 1, child.pid, 0, 0);

	sops[0].sem_num = 1;
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) e(0);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, 2, getpid(), 0, 0);
	TEST_SEM(id, 2, 1, child.pid, 0, 1);

	sops[0].sem_num = 2;
	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) e(0);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, 0, child.pid, 0, 0);
	TEST_SEM(id, 2, 0, child.pid, 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 1;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != 0) e(0);

	snd(&child, 5);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, getpid(), 1, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) e(0);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, 0, child.pid, 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) e(0);

	snd(&child, 6);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	TEST_SEM(id, 1, 1, getpid(), 0, 1);

	sops[0].sem_num = 1;
	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) e(0);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 4;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != -1) e(0);
	if (errno != EFBIG) e(0);

	sops[0].sem_num = 1;
	sops[0].sem_op = seminfo.semvmx;
	if (semop(id, sops, 1) != 0) e(0);

	snd(&child, 7);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, getpid(), 0, 1);
	TEST_SEM(id, 1, seminfo.semvmx, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = -1;
	if (semop(id, sops, 2) != 0) e(0);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, seminfo.semvmx, child.pid, 0, 0);

	sops[0].sem_num = 1;
	sops[0].sem_op = -2;
	if (semop(id, sops, 1) != 0) e(0);

	snd(&child, 8);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 1, 0);
	TEST_SEM(id, 1, seminfo.semvmx - 2, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) e(0);

	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	TEST_SEM(id, 1, seminfo.semvmx - 1, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = seminfo.semvmx - 1;
	sops[1].sem_num = 0;
	sops[1].sem_op = seminfo.semvmx - 1;
	sops[2].sem_num = 0;
	sops[2].sem_op = 2;
	if (semop(id, sops, 3) != -1) e(0);
	if (errno != ERANGE) e(0);

	TEST_SEM(id, 0, 1, getpid(), 0, 0);

	if (semctl(id, 1, SETVAL, 0) != 0) e(0);
	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) e(0);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 1, getpid(), 0, 0);

	snd(&child, 9);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 1, getpid(), 0, 1);

	kill(child.pid, SIGHUP);

	snd(&child, 10);

	usleep(WAIT_USECS);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);

	if ((id = semget(IPC_PRIVATE, 2, 0600)) == -1) e(0);

	snd(&child, id);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);

	if (semctl(id, 1, SETVAL, seminfo.semvmx) != 0) e(0);

	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, seminfo.semvmx, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);

	if (semctl(id, 0, SETVAL, 1) != 0) e(0);
	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, seminfo.semvmx, 0, 0, 0);

	if (semctl(id, 0, SETVAL, 0) != 0) e(0);

	snd(&child, 11);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, seminfo.semvmx, 0, 0, 1);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);

	if (semctl(id, 1, SETVAL, 0) != 0) e(0);

	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime != 0) e(0);

	time(&now);
	if (semctl(id, 0, SETVAL, 2) != 0) e(0);

	TEST_SEM(id, 0, 1, child.pid, 0, 0);
	TEST_SEM(id, 1, 0, child.pid, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime < now || semds.sem_otime >= now + 10) e(0);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);

	if ((id = semget(IPC_PRIVATE, 2, 0600)) == -1) e(0);

	snd(&child, id);

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

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, 0, child.pid, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
	if (semds.sem_otime < now || semds.sem_otime >= now + 10) e(0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 1;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != 0) e(0);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);

	if (rcv(&child) != 0) e(0);

	snd(&child, 12);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 1, 0);

	terminate(&child);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);

	free(sops);
}

/*
 * Test semctl(2) permission checks, part 1: regular commands.
 */
static void check_perm_result(int r, int required_bit, int tbit)
{
	if (r == -1 && errno != EACCES) e(0);
	if (((required_bit & tbit) == required_bit) != (r != -1)) e(0);
}

static void expect_eacces_noarg(int id, int cmd)
{
	if (semctl(id, 0, cmd) != -1) e(0);
	if (errno != EACCES) e(0);
}

static void expect_eacces_intarg(int id, int cmd, int arg)
{
	if (semctl(id, 0, cmd, arg) != -1) e(0);
	if (errno != EACCES) e(0);
}

static void expect_eacces_ptrarg(int id, int cmd, void *ptr)
{
	if (semctl(id, 0, cmd, ptr) != -1) e(0);
	if (errno != EACCES) e(0);
}

static void do_checks_noarg(int id0, int id1, int id2, int tbit, int cmd, int required_bit)
{
	int r;

	r = semctl(id0, 0, cmd);
	check_perm_result(r, required_bit, tbit);

	r = semctl(id1, 0, cmd);
	check_perm_result(r, required_bit, tbit);

	expect_eacces_noarg(id2, cmd);
}

static void do_checks_intarg(int id0, int id1, int id2, int tbit, int cmd, int arg, int required_bit)
{
	int r;

	r = semctl(id0, 0, cmd, arg);
	check_perm_result(r, required_bit, tbit);

	r = semctl(id1, 0, cmd, arg);
	check_perm_result(r, required_bit, tbit);

	expect_eacces_intarg(id2, cmd, arg);
}

static void do_checks_ptrarg(int id0, int id1, int id2, int tbit, int cmd, void *ptr, int required_bit)
{
	int r;

	r = semctl(id0, 0, cmd, ptr);
	check_perm_result(r, required_bit, tbit);

	r = semctl(id1, 0, cmd, ptr);
	check_perm_result(r, required_bit, tbit);

	expect_eacces_ptrarg(id2, cmd, ptr);
}

static void
test88c_perm1(struct link * parent)
{
	static const int cmds[] = { GETVAL, GETPID, GETNCNT, GETZCNT };
	struct semid_ds semds;
	struct seminfo seminfo;
	unsigned short val[3];
	int i, r, tbit, id[3];

	while ((tbit = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		for (i = 0; i < __arraycount(cmds); i++) {
			do_checks_noarg(id[0], id[1], id[2], tbit, cmds[i], 4);
		}

		do_checks_intarg(id[0], id[1], id[2], tbit, SETVAL, 0, 2);

		memset(val, 0, sizeof(val));

		{
			struct {
				int cmd;
				void *ptr;
				int bit;
			} pcmds[3] = {
				{ GETALL, val, 4 },
				{ SETALL, val, 2 },
				{ IPC_STAT, &semds, 4 }
			};

			for (i = 0; i < 3; i++) {
				do_checks_ptrarg(id[0], id[1], id[2], tbit, pcmds[i].cmd,
				    pcmds[i].ptr, pcmds[i].bit);
			}
		}

#ifndef IPCID_TO_IX
#define IPCID_TO_IX(id)		((id) & 0xffff)
#endif

		do_checks_ptrarg(IPCID_TO_IX(id[0]), IPCID_TO_IX(id[1]),
		    IPCID_TO_IX(id[2]), tbit, SEM_STAT, &semds, 4);

		if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
		if (semctl(0, 0, SEM_INFO, &seminfo) == -1) e(0);

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
	int i;

	for (;;) {
		shift = rcv(parent);
		if (shift == -1)
			break;

		for (i = 0; i < 3; i++)
			id[i] = rcv(parent);

		memset(&semds, 0, sizeof(semds));

		{
			int expect_success = (shift == 6);

			for (i = 0; i < 3; i++) {
				int r = semctl(id[i], 0, IPC_SET, &semds);
				if (r == -1 && errno != EPERM)
					e(0);
				if ((expect_success != 0) != (r != -1))
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
test88c_perm3(struct link *parent)
{
    int shift;
    int id[3];
    const int deny_shift = 6;

    for (;;) {
        shift = rcv(parent);
        if (shift == -1) {
            break;
        }

        id[0] = rcv(parent);
        id[1] = rcv(parent);
        id[2] = rcv(parent);

        for (int i = 0; i < 3; ++i) {
            int r = semctl(id[i], 0, IPC_RMID);
            if (r == -1 && errno != EPERM) {
                e(0);
            }
            if ((shift == deny_shift) != (r != -1)) {
                e(0);
            }
        }

        snd(parent, 0);
    }
}

/*
 * Test the basic semctl(2) functionality.
 */
static inline void wait_past_time(time_t ref, time_t *now_ptr) {
	while (time(now_ptr) == ref) usleep(250000);
}

static inline void ipc_stat_expect_no_update(int id, time_t now, struct semid_ds *semds) {
	if (semctl(id, 0, IPC_STAT, semds) != 0) e(0);
	if (semds->sem_otime != 0) e(0);
	if (semds->sem_ctime >= now) e(0);
}

static inline void ipc_stat_expect_ctime_updated(int id, time_t now, struct semid_ds *semds) {
	if (semctl(id, 0, IPC_STAT, semds) != 0) e(0);
	if (semds->sem_otime != 0) e(0);
	if (semds->sem_ctime < now || semds->sem_ctime >= now + 10) e(0);
}

static inline void expect_buffer_filled(const char *buf, size_t sz, unsigned char v) {
	for (size_t k = 0; k < sz; k++)
		if ((unsigned char)buf[k] != v) e(0);
}

#define EXPECT_OK(call) do { if ((call) != 0) e(0); } while (0)
#define EXPECT_ERR(call, errcode) do { errno = 0; if ((call) != -1) e(0); if (errno != (errcode)) e(0); } while (0)

static void
test88c(void)
{
	static const int cmds[] = { GETVAL, GETPID, GETNCNT, GETZCNT };
	struct seminfo seminfo;
	struct semid_ds semds, osemds;
	unsigned short val[4], seen[2];
	char statbuf[sizeof(struct semid_ds) + 1];
	unsigned int i, j;
	time_t now;
	int r, id, id2, badid1, badid2, cmd;

	subtest = 2;

	if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);

	test_perm(test88c_perm1, 0);
	test_perm(test88c_perm2, 1);
	test_perm(test88c_perm3, 1);

	if ((badid1 = semget(IPC_PRIVATE, 1, 0600)) < 0) e(0);

	EXPECT_OK(semctl(badid1, 0, IPC_RMID));

	memset(&semds, 0, sizeof(semds));
	badid2 = IXSEQ_TO_IPCID(seminfo.semmni, semds.sem_perm);

	if ((id = semget(IPC_PRIVATE, 3, IPC_CREAT | 0600)) < 0) e(0);

	EXPECT_OK(semctl(id, 0, IPC_STAT, &semds));
	if (semds.sem_otime != 0) e(0);
	if (semds.sem_ctime == 0) e(0);

	while (time(&now) == semds.sem_ctime)
		usleep(250000);

	for (i = 0; i < __arraycount(cmds); i++) {
		for (j = 0; j < 3; j++)
			EXPECT_OK(semctl(id, j, cmds[i]));

		EXPECT_ERR(semctl(badid1, 0, cmds[i]), EINVAL);
		EXPECT_ERR(semctl(badid2, 0, cmds[i]), EINVAL);
		EXPECT_ERR(semctl(-1, 0, cmds[i]), EINVAL);
		EXPECT_ERR(semctl(INT_MIN, 0, cmds[i]), EINVAL);
		EXPECT_ERR(semctl(id, -1, cmds[i]), EINVAL);
		EXPECT_ERR(semctl(id, 3, cmds[i]), EINVAL);

		ipc_stat_expect_no_update(id, now, &semds);
	}

	for (j = 0; j < 5; j++) {
		for (i = 0; i < __arraycount(val); i++)
			val[i] = USHRT_MAX;

		EXPECT_OK(semctl(id, (int)j - 1, GETALL, val));
		for (i = 0; i < 3; i++)
			if (val[i] != 0) e(0);
		if (val[i] != USHRT_MAX) e(0);
	}

	for (i = 0; i < __arraycount(val); i++)
		val[i] = USHRT_MAX;

	EXPECT_ERR(semctl(badid1, 0, GETALL, val), EINVAL);
	EXPECT_ERR(semctl(badid2, 0, GETALL, val), EINVAL);
	EXPECT_ERR(semctl(-1, 0, GETALL, val), EINVAL);
	EXPECT_ERR(semctl(INT_MIN, 0, GETALL, val), EINVAL);

	for (i = 0; i < __arraycount(val); i++)
		if (val[i] != USHRT_MAX) e(0);

	EXPECT_ERR(semctl(id, 0, GETALL, NULL), EFAULT);
	EXPECT_ERR(semctl(id, 0, GETALL, bad_ptr), EFAULT);
	EXPECT_ERR(semctl(id, 0, GETALL, ((unsigned short *)bad_ptr) - 2), EFAULT);
	EXPECT_OK(semctl(id, 0, GETALL, ((unsigned short *)bad_ptr) - 3));

	ipc_stat_expect_no_update(id, now, &semds);

	memset(statbuf, 0x5a, sizeof(statbuf));

	EXPECT_ERR(semctl(badid1, 0, IPC_STAT, statbuf), EINVAL);
	EXPECT_ERR(semctl(badid2, 0, IPC_STAT, statbuf), EINVAL);
	EXPECT_ERR(semctl(-1, 0, IPC_STAT, statbuf), EINVAL);
	EXPECT_ERR(semctl(INT_MIN, 0, IPC_STAT, statbuf), EINVAL);

	expect_buffer_filled(statbuf, sizeof(statbuf), 0x5a);

	EXPECT_OK(semctl(id, 0, IPC_STAT, statbuf));

	if (statbuf[sizeof(statbuf) - 1] != 0x5a) e(0);

	EXPECT_ERR(semctl(id, 0, IPC_STAT, NULL), EFAULT);
	EXPECT_ERR(semctl(id, 0, IPC_STAT, bad_ptr), EFAULT);

	if (semctl(id, 0, IPC_STAT, ((struct semid_ds *)bad_ptr) - 1) != 0)
		e(0);

	EXPECT_OK(semctl(id, -1, IPC_STAT, &semds));
	if (semds.sem_otime != 0) e(0);
	if (semds.sem_ctime >= now) e(0);

	if ((id2 = semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0642)) < 0) e(0);

	memset(statbuf, 0x5a, sizeof(statbuf));

	EXPECT_ERR(semctl(-1, 0, SEM_STAT, statbuf), EINVAL);
	EXPECT_ERR(semctl(seminfo.semmni, 0, SEM_STAT, statbuf), EINVAL);

	expect_buffer_filled(statbuf, sizeof(statbuf), 0x5a);

	memset(seen, 0, sizeof(seen));

	for (i = 0; i < seminfo.semmni; i++) {
		errno = 0;
		if ((r = semctl(i, i / 2 - 1, SEM_STAT, statbuf)) == -1) {
			if (errno != EINVAL) e(0);
			continue;
		}
		if (r < 0) e(0);
		memcpy(&semds, statbuf, sizeof(semds));
		if (!(semds.sem_perm.mode & SEM_ALLOC)) e(0);
		if (semds.sem_ctime == 0) e(0);
		if (IXSEQ_TO_IPCID(i, semds.sem_perm) != r) e(0);
		if (r == id) {
			seen[0]++;
			if (semds.sem_perm.mode != (SEM_ALLOC | 0600)) e(0);
			if (semds.sem_perm.uid != geteuid()) e(0);
			if (semds.sem_perm.gid != getegid()) e(0);
			if (semds.sem_perm.cuid != semds.sem_perm.uid) e(0);
			if (semds.sem_perm.cgid != semds.sem_perm.gid) e(0);
			if (semds.sem_perm._key != IPC_PRIVATE) e(0);
			if (semds.sem_nsems != 3) e(0);
			if (semds.sem_otime != 0) e(0);

			EXPECT_ERR(semctl(i, 0, SEM_STAT, NULL), EFAULT);
			EXPECT_ERR(semctl(i, 0, SEM_STAT, bad_ptr), EFAULT);
		} else if (r == id2) {
			seen[1]++;
			if (semds.sem_perm.mode != (SEM_ALLOC | 0642)) e(0);
			if (semds.sem_perm.uid != geteuid()) e(0);
			if (semds.sem_perm.gid != getegid()) e(0);
			if (semds.sem_perm.cuid != semds.sem_perm.uid) e(0);
			if (semds.sem_perm.cgid != semds.sem_perm.gid) e(0);
			if (semds.sem_perm._key != KEY_A) e(0);
			if (semds.sem_nsems != seminfo.semmsl) e(0);
		}
	}

	if (seen[0] != 1) e(0);
	if (seen[1] != 1) e(0);

	if (statbuf[sizeof(statbuf) - 1] != 0x5a) e(0);

	EXPECT_OK(semctl(id, 5, IPC_STAT, &semds));
	if (semds.sem_otime != 0) e(0);
	if (semds.sem_ctime >= now) e(0);

	EXPECT_ERR(semctl(badid1, 0, SETVAL, 1), EINVAL);
	EXPECT_ERR(semctl(badid2, 0, SETVAL, 1), EINVAL);
	EXPECT_ERR(semctl(-1, 0, SETVAL, 1), EINVAL);
	EXPECT_ERR(semctl(INT_MIN, 0, SETVAL, 1), EINVAL);
	EXPECT_ERR(semctl(id, -1, SETVAL, 1), EINVAL);
	EXPECT_ERR(semctl(id, 3, SETVAL, 1), EINVAL);
	EXPECT_ERR(semctl(id, 0, SETVAL, -1), ERANGE);
	EXPECT_ERR(semctl(id, 0, SETVAL, seminfo.semvmx + 1), ERANGE);

	TEST_SEM(id, 0, 0, 0, 0, 0);

	ipc_stat_expect_no_update(id, now, &semds);

	EXPECT_OK(semctl(id, 1, SETVAL, 0));

	ipc_stat_expect_ctime_updated(id, now, &semds);

	TEST_SEM(id, 1, 0, 0, 0, 0);

	EXPECT_OK(semctl(id, 2, SETVAL, seminfo.semvmx));

	TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

	EXPECT_OK(semctl(id, 0, SETVAL, 1));

	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

	EXPECT_OK(semctl(id, 0, GETALL, val));
	if (val[0] != 1) e(0);
	if (val[1] != 0) e(0);
	if (val[2] != seminfo.semvmx) e(0);

	EXPECT_OK(semctl(id, 0, IPC_STAT, &semds));

	wait_past_time(semds.sem_ctime, &now);

	EXPECT_ERR(semctl(badid1, 0, SETALL, 1), EINVAL);
	EXPECT_ERR(semctl(badid2, 0, SETALL, 1), EINVAL);
	EXPECT_ERR(semctl(-1, 0, SETALL, 1), EINVAL);
	EXPECT_ERR(semctl(INT_MIN, 0, SETALL, 1), EINVAL);

	val[0] = seminfo.semvmx + 1;
	val[1] = 0;
	val[2] = 0;
	EXPECT_ERR(semctl(id, 0, SETALL, val), ERANGE);

	val[0] = 0;
	val[1] = 1;
	val[2] = seminfo.semvmx + 1;
	EXPECT_ERR(semctl(id, 0, SETALL, val), ERANGE);

	EXPECT_ERR(semctl(id, 0, SETALL, NULL), EFAULT);
	EXPECT_ERR(semctl(id, 0, SETALL, bad_ptr), EFAULT);
	EXPECT_ERR(semctl(id, 0, SETALL, ((unsigned short *)bad_ptr) - 2), EFAULT);

	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

	ipc_stat_expect_no_update(id, now, &semds);

	val[0] = seminfo.semvmx;
	val[1] = 0;
	val[2] = 0;
	EXPECT_OK(semctl(id, 0, SETALL, val));

	ipc_stat_expect_ctime_updated(id, now, &semds);

	TEST_SEM(id, 0, seminfo.semvmx, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	TEST_SEM(id, 2, 0, 0, 0, 0);

	val[0] = 0;
	val[1] = 1;
	val[2] = seminfo.semvmx;
	EXPECT_OK(semctl(id, INT_MAX, SETALL, val));

	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, 1, 0, 0, 0);
	TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

	memset(page_ptr, 0, page_size);
	EXPECT_OK(semctl(id, 0, SETALL, ((unsigned short *)bad_ptr) - 3));

	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	TEST_SEM(id, 2, 0, 0, 0, 0);

	wait_past_time(semds.sem_ctime, &now);

	EXPECT_ERR(semctl(badid1, 0, IPC_SET, &semds), EINVAL);
	EXPECT_ERR(semctl(badid2, 0, IPC_SET, &semds), EINVAL);
	EXPECT_ERR(semctl(-1, 0, IPC_SET, &semds), EINVAL);
	EXPECT_ERR(semctl(INT_MIN, 0, IPC_SET, &semds), EINVAL);
	EXPECT_ERR(semctl(id, 0, IPC_SET, NULL), EFAULT);
	EXPECT_ERR(semctl(id, 0, IPC_SET, bad_ptr), EFAULT);

	EXPECT_OK(semctl(id, 0, IPC_STAT, &osemds));
	if (osemds.sem_otime != 0) e(0);
	if (osemds.sem_ctime >= now) e(0);

	memset(&semds, 0x5b, sizeof(semds));
	semds.sem_perm.mode = 0712;
	semds.sem_perm.uid = UID_MAX;
	semds.sem_perm.gid = GID_MAX - 1;
	EXPECT_OK(semctl(id, 0, IPC_SET, &semds));

	EXPECT_OK(semctl(id, 0, IPC_STAT, &semds));
	if (semds.sem_perm.mode != (SEM_ALLOC | 0712)) e(0);
	if (semds.sem_perm.uid != UID_MAX) e(0);
	if (semds.sem_perm.gid != GID_MAX - 1) e(0);
	if (semds.sem_perm.cuid != osemds.sem_perm.cuid) e(0);
	if (semds.sem_perm.cgid != osemds.sem_perm.cgid) e(0);
	if (semds.sem_perm._seq != osemds.sem_perm._seq) e(0);
	if (semds.sem_perm._key != osemds.sem_perm._key) e(0);
	if (semds.sem_nsems != osemds.sem_nsems) e(0);
	if (semds.sem_otime != osemds.sem_otime) e(0);
	if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);

	semds.sem_perm.uid = osemds.sem_perm.uid;
	semds.sem_perm.gid = osemds.sem_perm.gid;
	for (i = 0; i < 0777; i++) {
		semds.sem_perm.mode = i;
		EXPECT_OK(semctl(id, i / 2 - 1, IPC_SET, &semds));

		EXPECT_OK(semctl(id, i / 2 - 2, IPC_STAT, &semds));
		if (semds.sem_perm.mode != (SEM_ALLOC | i)) e(0);

		semds.sem_perm.mode = ~0777 | i;
		EXPECT_OK(semctl(id, i / 2 - 3, IPC_SET, &semds));

		EXPECT_OK(semctl(id, i / 2 - 4, IPC_STAT, &semds));
		if (semds.sem_perm.mode != (SEM_ALLOC | i)) e(0);
	}
	if (semds.sem_perm.uid != osemds.sem_perm.uid) e(0);
	if (semds.sem_perm.gid != osemds.sem_perm.gid) e(0);

	if (semctl(id, 0, IPC_SET, ((struct semid_ds *)bad_ptr) - 1) != 0)
		e(0);

	EXPECT_ERR(semctl(badid1, 0, IPC_RMID), EINVAL);
	EXPECT_ERR(semctl(badid2, 0, IPC_RMID), EINVAL);
	EXPECT_ERR(semctl(-1, 0, IPC_RMID), EINVAL);
	EXPECT_ERR(semctl(INT_MIN, 0, IPC_RMID), EINVAL);

	EXPECT_OK(semctl(id, 0, IPC_RMID));

	EXPECT_ERR(semctl(id, 0, IPC_RMID), EINVAL);
	EXPECT_ERR(semctl(id, 0, IPC_STAT, &semds), EINVAL);

	EXPECT_OK(semctl(id2, 1, IPC_RMID));

	EXPECT_ERR(semctl(id2, 1, IPC_RMID), EINVAL);

	if ((id = semget(IPC_PRIVATE, 3, 0600)) == -1) e(0);
	if ((id2 = semget(IPC_PRIVATE, 1, 0600)) == -1) e(0);

	for (i = 0; i <= 1; i++) {
		cmd = (i == 0) ? IPC_INFO : SEM_INFO;

		memset(&seminfo, 0xff, sizeof(seminfo));

		if ((r = semctl(0, 0, cmd, &seminfo)) == -1) e(0);

		if (r < 1 || r >= seminfo.semmni) e(0);

		if (seminfo.semmap < 0) e(0);
		if (seminfo.semmni < 3 || seminfo.semmni > USHRT_MAX) e(0);
		if (seminfo.semmns < 3 || seminfo.semmns > USHRT_MAX) e(0);
		if (seminfo.semmnu < 0) e(0);
		if (seminfo.semmsl < 3 || seminfo.semmsl > USHRT_MAX) e(0);
		if (seminfo.semopm < 3 || seminfo.semopm > USHRT_MAX) e(0);
		if (seminfo.semume < 0) e(0);
		if (cmd == SEM_INFO) {
			if (seminfo.semusz < 2) e(0);
		} else
			if (seminfo.semusz < 0) e(0);
		if (seminfo.semvmx < 3 || seminfo.semvmx > SHRT_MAX) e(0);
		if (cmd == SEM_INFO) {
			if (seminfo.semaem < 4) e(0);
		} else
			if (seminfo.semaem < 0) e(0);

		if (semctl(INT_MAX, -1, cmd, &seminfo) == -1) e(0);
		if (semctl(-1, INT_MAX, cmd, &seminfo) == -1) e(0);

		EXPECT_ERR(semctl(0, 0, cmd, NULL), EFAULT);
		EXPECT_ERR(semctl(0, 0, cmd, bad_ptr), EFAULT);

		if (semctl(0, 0, cmd, ((struct seminfo *)bad_ptr) - 1) == -1)
			e(0);
	}

	EXPECT_OK(semctl(id2, 0, IPC_RMID));

	EXPECT_ERR(semctl(id, 0, INT_MIN), EINVAL);
	EXPECT_ERR(semctl(id, 0, INT_MAX), EINVAL);

	EXPECT_OK(semctl(id, 0, IPC_RMID));
}

/*
 * Test SEM_UNDO support.  Right now this functionality is missing altogether.
 * For now, we test that any attempt to use SEM_UNDO fails.
 */
static void
test88d(void)
{
    struct sembuf sop;
    int semid;

    subtest = 3;

    semid = semget(IPC_PRIVATE, 1, 0600);
    if (semid == -1) {
        e(0);
    }

    if (!(SHRT_MAX & SEM_UNDO)) {
        e(0);
    }

    sop.sem_num = 0;
    sop.sem_op = 1;
    sop.sem_flg = SHRT_MAX;

    if (semop(semid, &sop, 1) != -1) {
        e(0);
    }
    if (errno != EINVAL) {
        e(0);
    }

    if (semctl(semid, 0, IPC_RMID) != 0) {
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
test88e_childaux(struct link *parent)
{
	struct sembuf sops[3];
	struct seminfo seminfo;
	const size_t ops_count = sizeof(sops) / sizeof(sops[0]);
	int child = rcv(parent);
	int id = rcv(parent);
	int num = rcv(parent);

	memset(sops, 0, sizeof(sops));

	switch (child) {
	case 1:
		sops[0].sem_num = (unsigned short)num;
		sops[0].sem_op = 1;
		sops[1].sem_num = (unsigned short)num;
		sops[1].sem_op = 0;
		sops[2].sem_num = 0;
		sops[2].sem_op = 1;
		break;
	case 2: {
		if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
		short op = (short)(-seminfo.semvmx);
		sops[0].sem_num = (unsigned short)num;
		sops[0].sem_op = op;
		sops[1].sem_num = (unsigned short)num;
		sops[1].sem_op = op;
		sops[2].sem_num = 0;
		sops[2].sem_op = 1;
		break;
	}
	default:
		e(0);
	}

	snd(parent, 0);

	if (semop(id, sops, ops_count) != -1) e(0);
	if (errno != EIDRM) e(0);
}

/*
 * First child procedure.
 */
static void
test88e_child1(struct link * parent)
{
	struct sembuf sops[3] = {0};
	size_t nsops = 2;
	int expect = 0;
	const int match = rcv(parent);
	const int semid = rcv(parent);

	sops[0].sem_num = 2;
	sops[0].sem_op = -1;

	switch (match) {
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
		expect = INT_MIN;
		break;
	case MATCH_FIRST:
	case MATCH_BOTH:
	case MATCH_CASCADE:
	case MATCH_ALL:
		sops[1].sem_num = 3;
		sops[1].sem_op = 1;
		break;
	default:
		e(0);
	}

	snd(parent, 0);

	if (semop(semid, sops, nsops) != expect) { e(0); }
	if (expect == -1 && errno != EIDRM) { e(0); }
}

/*
 * Second child procedure.
 */
static void
test88e_child2(struct link *parent)
{
	struct sembuf sops[2];
	size_t nsops = 1;
	int expect = 0;
	int match = rcv(parent);
	int semid = rcv(parent);

	enum { SEM_FIRST = 0, SEM_WAIT = 2, SEM_BOTH = 3 };

	sops[0].sem_num = SEM_WAIT;
	sops[0].sem_op = -1;
	sops[0].sem_flg = 0;
	sops[1].sem_num = 0;
	sops[1].sem_op = 0;
	sops[1].sem_flg = 0;

	switch (match) {
	case MATCH_FIRST:
		sops[1].sem_num = SEM_FIRST;
		sops[1].sem_op = 1;
		nsops = 2;
		expect = -1;
		break;
	case MATCH_SECOND:
	case MATCH_KILL:
		nsops = 1;
		break;
	case MATCH_BOTH:
	case MATCH_ALL:
		sops[1].sem_num = SEM_BOTH;
		sops[1].sem_op = 1;
		nsops = 2;
		break;
	case MATCH_CASCADE:
		sops[0].sem_num = SEM_BOTH;
		nsops = 1;
		break;
	default:
		e(0);
		return;
	}

	snd(parent, 0);

	{
		int ret = semop(semid, sops, nsops);
		if (ret != expect) {
			e(0);
			return;
		}
		if (expect == -1 && errno != EIDRM) e(0);
	}
}

/*
 * Third child procedure.
 */
static void test88e_child3(struct link *parent)
{
	struct sembuf sops[1] = {{0}};
	int match = rcv(parent);
	int id = rcv(parent);

	if (match != MATCH_ALL) {
		e(0);
	}

	sops[0].sem_num = 3;
	sops[0].sem_op = -2;

	snd(parent, 0);

	if (semop(id, sops, 1) == -1) e(0);
}

/*
 * Perform one test for operations affecting multiple processes.
 */
static void ensure_rcv_ok(struct link *l)
{
	if (rcv(l) != 0) e(0);
}

static void spawn_child_std(struct link *child, void (*fn)(void), int drop_flags,
    unsigned int match, int id)
{
	spawn(child, fn, drop_flags);
	snd(child, match);
	snd(child, id);
	ensure_rcv_ok(child);
}

static void spawn_aux_child(struct link *aux, int drop_flags, int order, int id,
    int deadlock_sem)
{
	spawn(aux, test88e_childaux, drop_flags);
	snd(aux, order);
	snd(aux, id);
	snd(aux, deadlock_sem);
	ensure_rcv_ok(aux);
}

static int needs_fairness_wait(unsigned int match)
{
	switch (match) {
	case MATCH_FIRST:
	case MATCH_SECOND:
	case MATCH_KILL:
		return 1;
	default:
		return 0;
	}
}

static void perform_resume(int id, unsigned int resume, int inc, unsigned int sem_main)
{
	struct sembuf sop;
	unsigned short val[4];

	switch (resume) {
	case RESUME_SEMOP:
		memset(&sop, 0, sizeof(sop));
		sop.sem_num = sem_main;
		sop.sem_op = inc;
		if (semop(id, &sop, 1) != 0) e(0);
		break;
	case RESUME_SETVAL:
		if (semctl(id, sem_main, SETVAL, inc) != 0) e(0);
		break;
	case RESUME_SETALL:
		memset(val, 0, sizeof(val));
		val[sem_main] = inc;
		if (semctl(id, 0, SETALL, val) != 0) e(0);
		break;
	default:
		e(0);
	}
}

static void
sub88e(unsigned int match, unsigned int resume, unsigned int aux)
{
	enum { SEM_ERR = 0, SEM_AUX = 1, SEM_MAIN = 2, SEM_EXTRA = 3, SEM_COUNT = 4 };
	struct link aux1, aux2, child1, child2, child3;
	int id, inc, aux_zcnt, aux_ncnt;

	if ((id = semget(IPC_PRIVATE, SEM_COUNT, 0666)) == -1) e(0);

	aux_zcnt = aux_ncnt = 0;

	if (aux & 1) {
		spawn_aux_child(&aux1, DROP_ALL, 1, id, (aux & 4) ? SEM_MAIN : SEM_AUX);
		if (aux & 4) aux_zcnt++;
	}

	spawn_child_std(&child1, test88e_child1, DROP_ALL, match, id);

	if (needs_fairness_wait(match)) usleep(WAIT_USECS);

	spawn_child_std(&child2, test88e_child2, DROP_NONE, match, id);

	if (match == MATCH_ALL) {
		spawn_child_std(&child3, test88e_child3, DROP_USER, match, id);
	}

	if (aux & 2) {
		spawn_aux_child(&aux2, DROP_NONE, 2, id, (aux & 4) ? SEM_MAIN : SEM_AUX);
		if (aux & 4) aux_ncnt++;
	}

	usleep(WAIT_USECS);

	inc = 1;
	switch (match) {
	case MATCH_FIRST:
	case MATCH_SECOND:
		TEST_SEM(id, SEM_MAIN, 0, 0, 2 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, SEM_EXTRA, 0, 0, 0, 0);
		break;
	case MATCH_KILL:
		TEST_SEM(id, SEM_MAIN, 0, 0, 2 + aux_ncnt, aux_zcnt);
		terminate(&child1);
		usleep(WAIT_USECS);
		TEST_SEM(id, SEM_MAIN, 0, 0, 1 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, SEM_EXTRA, 0, 0, 0, 0);
		break;
	case MATCH_BOTH:
		TEST_SEM(id, SEM_MAIN, 0, 0, 2 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, SEM_EXTRA, 0, 0, 0, 0);
		inc = 2;
		break;
	case MATCH_CASCADE:
		TEST_SEM(id, SEM_MAIN, 0, 0, 1 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, SEM_EXTRA, 0, 0, 1, 0);
		break;
	case MATCH_ALL:
		TEST_SEM(id, SEM_MAIN, 0, 0, 2 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, SEM_EXTRA, 0, 0, 1, 0);
		inc = 2;
		break;
	default:
		e(0);
	}

	TEST_SEM(id, SEM_ERR, 0, 0, 0, 0);
	TEST_SEM(id, SEM_AUX, 0, 0, -1, -1);

	perform_resume(id, resume, inc, SEM_MAIN);

	switch (match) {
	case MATCH_FIRST:
		TEST_SEM(id, SEM_MAIN, 0, child1.pid, 1 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, SEM_EXTRA, 1, child1.pid, 0, 0);
		collect(&child1);
		break;
	case MATCH_SECOND:
		TEST_SEM(id, SEM_MAIN, 0, child2.pid, 1 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, SEM_EXTRA, 0, 0, 0, 0);
		collect(&child2);
		break;
	case MATCH_KILL:
		TEST_SEM(id, SEM_MAIN, 0, child2.pid, aux_ncnt, aux_zcnt);
		TEST_SEM(id, SEM_EXTRA, 0, 0, 0, 0);
		collect(&child2);
		break;
	case MATCH_BOTH:
		TEST_SEM(id, SEM_MAIN, 0, -1, aux_ncnt, aux_zcnt);
		TEST_SEM(id, SEM_EXTRA, 2, -1, 0, 0);
		collect(&child1);
		collect(&child2);
		break;
	case MATCH_CASCADE:
		TEST_SEM(id, SEM_MAIN, 0, child1.pid, aux_ncnt, aux_zcnt);
		TEST_SEM(id, SEM_EXTRA, 0, child2.pid, 0, 0);
		collect(&child1);
		collect(&child2);
		break;
	case MATCH_ALL:
		TEST_SEM(id, SEM_MAIN, 0, -1, aux_ncnt, aux_zcnt);
		TEST_SEM(id, SEM_EXTRA, 0, child3.pid, 0, 0);
		collect(&child1);
		collect(&child2);
		collect(&child3);
		break;
	default:
		e(0);
	}

	TEST_SEM(id, SEM_ERR, 0, 0, 0, 0);
	TEST_SEM(id, SEM_AUX, 0, 0, -1, -1);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);

	switch (match) {
	case MATCH_FIRST:
		collect(&child2);
		break;
	case MATCH_SECOND:
		collect(&child1);
		break;
	case MATCH_KILL:
	case MATCH_BOTH:
	case MATCH_CASCADE:
	case MATCH_ALL:
		break;
	default:
		e(0);
	}

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
static void test88e(void)
{
    unsigned int resume;
    unsigned int match;
    unsigned int aux;
    const unsigned int aux_start = 1U;
    const unsigned int aux_end = 8U;

    subtest = 4U;

    if (aux_start > aux_end) {
        return;
    }

    for (match = 0U; match < NR_MATCHES; ++match) {
        for (resume = 0U; resume < NR_RESUMES; ++resume) {
            for (aux = aux_start; aux <= aux_end; ++aux) {
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
test88f_child(struct link *parent)
{
	static const int mib[] = { CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_INFO,
	    KERN_SYSVIPC_SEM_INFO };
	struct sem_sysctl_info *semsi = NULL;
	size_t len = 0;
	int id[2];
	int seen[2] = { 0, 0 };

	id[0] = rcv(parent);
	id[1] = rcv(parent);

	if (sysctl(mib, __arraycount(mib), NULL, &len, NULL, 0) != 0 || len == 0) e(0);

	semsi = malloc(len);
	if (semsi == NULL) e(0);

	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0) {
		free(semsi);
		e(0);
	}

	{
		long semni = semsi->seminfo.semmni;
		if (semni < 0) {
			free(semsi);
			e(0);
		}

		for (size_t i = 0; i < (size_t)semni; i++) {
			int id2;

			if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
				continue;

			id2 = IXSEQ_TO_IPCID((int)i, semsi->semids[i].sem_perm);
			if (id2 == id[0])
				seen[0]++;
			else if (id2 == id[1])
				seen[1]++;
		}
	}

	free(semsi);

	if (seen[0] != 1 || seen[1] != 1) e(0);
}

/*
 * Test sysctl(2) based information retrieval.  This test aims to ensure that
 * in particular ipcs(1) and ipcrm(1) will be able to do their jobs.
 */
static int
find_unique_sem_slot(const struct sem_sysctl_info *semsi, int semmni, int target_id)
{
	int32_t i;
	int found = -1;

	for (i = 0; i < semmni; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
			continue;

		if (IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm) == target_id) {
			if (found != -1)
				return -2;
			found = (int)i;
		}
	}

	return found;
}

static int
validate_semds(const struct semid_ds_sysctl *semds, uid_t uid, gid_t gid,
    mode_t mode, key_t key, u_short nsems)
{
	if (semds->sem_perm.uid != uid) return -1;
	if (semds->sem_perm.gid != gid) return -1;
	if (semds->sem_perm.cuid != uid) return -1;
	if (semds->sem_perm.cgid != gid) return -1;
	if (semds->sem_perm.mode != (SEM_ALLOC | mode)) return -1;
	if (semds->sem_perm._key != key) return -1;
	if (semds->sem_nsems != nsems) return -1;
	if (semds->sem_otime != 0) return -1;
	if (semds->sem_ctime == 0) return -1;

	return 0;
}

static void
test88f(void)
{
	static const int mib[] = { CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_INFO,
	    KERN_SYSVIPC_SEM_INFO };
	struct seminfo seminfo, seminfo2;
	struct sem_sysctl_info *semsi;
	struct semid_ds_sysctl *semds;
	struct link child;
	size_t len, size;
	int id[2], id2;
	int32_t i;
	int slot0, slot1;
	uid_t uid = geteuid();
	gid_t gid = getegid();

	len = sizeof(seminfo);
	if (sysctl(mib, __arraycount(mib), &seminfo, &len, NULL, 0) != 0) e(0);
	if (len != sizeof(seminfo)) e(0);

	if (semctl(0, 0, IPC_INFO, &seminfo2) == -1) e(0);

	if (memcmp(&seminfo, &seminfo2, sizeof(seminfo)) != 0) e(0);

	if (seminfo.semmni <= 0) e(0);
	if (seminfo.semmni > SHRT_MAX) e(0);

	size = sizeof(*semsi) +
	    sizeof(semsi->semids[0]) * (seminfo.semmni - 1);

	len = 0;
	if (sysctl(mib, __arraycount(mib), NULL, &len, NULL, 0) != 0) e(0);
	if (len != size) e(0);

	if ((id[0] = semget(KEY_A, 5, IPC_CREAT | 0612)) < 0) e(0);
	if ((id[1] = semget(IPC_PRIVATE, 3, 0650)) < 0) e(0);

	if ((semsi = malloc(size)) == NULL) e(0);

	len = size;
	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0) e(0);
	if (len != size) e(0);

	if (sizeof(semsi->seminfo) != sizeof(seminfo)) e(0);
	if (memcmp(&semsi->seminfo, &seminfo, sizeof(semsi->seminfo)) != 0) e(0);

	slot0 = find_unique_sem_slot(semsi, seminfo.semmni, id[0]);
	slot1 = find_unique_sem_slot(semsi, seminfo.semmni, id[1]);
	if (slot0 < 0) e(0);
	if (slot1 < 0) e(0);

	semds = &semsi->semids[slot0];
	if (validate_semds(semds, uid, gid, 0612, KEY_A, 5) != 0) e(0);

	semds = &semsi->semids[slot1];
	if (validate_semds(semds, uid, gid, 0650, IPC_PRIVATE, 3) != 0) e(0);

	spawn(&child, test88f_child, DROP_ALL);

	snd(&child, id[0]);
	snd(&child, id[1]);

	collect(&child);

	if (semctl(id[0], 0, IPC_RMID) != 0) e(0);
	if (semctl(id[1], 0, IPC_RMID) != 0) e(0);

	len = size;
	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0) e(0);
	if (len != size) e(0);

	for (i = 0; i < seminfo.semmni; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
			continue;

		id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
		if (id2 == id[0]) e(0);
		if (id2 == id[1]) e(0);
	}

	free(semsi);
}

/*
 * Initialize the test.
 */
static void
test88_init(void)
{
	static const int mib[] = { CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_SEM };
	struct group *gr;
	size_t len;
	int i;

	if (setuid(geteuid()) != 0) {
		e(0);
	}

	gr = getgrnam(ROOT_GROUP);
	if (gr == NULL) {
		e(0);
	}

	if (setgid(gr->gr_gid) != 0) {
		e(0);
	}
	if (setegid(gr->gr_gid) != 0) {
		e(0);
	}

	len = sizeof(i);
	if (sysctl(mib, __arraycount(mib), &i, &len, NULL, 0) != 0) {
		e(0);
	}
	if (len != sizeof(i)) {
		e(0);
	}

	if (i == 0) {
		printf("skipped\n");
		cleanup();
		exit(0);
	}

	page_size = getpagesize();
	page_ptr = mmap(NULL, page_size * 2, PROT_READ | PROT_WRITE,
	    MAP_ANON | MAP_PRIVATE, -1, 0);
	if (page_ptr == MAP_FAILED) {
		e(0);
	}
	bad_ptr = page_ptr + page_size;
	if (munmap(bad_ptr, page_size) != 0) {
		e(0);
	}
}

/*
 * Test program for SysV IPC semaphores.
 */
#include <limits.h>
#include <stdlib.h>

typedef void (*test_fn)(void);

int main(int argc, char **argv)
{
    int mask = 0xFF;
    long value;
    char *endptr;
    const test_fn tests[] = { test88a, test88b, test88c, test88d, test88e, test88f };
    const int bits[] = { 0x01, 0x02, 0x04, 0x08, 0x10, 0x20 };
    const size_t count = sizeof(tests) / sizeof(tests[0]);
    int i;
    size_t j;

    if (argc == 2) {
        endptr = NULL;
        value = strtol(argv[1], &endptr, 10);
        if (value > INT_MAX) {
            mask = INT_MAX;
        } else if (value < INT_MIN) {
            mask = INT_MIN;
        } else {
            mask = (int)value;
        }
    }

    start(88);
    test88_init();

    for (i = 0; i < ITERATIONS; i++) {
        for (j = 0; j < count; j++) {
            if ((mask & bits[j]) != 0) {
                tests[j]();
            }
        }
    }

    quit();
    return 0;
}
