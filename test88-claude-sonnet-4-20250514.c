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
spawn(struct link * link, void (* proc)(struct link *), int drop)
{
	struct passwd *pw;
	struct group *gr;
	int up[2], dn[2];

	fflush(stdout);
	fflush(stderr);

	if (pipe(up) != 0) e(0);
	if (pipe(dn) != 0) e(0);

	link->pid = fork();

	if (link->pid == 0) {
		close(up[1]);
		close(dn[0]);

		link->pid = getppid();
		link->rcvfd = up[0];
		link->sndfd = dn[1];

		errct = 0;

		if (drop == DROP_ALL) {
			if (setgroups(0, NULL) != 0) e(0);

			if ((gr = getgrnam(NONROOT_GROUP)) == NULL) e(0);

			if (setgid(gr->gr_gid) != 0) e(0);
			if (setegid(gr->gr_gid) != 0) e(0);

			drop = DROP_USER;
		}

		if (drop == DROP_USER) {
			if ((pw = getpwnam(NONROOT_USER)) == NULL) e(0);

			if (setuid(pw->pw_uid) != 0) e(0);
		}

		proc(link);

		exit(errct);
	}

	if (link->pid == -1) {
		e(0);
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
collect(struct link * link)
{
	int status;
	pid_t result;

	if (link == NULL) return;

	if (link->sndfd >= 0) {
		close(link->sndfd);
		link->sndfd = -1;
	}
	if (link->rcvfd >= 0) {
		close(link->rcvfd);
		link->rcvfd = -1;
	}

	if (link->pid <= 0) return;

	result = waitpid(link->pid, &status, 0);
	if (result != link->pid) {
		e(0);
		return;
	}

	if (!WIFEXITED(status)) {
		e(0);
	} else {
		errct += WEXITSTATUS(status);
	}
}

/*
 * Forcibly terminate a child process, and clean up.
 */
static void
terminate(struct link * link)
{
	int status;
	int kill_result;
	pid_t wait_result;

	kill_result = kill(link->pid, SIGKILL);
	if (kill_result != 0) {
		e(0);
	}

	close(link->sndfd);
	close(link->rcvfd);

	wait_result = waitpid(link->pid, &status, 0);
	if (wait_result <= 0) {
		e(0);
	}

	if (WIFSIGNALED(status)) {
		if (WTERMSIG(status) != SIGKILL) {
			e(0);
		}
	} else if (WIFEXITED(status)) {
		errct += WEXITSTATUS(status);
	} else {
		e(0);
	}
}

/*
 * Send an integer value to the child or parent.
 */
static void
snd(struct link * link, int val)
{
    ssize_t bytes_written;
    
    if (link == NULL || link->sndfd < 0) {
        e(0);
        return;
    }
    
    bytes_written = write(link->sndfd, &val, sizeof(val));
    if (bytes_written != sizeof(val)) {
        e(0);
    }
}

/*
 * Receive an integer value from the child or parent, or -1 on EOF.
 */
static int
rcv(struct link * link)
{
	int r, val;

	if (link == NULL || link->rcvfd < 0)
		return -1;

	r = read(link->rcvfd, (void *)&val, sizeof(val));
	
	if (r == 0)
		return -1;

	if (r < 0)
		return -1;

	if (r != sizeof(val))
		return -1;

	return val;
}

/*
 * Child procedure that creates semaphore sets.
 */
static void
test_perm_child(struct link * parent)
{
	struct passwd *pw;
	struct group *gr;
	struct semid_ds semds;
	uid_t uid;
	gid_t gid;
	int mask, rmask, sugid, id[3];

	while ((mask = rcv(parent)) != -1) {
		rmask = rcv(parent);
		sugid = rcv(parent);

		int creation_mask = (sugid == SUGID_NONE) ? mask : 0;
		if ((id[0] = semget(KEY_A, 3, IPC_CREAT | IPC_EXCL | creation_mask)) == -1) {
			e(0);
		}
		if ((id[1] = semget(KEY_B, 3, IPC_CREAT | IPC_EXCL | mask | rmask)) == -1) {
			e(0);
		}
		if ((id[2] = semget(KEY_C, 3, IPC_CREAT | IPC_EXCL | rmask)) == -1) {
			e(0);
		}

		uid = geteuid();
		gid = getegid();
		
		if (sugid != SUGID_NONE) {
			if (sugid == SUGID_ROOT_USER) {
				pw = getpwnam(ROOT_USER);
				if (pw == NULL) {
					e(0);
				}
				uid = pw->pw_uid;
			} else if (sugid == SUGID_NONROOT_USER) {
				pw = getpwnam(NONROOT_USER);
				if (pw == NULL) {
					e(0);
				}
				uid = pw->pw_uid;
			} else if (sugid == SUGID_ROOT_GROUP) {
				gr = getgrnam(ROOT_GROUP);
				if (gr == NULL) {
					e(0);
				}
				gid = gr->gr_gid;
			} else if (sugid == SUGID_NONROOT_GROUP) {
				gr = getgrnam(NONROOT_GROUP);
				if (gr == NULL) {
					e(0);
				}
				gid = gr->gr_gid;
			}

			semds.sem_perm.uid = uid;
			semds.sem_perm.gid = gid;
			semds.sem_perm.mode = mask;
			if (semctl(id[0], 0, IPC_SET, &semds) != 0) {
				e(0);
			}
			semds.sem_perm.mode = mask | rmask;
			if (semctl(id[1], 0, IPC_SET, &semds) != 0) {
				e(0);
			}
			semds.sem_perm.mode = rmask;
			if (semctl(id[2], 0, IPC_SET, &semds) != 0) {
				e(0);
			}
		}

		if (mask & IPC_R) {
			if (semctl(id[0], 0, IPC_STAT, &semds) != 0) {
				e(0);
			}
			if (semds.sem_perm.mode != (SEM_ALLOC | mask)) {
				e(0);
			}
			if (semds.sem_perm.uid != uid) {
				e(0);
			}
			if (semds.sem_perm.gid != gid) {
				e(0);
			}
			if (semds.sem_perm.cuid != geteuid()) {
				e(0);
			}
			if (semds.sem_perm.cgid != getegid()) {
				e(0);
			}
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
static void
test_perm(void (* proc)(struct link *), int owner_test)
{
	struct link child1, child2;
	int n, shift, bit, mask, rmask, drop1, drop2, sugid, id[3];

	for (n = 0; n < 7; n++) {
		get_test_parameters(n, &shift, &drop1, &drop2, &sugid);

		spawn(&child1, test_perm_child, drop1);
		spawn(&child2, proc, drop2);

		run_permission_tests(&child1, &child2, shift, sugid, owner_test);

		terminate_children(&child1, &child2);
		collect(&child1);
		collect(&child2);
	}
}

static void
get_test_parameters(int n, int *shift, int *drop1, int *drop2, int *sugid)
{
	switch (n) {
	case 0:
		*shift = 6;
		*drop1 = DROP_ALL;
		*drop2 = DROP_ALL;
		*sugid = SUGID_NONE;
		break;
	case 1:
		*shift = 6;
		*drop1 = DROP_NONE;
		*drop2 = DROP_ALL;
		*sugid = SUGID_NONROOT_USER;
		break;
	case 2:
		*shift = 6;
		*drop1 = DROP_USER;
		*drop2 = DROP_ALL;
		*sugid = SUGID_ROOT_USER;
		break;
	case 3:
		*shift = 3;
		*drop1 = DROP_NONE;
		*drop2 = DROP_USER;
		*sugid = SUGID_NONE;
		break;
	case 4:
		*shift = 3;
		*drop1 = DROP_NONE;
		*drop2 = DROP_ALL;
		*sugid = SUGID_NONROOT_GROUP;
		break;
	case 5:
		*shift = 3;
		*drop1 = DROP_NONE;
		*drop2 = DROP_USER;
		*sugid = SUGID_NONROOT_GROUP;
		break;
	case 6:
		*shift = 0;
		*drop1 = DROP_NONE;
		*drop2 = DROP_ALL;
		*sugid = SUGID_NONE;
		break;
	}
}

static void
run_permission_tests(struct link *child1, struct link *child2, int shift, int sugid, int owner_test)
{
	int bit, mask, rmask, id[3];

	for (bit = 0; bit <= 7; bit++) {
		mask = bit << shift;
		rmask = 0777 & ~(7 << shift);

		send_test_params_to_child1(child1, mask, rmask, sugid);
		receive_ids_from_child1(child1, id);
		
		send_test_params_to_child2(child2, owner_test, shift, bit, id);
		
		if (rcv(child2) != 0) e(0);
		snd(child1, 0);
	}
}

static void
send_test_params_to_child1(struct link *child1, int mask, int rmask, int sugid)
{
	snd(child1, mask);
	snd(child1, rmask);
	snd(child1, sugid);
}

static void
receive_ids_from_child1(struct link *child1, int *id)
{
	id[0] = rcv(child1);
	id[1] = rcv(child1);
	id[2] = rcv(child1);
}

static void
send_test_params_to_child2(struct link *child2, int owner_test, int shift, int bit, int *id)
{
	snd(child2, (owner_test) ? shift : bit);
	snd(child2, id[0]);
	snd(child2, id[1]);
	snd(child2, id[2]);
}

static void
terminate_children(struct link *child1, struct link *child2)
{
	snd(child1, -1);
	snd(child2, -1);
}

/*
 * Test semget(2) permission checks.  Please note that the checks are advisory:
 * nothing keeps a process from opening a semaphore set with fewer privileges
 * than required by the operations the process subsequently issues on the set.
 */
static void
test88a_perm(struct link * parent)
{
	int r, tbit, bit, mask, id[3];
	const int ID_A = 0;
	const int ID_B = 1;
	const int ID_C = 2;

	if (!parent) {
		return;
	}

	while ((tbit = rcv(parent)) != -1) {
		for (int i = 0; i < 3; i++) {
			id[i] = rcv(parent);
		}

		for (bit = 0; bit <= 7; bit++) {
			mask = bit << 6;
			int expected_result = (bit != 0 && (bit & tbit) == bit);

			r = semget(KEY_A, 0, mask);
			if (r < 0 && (r != -1 || errno != EACCES)) {
				e(0);
			}
			if (expected_result != (r != -1)) {
				e(0);
			}
			if (r != -1 && r != id[ID_A]) {
				e(0);
			}

			r = semget(KEY_B, 0, mask);
			if (r < 0 && (r != -1 || errno != EACCES)) {
				e(0);
			}
			if (expected_result != (r != -1)) {
				e(0);
			}
			if (r != -1 && r != id[ID_B]) {
				e(0);
			}

			if (semget(KEY_C, 0, mask) != -1) {
				e(0);
			}
			if (errno != EACCES) {
				e(0);
			}
		}

		snd(parent, 0);
	}
}

/*
 * Test the basic semget(2) functionality.
 */
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

	if ((id[1] = semget(IPC_PRIVATE, 1, IPC_CREAT | IPC_EXCL | 0600)) < 0)
		e(0);

	if ((id[2] = semget(IPC_PRIVATE, 1, 0600)) < 0) e(0);

	if (id[0] == id[1]) e(0);
	if (id[1] == id[2]) e(0);
	if (id[0] == id[2]) e(0);

	if (semctl(id[0], 0, IPC_RMID) != 0) e(0);
	if (semctl(id[1], 0, IPC_RMID) != 0) e(0);
	if (semctl(id[2], 0, IPC_RMID) != 0) e(0);

	if ((id[0] = semget(KEY_A, 0, 0600)) >= 0 &&
	    semctl(id[0], 0, IPC_RMID) == -1) e(0);
	if ((id[0] = semget(KEY_B, 0, 0600)) >= 0 &&
	    semctl(id[0], 0, IPC_RMID) == -1) e(0);

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

	if (semctl(id[0], 0, IPC_RMID) != 0) e(0);
	if (semctl(id[1], 0, IPC_RMID) != 0) e(0);

	if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
	if (seminfo.semmni < 3 || seminfo.semmni > USHRT_MAX) e(0);

	idp = malloc(sizeof(int) * (seminfo.semmni + 1));
	if (idp == NULL) e(0);

	for (i = 0; i < seminfo.semmni + 1; i++) {
		idp[i] = semget(KEY_A + i, 1, IPC_CREAT | 0600);
		if (idp[i] < 0)
			break;

		for (j = 0; j < i; j++)
			if (idp[i] == idp[j]) e(0);
	}

	if (errno != ENOSPC) e(0);
	if (i < 3) e(0);
	if (i == seminfo.semmni + 1) e(0);

	while (i-- > 0)
		if (semctl(idp[i], 0, IPC_RMID) != 0) e(0);

	free(idp);

	if (semget(KEY_A, -1, IPC_CREAT | 0600) != -1) e(0);
	if (errno != EINVAL) e(0);

	if (semget(KEY_A, 0, IPC_CREAT | 0600) != -1) e(0);
	if (errno != EINVAL) e(0);

	if (seminfo.semmsl < 3 || seminfo.semmsl > USHRT_MAX) e(0);
	if (semget(KEY_A, seminfo.semmsl + 1, IPC_CREAT | 0600) != -1) e(0);
	if (errno != EINVAL) e(0);

	if ((id[0] = semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0600)) < 0)
		e(0);
	if (semctl(id[0], 0, IPC_RMID) != 0) e(0);

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

	if (semctl(id[0], 0, IPC_RMID) != 0) e(0);

	time(&now);
	if (seminfo.semmns < 3 + seminfo.semmsl) e(0);
	if ((id[0] = semget(IPC_PRIVATE, 3, IPC_CREAT | IPC_EXCL | 0642)) < 0)
		e(0);
	if ((id[1] = semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0613)) < 0)
		e(0);

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

	for (i = 0; i < semds.sem_nsems; i++)
		TEST_SEM(id[0], i, 0, 0, 0, 0);

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

	for (i = 0; i < semds.sem_nsems; i++)
		TEST_SEM(id[1], i, 0, 0, 0, 0);

	if (semctl(id[1], 0, IPC_RMID) != 0) e(0);
	if (semctl(id[0], 0, IPC_RMID) != 0) e(0);

	if ((id[0] = semget(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0000)) < 0) e(0);

	if ((id[1] = semget(KEY_A, 0, 0600)) < 0) e(0);
	if (id[0] != id[1]) e(0);

	if ((id[1] = semget(KEY_A, 0, 0000)) < 0) e(0);
	if (id[0] != id[1]) e(0);

	if (semctl(id[0], 0, IPC_RMID) != 0) e(0);

	test_perm(test88a_perm, 0);
}

/*
 * Test semop(2) permission checks.
 */
static void
test88b_perm(struct link * parent)
{
    struct sembuf sops[2];
    size_t nsops;
    int i, r, tbit, bit, id[3];
    
    static const struct {
        int nsops;
        int bit;
        struct sembuf ops[2];
    } test_cases[] = {
        { 1, 4, { {0, 0, 0}, {0, 0, 0} } },
        { 1, 2, { {0, 1, 0}, {0, 0, 0} } },
        { 1, 2, { {0, -1, 0}, {0, 0, 0} } },
        { 2, 6, { {0, 0, 0}, {0, 1, 0} } },
        { 2, 6, { {1, 0, 0}, {0, -1, 0} } },
        { 2, 4, { {0, 0, 0}, {1, 0, 0} } },
        { 2, 2, { {0, 1, 0}, {0, -1, 0} } },
        { 2, 4, { {USHRT_MAX, 0, 0}, {0, 0, 0} } }
    };

    while ((tbit = rcv(parent)) != -1) {
        if (tbit < 0) break;
        
        id[0] = rcv(parent);
        id[1] = rcv(parent);  
        id[2] = rcv(parent);

        for (i = 0; i < 8; i++) {
            memcpy(sops, test_cases[i].ops, sizeof(sops));
            nsops = test_cases[i].nsops;
            bit = test_cases[i].bit;

            r = semop(id[0], sops, nsops);
            if (i == 7 && r == -1 && errno == EFBIG) {
                r = 0;
            }
            if (r < 0 && (r != -1 || errno != EACCES)) {
                e(0);
            }
            if (((bit & tbit) == bit) != (r != -1)) {
                e(0);
            }

            r = semop(id[1], sops, nsops);
            if (i == 7 && r == -1 && errno == EFBIG) {
                r = 0;
            }
            if (r < 0 && (r != -1 || errno != EACCES)) {
                e(0);
            }
            if (((bit & tbit) == bit) != (r != -1)) {
                e(0);
            }

            if (semop(id[2], sops, nsops) != -1) {
                e(0);
            }
            if (errno != EACCES) {
                e(0);
            }
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
		return;
	}
	if (nr_signals != 0) {
		e(0);
		return;
	}
	nr_signals++;
}

/*
 * Child process for semop(2) tests, mainly testing blocking operations.
 */
static void
test88b_child(struct link * parent)
{
	struct sembuf sops[5];
	struct sigaction act;
	int id;
	int recv_value;

	id = rcv(parent);
	if (id < 0) {
		e(0);
		return;
	}

	memset(sops, 0, sizeof(sops));
	if (semop(id, sops, 1) != 0) {
		e(0);
		return;
	}

	recv_value = rcv(parent);
	if (recv_value != 1) {
		e(0);
		return;
	}

	sops[0].sem_op = -3;
	if (semop(id, sops, 1) != 0) {
		e(0);
		return;
	}

	recv_value = rcv(parent);
	if (recv_value != 2) {
		e(0);
		return;
	}

	sops[0].sem_num = 2;
	sops[0].sem_op = 2;
	sops[1].sem_num = 1;
	sops[1].sem_op = -1;
	sops[2].sem_num = 0;
	sops[2].sem_op = 1;
	if (semop(id, sops, 3) != 0) {
		e(0);
		return;
	}

	recv_value = rcv(parent);
	if (recv_value != 3) {
		e(0);
		return;
	}

	sops[0].sem_num = 1;
	sops[0].sem_op = 0;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	sops[2].sem_num = 0;
	sops[2].sem_op = 0;
	sops[3].sem_num = 2;
	sops[3].sem_op = 0;
	sops[4].sem_num = 2;
	sops[4].sem_op = 1;
	if (semop(id, sops, 5) != 0) {
		e(0);
		return;
	}

	recv_value = rcv(parent);
	if (recv_value != 4) {
		e(0);
		return;
	}

	sops[0].sem_num = 1;
	sops[0].sem_op = -2;
	sops[1].sem_num = 2;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != 0) {
		e(0);
		return;
	}

	recv_value = rcv(parent);
	if (recv_value != 5) {
		e(0);
		return;
	}

	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = -1;
	sops[1].sem_flg = IPC_NOWAIT;
	if (semop(id, sops, 2) != 0) {
		e(0);
		return;
	}

	recv_value = rcv(parent);
	if (recv_value != 6) {
		e(0);
		return;
	}

	sops[0].sem_num = 1;
	sops[0].sem_op = 0;
	sops[1].sem_num = 0;
	sops[1].sem_op = 0;
	sops[1].sem_flg = IPC_NOWAIT;
	if (semop(id, sops, 2) != -1) {
		e(0);
		return;
	}
	if (errno != EAGAIN) {
		e(0);
		return;
	}

	recv_value = rcv(parent);
	if (recv_value != 7) {
		e(0);
		return;
	}

	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	sops[1].sem_flg = 0;
	if (semop(id, sops, 2) != 0) {
		e(0);
		return;
	}

	recv_value = rcv(parent);
	if (recv_value != 8) {
		e(0);
		return;
	}

	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 2;
	if (semop(id, sops, 2) != -1) {
		e(0);
		return;
	}
	if (errno != ERANGE) {
		e(0);
		return;
	}

	memset(&act, 0, sizeof(act));
	act.sa_handler = got_signal;
	if (sigfillset(&act.sa_mask) != 0) {
		e(0);
		return;
	}
	if (sigaction(SIGHUP, &act, NULL) != 0) {
		e(0);
		return;
	}

	recv_value = rcv(parent);
	if (recv_value != 9) {
		e(0);
		return;
	}

	memset(sops, 0, sizeof(sops));
	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 0;
	sops[1].sem_op = 1;
	sops[2].sem_num = 1;
	sops[2].sem_op = 0;
	if (semop(id, sops, 3) != -1) {
		if (errno != EINTR) {
			e(0);
			return;
		}
	}
	if (nr_signals != 1) {
		e(0);
		return;
	}

	TEST_SEM(id, 0, 0, parent->pid, 0, 0);
	TEST_SEM(id, 1, 1, parent->pid, 0, 0);

	recv_value = rcv(parent);
	if (recv_value != 10) {
		e(0);
		return;
	}

	memset(sops, 0, sizeof(sops));
	sops[0].sem_op = -3;
	if (semop(id, sops, 1) != -1) {
		e(0);
		return;
	}
	if (errno != EIDRM) {
		e(0);
		return;
	}

	id = rcv(parent);
	if (id < 0) {
		e(0);
		return;
	}

	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != -1) {
		e(0);
		return;
	}
	if (errno != ERANGE) {
		e(0);
		return;
	}

	recv_value = rcv(parent);
	if (recv_value != 11) {
		e(0);
		return;
	}

	sops[0].sem_num = 1;
	sops[0].sem_op = 0;
	sops[1].sem_num = 0;
	sops[1].sem_op = -1;
	if (semop(id, sops, 2) != 0) {
		e(0);
		return;
	}

	id = rcv(parent);
	if (id < 0) {
		e(0);
		return;
	}

	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != 0) {
		e(0);
		return;
	}

	snd(parent, errct);
	recv_value = rcv(parent);
	if (recv_value != 12) {
		e(0);
		return;
	}

	sops[0].sem_num = 1;
	sops[0].sem_op = -1;
	sops[1].sem_num = 0;
	sops[1].sem_op = 3;
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
	struct sembuf *sops, *sops2;
	size_t size;
	struct link child;
	time_t now;
	unsigned short val[2];
	int id;

	subtest = 1;

	if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);

	if (seminfo.semopm < 3 || seminfo.semopm > USHRT_MAX) e(0);

	size = sizeof(sops[0]) * (seminfo.semopm + 1);
	sops = malloc(size);
	if (sops == NULL) e(0);
	memset(sops, 0, size);

	id = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600);
	if (id == -1) e(0);

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

	id = semget(IPC_PRIVATE, 3, 0600);
	if (id == -1) e(0);

	memset(sops, 0, sizeof(sops[0]));
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

	memset(sops, 0, sizeof(sops[0]) * 2);
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

	id = semget(IPC_PRIVATE, 2, 0600);
	if (id == -1) e(0);

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

	id = semget(IPC_PRIVATE, 2, 0600);
	if (id == -1) e(0);

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
static void
test88c_perm1(struct link * parent)
{
    static const int cmds[] = { GETVAL, GETPID, GETNCNT, GETZCNT };
    struct semid_ds semds;
    struct seminfo seminfo;
    unsigned short val[3];
    int i, r, tbit, bit, id[3], cmd;
    void *ptr;

    while ((tbit = rcv(parent)) != -1) {
        id[0] = rcv(parent);
        id[1] = rcv(parent);
        id[2] = rcv(parent);

        bit = 4;
        for (i = 0; i < 4; i++) {
            r = semctl(id[0], 0, cmds[i]);
            if (r < 0 && (r != -1 || errno != EACCES)) e(0);
            if (((bit & tbit) == bit) != (r != -1)) e(0);

            r = semctl(id[1], 0, cmds[i]);
            if (r < 0 && (r != -1 || errno != EACCES)) e(0);
            if (((bit & tbit) == bit) != (r != -1)) e(0);

            if (semctl(id[2], 0, cmds[i]) != -1) e(0);
            if (errno != EACCES) e(0);
        }

        bit = 2;
        r = semctl(id[0], 0, SETVAL, 0);
        if (r < 0 && (r != -1 || errno != EACCES)) e(0);
        if (((bit & tbit) == bit) != (r != -1)) e(0);

        r = semctl(id[1], 0, SETVAL, 0);
        if (r < 0 && (r != -1 || errno != EACCES)) e(0);
        if (((bit & tbit) == bit) != (r != -1)) e(0);

        if (semctl(id[2], 0, SETVAL, 0) != -1) e(0);
        if (errno != EACCES) e(0);

        memset(val, 0, sizeof(val));

        for (i = 0; i < 3; i++) {
            if (i == 0) {
                cmd = GETALL;
                ptr = val;
                bit = 4;
            } else if (i == 1) {
                cmd = SETALL;
                ptr = val;
                bit = 2;
            } else {
                cmd = IPC_STAT;
                ptr = &semds;
                bit = 4;
            }

            r = semctl(id[0], 0, cmd, ptr);
            if (r < 0 && (r != -1 || errno != EACCES)) e(0);
            if (((bit & tbit) == bit) != (r != -1)) e(0);

            r = semctl(id[1], 0, cmd, ptr);
            if (r < 0 && (r != -1 || errno != EACCES)) e(0);
            if (((bit & tbit) == bit) != (r != -1)) e(0);

            if (semctl(id[2], 0, cmd, ptr) != -1) e(0);
            if (errno != EACCES) e(0);
        }

#ifndef IPCID_TO_IX
#define IPCID_TO_IX(id) ((id) & 0xffff)
#endif

        bit = 4;

        r = semctl(IPCID_TO_IX(id[0]), 0, SEM_STAT, &semds);
        if (r < 0 && (r != -1 || errno != EACCES)) e(0);
        if (((bit & tbit) == bit) != (r != -1)) e(0);

        r = semctl(IPCID_TO_IX(id[1]), 0, SEM_STAT, &semds);
        if (r < 0 && (r != -1 || errno != EACCES)) e(0);
        if (((bit & tbit) == bit) != (r != -1)) e(0);

        if (semctl(IPCID_TO_IX(id[2]), 0, SEM_STAT, &semds) != -1)
            e(0);
        if (errno != EACCES) e(0);

        if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
        if (semctl(0, 0, SEM_INFO, &seminfo) == -1) e(0);

        snd(parent, 0);
    }
}

/*
 * Test semctl(2) permission checks, part 2: the IPC_SET command.
 */
static void
test88c_perm2(struct link * parent)
{
	struct semid_ds semds;
	int r, shift, id[3];

	while ((shift = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		memset(&semds, 0, sizeof(semds));

		for (int i = 0; i < 3; i++) {
			r = semctl(id[i], 0, IPC_SET, &semds);
			if (r < 0 && (r != -1 || errno != EPERM)) e(0);
			if ((shift == 6) != (r != -1)) e(0);
		}

		snd(parent, 0);
	}
}

/*
 * Test semctl(2) permission checks, part 3: the IPC_RMID command.
 */
static void
test88c_perm3(struct link * parent)
{
	int r, shift, id[3];
	int i;

	while ((shift = rcv(parent)) != -1) {
		for (i = 0; i < 3; i++) {
			id[i] = rcv(parent);
		}

		for (i = 0; i < 3; i++) {
			r = semctl(id[i], 0, IPC_RMID);
			if (r < 0 && (r != -1 || errno != EPERM)) {
				e(0);
			}
			if ((shift == 6) != (r != -1)) {
				e(0);
			}
		}

		snd(parent, 0);
	}
}

/*
 * Test the basic semctl(2) functionality.
 */
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

    badid1 = semget(IPC_PRIVATE, 1, 0600);
    if (badid1 < 0) e(0);

    if (semctl(badid1, 0, IPC_RMID) != 0) e(0);

    memset(&semds, 0, sizeof(semds));
    badid2 = IXSEQ_TO_IPCID(seminfo.semmni, semds.sem_perm);

    id = semget(IPC_PRIVATE, 3, IPC_CREAT | 0600);
    if (id < 0) e(0);

    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime == 0) e(0);

    while (time(&now) == semds.sem_ctime)
        usleep(250000);

    for (i = 0; i < sizeof(cmds)/sizeof(cmds[0]); i++) {
        for (j = 0; j < 3; j++) {
            if (semctl(id, j, cmds[i]) != 0) e(0);
        }

        if (semctl(badid1, 0, cmds[i]) != -1) e(0);
        if (errno != EINVAL) e(0);

        if (semctl(badid2, 0, cmds[i]) != -1) e(0);
        if (errno != EINVAL) e(0);

        if (semctl(-1, 0, cmds[i]) != -1) e(0);
        if (errno != EINVAL) e(0);

        if (semctl(INT_MIN, 0, cmds[i]) != -1) e(0);
        if (errno != EINVAL) e(0);

        if (semctl(id, -1, cmds[i]) != -1) e(0);
        if (errno != EINVAL) e(0);

        if (semctl(id, 3, cmds[i]) != -1) e(0);
        if (errno != EINVAL) e(0);

        if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
        if (semds.sem_otime != 0) e(0);
        if (semds.sem_ctime >= now) e(0);
    }

    for (j = 0; j < 5; j++) {
        for (i = 0; i < sizeof(val)/sizeof(val[0]); i++)
            val[i] = USHRT_MAX;

        if (semctl(id, (int)j - 1, GETALL, val) != 0) e(0);
        for (i = 0; i < 3; i++) {
            if (val[i] != 0) e(0);
        }
        if (val[i] != USHRT_MAX) e(0);
    }

    for (i = 0; i < sizeof(val)/sizeof(val[0]); i++)
        val[i] = USHRT_MAX;

    if (semctl(badid1, 0, GETALL, val) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(badid2, 0, GETALL, val) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(-1, 0, GETALL, val) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(INT_MIN, 0, GETALL, val) != -1) e(0);
    if (errno != EINVAL) e(0);

    for (i = 0; i < sizeof(val)/sizeof(val[0]); i++) {
        if (val[i] != USHRT_MAX) e(0);
    }

    if (semctl(id, 0, GETALL, NULL) != -1) e(0);
    if (errno != EFAULT) e(0);

    if (semctl(id, 0, GETALL, bad_ptr) != -1) e(0);
    if (errno != EFAULT) e(0);

    if (semctl(id, 0, GETALL, ((unsigned short *)bad_ptr) - 2) != -1) e(0);
    if (errno != EFAULT) e(0);

    if (semctl(id, 0, GETALL, ((unsigned short *)bad_ptr) - 3) != 0) e(0);

    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime >= now) e(0);

    memset(statbuf, 0x5a, sizeof(statbuf));

    if (semctl(badid1, 0, IPC_STAT, statbuf) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(badid2, 0, IPC_STAT, statbuf) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(-1, 0, IPC_STAT, statbuf) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(INT_MIN, 0, IPC_STAT, statbuf) != -1) e(0);
    if (errno != EINVAL) e(0);

    for (i = 0; i < sizeof(statbuf); i++) {
        if (statbuf[i] != 0x5a) e(0);
    }

    if (semctl(id, 0, IPC_STAT, statbuf) != 0) e(0);

    if (statbuf[sizeof(statbuf) - 1] != 0x5a) e(0);

    if (semctl(id, 0, IPC_STAT, NULL) != -1) e(0);
    if (errno != EFAULT) e(0);

    if (semctl(id, 0, IPC_STAT, bad_ptr) != -1) e(0);
    if (errno != EFAULT) e(0);

    if (semctl(id, 0, IPC_STAT, ((struct semid_ds *)bad_ptr) - 1) != 0)
        e(0);

    if (semctl(id, -1, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime >= now) e(0);

    id2 = semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0642);
    if (id2 < 0) e(0);

    memset(statbuf, 0x5a, sizeof(statbuf));

    if (semctl(-1, 0, SEM_STAT, statbuf) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(seminfo.semmni, 0, SEM_STAT, statbuf) != -1) e(0);
    if (errno != EINVAL) e(0);

    for (i = 0; i < sizeof(statbuf); i++) {
        if (statbuf[i] != 0x5a) e(0);
    }

    memset(seen, 0, sizeof(seen));

    for (i = 0; i < seminfo.semmni; i++) {
        errno = 0;
        r = semctl(i, i / 2 - 1, SEM_STAT, statbuf);
        if (r == -1) {
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

            if (semctl(i, 0, SEM_STAT, NULL) != -1) e(0);
            if (errno != EFAULT) e(0);

            if (semctl(i, 0, SEM_STAT, bad_ptr) != -1) e(0);
            if (errno != EFAULT) e(0);
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

    if (semctl(id, 5, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime >= now) e(0);

    if (semctl(badid1, 0, SETVAL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(badid2, 0, SETVAL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(-1, 0, SETVAL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(INT_MIN, 0, SETVAL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(id, -1, SETVAL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(id, 3, SETVAL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(id, 0, SETVAL, -1) != -1) e(0);
    if (errno != ERANGE) e(0);

    if (semctl(id, 0, SETVAL, seminfo.semvmx + 1) != -1) e(0);
    if (errno != ERANGE) e(0);

    TEST_SEM(id, 0, 0, 0, 0, 0);

    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime >= now) e(0);

    if (semctl(id, 1, SETVAL, 0) != 0) e(0);

    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);

    TEST_SEM(id, 1, 0, 0, 0, 0);

    if (semctl(id, 2, SETVAL, seminfo.semvmx) != 0) e(0);

    TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

    if (semctl(id, 0, SETVAL, 1) != 0) e(0);

    TEST_SEM(id, 0, 1, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

    if (semctl(id, 0, GETALL, val) != 0) e(0);
    if (val[0] != 1) e(0);
    if (val[1] != 0) e(0);
    if (val[2] != seminfo.semvmx) e(0);

    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);

    while (time(&now) == semds.sem_ctime)
        usleep(250000);

    if (semctl(badid1, 0, SETALL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(badid2, 0, SETALL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(-1, 0, SETALL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(INT_MIN, 0, SETALL, 1) != -1) e(0);
    if (errno != EINVAL) e(0);

    val[0] = seminfo.semvmx + 1;
    val[1] = 0;
    val[2] = 0;
    if (semctl(id, 0, SETALL, val) != -1) e(0);
    if (errno != ERANGE) e(0);

    val[0] = 0;
    val[1] = 1;
    val[2] = seminfo.semvmx + 1;
    if (semctl(id, 0, SETALL, val) != -1) e(0);
    if (errno != ERANGE) e(0);

    if (semctl(id, 0, SETALL, NULL) != -1) e(0);
    if (errno != EFAULT) e(0);

    if (semctl(id, 0, SETALL, bad_ptr) != -1) e(0);
    if (errno != EFAULT) e(0);

    if (semctl(id, 0, SETALL, ((unsigned short *)bad_ptr) - 2) != -1) e(0);
    if (errno != EFAULT) e(0);

    TEST_SEM(id, 0, 1, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime >= now) e(0);

    val[0] = seminfo.semvmx;
    val[1] = 0;
    val[2] = 0;
    if (semctl(id, 0, SETALL, val) != 0) e(0);

    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);

    TEST_SEM(id, 0, seminfo.semvmx, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, 0, 0, 0, 0);

    val[0] = 0;
    val[1] = 1;
    val[2] = seminfo.semvmx;
    if (semctl(id, INT_MAX, SETALL, val) != 0) e(0);

    TEST_SEM(id, 0, 0, 0, 0, 0);
    TEST_SEM(id, 1, 1, 0, 0, 0);
    TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

    memset(page_ptr, 0, page_size);
    if (semctl(id, 0, SETALL, ((unsigned short *)bad_ptr) - 3) != 0) e(0);

    TEST_SEM(id, 0, 0, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, 0, 0, 0, 0);

    while (time(&now) == semds.sem_ctime)
        usleep(250000);

    if (semctl(badid1, 0, IPC_SET, &semds) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(badid2, 0, IPC_SET, &semds) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(-1, 0, IPC_SET, &semds) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(INT_MIN, 0, IPC_SET, &semds) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(id, 0, IPC_SET, NULL) != -1) e(0);
    if (errno != EFAULT) e(0);

    if (semctl(id, 0, IPC_SET, bad_ptr) != -1) e(0);
    if (errno != EFAULT) e(0);

    if (semctl(id, 0, IPC_STAT, &osemds) != 0) e(0);
    if (osemds.sem_otime != 0) e(0);
    if (osemds.sem_ctime >= now) e(0);

    memset(&semds, 0x5b, sizeof(semds));
    semds.sem_perm.mode = 0712;
    semds.sem_perm.uid = UID_MAX;
    semds.sem_perm.gid = GID_MAX - 1;
    if (semctl(id, 0, IPC_SET, &semds) != 0) e(0);

    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
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
        if (semctl(id, i / 2 - 1, IPC_SET, &semds) != 0) e(0);

        if (semctl(id, i / 2 - 2, IPC_STAT, &semds) != 0) e(0);
        if (semds.sem_perm.mode != (SEM_ALLOC | i)) e(0);

        semds.sem_perm.mode = ~0777 | i;
        if (semctl(id, i / 2 - 3, IPC_SET, &semds) != 0) e(0);

        if (semctl(id, i / 2 - 4, IPC_STAT, &semds) != 0) e(0);
        if (semds.sem_perm.mode != (SEM_ALLOC | i)) e(0);
    }
    if (semds.sem_perm.uid != osemds.sem_perm.uid) e(0);
    if (semds.sem_perm.gid != osemds.sem_perm.gid) e(0);

    if (semctl(id, 0, IPC_SET, ((struct semid_ds *)bad_ptr) - 1) != 0)
        e(0);

    if (semctl(badid1, 0, IPC_RMID) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(badid2, 0, IPC_RMID) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(-1, 0, IPC_RMID) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(INT_MIN, 0, IPC_RMID) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(id, 0, IPC_RMID) != 0) e(0);

    if (semctl(id, 0, IPC_RMID) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(id, 0, IPC_STAT, &semds) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(id2, 1, IPC_RMID) != 0) e(0);

    if (semctl(id2, 1, IPC_RMID) != -1) e(0);
    if (errno != EINVAL) e(0);

    id = semget(IPC_PRIVATE, 3, 0600);
    if (id == -1) e(0);
    id2 = semget(IPC_PRIVATE, 1, 0600);
    if (id2 == -1) e(0);

    for (i = 0; i <= 1; i++) {
        cmd = (i == 0) ? IPC_INFO : SEM_INFO;

        memset(&seminfo, 0xff, sizeof(seminfo));

        r = semctl(0, 0, cmd, &seminfo);
        if (r == -1) e(0);

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
        } else {
            if (seminfo.semusz < 0) e(0);
        }
        if (seminfo.semvmx < 3 || seminfo.semvmx > SHRT_MAX) e(0);
        if (cmd == SEM_INFO) {
            if (seminfo.semaem < 4) e(0);
        } else {
            if (seminfo.semaem < 0) e(0);
        }

        if (semctl(INT_MAX, -1, cmd, &seminfo) == -1) e(0);
        if (semctl(-1, INT_MAX, cmd, &seminfo) == -1) e(0);

        if (semctl(0, 0, cmd, NULL) != -1) e(0);
        if (errno != EFAULT) e(0);

        if (semctl(0, 0, cmd, bad_ptr) != -1) e(0);
        if (errno != EFAULT) e(0);

        if (semctl(0, 0, cmd, ((struct seminfo *)bad_ptr) - 1) == -1)
            e(0);
    }

    if (semctl(id2, 0, IPC_RMID) != 0) e(0);

    if (semctl(id, 0, INT_MIN) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(id, 0, INT_MAX) != -1) e(0);
    if (errno != EINVAL) e(0);

    if (semctl(id, 0, IPC_RMID) != 0) e(0);
}

/*
 * Test SEM_UNDO support.  Right now this functionality is missing altogether.
 * For now, we test that any attempt to use SEM_UNDO fails.
 */
static void
test88d(void)
{
	struct sembuf sop;
	int id;

	subtest = 3;

	id = semget(IPC_PRIVATE, 1, 0600);
	if (id == -1) {
		e(0);
		return;
	}

	if (!(SHRT_MAX & SEM_UNDO)) {
		e(0);
		semctl(id, 0, IPC_RMID);
		return;
	}

	sop.sem_num = 0;
	sop.sem_op = 1;
	sop.sem_flg = SHRT_MAX;

	if (semop(id, &sop, 1) != -1) {
		e(0);
		semctl(id, 0, IPC_RMID);
		return;
	}

	if (errno != EINVAL) {
		e(0);
		semctl(id, 0, IPC_RMID);
		return;
	}

	if (semctl(id, 0, IPC_RMID) != 0) {
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
	struct sembuf sops[3];
	struct seminfo seminfo;
	int child, id, num;

	if (!parent) return;

	child = rcv(parent);
	id = rcv(parent);
	num = rcv(parent);

	memset(sops, 0, sizeof(sops));

	switch (child) {
	case 1:
		sops[0].sem_num = num;
		sops[0].sem_op = 1;
		sops[1].sem_num = num;
		sops[1].sem_op = 0;
		sops[2].sem_num = 0;
		sops[2].sem_op = 1;
		break;
	case 2:
		if (semctl(0, 0, IPC_INFO, &seminfo) == -1) {
			e(0);
			return;
		}
		sops[0].sem_num = num;
		sops[0].sem_op = -seminfo.semvmx;
		sops[1].sem_num = num;
		sops[1].sem_op = -seminfo.semvmx;
		sops[2].sem_num = 0;
		sops[2].sem_op = 1;
		break;
	default:
		e(0);
		return;
	}

	snd(parent, 0);

	if (semop(id, sops, 3) != -1) {
		e(0);
		return;
	}
	if (errno != EIDRM) {
		e(0);
		return;
	}
}

/*
 * First child procedure.
 */
static void
test88e_child1(struct link * parent)
{
	struct sembuf sops[3];
	size_t nsops;
	int match, id, expect;

	match = rcv(parent);
	id = rcv(parent);

	memset(sops, 0, sizeof(sops));
	sops[0].sem_num = 2;
	sops[0].sem_op = -1;
	nsops = 2;
	expect = 0;

	switch (match) {
	case MATCH_FIRST:
	case MATCH_BOTH:
	case MATCH_CASCADE:
	case MATCH_ALL:
		sops[1].sem_num = 3;
		sops[1].sem_op = 1;
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
		expect = INT_MIN;
		break;
	default:
		e(0);
		return;
	}

	snd(parent, 0);

	if (semop(id, sops, nsops) != expect) {
		e(0);
		return;
	}
	if (expect == -1 && errno != EIDRM) {
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
	int match, id, expect;

	match = rcv(parent);
	id = rcv(parent);

	memset(sops, 0, sizeof(sops));
	sops[0].sem_num = 2;
	sops[0].sem_op = -1;
	nsops = 2;
	expect = 0;

	switch (match) {
	case MATCH_FIRST:
		sops[1].sem_num = 0;
		sops[1].sem_op = 1;
		expect = -1;
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
		return;
	}

	snd(parent, 0);

	if (semop(id, sops, nsops) != expect) {
		e(0);
		return;
	}
	if (expect == -1 && errno != EIDRM) {
		e(0);
		return;
	}
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
		return;
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
static void
sub88e(unsigned int match, unsigned int resume, unsigned int aux)
{
	struct link aux1, aux2, child1, child2, child3;
	struct sembuf sop;
	unsigned short val[4];
	int id, inc, aux_zcnt, aux_ncnt;

	id = semget(IPC_PRIVATE, __arraycount(val), 0666);
	if (id == -1) e(0);

	aux_zcnt = aux_ncnt = 0;

	if (aux & 1) {
		spawn(&aux1, test88e_childaux, DROP_ALL);
		snd(&aux1, 1);
		snd(&aux1, id);
		snd(&aux1, (aux & 4) ? 2 : 1);
		if (rcv(&aux1) != 0) e(0);
		if (aux & 4) aux_zcnt++;
	}

	spawn(&child1, test88e_child1, DROP_ALL);
	snd(&child1, match);
	snd(&child1, id);
	if (rcv(&child1) != 0) e(0);

	if (match == MATCH_FIRST || match == MATCH_SECOND || match == MATCH_KILL) {
		usleep(WAIT_USECS);
	}

	spawn(&child2, test88e_child2, DROP_NONE);
	snd(&child2, match);
	snd(&child2, id);
	if (rcv(&child2) != 0) e(0);

	if (match == MATCH_ALL) {
		spawn(&child3, test88e_child3, DROP_USER);
		snd(&child3, match);
		snd(&child3, id);
		if (rcv(&child3) != 0) e(0);
	}

	if (aux & 2) {
		spawn(&aux2, test88e_childaux, DROP_NONE);
		snd(&aux2, 2);
		snd(&aux2, id);
		snd(&aux2, (aux & 4) ? 2 : 1);
		if (rcv(&aux2) != 0) e(0);
		if (aux & 4) aux_ncnt++;
	}

	usleep(WAIT_USECS);

	inc = 1;
	if (match == MATCH_FIRST || match == MATCH_SECOND) {
		TEST_SEM(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, 3, 0, 0, 0, 0);
	} else if (match == MATCH_KILL) {
		TEST_SEM(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
		terminate(&child1);
		usleep(WAIT_USECS);
		TEST_SEM(id, 2, 0, 0, 1 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, 3, 0, 0, 0, 0);
	} else if (match == MATCH_BOTH) {
		TEST_SEM(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, 3, 0, 0, 0, 0);
		inc = 2;
	} else if (match == MATCH_CASCADE) {
		TEST_SEM(id, 2, 0, 0, 1 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, 3, 0, 0, 1, 0);
	} else if (match == MATCH_ALL) {
		TEST_SEM(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, 3, 0, 0, 1, 0);
		inc = 2;
	} else {
		e(0);
	}

	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, -1, -1);

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

	if (match == MATCH_FIRST) {
		TEST_SEM(id, 2, 0, child1.pid, 1 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, 3, 1, child1.pid, 0, 0);
		collect(&child1);
	} else if (match == MATCH_SECOND) {
		TEST_SEM(id, 2, 0, child2.pid, 1 + aux_ncnt, aux_zcnt);
		TEST_SEM(id, 3, 0, 0, 0, 0);
		collect(&child2);
	} else if (match == MATCH_KILL) {
		TEST_SEM(id, 2, 0, child2.pid, aux_ncnt, aux_zcnt);
		TEST_SEM(id, 3, 0, 0, 0, 0);
		collect(&child2);
	} else if (match == MATCH_BOTH) {
		TEST_SEM(id, 2, 0, -1, aux_ncnt, aux_zcnt);
		TEST_SEM(id, 3, 2, -1, 0, 0);
		collect(&child1);
		collect(&child2);
	} else if (match == MATCH_CASCADE) {
		TEST_SEM(id, 2, 0, child1.pid, aux_ncnt, aux_zcnt);
		TEST_SEM(id, 3, 0, child2.pid, 0, 0);
		collect(&child1);
		collect(&child2);
	} else if (match == MATCH_ALL) {
		TEST_SEM(id, 2, 0, -1, aux_ncnt, aux_zcnt);
		TEST_SEM(id, 3, 0, child3.pid, 0, 0);
		collect(&child1);
		collect(&child2);
		collect(&child3);
	} else {
		e(0);
	}

	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, -1, -1);

	if (semctl(id, 0, IPC_RMID) != 0) e(0);

	if (match == MATCH_FIRST) {
		collect(&child2);
	} else if (match == MATCH_SECOND) {
		collect(&child1);
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
static void
test88e(void)
{
	unsigned int resume, match, aux;

	subtest = 4;

	for (match = 0; match < NR_MATCHES; match++) {
		for (resume = 0; resume < NR_RESUMES; resume++) {
			for (aux = 1; aux <= 8; aux++) {
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
	struct sem_sysctl_info *semsi = NULL;
	size_t len = 0;
	int id[2], id2, seen[2];
	int32_t i;

	if (!parent) {
		e(0);
		return;
	}

	id[0] = rcv(parent);
	id[1] = rcv(parent);

	if (sysctl(mib, __arraycount(mib), NULL, &len, NULL, 0) != 0) {
		e(0);
		return;
	}

	if (len == 0) {
		e(0);
		return;
	}

	semsi = malloc(len);
	if (semsi == NULL) {
		e(0);
		return;
	}

	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0) {
		free(semsi);
		e(0);
		return;
	}

	seen[0] = 0;
	seen[1] = 0;
	
	for (i = 0; i < semsi->seminfo.semmni; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
			continue;

		id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
		if (id2 == id[0]) {
			seen[0]++;
		} else if (id2 == id[1]) {
			seen[1]++;
		}
	}

	free(semsi);

	if (seen[0] != 1) {
		e(0);
		return;
	}
	if (seen[1] != 1) {
		e(0);
		return;
	}
}

/*
 * Test sysctl(2) based information retrieval.  This test aims to ensure that
 * in particular ipcs(1) and ipcrm(1) will be able to do their jobs.
 */
static void
test88f(void)
{
	static const int mib[] = { CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_INFO,
	    KERN_SYSVIPC_SEM_INFO };
	struct seminfo seminfo, seminfo2;
	struct sem_sysctl_info *semsi = NULL;
	struct semid_ds_sysctl *semds;
	struct link child;
	size_t len, size;
	int id[2] = {-1, -1}, id2;
	int32_t i, slot[2];

	len = sizeof(seminfo);
	if (sysctl(mib, __arraycount(mib), &seminfo, &len, NULL, 0) != 0) e(0);
	if (len != sizeof(seminfo)) e(0);

	if (semctl(0, 0, IPC_INFO, &seminfo2) == -1) e(0);

	if (memcmp(&seminfo, &seminfo2, sizeof(seminfo)) != 0) e(0);

	if (seminfo.semmni <= 0) e(0);
	if (seminfo.semmni > SHRT_MAX) e(0);

	size = sizeof(*semsi) + sizeof(semsi->semids[0]) * (seminfo.semmni - 1);

	len = 0;
	if (sysctl(mib, __arraycount(mib), NULL, &len, NULL, 0) != 0) e(0);
	if (len != size) e(0);

	id[0] = semget(KEY_A, 5, IPC_CREAT | 0612);
	if (id[0] < 0) e(0);

	id[1] = semget(IPC_PRIVATE, 3, 0650);
	if (id[1] < 0) {
		semctl(id[0], 0, IPC_RMID);
		e(0);
	}

	semsi = malloc(size);
	if (semsi == NULL) {
		semctl(id[0], 0, IPC_RMID);
		semctl(id[1], 0, IPC_RMID);
		e(0);
	}

	len = size;
	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0) {
		free(semsi);
		semctl(id[0], 0, IPC_RMID);
		semctl(id[1], 0, IPC_RMID);
		e(0);
	}
	if (len != size) {
		free(semsi);
		semctl(id[0], 0, IPC_RMID);
		semctl(id[1], 0, IPC_RMID);
		e(0);
	}

	if (sizeof(semsi->seminfo) != sizeof(seminfo)) {
		free(semsi);
		semctl(id[0], 0, IPC_RMID);
		semctl(id[1], 0, IPC_RMID);
		e(0);
	}
	if (memcmp(&semsi->seminfo, &seminfo, sizeof(semsi->seminfo)) != 0) {
		free(semsi);
		semctl(id[0], 0, IPC_RMID);
		semctl(id[1], 0, IPC_RMID);
		e(0);
	}

	slot[0] = slot[1] = -1;
	for (i = 0; i < seminfo.semmni; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
			continue;

		id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
		if (id2 == id[0]) {
			if (slot[0] != -1) {
				free(semsi);
				semctl(id[0], 0, IPC_RMID);
				semctl(id[1], 0, IPC_RMID);
				e(0);
			}
			slot[0] = i;
		} else if (id2 == id[1]) {
			if (slot[1] != -1) {
				free(semsi);
				semctl(id[0], 0, IPC_RMID);
				semctl(id[1], 0, IPC_RMID);
				e(0);
			}
			slot[1] = i;
		}
	}

	if (slot[0] < 0 || slot[1] < 0) {
		free(semsi);
		semctl(id[0], 0, IPC_RMID);
		semctl(id[1], 0, IPC_RMID);
		e(0);
	}

	semds = &semsi->semids[slot[0]];
	if (semds->sem_perm.uid != geteuid() ||
	    semds->sem_perm.gid != getegid() ||
	    semds->sem_perm.cuid != geteuid() ||
	    semds->sem_perm.cgid != getegid() ||
	    semds->sem_perm.mode != (SEM_ALLOC | 0612) ||
	    semds->sem_perm._key != KEY_A ||
	    semds->sem_nsems != 5 ||
	    semds->sem_otime != 0 ||
	    semds->sem_ctime == 0) {
		free(semsi);
		semctl(id[0], 0, IPC_RMID);
		semctl(id[1], 0, IPC_RMID);
		e(0);
	}

	semds = &semsi->semids[slot[1]];
	if (semds->sem_perm.uid != geteuid() ||
	    semds->sem_perm.gid != getegid() ||
	    semds->sem_perm.cuid != geteuid() ||
	    semds->sem_perm.cgid != getegid() ||
	    semds->sem_perm.mode != (SEM_ALLOC | 0650) ||
	    semds->sem_perm._key != IPC_PRIVATE ||
	    semds->sem_nsems != 3 ||
	    semds->sem_otime != 0 ||
	    semds->sem_ctime == 0) {
		free(semsi);
		semctl(id[0], 0, IPC_RMID);
		semctl(id[1], 0, IPC_RMID);
		e(0);
	}

	spawn(&child, test88f_child, DROP_ALL);
	snd(&child, id[0]);
	snd(&child, id[1]);
	collect(&child);

	if (semctl(id[0], 0, IPC_RMID) != 0) e(0);
	if (semctl(id[1], 0, IPC_RMID) != 0) e(0);

	len = size;
	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0) {
		free(semsi);
		e(0);
	}
	if (len != size) {
		free(semsi);
		e(0);
	}

	for (i = 0; i < seminfo.semmni; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
			continue;

		id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
		if (id2 == id[0] || id2 == id[1]) {
			free(semsi);
			e(0);
		}
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

	if (setuid(geteuid()) != 0) e(0);

	gr = getgrnam(ROOT_GROUP);
	if (gr == NULL) e(0);

	if (setgid(gr->gr_gid) != 0) e(0);
	if (setegid(gr->gr_gid) != 0) e(0);

	len = sizeof(i);
	if (sysctl(mib, __arraycount(mib), &i, &len, NULL, 0) != 0) e(0);
	if (len != sizeof(i)) e(0);

	if (i == 0) {
		printf("skipped\n");
		cleanup();
		exit(0);
	}

	page_size = getpagesize();
	page_ptr = mmap(NULL, page_size * 2, PROT_READ | PROT_WRITE,
	    MAP_ANON | MAP_PRIVATE, -1, 0);
	if (page_ptr == MAP_FAILED) e(0);
	bad_ptr = page_ptr + page_size;
	if (munmap(bad_ptr, page_size) != 0) e(0);
}

/*
 * Test program for SysV IPC semaphores.
 */
#include <stdlib.h>

#define DEFAULT_MASK 0xFF
#define MAX_TESTS 6

int
main(int argc, char ** argv)
{
	int i, m;
	void (*test_functions[])(void) = {
		test88a, test88b, test88c, test88d, test88e, test88f
	};

	start(88);
	test88_init();

	m = (argc == 2) ? atoi(argv[1]) : DEFAULT_MASK;

	for (i = 0; i < ITERATIONS; i++) {
		for (int test_idx = 0; test_idx < MAX_TESTS; test_idx++) {
			if (m & (1 << test_idx)) {
				test_functions[test_idx]();
			}
		}
	}

	quit();
	return 0;
}
