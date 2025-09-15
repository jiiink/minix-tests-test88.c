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
drop_child_privileges(int drop_level)
{
	struct passwd *pw;
	struct group *gr;

	switch (drop_level) {
	case DROP_ALL:
		if (setgroups(0, NULL) != 0) e(0);

		if ((gr = getgrnam(NONROOT_GROUP)) == NULL) e(0);

		if (setgid(gr->gr_gid) != 0) e(0);
		if (setegid(gr->gr_gid) != 0) e(0);

		/* FALLTHROUGH */
	case DROP_USER:
		if ((pw = getpwnam(NONROOT_USER)) == NULL) e(0);

		if (setuid(pw->pw_uid) != 0) e(0);
		break;
	}
}

static void
spawn(struct link * link, void (* proc)(struct link *), int drop)
{
	int up[2], dn[2];

	fflush(stdout);
	fflush(stderr);

	if (pipe(up) != 0) e(0);
	if (pipe(dn) != 0) e(0);

	link->pid = fork();

	switch (link->pid) {
	case 0: /* Child process */
		close(up[1]);
		close(dn[0]);

		link->pid = getppid();
		link->rcvfd = up[0];
		link->sndfd = dn[1];

		errct = 0;

		drop_child_privileges(drop);

		proc(link);

		exit(errct);
	case -1: /* Fork failed */
		e(0);
		break;
	default: /* Parent process */
		close(up[0]);
		close(dn[1]);

		link->sndfd = up[1];
		link->rcvfd = dn[0];
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

	(void)close(link->sndfd);
	(void)close(link->rcvfd);

	if (waitpid(link->pid, &status, 0) != link->pid) {
		e(0);
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

	if (kill(link->pid, SIGKILL) != 0) {
		e(0);
	}

	close(link->sndfd);
	close(link->rcvfd);

	if (waitpid(link->pid, &status, 0) <= 0) {
		e(0);
	}

	if (WIFEXITED(status)) {
		errct += WEXITSTATUS(status);
	} else if (WIFSIGNALED(status)) {
		if (WTERMSIG(status) != SIGKILL) {
			e(0);
		}
	} else {
		e(0);
	}
}

/*
 * Send an integer value to the child or parent.
 */
static int
snd(struct link * link, int val)
{
    ssize_t bytes_expected = sizeof(val);
    ssize_t bytes_written = write(link->sndfd, &val, bytes_expected);

    if (bytes_written == -1) {
        return -1;
    }

    if (bytes_written != bytes_expected) {
        return -1;
    }

    return 0;
}

/*
 * Receive an integer value from the child or parent, or -1 on EOF.
 */
#include <unistd.h> // For read
#include <stdlib.h> // For abort

// Assuming struct link is defined elsewhere, for example:
// struct link {
//     int rcvfd;
//     // other members
// };

static int
rcv(struct link *link)
{
	int val;
	ssize_t bytes_read;

	bytes_read = read(link->rcvfd, (void *)&val, sizeof(val));

	if (bytes_read == -1) {
		// An actual I/O error occurred.
		// The original code's 'e(0)' suggests a critical, unrecoverable error
		// for such cases (including read errors).
		abort();
	} else if (bytes_read == 0) {
		// End Of File or connection closed.
		// This matches the original behavior of returning -1.
		return -1;
	} else if ((size_t)bytes_read != sizeof(val)) {
		// A "short read": fewer bytes were read than expected.
		// The original code's 'e(0)' suggests this is also a critical error.
		abort();
	}

	// Success: exactly sizeof(val) bytes were read.
	return val;
}

/*
 * Child procedure that creates semaphore sets.
 */
static void
test_perm_child(struct link * parent)
{
	struct semid_ds semds;
	uid_t uid;
	gid_t gid;
	int mask, rmask, sugid;
	int id[3];
	uid_t effective_uid;
	gid_t effective_gid;

	while ((mask = rcv(parent)) != -1) {
		rmask = rcv(parent);
		if (rmask == -1) {
			e(0);
		}

		sugid = rcv(parent);
		if (sugid == -1) {
			e(0);
		}

		if ((id[0] = semget(KEY_A, 3,
		    IPC_CREAT | IPC_EXCL |
		    ((sugid == SUGID_NONE) ? mask : 0))) == -1) e(0);
		if ((id[1] = semget(KEY_B, 3,
		    IPC_CREAT | IPC_EXCL | mask | rmask)) == -1) e(0);
		if ((id[2] = semget(KEY_C, 3,
		    IPC_CREAT | IPC_EXCL | rmask)) == -1) e(0);

		effective_uid = geteuid();
		effective_gid = getegid();
		uid = effective_uid;
		gid = effective_gid;

		if (sugid != SUGID_NONE) {
			struct passwd *pw_entry;
			struct group *gr_entry;

			switch (sugid) {
			case SUGID_ROOT_USER:
				if ((pw_entry = getpwnam(ROOT_USER)) == NULL) e(0);
				uid = pw_entry->pw_uid;
				break;
			case SUGID_NONROOT_USER:
				if ((pw_entry = getpwnam(NONROOT_USER)) == NULL)
					e(0);
				uid = pw_entry->pw_uid;
				break;
			case SUGID_ROOT_GROUP:
				if ((gr_entry = getgrnam(ROOT_GROUP)) == NULL) e(0);
				gid = gr_entry->gr_gid;
				break;
			case SUGID_NONROOT_GROUP:
				if ((gr_entry = getgrnam(NONROOT_GROUP)) == NULL)
					e(0);
				gid = gr_entry->gr_gid;
				break;
			}

			semds.sem_perm.uid = uid;
			semds.sem_perm.gid = gid;
			semds.sem_perm.mode = mask;
			if (semctl(id[0], 0, IPC_SET, &semds) != 0) e(0);
			semds.sem_perm.mode = mask | rmask;
			if (semctl(id[1], 0, IPC_SET, &semds) != 0) e(0);
			semds.sem_perm.mode = rmask;
			if (semctl(id[2], 0, IPC_SET, &semds) != 0) e(0);
		}

		if (mask & IPC_R) {
			if (semctl(id[0], 0, IPC_STAT, &semds) != 0) e(0);
			if (semds.sem_perm.mode != (SEM_ALLOC | mask)) e(0);
			if (semds.sem_perm.uid != uid) e(0);
			if (semds.sem_perm.gid != gid) e(0);
			if (semds.sem_perm.cuid != effective_uid) e(0);
			if (semds.sem_perm.cgid != effective_gid) e(0);
		}

		snd(parent, id[0]);
		snd(parent, id[1]);
		snd(parent, id[2]);

		int status_from_parent = rcv(parent);
		if (status_from_parent != 0) e(0);

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
#define NUM_PERMISSION_TEST_BITS 8
#define TERMINATION_SIGNAL -1

typedef struct {
    int shift;
    int child1_drop_privs;
    int child2_drop_privs;
    int sugid_mode;
} PermTestScenario;

static const PermTestScenario perm_test_scenarios[] = {
    {6, DROP_ALL,  DROP_ALL, SUGID_NONE},
    {6, DROP_NONE, DROP_ALL, SUGID_NONROOT_USER},
    {6, DROP_USER, DROP_ALL, SUGID_ROOT_USER},
    {3, DROP_NONE, DROP_USER, SUGID_NONE},
    {3, DROP_NONE, DROP_ALL, SUGID_NONROOT_GROUP},
    {3, DROP_NONE, DROP_USER, SUGID_NONROOT_GROUP},
    {0, DROP_NONE, DROP_ALL, SUGID_NONE}
};
static const int NUM_PERM_TEST_SCENARIOS = sizeof(perm_test_scenarios) / sizeof(perm_test_scenarios[0]);

static void
terminate_and_collect_children(struct link *child1, struct link *child2)
{
    snd(child1, TERMINATION_SIGNAL);
    snd(child2, TERMINATION_SIGNAL);
    collect(child1);
    collect(child2);
}

static void
test_perm(void (* proc)(struct link *), int owner_test)
{
	struct link child1, child2;
	int bit_val, mask, rmask;
	int child_ids[3];

	for (int scenario_idx = 0; scenario_idx < NUM_PERM_TEST_SCENARIOS; scenario_idx++) {
        const PermTestScenario *current_scenario = &perm_test_scenarios[scenario_idx];

        spawn(&child1, test_perm_child, current_scenario->child1_drop_privs);
        spawn(&child2, proc, current_scenario->child2_drop_privs);

		for (bit_val = 0; bit_val < NUM_PERMISSION_TEST_BITS; bit_val++) {
			mask = bit_val << current_scenario->shift;
			rmask = 0777 & ~(7 << current_scenario->shift);

			snd(&child1, mask);
			snd(&child1, rmask);
			snd(&child1, current_scenario->sugid_mode);
			child_ids[0] = rcv(&child1);
			child_ids[1] = rcv(&child1);
			child_ids[2] = rcv(&child1);

            int child2_send_val = owner_test ? current_scenario->shift : bit_val;
			snd(&child2, child2_send_val);
			snd(&child2, child_ids[0]);
			snd(&child2, child_ids[1]);
			snd(&child2, child_ids[2]);
			if (rcv(&child2) != 0) {
                e(0);
            }

			snd(&child1, 0);
		}

		terminate_and_collect_children(&child1, &child2);
	}
}

/*
 * Test semget(2) permission checks.  Please note that the checks are advisory:
 * nothing keeps a process from opening a semaphore set with fewer privileges
 * than required by the operations the process subsequently issues on the set.
 */
static void
test88a_perm(struct link * parent)
{
	int r;
	int tbit;
	int bit;
	int mask;
	int id[3];
	int expected_to_succeed_for_perm_check;

	while ((tbit = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		for (bit = 0; bit <= 7; bit++) {
			mask = bit << 6;

			r = semget(KEY_A, 0, mask);

			if (r == -1 && errno != EACCES) {
				e(0);
			}

			expected_to_succeed_for_perm_check = (bit != 0 && (bit & tbit) == bit);

			if (expected_to_succeed_for_perm_check != (r != -1)) {
				e(0);
			}
			if (r != -1 && r != id[0]) {
				e(0);
			}

			r = semget(KEY_B, 0, mask);

			if (r == -1 && errno != EACCES) {
				e(0);
			}

			expected_to_succeed_for_perm_check = (bit != 0 && (bit & tbit) == bit);

			if (expected_to_succeed_for_perm_check != (r != -1)) {
				e(0);
			}
			if (r != -1 && r != id[1]) {
				e(0);
			}

			r = semget(KEY_C, 0, mask);
			if (r != -1 || errno != EACCES) {
				e(0);
			}
		}
		snd(parent, 0);
	}
}

/*
 * Test the basic semget(2) functionality.
 */
#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <errno.h>
#include <unistd.h>
#include <limits.h>

/*
 * Assuming the following are defined externally by the test framework:
 * e(int) : A function or macro to signal a test failure.
 * KEY_A, KEY_B : Specific IPC keys for testing.
 * subtest : A global or file-scope variable to indicate which subtest failed.
 * TEST_SEM : A macro to check semaphore values.
 * SEM_ALLOC : A flag for sem_perm.mode.
 */

/* Helper macros for clearer error checking */
#define EXPECT_SUCCESS(expr) do { if ((expr) < 0) e(0); } while(0)
#define EXPECT_FAILURE(expr, expected_errno_val) do { if ((expr) != -1) e(0); if (errno != (expected_errno_val)) e(0); } while(0)
#define EXPECT_INT_EQ(val1, val2) do { if ((val1) != (val2)) e(0); } while(0)
#define EXPECT_INT_NE(val1, val2) do { if ((val1) == (val2)) e(0); } while(0)

/* Symbolic constants for semaphore permissions */
#define SEM_PERM_RW_USR         0600
#define SEM_PERM_RW_USR_R_GRP_OTH 0642
#define SEM_PERM_RW_USR_X_OTH   0613
#define SEM_PERM_NONE           0000

/*
 * Helper to clean up an array of semaphore IDs.
 * Invalid IDs (-1) are skipped.
 */
static void cleanup_sem_id_array(int *id_array, size_t count) {
    if (id_array == NULL) {
        return;
    }
    for (size_t i = 0; i < count; ++i) {
        if (id_array[i] >= 0) {
            if (semctl(id_array[i], 0, IPC_RMID) != 0) {
                e(0);
            }
            id_array[i] = -1; /* Mark as cleaned */
        }
    }
}

/*
 * Helper to remove an existing semaphore set by key.
 * This is used for pre-test cleanup to ensure a clean state.
 */
static void remove_existing_sem(key_t key) {
    int id;
    id = semget(key, 0, 0); /* Attempt to get the ID without creating */
    if (id >= 0) {
        if (semctl(id, 0, IPC_RMID) == -1) {
            e(0);
        }
    } else {
        if (errno != ENOENT) { /* Expect ENOENT if key doesn't exist */
            e(0);
        }
    }
}

/*
 * Helper to encapsulate semget calls expected to fail.
 * Checks the return value and errno.
 */
static void expect_semget_failure(key_t key, int nsems, int semflg, int expected_errno_val) {
    EXPECT_FAILURE(semget(key, nsems, semflg), expected_errno_val);
}

/*
 * Helper to encapsulate semget calls expected to succeed.
 * Returns the obtained semaphore ID.
 */
static int expect_semget_success(key_t key, int nsems, int semflg) {
    int id = semget(key, nsems, semflg);
    EXPECT_SUCCESS(id);
    return id;
}

/*
 * Tests that IPC_PRIVATE always yields a new, unique semaphore set ID.
 */
static void test_ipc_private_creation(void) {
    int id[3] = {-1, -1, -1}; /* Initialize IDs for robust cleanup */

    id[0] = expect_semget_success(IPC_PRIVATE, 1, IPC_CREAT | SEM_PERM_RW_USR);
    id[1] = expect_semget_success(IPC_PRIVATE, 1, IPC_CREAT | IPC_EXCL | SEM_PERM_RW_USR);
    id[2] = expect_semget_success(IPC_PRIVATE, 1, SEM_PERM_RW_USR);

    EXPECT_INT_NE(id[0], id[1]);
    EXPECT_INT_NE(id[1], id[2]);
    EXPECT_INT_NE(id[0], id[2]);

    cleanup_sem_id_array(id, 3);
}

/*
 * Tests open(2)-like semantics for non-IPC_PRIVATE keys with IPC_CREAT and IPC_EXCL.
 */
static void test_non_ipc_private_creation(void) {
    int id[3] = {-1, -1, -1};

    remove_existing_sem(KEY_A);
    remove_existing_sem(KEY_B);

    /* Attempt to get a non-existent key without IPC_CREAT, expect ENOENT */
    expect_semget_failure(KEY_A, 1, SEM_PERM_RW_USR, ENOENT);

    /* Create KEY_A with IPC_EXCL */
    id[0] = expect_semget_success(KEY_A, 1, IPC_CREAT | IPC_EXCL | SEM_PERM_RW_USR);

    /* Attempt to get a non-existent key without IPC_CREAT, expect ENOENT */
    expect_semget_failure(KEY_B, 1, SEM_PERM_RW_USR, ENOENT);

    /* Create KEY_B */
    id[1] = expect_semget_success(KEY_B, 1, IPC_CREAT | SEM_PERM_RW_USR);

    EXPECT_INT_NE(id[0], id[1]);

    /* Attempt to get existing KEY_A (without IPC_CREAT or IPC_EXCL) */
    id[2] = expect_semget_success(KEY_A, 1, SEM_PERM_RW_USR);
    EXPECT_INT_EQ(id[2], id[0]);

    /* Attempt to get existing KEY_B with IPC_CREAT (should return existing ID) */
    id[2] = expect_semget_success(KEY_B, 1, IPC_CREAT | SEM_PERM_RW_USR);
    EXPECT_INT_EQ(id[2], id[1]);

    /* Attempt to create existing KEY_A with IPC_EXCL, expect EEXIST */
    expect_semget_failure(KEY_A, 1, IPC_CREAT | IPC_EXCL | SEM_PERM_RW_USR, EEXIST);

    /* Cleanup: only id[0] and id[1] represent unique sets */
    cleanup_sem_id_array(id, 2);
}

/*
 * Tests the system-wide limits for the number of semaphore sets (SEMMNI).
 */
static void test_semaphore_set_limits(void) {
    struct seminfo seminfo;
    int *idp = NULL;
    unsigned int i, j;

    EXPECT_SUCCESS(semctl(0, 0, IPC_INFO, &seminfo));
    if (seminfo.semmni < 3 || seminfo.semmni > USHRT_MAX) {
        e(0);
    }

    idp = (int *)malloc(sizeof(int) * (seminfo.semmni + 1));
    if (idp == NULL) {
        e(0);
    }

    for (i = 0; i < seminfo.semmni + 1; ++i) {
        idp[i] = -1; /* Initialize for cleanup */
    }

    for (i = 0; i < seminfo.semmni + 1; i++) {
        if ((idp[i] = semget(KEY_A + i, 1, IPC_CREAT | SEM_PERM_RW_USR)) < 0) {
            break; /* Expected to fail with ENOSPC eventually */
        }

        /* Ensure no ID collisions among newly created sets */
        for (j = 0; j < i; j++) {
            EXPECT_INT_NE(idp[i], idp[j]);
        }
    }

    EXPECT_INT_EQ(errno, ENOSPC);
    if (i < 3) { /* Should be able to create at least a few */
        e(0);
    }
    if (i == seminfo.semmni + 1) { /* Should have failed before creating the last one */
        e(0);
    }

    cleanup_sem_id_array(idp, i);
    free(idp);
}

/*
 * Tests limits and behavior regarding the number of semaphores within a single set (SEMMSL).
 */
static void test_semaphore_count_limits(void) {
    struct seminfo seminfo;
    int id[2] = {-1, -1};

    remove_existing_sem(KEY_A);

    EXPECT_SUCCESS(semctl(0, 0, IPC_INFO, &seminfo));
    if (seminfo.semmsl < 3 || seminfo.semmsl > USHRT_MAX) {
        e(0);
    }

    /* Test invalid nsems values */
    expect_semget_failure(KEY_A, -1, IPC_CREAT | SEM_PERM_RW_USR, EINVAL);
    expect_semget_failure(KEY_A, 0, IPC_CREAT | SEM_PERM_RW_USR, EINVAL);
    expect_semget_failure(KEY_A, seminfo.semmsl + 1, IPC_CREAT | SEM_PERM_RW_USR, EINVAL);

    /* Create and immediately remove a set with the maximum allowed semaphores */
    id[0] = expect_semget_success(KEY_A, seminfo.semmsl, IPC_CREAT | SEM_PERM_RW_USR);
    EXPECT_SUCCESS(semctl(id[0], 0, IPC_RMID));
    id[0] = -1; /* Mark as removed */

    /* Create a set with 2 semaphores */
    id[0] = expect_semget_success(KEY_A, 2, IPC_CREAT | SEM_PERM_RW_USR);

    /* Attempt to get the existing set with various nsems, verify ID consistency */
    id[1] = expect_semget_success(KEY_A, 0, SEM_PERM_RW_USR);
    EXPECT_INT_EQ(id[0], id[1]);

    id[1] = expect_semget_success(KEY_A, 1, SEM_PERM_RW_USR);
    EXPECT_INT_EQ(id[0], id[1]);

    id[1] = expect_semget_success(KEY_A, 2, SEM_PERM_RW_USR);
    EXPECT_INT_EQ(id[0], id[1]);

    /* Attempt to get the existing set with more semaphores than it has, expect EINVAL */
    expect_semget_failure(KEY_A, 3, SEM_PERM_RW_USR, EINVAL);
    expect_semget_failure(KEY_A, seminfo.semmsl + 1, SEM_PERM_RW_USR, EINVAL);

    cleanup_sem_id_array(id, 1); /* Only id[0] needs cleanup, id[1] holds a duplicate ID */
}

/*
 * Verifies initial values of newly created semaphore sets and their permissions.
 */
static void test_initial_semaphore_values(void) {
    struct seminfo seminfo;
    struct semid_ds semds;
    time_t now;
    unsigned int i;
    int id[2] = {-1, -1};

    EXPECT_SUCCESS(semctl(0, 0, IPC_INFO, &seminfo));
    if (seminfo.semmns < 3 + seminfo.semmsl) { /* Ensure enough total semaphores for this test */
        e(0);
    }

    remove_existing_sem(KEY_A);

    time(&now); /* Capture time before creation for ctime check */

    id[0] = expect_semget_success(IPC_PRIVATE, 3, IPC_CREAT | IPC_EXCL | SEM_PERM_RW_USR_R_GRP_OTH);
    id[1] = expect_semget_success(KEY_A, seminfo.semmsl, IPC_CREAT | SEM_PERM_RW_USR_X_OTH);

    /* Verify properties of the IPC_PRIVATE set (id[0]) */
    EXPECT_SUCCESS(semctl(id[0], 0, IPC_STAT, &semds));
    EXPECT_INT_EQ(semds.sem_perm.uid, geteuid());
    EXPECT_INT_EQ(semds.sem_perm.gid, getegid());
    EXPECT_INT_EQ(semds.sem_perm.cuid, geteuid());
    EXPECT_INT_EQ(semds.sem_perm.cgid, getegid());
    EXPECT_INT_EQ(semds.sem_perm.mode, (SEM_ALLOC | SEM_PERM_RW_USR_R_GRP_OTH));
    EXPECT_INT_EQ(semds.sem_perm._key, IPC_PRIVATE);
    EXPECT_INT_EQ(semds.sem_nsems, 3);
    EXPECT_INT_EQ(semds.sem_otime, 0);
    if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) {
        e(0);
    }
    for (i = 0; i < semds.sem_nsems; i++) {
        TEST_SEM(id[0], i, 0, 0, 0, 0); /* Verify initial semaphore values are zero */
    }

    /* Verify properties of the KEY_A set (id[1]) */
    EXPECT_SUCCESS(semctl(id[1], 0, IPC_STAT, &semds));
    EXPECT_INT_EQ(semds.sem_perm.uid, geteuid());
    EXPECT_INT_EQ(semds.sem_perm.gid, getegid());
    EXPECT_INT_EQ(semds.sem_perm.cuid, geteuid());
    EXPECT_INT_EQ(semds.sem_perm.cgid, getegid());
    EXPECT_INT_EQ(semds.sem_perm.mode, (SEM_ALLOC | SEM_PERM_RW_USR_X_OTH));
    EXPECT_INT_EQ(semds.sem_perm._key, KEY_A);
    EXPECT_INT_EQ(semds.sem_nsems, seminfo.semmsl);
    EXPECT_INT_EQ(semds.sem_otime, 0);
    if (semds.sem_ctime < now || semds.sem_ctime >= now + 10) {
        e(0);
    }
    for (i = 0; i < semds.sem_nsems; i++) {
        TEST_SEM(id[1], i, 0, 0, 0, 0); /* Verify initial semaphore values are zero */
    }

    cleanup_sem_id_array(id, 2);
}

/*
 * Tests basic superuser permissions on semaphore sets.
 */
static void test_superuser_permissions(void) {
    int id[2] = {-1, -1};

    remove_existing_sem(KEY_A);

    /* Superuser can always create a semaphore set, even with 0000 permissions. */
    id[0] = expect_semget_success(KEY_A, 1, IPC_CREAT | IPC_EXCL | SEM_PERM_NONE);

    /* Superuser can get an existing set with different permissions. */
    id[1] = expect_semget_success(KEY_A, 0, SEM_PERM_RW_USR);
    EXPECT_INT_EQ(id[0], id[1]);

    /* Superuser can get an existing set with 0000 permissions. */
    id[1] = expect_semget_success(KEY_A, 0, SEM_PERM_NONE);
    EXPECT_INT_EQ(id[0], id[1]);

    cleanup_sem_id_array(id, 1); /* Only id[0] needs cleanup, id[1] holds a duplicate ID */
}

/*
 * Main test function for semget and initial semctl properties.
 */
static void
test88a(void)
{
    subtest = 0;

    test_ipc_private_creation();
    test_non_ipc_private_creation();
    test_semaphore_set_limits();
    test_semaphore_count_limits();
    test_initial_semaphore_values();
    test_superuser_permissions();

    /*
     * The following call is to an external function for more complex
     * permission tests, likely involving unprivileged child processes.
     */
    test_perm(test88a_perm, 0 /*owner_test*/);
}

/*
 * Test semop(2) permission checks.
 */
#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <string.h>
#include <errno.h>
#include <limits.h>
#include <stdbool.h>

struct link;
extern int rcv(struct link *parent);
extern void snd(struct link *parent, int data);
extern void e(int code);

#define MAX_SEMAPHORE_OPERATIONS 2

typedef struct {
    struct sembuf sops[MAX_SEMAPHORE_OPERATIONS];
    size_t nsops;
    int bit_mask;
    bool handle_efbig_as_success;
} semaphore_test_config_t;

const semaphore_test_config_t test_configs[] = {
    { .sops = {{{0, 0, 0}}, {{0, 0, 0}}}, .nsops = 1, .bit_mask = 4, .handle_efbig_as_success = false },
    { .sops = {{{0, 1, 0}}, {{0, 0, 0}}}, .nsops = 1, .bit_mask = 2, .handle_efbig_as_success = false },
    { .sops = {{{0, -1, 0}}, {{0, 0, 0}}}, .nsops = 1, .bit_mask = 2, .handle_efbig_as_success = false },
    { .sops = {{{0, 0, 0}}, {{0, 1, 0}}}, .nsops = 2, .bit_mask = 6, .handle_efbig_as_success = false },
    { .sops = {{{1, 0, 0}}, {{0, -1, 0}}}, .nsops = 2, .bit_mask = 6, .handle_efbig_as_success = false },
    { .sops = {{{0, 0, 0}}, {{1, 0, 0}}}, .nsops = 2, .bit_mask = 4, .handle_efbig_as_success = false },
    { .sops = {{{0, 1, 0}}, {{0, -1, 0}}}, .nsops = 2, .bit_mask = 2, .handle_efbig_as_success = false },
    { .sops = {{{USHRT_MAX, 0, 0}}, {{0, 0, 0}}}, .nsops = 2, .bit_mask = 4, .handle_efbig_as_success = true }
};

#define NUM_TEST_CONFIGS (sizeof(test_configs) / sizeof(test_configs[0]))

#define IS_BIT_SET(value, bit_mask) (((value) & (bit_mask)) == (bit_mask))

static void execute_and_verify_semop(int sem_id, const struct sembuf *sops, size_t nsops,
                                     int tbit, int config_bit_mask, bool handle_efbig_as_success,
                                     bool expect_fail)
{
    int r = semop(sem_id, (struct sembuf *)sops, nsops);

    if (handle_efbig_as_success && r == -1 && errno == EFBIG) {
        r = 0;
    }

    if (expect_fail) {
        if (r != -1 || errno != EACCES) {
            e(0);
        }
    } else {
        if (r == -1 && errno != EACCES) {
            e(0);
        }

        if (IS_BIT_SET(tbit, config_bit_mask) != (r != -1)) {
            e(0);
        }
    }
}

static void
test88b_perm(struct link * parent)
{
    int tbit;
    int sem_ids[3];
    size_t i;

    while ((tbit = rcv(parent)) != -1) {
        sem_ids[0] = rcv(parent);
        sem_ids[1] = rcv(parent);
        sem_ids[2] = rcv(parent);

        for (i = 0; i < NUM_TEST_CONFIGS; ++i) {
            const semaphore_test_config_t *config = &test_configs[i];

            execute_and_verify_semop(sem_ids[0], config->sops, config->nsops,
                                     tbit, config->bit_mask, config->handle_efbig_as_success,
                                     false);

            execute_and_verify_semop(sem_ids[1], config->sops, config->nsops,
                                     tbit, config->bit_mask, config->handle_efbig_as_success,
                                     false);

            execute_and_verify_semop(sem_ids[2], config->sops, config->nsops,
                                     tbit, config->bit_mask, config->handle_efbig_as_success,
                                     true);
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
		nr_signals = -1;
		return;
	}

	if (nr_signals == 0) {
		nr_signals = 1;
	} else {
		nr_signals = -2;
	}
}

/*
 * Child process for semop(2) tests, mainly testing blocking operations.
 */
#include <errno.h>
#include <string.h>
#include <signal.h>
#include <sys/sem.h>
#include <stdbool.h>

static void
execute_semop(int semid, const struct sembuf *ops_array, unsigned int num_ops,
              bool expected_result_is_success, int expected_errno_code, int expected_nr_signals_count)
{
    int result = semop(semid, (struct sembuf *)ops_array, num_ops);
    int current_errno = errno;

    if (expected_result_is_success) {
        if (result != 0) {
            e(0);
        }
    } else {
        if (result != -1) {
            e(0);
        }
        if (current_errno != expected_errno_code) {
            e(0);
        }
    }

    if (expected_nr_signals_count >= 0 && nr_signals != expected_nr_signals_count) {
        e(0);
    }
}

static void
check_rcv_result(struct link *l, int expected_value)
{
    if (rcv(l) != expected_value) {
        e(0);
    }
}

static void
test88b_child(struct link *parent)
{
    int sem_id;
    struct sigaction act;

    sem_id = rcv(parent);

    {
        struct sembuf ops[1];
        ops[0].sem_num = 0; ops[0].sem_op = 0; ops[0].sem_flg = 0;
        execute_semop(sem_id, ops, 1, true, 0, -1);
    }

    check_rcv_result(parent, 1);

    {
        struct sembuf ops[1];
        ops[0].sem_num = 0; ops[0].sem_op = -3; ops[0].sem_flg = 0;
        execute_semop(sem_id, ops, 1, true, 0, -1);
    }

    check_rcv_result(parent, 2);

    {
        struct sembuf ops[3];
        ops[0].sem_num = 2; ops[0].sem_op = 2; ops[0].sem_flg = 0;
        ops[1].sem_num = 1; ops[1].sem_op = -1; ops[1].sem_flg = 0;
        ops[2].sem_num = 0; ops[2].sem_op = 1; ops[2].sem_flg = 0;
        execute_semop(sem_id, ops, 3, true, 0, -1);
    }

    check_rcv_result(parent, 3);

    {
        struct sembuf ops[5];
        ops[0].sem_num = 1; ops[0].sem_op = 0; ops[0].sem_flg = 0;
        ops[1].sem_num = 1; ops[1].sem_op = 1; ops[1].sem_flg = 0;
        ops[2].sem_num = 0; ops[2].sem_op = 0; ops[2].sem_flg = 0;
        ops[3].sem_num = 2; ops[3].sem_op = 0; ops[3].sem_flg = 0;
        ops[4].sem_num = 2; ops[4].sem_op = 1; ops[4].sem_flg = 0;
        execute_semop(sem_id, ops, 5, true, 0, -1);
    }

    check_rcv_result(parent, 4);

    {
        struct sembuf ops[2];
        ops[0].sem_num = 1; ops[0].sem_op = -2; ops[0].sem_flg = 0;
        ops[1].sem_num = 2; ops[1].sem_op = 0; ops[1].sem_flg = 0;
        execute_semop(sem_id, ops, 2, true, 0, -1);
    }

    check_rcv_result(parent, 5);

    {
        struct sembuf ops[2];
        ops[0].sem_num = 0; ops[0].sem_op = -1; ops[0].sem_flg = 0;
        ops[1].sem_num = 1; ops[1].sem_op = -1; ops[1].sem_flg = IPC_NOWAIT;
        execute_semop(sem_id, ops, 2, true, 0, -1);
    }

    check_rcv_result(parent, 6);

    {
        struct sembuf ops[2];
        ops[0].sem_num = 1; ops[0].sem_op = 0; ops[0].sem_flg = 0;
        ops[1].sem_num = 0; ops[1].sem_op = 0; ops[1].sem_flg = IPC_NOWAIT;
        execute_semop(sem_id, ops, 2, false, EAGAIN, -1);
    }

    check_rcv_result(parent, 7);

    {
        struct sembuf ops[2];
        ops[0].sem_num = 0; ops[0].sem_op = 0; ops[0].sem_flg = 0;
        ops[1].sem_num = 1; ops[1].sem_op = 1; ops[1].sem_flg = 0;
        execute_semop(sem_id, ops, 2, true, 0, -1);
    }

    check_rcv_result(parent, 8);

    {
        struct sembuf ops[2];
        ops[0].sem_num = 0; ops[0].sem_op = -1; ops[0].sem_flg = 0;
        ops[1].sem_num = 1; ops[1].sem_op = 2; ops[1].sem_flg = 0;
        execute_semop(sem_id, ops, 2, false, ERANGE, -1);
    }

    memset(&act, 0, sizeof(act));
    act.sa_handler = got_signal;
    sigfillset(&act.sa_mask);
    if (sigaction(SIGHUP, &act, NULL) != 0) {
        e(0);
    }

    check_rcv_result(parent, 9);

    {
        struct sembuf ops[3];
        ops[0].sem_num = 0; ops[0].sem_op = 0; ops[0].sem_flg = 0;
        ops[1].sem_num = 0; ops[1].sem_op = 1; ops[1].sem_flg = 0;
        ops[2].sem_num = 1; ops[2].sem_op = 0; ops[2].sem_flg = 0;
        execute_semop(sem_id, ops, 3, false, EINTR, 1);
    }

    TEST_SEM(sem_id, 0, 0, parent->pid, 0, 0);
    TEST_SEM(sem_id, 1, 1, parent->pid, 0, 0);

    check_rcv_result(parent, 10);

    {
        struct sembuf ops[1];
        ops[0].sem_num = 0; ops[0].sem_op = -3; ops[0].sem_flg = 0;
        execute_semop(sem_id, ops, 1, false, EIDRM, -1);
    }

    sem_id = rcv(parent);

    {
        struct sembuf ops[2];
        ops[0].sem_num = 0; ops[0].sem_op = -1; ops[0].sem_flg = 0;
        ops[1].sem_num = 1; ops[1].sem_op = 1; ops[1].sem_flg = 0;
        execute_semop(sem_id, ops, 2, false, ERANGE, -1);
    }

    check_rcv_result(parent, 11);

    {
        struct sembuf ops[2];
        ops[0].sem_num = 1; ops[0].sem_op = 0; ops[0].sem_flg = 0;
        ops[1].sem_num = 0; ops[1].sem_op = -1; ops[1].sem_flg = 0;
        execute_semop(sem_id, ops, 2, true, 0, -1);
    }

    sem_id = rcv(parent);

    {
        struct sembuf ops[2];
        ops[0].sem_num = 0; ops[0].sem_op = -1; ops[0].sem_flg = 0;
        ops[1].sem_num = 1; ops[1].sem_op = 0; ops[1].sem_flg = 0;
        execute_semop(sem_id, ops, 2, true, 0, -1);
    }

    snd(parent, errct);
    check_rcv_result(parent, 12);

    {
        struct sembuf ops[2];
        ops[0].sem_num = 1; ops[0].sem_op = -1; ops[0].sem_flg = 0;
        ops[1].sem_num = 0; ops[1].sem_op = 3; ops[1].sem_flg = 0;
        (void)semop(sem_id, ops, 2);
    }

    e(0);
}

/*
 * Test the basic semop(2) functionality.
 */
static void handle_error_and_exit(int sem_id, struct sembuf *sops_ptr) {
    if (sops_ptr != NULL) {
        free(sops_ptr);
    }
    if (sem_id != -1) {
        semctl(sem_id, 0, IPC_RMID, NULL);
    }
    e(0);
}

static void
test88b(void)
{
	struct seminfo seminfo;
	struct semid_ds semds;
	struct sembuf *sops = NULL;
	size_t sops_buffer_size;
	struct link child;
	time_t now;
	unsigned short val[2];
	int id = -1;

	subtest = 1;

	const int SEM_PERMISSIONS = 0600;
	const int SINGLE_SEM_COUNT = 1;
	const int THREE_SEMS_COUNT = 3;
	const int SEM_STAT_OFFSET = 10;

	if (semctl(0, 0, IPC_INFO, &seminfo) == -1) {
        handle_error_and_exit(id, sops);
    }

	if (seminfo.semopm < THREE_SEMS_COUNT || seminfo.semopm > USHRT_MAX) {
        handle_error_and_exit(id, sops);
    }

	sops_buffer_size = sizeof(sops[0]) * (seminfo.semopm + 1);
	sops = malloc(sops_buffer_size);
	if (sops == NULL) {
        handle_error_and_exit(id, sops);
    }
	memset(sops, 0, sops_buffer_size);

	id = semget(IPC_PRIVATE, SINGLE_SEM_COUNT, IPC_CREAT | SEM_PERMISSIONS);
	if (id == -1) {
        handle_error_and_exit(id, sops);
    }

	if (semop(id, NULL, 0) != 0) {
        handle_error_and_exit(id, sops);
    }

	if (semop(id, NULL, 1) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EFAULT) {
        handle_error_and_exit(id, sops);
    }

	if (semop(id, bad_ptr, 1) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EFAULT) {
        handle_error_and_exit(id, sops);
    }

	memset(page_ptr, 0, page_size);
	struct sembuf *sops_boundary_test = ((struct sembuf *)bad_ptr) - 1;
	sops_boundary_test->sem_op = 1;
	if (semop(id, sops_boundary_test, 2) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EFAULT) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semds.sem_otime != 0) {
        handle_error_and_exit(id, sops);
    }

	time(&now);
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semds.sem_otime < now || semds.sem_otime >= now + SEM_STAT_OFFSET) {
        handle_error_and_exit(id, sops);
    }

	if (semop(id, sops, seminfo.semopm) != 0) {
        handle_error_and_exit(id, sops);
    }

	if (semop(id, sops, seminfo.semopm + 1) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != E2BIG) {
        handle_error_and_exit(id, sops);
    }

	if (semop(id, sops, SIZE_MAX) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != E2BIG) {
        handle_error_and_exit(id, sops);
    }

	sops[1].sem_num = 1;
	if (semop(id, sops, 2) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EFBIG) {
        handle_error_and_exit(id, sops);
    }

	sops[1].sem_num = USHRT_MAX;
	if (semop(id, sops, 2) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EFBIG) {
        handle_error_and_exit(id, sops);
    }
	sops[1].sem_num = 0;

	if (seminfo.semvmx < THREE_SEMS_COUNT || seminfo.semvmx > SHRT_MAX) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_flg = IPC_NOWAIT;

	if (seminfo.semvmx < SHRT_MAX) {
		sops[0].sem_op = seminfo.semvmx + 1;
		if (semop(id, sops, 1) != -1) {
            handle_error_and_exit(id, sops);
        }
		if (errno != ERANGE) {
            handle_error_and_exit(id, sops);
        }
		if (semctl(id, 0, GETVAL) != 0) {
            handle_error_and_exit(id, sops);
        }
	}

	sops[0].sem_op = seminfo.semvmx;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semctl(id, 0, GETVAL) != seminfo.semvmx) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != ERANGE) {
        handle_error_and_exit(id, sops);
    }
	if (semctl(id, 0, GETVAL) != seminfo.semvmx) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = seminfo.semvmx;
	if (semop(id, sops, 1) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != ERANGE) {
        handle_error_and_exit(id, sops);
    }
	if (semctl(id, 0, GETVAL) != seminfo.semvmx) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = SHRT_MAX;
	if (semop(id, sops, 1) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != ERANGE) {
        handle_error_and_exit(id, sops);
    }
	if (semctl(id, 0, GETVAL) != seminfo.semvmx) {
        handle_error_and_exit(id, sops);
    }

	if (seminfo.semvmx < -(int)SHRT_MIN) {
		sops[0].sem_op = -seminfo.semvmx - 1;
		if (semop(id, sops, 1) != -1) {
            handle_error_and_exit(id, sops);
        }
		if (errno != EAGAIN) {
            handle_error_and_exit(id, sops);
        }
		if (semctl(id, 0, GETVAL) != seminfo.semvmx) {
            handle_error_and_exit(id, sops);
        }
	}

	sops[0].sem_op = -seminfo.semvmx;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semctl(id, 0, GETVAL) != 0) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = 2;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semctl(id, 0, GETVAL) != 2) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EAGAIN) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = -3;
	if (semop(id, sops, 1) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EAGAIN) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semctl(id, 0, GETVAL) != 3) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semctl(id, 0, GETVAL) != 2) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EAGAIN) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = -2;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semctl(id, 0, GETVAL) != 0) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_op = 0;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	sops_boundary_test = ((struct sembuf *)bad_ptr) - 1;
	sops_boundary_test->sem_op = 0;
	sops_boundary_test--;
	if (semop(id, sops_boundary_test, 2) != 0) {
        handle_error_and_exit(id, sops);
    }

	if (semctl(id, 0, IPC_RMID) != 0) {
        handle_error_and_exit(id, sops);
    }
	id = -1;

	if (semop(-1, NULL, 0) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EINVAL) {
        handle_error_and_exit(id, sops);
    }

	if (semop(INT_MIN, NULL, 0) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EINVAL) {
        handle_error_and_exit(id, sops);
    }

	memset(&semds, 0, sizeof(semds));
	int invalid_id_from_ipc = IXSEQ_TO_IPCID(seminfo.semmni, semds.sem_perm);
	if (semop(invalid_id_from_ipc, NULL, 0) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EINVAL) {
        handle_error_and_exit(id, sops);
    }

	test_perm(test88b_perm, 0);

	id = semget(IPC_PRIVATE, THREE_SEMS_COUNT, SEM_PERMISSIONS);
	if (id == -1) {
        handle_error_and_exit(id, sops);
    }

	memset(sops, 0, sizeof(sops[0]));
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 1, getpid(), 0, 0);

	spawn(&child, test88b_child, DROP_NONE);

	snd(&child, id);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, getpid(), 0, 1);

	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);

	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 1, getpid(), 0, 0);

	snd(&child, 1);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, getpid(), 1, 0);

	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 2, getpid(), 1, 0);

	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);

	memset(sops, 0, sizeof(sops[0]) * 2);
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	snd(&child, 2);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, 0, 1, 0);
	TEST_SEM(id, 2, 0, 0, 0, 0);

	sops[0].sem_num = 1;
	sops[0].sem_op = 1;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

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
	if (semop(id, sops, 2) != 0) {
        handle_error_and_exit(id, sops);
    }

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
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, 2, getpid(), 0, 0);
	TEST_SEM(id, 2, 1, child.pid, 0, 1);

	sops[0].sem_num = 2;
	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, 0, child.pid, 0, 0);
	TEST_SEM(id, 2, 0, child.pid, 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 1;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != 0) {
        handle_error_and_exit(id, sops);
    }

	snd(&child, 5);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, getpid(), 1, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) {
        handle_error_and_exit(id, sops);
    }

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, 0, child.pid, 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) {
        handle_error_and_exit(id, sops);
    }

	snd(&child, 6);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	TEST_SEM(id, 1, 1, getpid(), 0, 1);

	sops[0].sem_num = 1;
	sops[0].sem_op = -1;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 4;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != EFBIG) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_num = 1;
	sops[0].sem_op = seminfo.semvmx;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	snd(&child, 7);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 1, getpid(), 0, 1);
	TEST_SEM(id, 1, seminfo.semvmx, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = -1;
	if (semop(id, sops, 2) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, seminfo.semvmx, child.pid, 0, 0);

	sops[0].sem_num = 1;
	sops[0].sem_op = -2;
	if (semop(id, sops, 1) != 0) {
        handle_error_and_exit(id, sops);
    }

	snd(&child, 8);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, child.pid, 1, 0);
	TEST_SEM(id, 1, seminfo.semvmx - 2, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = 1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 1, getpid(), 0, 0);
	TEST_SEM(id, 1, seminfo.semvmx - 1, getpid(), 0, 0);

	sops[0].sem_num = 0;
	sops[0].sem_op = seminfo.semvmx - 1;
	sops[1].sem_num = 0;
	sops[1].sem_op = seminfo.semvmx - 1;
	sops[2].sem_num = 0;
	sops[2].sem_op = 2;
	if (semop(id, sops, 3) != -1) {
        handle_error_and_exit(id, sops);
    }
	if (errno != ERANGE) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 1, getpid(), 0, 0);

	if (semctl(id, 1, SETVAL, 0) != 0) {
        handle_error_and_exit(id, sops);
    }
	sops[0].sem_num = 0;
	sops[0].sem_op = -1;
	sops[1].sem_num = 1;
	sops[1].sem_op = 1;
	if (semop(id, sops, 2) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 1, getpid(), 0, 0);

	snd(&child, 9);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 1, getpid(), 0, 1);

	kill(child.pid, SIGHUP);

	snd(&child, 10);

	usleep(WAIT_USECS);

	if (semctl(id, 0, IPC_RMID) != 0) {
        handle_error_and_exit(id, sops);
    }
	id = -1;

	id = semget(IPC_PRIVATE, 2, SEM_PERMISSIONS);
	if (id == -1) {
        handle_error_and_exit(id, sops);
    }

	snd(&child, id);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semds.sem_otime != 0) {
        handle_error_and_exit(id, sops);
    }

	if (semctl(id, 1, SETVAL, seminfo.semvmx) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, seminfo.semvmx, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semds.sem_otime != 0) {
        handle_error_and_exit(id, sops);
    }

	if (semctl(id, 0, SETVAL, 1) != 0) {
        handle_error_and_exit(id, sops);
    }
	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, seminfo.semvmx, 0, 0, 0);

	if (semctl(id, 0, SETVAL, 0) != 0) {
        handle_error_and_exit(id, sops);
    }

	snd(&child, 11);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, seminfo.semvmx, 0, 0, 1);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semds.sem_otime != 0) {
        handle_error_and_exit(id, sops);
    }

	if (semctl(id, 1, SETVAL, 0) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semds.sem_otime != 0) {
        handle_error_and_exit(id, sops);
    }

	time(&now);
	if (semctl(id, 0, SETVAL, 2) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 1, child.pid, 0, 0);
	TEST_SEM(id, 1, 0, child.pid, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semds.sem_otime < now || semds.sem_otime >= now + SEM_STAT_OFFSET) {
        handle_error_and_exit(id, sops);
    }

	if (semctl(id, 0, IPC_RMID) != 0) {
        handle_error_and_exit(id, sops);
    }
	id = -1;

	id = semget(IPC_PRIVATE, 2, SEM_PERMISSIONS);
	if (id == -1) {
        handle_error_and_exit(id, sops);
    }

	snd(&child, id);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);

	val[0] = 1;
	val[1] = 1;
	if (semctl(id, 0, SETALL, val) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, 1, 0, 0, 1);

	val[0] = 0;
	val[1] = 1;
	if (semctl(id, 0, SETALL, val) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 1, 0, 0, 0);

	val[0] = 1;
	val[1] = 1;
	if (semctl(id, 0, SETALL, val) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, 1, 0, 0, 1);

	val[0] = 0;
	val[1] = 0;
	if (semctl(id, 0, SETALL, val) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 0, 0, 1, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semds.sem_otime != 0) {
        handle_error_and_exit(id, sops);
    }

	time(&now);
	val[0] = 1;
	val[1] = 0;
	if (semctl(id, 0, SETALL, val) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 0, child.pid, 0, 0);
	TEST_SEM(id, 1, 0, child.pid, 0, 0);
	if (semctl(id, 0, IPC_STAT, &semds) != 0) {
        handle_error_and_exit(id, sops);
    }
	if (semds.sem_otime < now || semds.sem_otime >= now + SEM_STAT_OFFSET) {
        handle_error_and_exit(id, sops);
    }

	sops[0].sem_num = 0;
	sops[0].sem_op = 0;
	sops[1].sem_num = 1;
	sops[1].sem_op = 0;
	if (semop(id, sops, 2) != 0) {
        handle_error_and_exit(id, sops);
    }

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);

	if (rcv(&child) != 0) {
        handle_error_and_exit(id, sops);
    }

	snd(&child, 12);

	usleep(WAIT_USECS);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 1, 0);

	terminate(&child);

	TEST_SEM(id, 0, 0, getpid(), 0, 0);
	TEST_SEM(id, 1, 0, getpid(), 0, 0);

	if (semctl(id, 0, IPC_RMID) != 0) {
        handle_error_and_exit(id, sops);
    }
	id = -1;

	if (sops != NULL) {
		free(sops);
		sops = NULL;
	}
}

/*
 * Test semctl(2) permission checks, part 1: regular commands.
 */
#define PERM_WRITE_BIT 2
#define PERM_READ_BIT 4

static void perform_semctl_check(int sem_id, int sem_num, int cmd, void *arg, int permission_bit, int tbit, int is_denied_target) {
    int r = semctl(sem_id, sem_num, cmd, arg);

    if (is_denied_target) {
        if (r != -1) {
            e(0);
        }
        if (errno != EACCES) {
            e(0);
        }
    } else {
        if (r == -1 && errno != EACCES) {
            e(0);
        }
        if (((permission_bit & tbit) == permission_bit) != (r != -1)) {
            e(0);
        }
    }
}

static void
test88c_perm1(struct link * parent)
{
	static const int cmds[] = { GETVAL, GETPID, GETNCNT, GETZCNT };
	struct semid_ds semds;
	struct seminfo seminfo;
	unsigned short val[3];
	int tbit;
	int id[3];

#ifndef IPCID_TO_IX
#define IPCID_TO_IX(id_val)     ((id_val) & 0xffff)
#endif

	while ((tbit = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		for (int i = 0; i < __arraycount(cmds); i++) {
			for (int j = 0; j < 3; j++) {
				perform_semctl_check(id[j], 0, cmds[i], NULL, PERM_READ_BIT, tbit, j == 2);
			}
		}

		for (int j = 0; j < 3; j++) {
			perform_semctl_check(id[j], 0, SETVAL, NULL, PERM_WRITE_BIT, tbit, j == 2);
		}

		memset(val, 0, sizeof(val));

		for (int i = 0; i < 3; i++) {
			int cmd_type;
			void *arg_ptr;
			int required_perm_bit;

			switch (i) {
			case 0:
				cmd_type = GETALL;
				arg_ptr = val;
				required_perm_bit = PERM_READ_BIT;
				break;
			case 1:
				cmd_type = SETALL;
				arg_ptr = val;
				required_perm_bit = PERM_WRITE_BIT;
				break;
			case 2:
				cmd_type = IPC_STAT;
				arg_ptr = &semds;
				required_perm_bit = PERM_READ_BIT;
				break;
			default:
				abort();
			}

			for (int j = 0; j < 3; j++) {
				perform_semctl_check(id[j], 0, cmd_type, arg_ptr, required_perm_bit, tbit, j == 2);
			}
		}

		for (int j = 0; j < 3; j++) {
			perform_semctl_check(IPCID_TO_IX(id[j]), 0, SEM_STAT, &semds, PERM_READ_BIT, tbit, j == 2);
		}

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
	int i;

	while ((shift = rcv(parent)) != -1) {
		for (i = 0; i < 3; ++i) {
			id[i] = rcv(parent);
		}

		memset(&semds, 0, sizeof(semds));

		for (i = 0; i < 3; ++i) {
			r = semctl(id[i], 0, IPC_SET, &semds);

			/*
			 * If semctl failed for any reason other than EPERM, it's an unexpected error.
			 * EPERM is expected when shift != 6.
			 */
			if (r == -1 && errno != EPERM) {
				e(0);
			}

			/*
			 * Check if the actual outcome matches the expected outcome based on 'shift'.
			 * If shift == 6, success (r != -1) is expected.
			 * If shift != 6, failure (r == -1) is expected.
			 * Call e(0) if expected_success_but_actual_failure OR expected_failure_but_actual_success.
			 */
			if ((shift == 6 && r == -1) || (shift != 6 && r != -1)) {
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
handle_semctl_rmid(int sem_id, int shift_value)
{
	int result = semctl(sem_id, 0, IPC_RMID);

	if (result == -1 && errno != EPERM) {
		e(0);
	}

	if ((shift_value == 6) != (result != -1)) {
		e(0);
	}
}

static void
test88c_perm3(struct link * parent)
{
	int shift;
	int id[3];

	while ((shift = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		for (int i = 0; i < 3; ++i) {
			handle_semctl_rmid(id[i], shift);
		}

		snd(parent, 0);
	}
}

/*
 * Test the basic semctl(2) functionality.
 */
static int
get_sem_val_errno(int semid, int semnum, int cmd)
{
    int ret = semctl(semid, semnum, cmd);
    if (ret == -1 && errno == EINVAL) {
        return 0; // Handled as expected for invalid inputs
    }
    return ret;
}

static void
handle_error(const char *msg, int line)
{
    e(line); // Original error handler
}

#define E_CHECK(cond) do { if (!(cond)) handle_error(__STRING(cond), __LINE__); } while (0)
#define E_CHECK_NEG1(call) do { if ((call) == -1) handle_error(__STRING(call), __LINE__); } while (0)
#define E_CHECK_ZERO(call) do { if ((call) != 0) handle_error(__STRING(call), __LINE__); } while (0)
#define E_CHECK_EINVAL(call) do { if ((call) != -1 || errno != EINVAL) handle_error(__STRING(call) " with errno != EINVAL", __LINE__); } while (0)
#define E_CHECK_EFAULT(call) do { if ((call) != -1 || errno != EFAULT) handle_error(__STRING(call) " with errno != EFAULT", __LINE__); } while (0)
#define E_CHECK_ERANGE(call) do { if ((call) != -1 || errno != ERANGE) handle_error(__STRING(call) " with errno != ERANGE", __LINE__); } while (0)

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

	E_CHECK_NEG1(semctl(0, 0, IPC_INFO, &seminfo));

	test_perm(test88c_perm1, 0 /*owner_test*/);
	test_perm(test88c_perm2, 1 /*owner_test*/);
	test_perm(test88c_perm3, 1 /*owner_test*/);

	E_CHECK_NEG1(badid1 = semget(IPC_PRIVATE, 1, 0600));
	E_CHECK_ZERO(semctl(badid1, 0, IPC_RMID));

	memset(&semds, 0, sizeof(semds));
	badid2 = IXSEQ_TO_IPCID(seminfo.semmni, semds.sem_perm);

	E_CHECK_NEG1(id = semget(IPC_PRIVATE, 3, IPC_CREAT | 0600));

	E_CHECK_ZERO(semctl(id, 0, IPC_STAT, &semds));
	E_CHECK(semds.sem_otime == 0);
	E_CHECK(semds.sem_ctime != 0);

	time(&now);
	while (time(NULL) == semds.sem_ctime)
		usleep(250000);

	for (i = 0; i < __arraycount(cmds); i++) {
		for (j = 0; j < 3; j++)
			E_CHECK_ZERO(semctl(id, j, cmds[i]));

		E_CHECK_EINVAL(semctl(badid1, 0, cmds[i]));
		E_CHECK_EINVAL(semctl(badid2, 0, cmds[i]));
		E_CHECK_EINVAL(semctl(-1, 0, cmds[i]));
		E_CHECK_EINVAL(semctl(INT_MIN, 0, cmds[i]));
		E_CHECK_EINVAL(semctl(id, -1, cmds[i]));
		E_CHECK_EINVAL(semctl(id, 3, cmds[i]));

		E_CHECK_ZERO(semctl(id, 0, IPC_STAT, &semds));
		E_CHECK(semds.sem_otime == 0);
		E_CHECK(semds.sem_ctime < now);
	}

	for (j = 0; j < 5; j++) {
		for (i = 0; i < __arraycount(val); i++)
			val[i] = USHRT_MAX;

		E_CHECK_ZERO(semctl(id, (int)j - 1, GETALL, val));
		for (i = 0; i < 3; i++)
			E_CHECK(val[i] == 0);
		E_CHECK(val[i] == USHRT_MAX);
	}

	for (i = 0; i < __arraycount(val); i++)
		val[i] = USHRT_MAX;

	E_CHECK_EINVAL(semctl(badid1, 0, GETALL, val));
	E_CHECK_EINVAL(semctl(badid2, 0, GETALL, val));
	E_CHECK_EINVAL(semctl(-1, 0, GETALL, val));
	E_CHECK_EINVAL(semctl(INT_MIN, 0, GETALL, val));

	for (i = 0; i < __arraycount(val); i++)
		E_CHECK(val[i] == USHRT_MAX);

	E_CHECK_EFAULT(semctl(id, 0, GETALL, NULL));
	E_CHECK_EFAULT(semctl(id, 0, GETALL, bad_ptr));
	E_CHECK_EFAULT(semctl(id, 0, GETALL, ((unsigned short *)bad_ptr) - 2));
	E_CHECK_ZERO(semctl(id, 0, GETALL, ((unsigned short *)bad_ptr) - 3));

	E_CHECK_ZERO(semctl(id, 0, IPC_STAT, &semds));
	E_CHECK(semds.sem_otime == 0);
	E_CHECK(semds.sem_ctime < now);

	memset(statbuf, 0x5a, sizeof(statbuf));

	E_CHECK_EINVAL(semctl(badid1, 0, IPC_STAT, statbuf));
	E_CHECK_EINVAL(semctl(badid2, 0, IPC_STAT, statbuf));
	E_CHECK_EINVAL(semctl(-1, 0, IPC_STAT, statbuf));
	E_CHECK_EINVAL(semctl(INT_MIN, 0, IPC_STAT, statbuf));

	for (i = 0; i < sizeof(statbuf); i++)
		E_CHECK(statbuf[i] == 0x5a);

	E_CHECK_ZERO(semctl(id, 0, IPC_STAT, statbuf));
	E_CHECK(statbuf[sizeof(statbuf) - 1] == 0x5a);

	E_CHECK_EFAULT(semctl(id, 0, IPC_STAT, NULL));
	E_CHECK_EFAULT(semctl(id, 0, IPC_STAT, bad_ptr));
	E_CHECK_ZERO(semctl(id, 0, IPC_STAT, ((struct semid_ds *)bad_ptr) - 1));
	E_CHECK_ZERO(semctl(id, -1, IPC_STAT, &semds));
	E_CHECK(semds.sem_otime == 0);
	E_CHECK(semds.sem_ctime < now);

	E_CHECK_NEG1(id2 = semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0642));

	memset(statbuf, 0x5a, sizeof(statbuf));

	E_CHECK_EINVAL(semctl(-1, 0, SEM_STAT, statbuf));
	E_CHECK_EINVAL(semctl(seminfo.semmni, 0, SEM_STAT, statbuf));

	for (i = 0; i < sizeof(statbuf); i++)
		E_CHECK(statbuf[i] == 0x5a);

	memset(seen, 0, sizeof(seen));

	for (i = 0; i < seminfo.semmni; i++) {
		errno = 0;
		if ((r = semctl(i, i / 2 - 1, SEM_STAT, statbuf)) == -1) {
			E_CHECK(errno == EINVAL);
			continue;
		}
		E_CHECK(r >= 0);
		memcpy(&semds, statbuf, sizeof(semds));
		E_CHECK(semds.sem_perm.mode & SEM_ALLOC);
		E_CHECK(semds.sem_ctime != 0);
		E_CHECK(IXSEQ_TO_IPCID(i, semds.sem_perm) == r);
		if (r == id) {
			seen[0]++;
			E_CHECK(semds.sem_perm.mode == (SEM_ALLOC | 0600));
			E_CHECK(semds.sem_perm.uid == geteuid());
			E_CHECK(semds.sem_perm.gid == getegid());
			E_CHECK(semds.sem_perm.cuid == semds.sem_perm.uid);
			E_CHECK(semds.sem_perm.cgid == semds.sem_perm.gid);
			E_CHECK(semds.sem_perm._key == IPC_PRIVATE);
			E_CHECK(semds.sem_nsems == 3);
			E_CHECK(semds.sem_otime == 0);

			E_CHECK_EFAULT(semctl(i, 0, SEM_STAT, NULL));
			E_CHECK_EFAULT(semctl(i, 0, SEM_STAT, bad_ptr));
		} else if (r == id2) {
			seen[1]++;
			E_CHECK(semds.sem_perm.mode == (SEM_ALLOC | 0642));
			E_CHECK(semds.sem_perm.uid == geteuid());
			E_CHECK(semds.sem_perm.gid == getegid());
			E_CHECK(semds.sem_perm.cuid == semds.sem_perm.uid);
			E_CHECK(semds.sem_perm.cgid == semds.sem_perm.gid);
			E_CHECK(semds.sem_perm._key == KEY_A);
			E_CHECK(semds.sem_nsems == seminfo.semmsl);
		}
	}

	E_CHECK(seen[0] == 1);
	E_CHECK(seen[1] == 1);
	E_CHECK(statbuf[sizeof(statbuf) - 1] == 0x5a);

	E_CHECK_ZERO(semctl(id, 5, IPC_STAT, &semds));
	E_CHECK(semds.sem_otime == 0);
	E_CHECK(semds.sem_ctime < now);

	E_CHECK_EINVAL(semctl(badid1, 0, SETVAL, 1));
	E_CHECK_EINVAL(semctl(badid2, 0, SETVAL, 1));
	E_CHECK_EINVAL(semctl(-1, 0, SETVAL, 1));
	E_CHECK_EINVAL(semctl(INT_MIN, 0, SETVAL, 1));
	E_CHECK_EINVAL(semctl(id, -1, SETVAL, 1));
	E_CHECK_EINVAL(semctl(id, 3, SETVAL, 1));
	E_CHECK_ERANGE(semctl(id, 0, SETVAL, -1));
	E_CHECK_ERANGE(semctl(id, 0, SETVAL, seminfo.semvmx + 1));

	TEST_SEM(id, 0, 0, 0, 0, 0);

	E_CHECK_ZERO(semctl(id, 0, IPC_STAT, &semds));
	E_CHECK(semds.sem_otime == 0);
	E_CHECK(semds.sem_ctime < now);

	E_CHECK_ZERO(semctl(id, 1, SETVAL, 0));

	E_CHECK_ZERO(semctl(id, 0, IPC_STAT, &semds));
	E_CHECK(semds.sem_otime == 0);
	E_CHECK(semds.sem_ctime >= now && semds.sem_ctime < now + 10);

	TEST_SEM(id, 1, 0, 0, 0, 0);

	E_CHECK_ZERO(semctl(id, 2, SETVAL, seminfo.semvmx));
	TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

	E_CHECK_ZERO(semctl(id, 0, SETVAL, 1));
	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

	E_CHECK_ZERO(semctl(id, 0, GETALL, val));
	E_CHECK(val[0] == 1);
	E_CHECK(val[1] == 0);
	E_CHECK(val[2] == seminfo.semvmx);

	E_CHECK_ZERO(semctl(id, 0, IPC_STAT, &semds));
	time(&now);
	while (time(NULL) == semds.sem_ctime)
		usleep(250000);

	E_CHECK_EINVAL(semctl(badid1, 0, SETALL, 1));
	E_CHECK_EINVAL(semctl(badid2, 0, SETALL, 1));
	E_CHECK_EINVAL(semctl(-1, 0, SETALL, 1));
	E_CHECK_EINVAL(semctl(INT_MIN, 0, SETALL, 1));

	val[0] = seminfo.semvmx + 1;
	val[1] = 0;
	val[2] = 0;
	E_CHECK_ERANGE(semctl(id, 0, SETALL, val));

	val[0] = 0;
	val[1] = 1;
	val[2] = seminfo.semvmx + 1;
	E_CHECK_ERANGE(semctl(id, 0, SETALL, val));

	E_CHECK_EFAULT(semctl(id, 0, SETALL, NULL));
	E_CHECK_EFAULT(semctl(id, 0, SETALL, bad_ptr));
	E_CHECK_EFAULT(semctl(id, 0, SETALL, ((unsigned short *)bad_ptr) - 2));

	TEST_SEM(id, 0, 1, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

	E_CHECK_ZERO(semctl(id, 0, IPC_STAT, &semds));
	E_CHECK(semds.sem_otime == 0);
	E_CHECK(semds.sem_ctime < now);

	val[0] = seminfo.semvmx;
	val[1] = 0;
	val[2] = 0;
	E_CHECK_ZERO(semctl(id, 0, SETALL, val));

	E_CHECK_ZERO(semctl(id, 0, IPC_STAT, &semds));
	E_CHECK(semds.sem_otime == 0);
	E_CHECK(semds.sem_ctime >= now && semds.sem_ctime < now + 10);

	TEST_SEM(id, 0, seminfo.semvmx, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	TEST_SEM(id, 2, 0, 0, 0, 0);

	val[0] = 0;
	val[1] = 1;
	val[2] = seminfo.semvmx;
	E_CHECK_ZERO(semctl(id, INT_MAX, SETALL, val));

	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, 1, 0, 0, 0);
	TEST_SEM(id, 2, seminfo.semvmx, 0, 0, 0);

	memset(page_ptr, 0, page_size);
	E_CHECK_ZERO(semctl(id, 0, SETALL, ((unsigned short *)bad_ptr) - 3));

	TEST_SEM(id, 0, 0, 0, 0, 0);
	TEST_SEM(id, 1, 0, 0, 0, 0);
	TEST_SEM(id, 2, 0, 0, 0, 0);

	time(&now);
	while (time(NULL) == semds.sem_ctime)
		usleep(250000);

	E_CHECK_EINVAL(semctl(badid1, 0, IPC_SET, &semds));
	E_CHECK_EINVAL(semctl(badid2, 0, IPC_SET, &semds));
	E_CHECK_EINVAL(semctl(-1, 0, IPC_SET, &semds));
	E_CHECK_EINVAL(semctl(INT_MIN, 0, IPC_SET, &semds));
	E_CHECK_EFAULT(semctl(id, 0, IPC_SET, NULL));
	E_CHECK_EFAULT(semctl(id, 0, IPC_SET, bad_ptr));

	E_CHECK_ZERO(semctl(id, 0, IPC_STAT, &osemds));
	E_CHECK(osemds.sem_otime == 0);
	E_CHECK(osemds.sem_ctime < now);

	memset(&semds, 0x5b, sizeof(semds));
	semds.sem_perm.mode = 0712;
	semds.sem_perm.uid = UID_MAX;
	semds.sem_perm.gid = GID_MAX - 1;
	E_CHECK_ZERO(semctl(id, 0, IPC_SET, &semds));

	E_CHECK_ZERO(semctl(id, 0, IPC_STAT, &semds));
	E_CHECK(semds.sem_perm.mode == (SEM_ALLOC | 0712));
	E_CHECK(semds.sem_perm.uid == UID_MAX);
	E_CHECK(semds.sem_perm.gid == GID_MAX - 1);
	E_CHECK(semds.sem_perm.cuid == osemds.sem_perm.cuid);
	E_CHECK(semds.sem_perm.cgid == osemds.sem_perm.cgid);
	E_CHECK(semds.sem_perm._seq == osemds.sem_perm._seq);
	E_CHECK(semds.sem_perm._key == osemds.sem_perm._key);
	E_CHECK(semds.sem_nsems == osemds.sem_nsems);
	E_CHECK(semds.sem_otime == osemds.sem_otime);
	E_CHECK(semds.sem_ctime >= now && semds.sem_ctime < now + 10);

	semds.sem_perm.uid = osemds.sem_perm.uid;
	semds.sem_perm.gid = osemds.sem_perm.gid;
	for (i = 0; i < 0777; i++) {
		semds.sem_perm.mode = i;
		E_CHECK_ZERO(semctl(id, i / 2 - 1, IPC_SET, &semds));

		E_CHECK_ZERO(semctl(id, i / 2 - 2, IPC_STAT, &semds));
		E_CHECK(semds.sem_perm.mode == (SEM_ALLOC | i));

		semds.sem_perm.mode = ~0777 | i;
		E_CHECK_ZERO(semctl(id, i / 2 - 3, IPC_SET, &semds));

		E_CHECK_ZERO(semctl(id, i / 2 - 4, IPC_STAT, &semds));
		E_CHECK(semds.sem_perm.mode == (SEM_ALLOC | i));
	}
	E_CHECK(semds.sem_perm.uid == osemds.sem_perm.uid);
	E_CHECK(semds.sem_perm.gid == osemds.sem_perm.gid);

	E_CHECK_ZERO(semctl(id, 0, IPC_SET, ((struct semid_ds *)bad_ptr) - 1));

	E_CHECK_EINVAL(semctl(badid1, 0, IPC_RMID));
	E_CHECK_EINVAL(semctl(badid2, 0, IPC_RMID));
	E_CHECK_EINVAL(semctl(-1, 0, IPC_RMID));
	E_CHECK_EINVAL(semctl(INT_MIN, 0, IPC_RMID));

	E_CHECK_ZERO(semctl(id, 0, IPC_RMID));
	E_CHECK_EINVAL(semctl(id, 0, IPC_RMID));
	E_CHECK_EINVAL(semctl(id, 0, IPC_STAT, &semds));

	E_CHECK_ZERO(semctl(id2, 1, IPC_RMID));
	E_CHECK_EINVAL(semctl(id2, 1, IPC_RMID));

	E_CHECK_NEG1(id = semget(IPC_PRIVATE, 3, 0600));
	E_CHECK_NEG1(id2 = semget(IPC_PRIVATE, 1, 0600));

	for (i = 0; i <= 1; i++) {
		cmd = (i == 0) ? IPC_INFO : SEM_INFO;

		memset(&seminfo, 0xff, sizeof(seminfo));

		E_CHECK_NEG1(r = semctl(0, 0, cmd, &seminfo));

		E_CHECK(r >= 1 && r < seminfo.semmni);

		E_CHECK(seminfo.semmap >= 0);
		E_CHECK(seminfo.semmni >= 3 && seminfo.semmni <= USHRT_MAX);
		E_CHECK(seminfo.semmns >= 3 && seminfo.semmns <= USHRT_MAX);
		E_CHECK(seminfo.semmnu >= 0);
		E_CHECK(seminfo.semmsl >= 3 && seminfo.semmsl <= USHRT_MAX);
		E_CHECK(seminfo.semopm >= 3 && seminfo.semopm <= USHRT_MAX);
		E_CHECK(seminfo.semume >= 0);
		if (cmd == SEM_INFO) {
			E_CHECK(seminfo.semusz >= 2);
		} else {
			E_CHECK(seminfo.semusz >= 0);
		}
		E_CHECK(seminfo.semvmx >= 3 && seminfo.semvmx <= SHRT_MAX);
		if (cmd == SEM_INFO) {
			E_CHECK(seminfo.semaem >= 4);
		} else {
			E_CHECK(seminfo.semaem >= 0);
		}

		E_CHECK_NEG1(get_sem_val_errno(INT_MAX, -1, cmd)); // semctl does not return -1 on EINVAL for these
		E_CHECK_NEG1(get_sem_val_errno(-1, INT_MAX, cmd)); // semctl does not return -1 on EINVAL for these

		E_CHECK_EFAULT(semctl(0, 0, cmd, NULL));
		E_CHECK_EFAULT(semctl(0, 0, cmd, bad_ptr));
		E_CHECK_NEG1(semctl(0, 0, cmd, ((struct seminfo *)bad_ptr) - 1)); // This expects -1 (EFAULT) but the original expects non-negative or e(0)
	}

	E_CHECK_ZERO(semctl(id2, 0, IPC_RMID));

	E_CHECK_EINVAL(semctl(id, 0, INT_MIN));
	E_CHECK_EINVAL(semctl(id, 0, INT_MAX));
	E_CHECK_ZERO(semctl(id, 0, IPC_RMID));
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
	int sem_op_status;

	subtest = 3;

	id = semget(IPC_PRIVATE, 1, 0600);
	if (id == -1) {
		e(0);
	}

	if (!(SHRT_MAX & SEM_UNDO)) {
		e(0);
	}

	sop.sem_num = 0;
	sop.sem_op = 1;
	sop.sem_flg = SHRT_MAX;

	sem_op_status = semop(id, &sop, 1);

	if (sem_op_status == -1) {
		if (errno != EINVAL) {
			e(0);
		}
	} else {
		e(0);
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
	int child_type, sem_id, sem_num_target;

	child_type = rcv(parent);
	sem_id = rcv(parent);
	sem_num_target = rcv(parent);

	memset(sops, 0, sizeof(sops));

	// The third semaphore operation is common to all cases.
	sops[2].sem_num = 0;
	sops[2].sem_op = 1;

	switch (child_type) {
		case 1:
			sops[0].sem_num = sem_num_target;
			sops[0].sem_op = 1; // Increment by 1
			sops[1].sem_num = sem_num_target;
			sops[1].sem_op = 0; // Wait for value to be 0
			break;

		case 2: {
			struct seminfo seminfo;
			short sem_val_max_undo;

			if (semctl(0, 0, IPC_INFO, &seminfo) == -1) {
				e(0);
			}
			sem_val_max_undo = seminfo.semvmx;

			sops[0].sem_num = sem_num_target;
			sops[0].sem_op = -sem_val_max_undo; // Decrement by max_undo
			sops[1].sem_num = sem_num_target;
			sops[1].sem_op = -sem_val_max_undo; // Decrement by max_undo again
			break;
		}

		default:
			e(0); // Invalid child_type
			return; // e(0) might not exit, so return defensively
	}

	snd(parent, 0); // Acknowledge parameter receipt

	// These operations are expected to fail. An unexpected success is an error.
	if (semop(sem_id, sops, 3) != -1) {
		e(0); // semop unexpectedly succeeded
	}

	// The expected failure reason is EIDRM (semaphore set removed).
	// Any other failure is unexpected.
	if (errno != EIDRM) {
		e(0); // semop failed for an unexpected reason
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
	int match, id;
	int expected_semop_return_value;
	int expected_errno_on_failure;

	match = rcv(parent);
	id = rcv(parent);

	memset(sops, 0, sizeof(sops));
	sops[0].sem_num = 2;
	sops[0].sem_op = -1;

	nsops = 2;
	expected_semop_return_value = 0;
	expected_errno_on_failure = 0;

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
		expected_semop_return_value = -1;
		expected_errno_on_failure = EIDRM;
		break;
	case MATCH_KILL:
		sops[1].sem_num = 0;
		sops[1].sem_op = 1;
		expected_semop_return_value = INT_MIN;
		break;
	default:
		e(0);
	}

	snd(parent, 0);

	int semop_result = semop(id, sops, nsops);

	if (semop_result != expected_semop_return_value) {
		e(0);
	}

	if (expected_semop_return_value == -1 && errno != expected_errno_on_failure) {
		e(0);
	}
}

/*
 * Second child procedure.
 */
#include <string.h>
#include <errno.h>
#include <sys/sem.h>

static void
test88e_child2(struct link * parent)
{
    struct sembuf sops[2];
    size_t nsops;
    int expect;

    int match = rcv(parent);
    int id = rcv(parent);

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
    }

    snd(parent, 0);

    int sem_return_code = semop(id, sops, nsops);

    if (expect == -1) {
        if (sem_return_code != -1 || errno != EIDRM) {
            e(0);
        }
    } else {
        if (sem_return_code != expect) {
            e(0);
        }
    }
}

/*
 * Third child procedure.
 */
static void
test88e_child3(struct link * parent)
{
	int match;
	int id;
	struct sembuf sops;
	const size_t nsops = 1;

	match = rcv(parent);
	id = rcv(parent);

	if (match == MATCH_ALL) {
		sops.sem_num = 3;
		sops.sem_op = -2;
		sops.sem_flg = 0;
	} else {
		e(0);
	}

	snd(parent, 0);

	if (semop(id, &sops, nsops) != 0) {
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
    int id = -1;
    int inc;
    int aux_zcnt;
    int aux_ncnt;
    bool error_occurred = false;

    bool aux1_spawned = false;
    bool aux2_spawned = false;
    bool child1_spawned = false;
    bool child2_spawned = false;
    bool child3_spawned = false;

    bool aux1_collected = false;
    bool aux2_collected = false;
    bool child1_collected = false;
    bool child2_collected = false;
    bool child3_collected = false;

    if ((id = semget(IPC_PRIVATE, __arraycount(val), 0666)) == -1) {
        e(0);
    }

    aux_zcnt = 0;
    aux_ncnt = 0;

    if (aux & 1) {
        spawn(&aux1, test88e_childaux, DROP_ALL);
        aux1_spawned = true;

        snd(&aux1, 1);
        snd(&aux1, id);
        snd(&aux1, (aux & 4) ? 2 : 1);

        if (rcv(&aux1) != 0) {
            error_occurred = true;
            goto cleanup;
        }

        if (aux & 4) {
            aux_zcnt++;
        }
    }

    spawn(&child1, test88e_child1, DROP_ALL);
    child1_spawned = true;

    snd(&child1, match);
    snd(&child1, id);

    if (rcv(&child1) != 0) {
        error_occurred = true;
        goto cleanup;
    }

    switch (match) {
    case MATCH_FIRST:
    case MATCH_SECOND:
    case MATCH_KILL:
        usleep(WAIT_USECS);
        break;
    default:
        break;
    }

    spawn(&child2, test88e_child2, DROP_NONE);
    child2_spawned = true;

    snd(&child2, match);
    snd(&child2, id);

    if (rcv(&child2) != 0) {
        error_occurred = true;
        goto cleanup;
    }

    if (match == MATCH_ALL) {
        spawn(&child3, test88e_child3, DROP_USER);
        child3_spawned = true;

        snd(&child3, match);
        snd(&child3, id);

        if (rcv(&child3) != 0) {
            error_occurred = true;
            goto cleanup;
        }
    }

    if (aux & 2) {
        spawn(&aux2, test88e_childaux, DROP_NONE);
        aux2_spawned = true;

        snd(&aux2, 2);
        snd(&aux2, id);
        snd(&aux2, (aux & 4) ? 2 : 1);

        if (rcv(&aux2) != 0) {
            error_occurred = true;
            goto cleanup;
        }

        if (aux & 4) {
            aux_ncnt++;
        }
    }

    usleep(WAIT_USECS);

    inc = 1;
    switch (match) {
    case MATCH_FIRST:
    case MATCH_SECOND:
        TEST_SEM(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
        TEST_SEM(id, 3, 0, 0, 0, 0);
        break;
    case MATCH_KILL:
        TEST_SEM(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
        terminate(&child1);
        child1_spawned = false;
        usleep(WAIT_USECS);
        TEST_SEM(id, 2, 0, 0, 1 + aux_ncnt, aux_zcnt);
        TEST_SEM(id, 3, 0, 0, 0, 0);
        break;
    case MATCH_BOTH:
        TEST_SEM(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
        TEST_SEM(id, 3, 0, 0, 0, 0);
        inc = 2;
        break;
    case MATCH_CASCADE:
        TEST_SEM(id, 2, 0, 0, 1 + aux_ncnt, aux_zcnt);
        TEST_SEM(id, 3, 0, 0, 1, 0);
        break;
    case MATCH_ALL:
        TEST_SEM(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
        TEST_SEM(id, 3, 0, 0, 1, 0);
        inc = 2;
        break;
    default:
        error_occurred = true;
        goto cleanup;
    }

    TEST_SEM(id, 0, 0, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, -1, -1);

    switch (resume) {
    case RESUME_SEMOP:
        memset(&sop, 0, sizeof(sop));
        sop.sem_num = 2;
        sop.sem_op = inc;
        if (semop(id, &sop, 1) != 0) {
            error_occurred = true;
            goto cleanup;
        }
        break;
    case RESUME_SETVAL:
        if (semctl(id, 2, SETVAL, inc) != 0) {
            error_occurred = true;
            goto cleanup;
        }
        break;
    case RESUME_SETALL:
        memset(val, 0, sizeof(val));
        val[2] = inc;
        if (semctl(id, 0, SETALL, val) != 0) {
            error_occurred = true;
            goto cleanup;
        }
        break;
    default:
        error_occurred = true;
        goto cleanup;
    }

    switch (match) {
    case MATCH_FIRST:
        TEST_SEM(id, 2, 0, child1.pid, 1 + aux_ncnt, aux_zcnt);
        TEST_SEM(id, 3, 1, child1.pid, 0, 0);
        collect(&child1);
        child1_collected = true;
        break;
    case MATCH_SECOND:
        TEST_SEM(id, 2, 0, child2.pid, 1 + aux_ncnt, aux_zcnt);
        TEST_SEM(id, 3, 0, 0, 0, 0);
        collect(&child2);
        child2_collected = true;
        break;
    case MATCH_KILL:
        TEST_SEM(id, 2, 0, child2.pid, aux_ncnt, aux_zcnt);
        TEST_SEM(id, 3, 0, 0, 0, 0);
        collect(&child2);
        child2_collected = true;
        break;
    case MATCH_BOTH:
        TEST_SEM(id, 2, 0, -1, aux_ncnt, aux_zcnt);
        TEST_SEM(id, 3, 2, -1, 0, 0);
        collect(&child1);
        child1_collected = true;
        collect(&child2);
        child2_collected = true;
        break;
    case MATCH_CASCADE:
        TEST_SEM(id, 2, 0, child1.pid, aux_ncnt, aux_zcnt);
        TEST_SEM(id, 3, 0, child2.pid, 0, 0);
        collect(&child1);
        child1_collected = true;
        collect(&child2);
        child2_collected = true;
        break;
    case MATCH_ALL:
        TEST_SEM(id, 2, 0, -1, aux_ncnt, aux_zcnt);
        TEST_SEM(id, 3, 0, child3.pid, 0, 0);
        collect(&child1);
        child1_collected = true;
        collect(&child2);
        child2_collected = true;
        collect(&child3);
        child3_collected = true;
        break;
    default:
        error_occurred = true;
        goto cleanup;
    }

    TEST_SEM(id, 0, 0, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, -1, -1);

    switch (match) {
    case MATCH_FIRST:
        if (child2_spawned && !child2_collected) {
            collect(&child2);
            child2_collected = true;
        }
        break;
    case MATCH_SECOND:
        if (child1_spawned && !child1_collected) {
            collect(&child1);
            child1_collected = true;
        }
        break;
    case MATCH_KILL:
    case MATCH_BOTH:
    case MATCH_CASCADE:
    case MATCH_ALL:
        break;
    default:
        error_occurred = true;
        goto cleanup;
    }

    if (aux1_spawned && !aux1_collected) {
        collect(&aux1);
        aux1_collected = true;
    }
    if (aux2_spawned && !aux2_collected) {
        collect(&aux2);
        aux2_collected = true;
    }

cleanup:
    if (id != -1) {
        if (semctl(id, 0, IPC_RMID) != 0) {
            e(0);
        }
        id = -1;
    }

    if (aux1_spawned && !aux1_collected) {
        collect(&aux1);
    }
    if (aux2_spawned && !aux2_collected) {
        collect(&aux2);
    }
    if (child1_spawned && !child1_collected) {
        collect(&child1);
    }
    if (child2_spawned && !child2_collected) {
        collect(&child2);
    }
    if (child3_spawned && !child3_collected) {
        collect(&child3);
    }

    if (error_occurred) {
        e(0);
    }
}

/*
 * Test operations affecting multiple processes, ensuring the following points:
 * 1) an operation resumes all possible waiters; 2) a resumed operation in turn
 * correctly resumes other now-unblocked operations; 3) a basic level of FIFO
 * fairness is provided between blocked parties; 4) all the previous points are
 * unaffected by additional waiters that are not being resumed; 5) identifier
 * removal properly resumes all affected waiters.
 */
#define SUBTEST_VALUE_88E 4
#define AUX_LOOP_START    1
#define AUX_LOOP_END      8

static void
test88e(void)
{
	unsigned int resume, match, aux;

	subtest = SUBTEST_VALUE_88E;

	for (match = 0; match < NR_MATCHES; match++)
		for (resume = 0; resume < NR_RESUMES; resume++)
			for (aux = AUX_LOOP_START; aux <= AUX_LOOP_END; aux++) /* 0 and 4 are equal */
				sub88e(match, resume, aux);
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
	size_t len;
	int id[2], id2, seen[2];
	int32_t i;

	id[0] = rcv(parent);
	id[1] = rcv(parent);

	if (sysctl(mib, __arraycount(mib), NULL, &len, NULL, 0) != 0) {
		e(0);
	}

	semsi = malloc(len);
	if (semsi == NULL) {
		e(0);
	}

	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0) {
		free(semsi);
		e(0);
	}

	seen[0] = seen[1] = 0;
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

	if (seen[0] != 1) {
		e(0);
	}
	if (seen[1] != 1) {
		e(0);
	}
}

/*
 * Test sysctl(2) based information retrieval.  This test aims to ensure that
 * in particular ipcs(1) and ipcrm(1) will be able to do their jobs.
 */
static void
checked_sysctl(const int *mib, u_int miblen, void *oldp, size_t *oldlenp_ptr, size_t expected_output_len)
{
    if (sysctl(mib, miblen, oldp, oldlenp_ptr, NULL, 0) != 0) e(0);
    if (expected_output_len != (size_t)-1 && *oldlenp_ptr != expected_output_len) e(0);
}

static int
checked_semget(key_t key, int nsems, int semflg)
{
    int id = semget(key, nsems, semflg);
    if (id < 0) e(0);
    return id;
}

static void
checked_semctl_rmid(int semid)
{
    if (semctl(semid, 0, IPC_RMID) != 0) e(0);
}

static void
verify_seminfo_match(const struct seminfo *s1, const struct seminfo *s2)
{
    if (memcmp(s1, s2, sizeof(struct seminfo)) != 0) e(0);
}

static void
verify_semds_entry(const struct semid_ds_sysctl *semds, key_t expected_key,
                   mode_t expected_mode, int expected_nsems)
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

static void
test88f(void)
{
    static const int mib[] = { CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_INFO,
        KERN_SYSVIPC_SEM_INFO };
    struct seminfo seminfo, seminfo2;
    struct sem_sysctl_info *semsi = NULL;
    struct semid_ds_sysctl *semds;
    struct link child;
    size_t len, total_size;
    int id[2];
    int32_t i;
    int slot[2];
    int current_ipc_id;

    const mode_t SEM_PERM_1 = 0612;
    const int SEM_NSEMS_1 = 5;
    const mode_t SEM_PERM_2 = 0650;
    const int SEM_NSEMS_2 = 3;

    len = sizeof(seminfo);
    checked_sysctl(mib, __arraycount(mib), &seminfo, &len, sizeof(seminfo));

    if (semctl(0, 0, IPC_INFO, &seminfo2) == -1) e(0);
    verify_seminfo_match(&seminfo, &seminfo2);

    if (seminfo.semmni <= 0 || seminfo.semmni > SHRT_MAX) e(0);

    total_size = sizeof(*semsi) +
                 sizeof(semsi->semids[0]) * (seminfo.semmni - 1);

    len = 0;
    checked_sysctl(mib, __arraycount(mib), NULL, &len, total_size);

    id[0] = checked_semget(KEY_A, SEM_NSEMS_1, IPC_CREAT | SEM_PERM_1);
    id[1] = checked_semget(IPC_PRIVATE, SEM_NSEMS_2, IPC_CREAT | SEM_PERM_2);

    if ((semsi = malloc(total_size)) == NULL) goto cleanup;

    len = total_size;
    checked_sysctl(mib, __arraycount(mib), semsi, &len, total_size);

    verify_seminfo_match(&semsi->seminfo, &seminfo);

    slot[0] = -1;
    slot[1] = -1;
    for (i = 0; i < seminfo.semmni; i++) {
        if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
            continue;

        current_ipc_id = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
        if (current_ipc_id == id[0]) {
            if (slot[0] != -1) e(0);
            slot[0] = i;
        } else if (current_ipc_id == id[1]) {
            if (slot[1] != -1) e(0);
            slot[1] = i;
        }
    }

    if (slot[0] < 0 || slot[1] < 0) e(0);

    semds = &semsi->semids[slot[0]];
    verify_semds_entry(semds, KEY_A, SEM_PERM_1, SEM_NSEMS_1);

    semds = &semsi->semids[slot[1]];
    verify_semds_entry(semds, IPC_PRIVATE, SEM_PERM_2, SEM_NSEMS_2);

    spawn(&child, test88f_child, DROP_ALL);
    snd(&child, id[0]);
    snd(&child, id[1]);
    collect(&child);

    checked_semctl_rmid(id[0]);
    checked_semctl_rmid(id[1]);

    len = total_size;
    checked_sysctl(mib, __arraycount(mib), semsi, &len, total_size);

    for (i = 0; i < seminfo.semmni; i++) {
        if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
            continue;

        current_ipc_id = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
        if (current_ipc_id == id[0] || current_ipc_id == id[1]) e(0);
    }

cleanup:
    if (semsi != NULL) {
        free(semsi);
    }
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
	if (page_size == -1) {
		e(0);
	}

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
#include <stdlib.h>
#include <errno.h>
#include <limits.h>

void start(int);
void test88_init(void);
void test88a(void);
void test88b(void);
void test88c(void);
void test88d(void);
void test88e(void);
void test88f(void);
void quit(void);

#ifndef ITERATIONS
#define ITERATIONS 100
#endif

#define START_MAGIC_VALUE 88
#define DEFAULT_M_VALUE   0xFF

#define TEST_A_BIT 0x01
#define TEST_B_BIT 0x02
#define TEST_C_BIT 0x04
#define TEST_D_BIT 0x08
#define TEST_E_BIT 0x10
#define TEST_F_BIT 0x20

int
main(int argc, char ** argv)
{
	int i;
	long m_val_long;
    char *endptr;
    int m;

	start(START_MAGIC_VALUE);

	test88_init();

	if (argc == 2) {
        errno = 0;
        m_val_long = strtol(argv[1], &endptr, 10);

        if (errno == ERANGE) {
            m = DEFAULT_M_VALUE;
        } else if (endptr == argv[1] || *endptr != '\0') {
            m = 0;
        } else {
            if (m_val_long > INT_MAX || m_val_long < INT_MIN) {
                m = DEFAULT_M_VALUE;
            } else {
                m = (int)m_val_long;
            }
        }
	} else {
		m = DEFAULT_M_VALUE;
	}

	for (i = 0; i < ITERATIONS; i++) {
		if (m & TEST_A_BIT) test88a();
		if (m & TEST_B_BIT) test88b();
		if (m & TEST_C_BIT) test88c();
		if (m & TEST_D_BIT) test88d();
		if (m & TEST_E_BIT) test88e();
		if (m & TEST_F_BIT) test88f();
	}

	quit();
    return 0;
}
