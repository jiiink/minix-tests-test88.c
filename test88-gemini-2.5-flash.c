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
static void drop_privileges(int drop_level) {
  struct passwd *pw;
  struct group *gr;

  switch (drop_level) {
  case DROP_ALL:
    if (setgroups(0, NULL) != 0) {
      e(0);
    }

    if ((gr = getgrnam(NONROOT_GROUP)) == NULL) {
      e(0);
    }
    if (setgid(gr->gr_gid) != 0) {
      e(0);
    }
    if (setegid(gr->gr_gid) != 0) {
      e(0);
    }
  case DROP_USER:
    if ((pw = getpwnam(NONROOT_USER)) == NULL) {
      e(0);
    }
    if (setuid(pw->pw_uid) != 0) {
      e(0);
    }
    break;
  }
}

static void spawn(struct link *link, void (*proc)(struct link *), int drop) {
  int up[2], dn[2];

  fflush(stdout);
  fflush(stderr);

  if (pipe(up) != 0) {
    e(0);
  }
  if (pipe(dn) != 0) {
    close(up[0]);
    close(up[1]);
    e(0);
  }

  link->pid = fork();

  switch (link->pid) {
  case 0:
    close(up[1]);
    close(dn[0]);

    link->pid = getppid();
    link->rcvfd = up[0];
    link->sndfd = dn[1];

    errct = 0;

    drop_privileges(drop);

    proc(link);

    exit(errct);

  case -1:
    close(up[0]);
    close(up[1]);
    close(dn[0]);
    close(dn[1]);
    e(0);

  default:
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
	pid_t waited_pid;

	if (close(link->sndfd) == -1) {
		e(0);
	}

	if (close(link->rcvfd) == -1) {
		e(0);
	}

	waited_pid = waitpid(link->pid, &status, 0);

	if (waited_pid == -1) {
		e(0);
	} else if (waited_pid != link->pid) {
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
static int
terminate(struct link * link)
{
	int status;

	if (kill(link->pid, SIGKILL) != 0) {
		return -1;
	}

	close(link->sndfd);
	close(link->rcvfd);

	if (waitpid(link->pid, &status, 0) <= 0) {
		return -1;
	}

	if (WIFSIGNALED(status)) {
		if (WTERMSIG(status) != SIGKILL) {
			return -1;
		}
	} else {
		if (!WIFEXITED(status)) {
			return -1;
		} else {
			errct += WEXITSTATUS(status);
		}
	}

	return 0;
}

/*
 * Send an integer value to the child or parent.
 */
static int
snd(struct link *link, int val)
{
    ssize_t bytes_to_write = sizeof(val);
    ssize_t bytes_written = write(link->sndfd, &val, bytes_to_write);

    if (bytes_written != bytes_to_write) {
        return -1;
    }
    return 0;
}

/*
 * Receive an integer value from the child or parent, or -1 on EOF.
 */
static int
rcv(struct link * link)
{
    int r;
    int val;

    r = read(link->rcvfd, (void *)&val, sizeof(val));

    if (r == -1) {
        return -2;
    }

    if (r == 0) {
        return -1;
    }

    if (r != sizeof(val)) {
        return -3;
    }

    return val;
}

/*
 * Child procedure that creates semaphore sets.
 */
static void
resolve_target_ownership(int sugid_type, uid_t *out_uid, gid_t *out_gid)
{
    struct passwd *pw;
    struct group *gr;

    *out_uid = geteuid();
    *out_gid = getegid();

    if (sugid_type == SUGID_NONE) {
        return;
    }

    switch (sugid_type) {
        case SUGID_ROOT_USER:
            if ((pw = getpwnam(ROOT_USER)) == NULL) e(0);
            *out_uid = pw->pw_uid;
            break;
        case SUGID_NONROOT_USER:
            if ((pw = getpwnam(NONROOT_USER)) == NULL) e(0);
            *out_uid = pw->pw_uid;
            break;
        case SUGID_ROOT_GROUP:
            if ((gr = getgrnam(ROOT_GROUP)) == NULL) e(0);
            *out_gid = gr->gr_gid;
            break;
        case SUGID_NONROOT_GROUP:
            if ((gr = getgrnam(NONROOT_GROUP)) == NULL) e(0);
            *out_gid = gr->gr_gid;
            break;
        default:
            e(0);
            break;
    }
}

static void
test_perm_child(struct link * parent)
{
	int mask, rmask, sugid_type;
	int sem_ids[3];
	struct semid_ds semds;
	uid_t expected_uid, expected_gid;

	while ((mask = rcv(parent)) != -1) {
		rmask = rcv(parent);
		sugid_type = rcv(parent);

		resolve_target_ownership(sugid_type, &expected_uid, &expected_gid);

		if ((sem_ids[0] = semget(KEY_A, 3,
		    IPC_CREAT | IPC_EXCL |
		    ((sugid_type == SUGID_NONE) ? mask : 0))) == -1) e(0);
		if ((sem_ids[1] = semget(KEY_B, 3,
		    IPC_CREAT | IPC_EXCL | mask | rmask)) == -1) e(0);
		if ((sem_ids[2] = semget(KEY_C, 3,
		    IPC_CREAT | IPC_EXCL | rmask)) == -1) e(0);

		if (sugid_type != SUGID_NONE) {
			semds.sem_perm.uid = expected_uid;
			semds.sem_perm.gid = expected_gid;

			semds.sem_perm.mode = mask;
			if (semctl(sem_ids[0], 0, IPC_SET, &semds) != 0) e(0);

			semds.sem_perm.mode = mask | rmask;
			if (semctl(sem_ids[1], 0, IPC_SET, &semds) != 0) e(0);

			semds.sem_perm.mode = rmask;
			if (semctl(sem_ids[2], 0, IPC_SET, &semds) != 0) e(0);
		}

		if (mask & IPC_R) {
			if (semctl(sem_ids[0], 0, IPC_STAT, &semds) != 0) e(0);
			if (semds.sem_perm.mode != (SEM_ALLOC | mask)) e(0);
			if (semds.sem_perm.uid != expected_uid) e(0);
			if (semds.sem_perm.gid != expected_gid) e(0);
			if (semds.sem_perm.cuid != geteuid()) e(0);
			if (semds.sem_perm.cgid != getegid()) e(0);
		}

		snd(parent, sem_ids[0]);
		snd(parent, sem_ids[1]);
		snd(parent, sem_ids[2]);

		if (rcv(parent) != 0) e(0);

		(void)semctl(sem_ids[0], 0, IPC_RMID);
		(void)semctl(sem_ids[1], 0, IPC_RMID);
		(void)semctl(sem_ids[2], 0, IPC_RMID);
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
struct TestConfig {
    int shift;
    int drop1;
    int drop2;
    int sugid;
};

static const struct TestConfig test_configs[] = {
    {6, DROP_ALL,  DROP_ALL,  SUGID_NONE},
    {6, DROP_NONE, DROP_ALL,  SUGID_NONROOT_USER},
    {6, DROP_USER, DROP_ALL,  SUGID_ROOT_USER},
    {3, DROP_NONE, DROP_USER, SUGID_NONE},
    {3, DROP_NONE, DROP_ALL,  SUGID_NONROOT_GROUP},
    {3, DROP_NONE, DROP_USER, SUGID_NONROOT_GROUP},
    {0, DROP_NONE, DROP_ALL,  SUGID_NONE}
};

#define NUM_TEST_CONFIGS (sizeof(test_configs) / sizeof(test_configs[0]))
#define MAX_PERM_BIT_VALUE 7
#define FULL_PERM_MASK 0777
#define THREE_BIT_PERM_MASK 7

static void
test_perm(void (* proc)(struct link *), int owner_test)
{
	struct link child1, child2;
	int config_idx;
	int bit;
	int mask, rmask;
	int id[3];

	for (config_idx = 0; config_idx < NUM_TEST_CONFIGS; ++config_idx) {
		const struct TestConfig *current_config = &test_configs[config_idx];

		spawn(&child1, test_perm_child, current_config->drop1);
		spawn(&child2, proc, current_config->drop2);

		for (bit = 0; bit <= MAX_PERM_BIT_VALUE; ++bit) {
			mask = bit << current_config->shift;
			rmask = FULL_PERM_MASK & ~(THREE_BIT_PERM_MASK << current_config->shift);

			snd(&child1, mask);
			snd(&child1, rmask);
			snd(&child1, current_config->sugid);
			id[0] = rcv(&child1);
			id[1] = rcv(&child1);
			id[2] = rcv(&child1);

			snd(&child2, (owner_test) ? current_config->shift : bit);
			snd(&child2, id[0]);
			snd(&child2, id[1]);
			snd(&child2, id[2]);
			if (rcv(&child2) != 0) {
				e(0);
			}

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
enum {
    SEM_ERROR = -1,
    SEM_MASK_SHIFT = 6,
    MAX_BIT_VALUE = 7,
    ID_ARRAY_SIZE = 3
};

static void
check_semaphore_access_and_id(key_t key, int expected_id, int current_bit_value, int tbit_from_rcv)
{
    int sem_id;
    int mask = current_bit_value << SEM_MASK_SHIFT;

    sem_id = semget(key, 0, mask);

    // Opening semaphore set must succeed iff the given bits are all set in
    // the relevant three-bit section of the creation mask, and the bit is not zero.
    int access_expected_to_succeed = (current_bit_value != 0 && (current_bit_value & tbit_from_rcv) == current_bit_value);

    if (access_expected_to_succeed) {
        if (sem_id == SEM_ERROR) {
            // Expected success, but semget failed.
            e(0);
        }
        if (sem_id != expected_id) {
            // Succeeded, but returned the wrong semaphore ID.
            e(0);
        }
    } else {
        // Expected failure. It must fail with SEM_ERROR and errno set to EACCES.
        if (sem_id != SEM_ERROR || errno != EACCES) {
            e(0);
        }
    }
}

static void
test88a_perm(struct link * parent)
{
    int tbit_val;
    int received_ids[ID_ARRAY_SIZE];
    int current_bit_value;

    while ((tbit_val = rcv(parent)) != SEM_ERROR) {
        received_ids[0] = rcv(parent);
        received_ids[1] = rcv(parent);
        received_ids[2] = rcv(parent);

        /*
         * We skip setting lower bits, as it is not clear what effect
         * that should have.  We assume that zero bits should result in
         * failure.
         */
        for (current_bit_value = 0; current_bit_value <= MAX_BIT_VALUE; current_bit_value++) {
            // Check semaphore set A
            check_semaphore_access_and_id(KEY_A, received_ids[0], current_bit_value, tbit_val);

            // Check semaphore set B
            check_semaphore_access_and_id(KEY_B, received_ids[1], current_bit_value, tbit_val);

            /*
             * Semaphore set C was created with only irrelevant
             * mode bits set, so opening it must always fail.
             */
            int mask_c = current_bit_value << SEM_MASK_SHIFT;
            int sem_id_c = semget(KEY_C, 0, mask_c);

            if (sem_id_c != SEM_ERROR) {
                e(0); // Expected failure, but semget succeeded
            }
            if (errno != EACCES) {
                e(0); // Expected EACCES, but failed with a different error
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
    time_t current_time;
    int id_local[3]; // Used for various temporary IDs

    // Helper for semget and error checking (fatal for test failures)
    int safe_semget(key_t key, int nsems, int semflg) {
        int res = semget(key, nsems, semflg);
        if (res < 0) {
            e(0);
        }
        return res;
    }

    // Helper for semctl IPC_RMID and error checking (fatal for test failures)
    void safe_semctl_rmid(int semid) {
        if (semid >= 0 && semctl(semid, 0, IPC_RMID) != 0) {
            e(0);
        }
    }

    // Helper for semget expecting failure with a specific errno (fatal for test failures)
    void expect_semget_fail(key_t key, int nsems, int semflg, int expected_errno) {
        if (semget(key, nsems, semflg) != -1) {
            e(0);
        }
        if (errno != expected_errno) {
            e(0);
        }
    }

    // Helper to verify semid_ds structure (fatal for test failures)
    void verify_sem_ds(int semid, key_t expected_key, int expected_nsems, int expected_mode, time_t creation_time) {
        struct semid_ds ds;
        if (semctl(semid, 0, IPC_STAT, &ds) != 0) {
            e(0);
        }

        if (ds.sem_perm.uid != geteuid()) e(0);
        if (ds.sem_perm.gid != getegid()) e(0);
        if (ds.sem_perm.cuid != geteuid()) e(0);
        if (ds.sem_perm.cgid != getegid()) e(0);
        if (ds.sem_perm.mode != (SEM_ALLOC | expected_mode)) e(0);
        if (ds.sem_perm._key != expected_key) e(0);
        if (ds.sem_nsems != expected_nsems) e(0);
        if (ds.sem_otime != 0) e(0);
        // Allow for a small time delta for ctime
        if (ds.sem_ctime < creation_time || ds.sem_ctime >= creation_time + 10) e(0);

        // Verify individual semaphore initial values
        for (unsigned int k = 0; k < ds.sem_nsems; k++) {
            TEST_SEM(semid, k, 0, 0, 0, 0);
        }
    }

    subtest = 0;

    /*
     * The key IPC_PRIVATE must always yield a new semaphore set identifier
     * regardless of whether IPC_CREAT and IPC_EXCL are supplied.
     */
    int private_mode = 0600;
    id_local[0] = safe_semget(IPC_PRIVATE, 1, IPC_CREAT | private_mode);
    id_local[1] = safe_semget(IPC_PRIVATE, 1, IPC_CREAT | IPC_EXCL | private_mode);
    id_local[2] = safe_semget(IPC_PRIVATE, 1, private_mode);

    if (id_local[0] == id_local[1] || id_local[1] == id_local[2] || id_local[0] == id_local[2]) {
        e(0);
    }

    safe_semctl_rmid(id_local[0]);
    safe_semctl_rmid(id_local[1]);
    safe_semctl_rmid(id_local[2]);

    /* Remove any leftovers from previous test runs. */
    // Helper to cleanup by key
    void try_cleanup_sem_by_key(key_t key, int mode) {
        int existing_id = semget(key, 0, mode);
        if (existing_id >= 0) {
            safe_semctl_rmid(existing_id);
        } else if (errno != ENOENT) {
            e(0);
        }
    }
    try_cleanup_sem_by_key(KEY_A, 0600);
    try_cleanup_sem_by_key(KEY_B, 0600);

    /*
     * For non-IPC_PRIVATE keys, open(2)-like semantics apply with respect
     * to IPC_CREAT and IPC_EXCL flags.
     */
    // Test opening non-existent key fails with ENOENT
    expect_semget_fail(KEY_A, 1, 0600, ENOENT);

    int key_mode = IPC_CREAT | 0600;
    id_local[0] = safe_semget(KEY_A, 1, key_mode | IPC_EXCL);
    id_local[1] = safe_semget(KEY_B, 1, key_mode);

    if (id_local[0] == id_local[1]) e(0);

    // Test opening existing key_A (nsems=1 is compatible with existing)
    id_local[2] = safe_semget(KEY_A, 1, 0600);
    if (id_local[2] != id_local[0]) e(0);

    // Test opening existing key_B (nsems=1 is compatible with existing)
    id_local[2] = safe_semget(KEY_B, 1, key_mode); // IPC_CREAT is redundant for existing
    if (id_local[2] != id_local[1]) e(0);

    // Test creating with IPC_EXCL on existing key_A fails with EEXIST
    expect_semget_fail(KEY_A, 1, key_mode | IPC_EXCL, EEXIST);

    safe_semctl_rmid(id_local[0]);
    safe_semctl_rmid(id_local[1]);

    /*
     * Check that we get the right error when we run out of semaphore sets.
     */
    int *id_saturation_ptr = NULL;
    unsigned int actual_created_sets = 0;
    int saved_errno = 0;

    if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
    if (seminfo.semmni < 3 || seminfo.semmni > USHRT_MAX) e(0);

    id_saturation_ptr = (int *)malloc(sizeof(int) * (seminfo.semmni + 1));
    if (id_saturation_ptr == NULL) e(0);

    for (unsigned int k = 0; k < seminfo.semmni + 1; k++) {
        id_saturation_ptr[k] = semget(KEY_A + k, 1, IPC_CREAT | 0600);
        if (id_saturation_ptr[k] < 0) {
            saved_errno = errno; // Capture errno on failure
            break;
        }
        // Ensure that there are no ID collisions. O(n**2).
        for (unsigned int l = 0; l < k; l++) {
            if (id_saturation_ptr[k] == id_saturation_ptr[l]) {
                actual_created_sets = k + 1; // For cleanup, including current
                goto cleanup_saturation_and_exit; // Collision is a test failure
            }
        }
        actual_created_sets++;
    }

    if (saved_errno != ENOSPC) goto cleanup_saturation_and_exit;
    if (actual_created_sets < 3) goto cleanup_saturation_and_exit;
    if (actual_created_sets == seminfo.semmni + 1) goto cleanup_saturation_and_exit;

    // Clean up all successfully created semaphore sets
    for (unsigned int k = 0; k < actual_created_sets; k++) {
        safe_semctl_rmid(id_saturation_ptr[k]);
    }
    free(id_saturation_ptr);
    id_saturation_ptr = NULL; // Defensive NULLing

    /*
     * The given number of semaphores must be within bounds.
     */
    expect_semget_fail(KEY_A, -1, IPC_CREAT | 0600, EINVAL);
    expect_semget_fail(KEY_A, 0, IPC_CREAT | 0600, EINVAL);

    // seminfo must be up to date for semmsl check
    if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
    if (seminfo.semmsl < 3 || seminfo.semmsl > USHRT_MAX) e(0);
    expect_semget_fail(KEY_A, seminfo.semmsl + 1, IPC_CREAT | 0600, EINVAL);

    int id_sem_bounds_check;
    id_sem_bounds_check = safe_semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0600);
    safe_semctl_rmid(id_sem_bounds_check);

    id_sem_bounds_check = safe_semget(KEY_A, 2, IPC_CREAT | 0600); // Create with 2 semaphores

    int id_sem_open_check;
    id_sem_open_check = safe_semget(KEY_A, 0, 0600);
    if (id_sem_bounds_check != id_sem_open_check) e(0);

    id_sem_open_check = safe_semget(KEY_A, 1, 0600);
    if (id_sem_bounds_check != id_sem_open_check) e(0);

    id_sem_open_check = safe_semget(KEY_A, 2, 0600);
    if (id_sem_bounds_check != id_sem_open_check) e(0);

    // Requesting more semaphores than an existing set has should fail with EINVAL
    expect_semget_fail(KEY_A, 3, 0600, EINVAL);
    expect_semget_fail(KEY_A, seminfo.semmsl + 1, 0600, EINVAL);

    safe_semctl_rmid(id_sem_bounds_check);

    /*
     * Verify that the initial values for the semaphore set are as expected.
     */
    time(&current_time);
    // seminfo must be up to date for semmns check
    if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
    if (seminfo.semmns < 3 + seminfo.semmsl) e(0);

    int id_initial_values[2];
    id_initial_values[0] = safe_semget(IPC_PRIVATE, 3, IPC_CREAT | IPC_EXCL | 0642);
    id_initial_values[1] = safe_semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0613);

    verify_sem_ds(id_initial_values[0], IPC_PRIVATE, 3, 0642, current_time);
    verify_sem_ds(id_initial_values[1], KEY_A, seminfo.semmsl, 0613, current_time);

    safe_semctl_rmid(id_initial_values[1]);
    safe_semctl_rmid(id_initial_values[0]);

    /*
     * Finally, perform a number of permission-related checks.
     */
    // The superuser can always open and destroy a semaphore set.
    int id_perm_check;
    id_perm_check = safe_semget(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0000); // Superuser creates with no user permissions

    int id_perm_open_check;
    id_perm_open_check = safe_semget(KEY_A, 0, 0600); // Superuser can open it with any permissions
    if (id_perm_check != id_perm_open_check) e(0);

    id_perm_open_check = safe_semget(KEY_A, 0, 0000); // Even with 0000 mode (no access)
    if (id_perm_check != id_perm_open_check) e(0);

    safe_semctl_rmid(id_perm_check);

    /*
     * When an unprivileged process tries to open a semaphore set, the
     * given upper three permission bits from the mode (0700) are tested
     * against the appropriate permission bits from the semaphore set.
     */
    test_perm(test88a_perm, 0 /*owner_test*/);

    return; // Normal exit from test function

cleanup_saturation_and_exit:
    // This label is reached if there was an error during semaphore saturation test.
    // It cleans up any semaphores that were successfully created before the error.
    for (unsigned int k = 0; k < actual_created_sets; k++) {
        safe_semctl_rmid(id_saturation_ptr[k]);
    }
    free(id_saturation_ptr); // Free the allocated memory
    e(0); // Exit the test on failure in this section
}

/*
 * Test semop(2) permission checks.
 */
static void e(int code);
static int rcv(struct link *parent);
static void snd(struct link *parent, int val);

enum TestCaseIndex {
    TEST_CASE_0 = 0,
    TEST_CASE_1,
    TEST_CASE_2,
    TEST_CASE_3,
    TEST_CASE_4,
    TEST_CASE_5,
    TEST_CASE_6,
    TEST_CASE_7,
    NUM_TEST_CASES
};

typedef struct {
    struct sembuf sops[2];
    size_t nsops;
    int expected_bit_mask;
} TestCaseParams;

static const TestCaseParams test_params[NUM_TEST_CASES] = {
    {{{{0, 0, 0}}}, 1, 4},
    {{{{0, 1, 0}}}, 1, 2},
    {{{{0, -1, 0}}}, 1, 2},
    {{{{0, 0, 0}}, {{0, 1, 0}}}, 2, 6},
    {{{{1, 0, 0}}, {{0, -1, 0}}}, 2, 6},
    {{{{0, 0, 0}}, {{1, 0, 0}}}, 2, 4},
    {{{{0, 1, 0}}, {{0, -1, 0}}}, 2, 2},
    {{{{USHRT_MAX, 0, 0}}, {{0, 0, 0}}}, 2, 4}
};

static void
handle_semop_primary_check(int sem_id, const struct sembuf *sops, size_t nsops, int current_test_case_idx, int tbit, int expected_bit_mask)
{
    int r = semop(sem_id, (struct sembuf *)sops, nsops);

    if (current_test_case_idx == TEST_CASE_7 && r == -1 && errno == EFBIG) {
        r = 0;
    }

    if (r == -1 && errno != EACCES) {
        e(0);
    }

    if (((expected_bit_mask & tbit) == expected_bit_mask) != (r != -1)) {
        e(0);
    }
}

static void
handle_semop_expect_access_denied(int sem_id, const struct sembuf *sops, size_t nsops)
{
    if (semop(sem_id, (struct sembuf *)sops, nsops) != -1) {
        e(0);
    }
    if (errno != EACCES) {
        e(0);
    }
}

static void
test88b_perm(struct link * parent)
{
    int tbit;
    int i;
    int id[3];

    while ((tbit = rcv(parent)) != -1) {
        id[0] = rcv(parent);
        id[1] = rcv(parent);
        id[2] = rcv(parent);

        for (i = 0; i < NUM_TEST_CASES; i++) {
            const TestCaseParams *current_params = &test_params[i];

            handle_semop_primary_check(id[0], current_params->sops, current_params->nsops, i, tbit, current_params->expected_bit_mask);
            handle_semop_primary_check(id[1], current_params->sops, current_params->nsops, i, tbit, current_params->expected_bit_mask);
            handle_semop_expect_access_denied(id[2], current_params->sops, current_params->nsops);
        }

        snd(parent, 0);
    }
}

/*
 * Signal handler.
 */
#include <signal.h>
#include <unistd.h>
#include <stdlib.h>

static void
got_signal(int sig)
{
	if (sig != SIGHUP) {
		_exit(EXIT_FAILURE);
	}
	if (nr_signals != 0) {
		_exit(EXIT_FAILURE);
	}
	nr_signals++;
}

/*
 * Child process for semop(2) tests, mainly testing blocking operations.
 */
static void
execute_sem_op(int sem_id, struct sembuf *sops, unsigned int nsops, int expected_retval, int expected_errno)
{
    int result = semop(sem_id, sops, nsops);
    if (result != expected_retval) {
        e(0);
    }
    if (expected_retval == -1 && errno != expected_errno) {
        e(0);
    }
}

static void
set_sem_op(struct sembuf *sbuf, unsigned short sem_num, short sem_op, short sem_flg)
{
    sbuf->sem_num = sem_num;
    sbuf->sem_op = sem_op;
    sbuf->sem_flg = sem_flg;
}


static void
test88b_child(struct link * parent)
{
	struct sembuf ops[5];
	struct sigaction act;
	int id;

	id = rcv(parent);

	set_sem_op(&ops[0], 0, 0, 0);
	execute_sem_op(id, ops, 1, 0, 0);

	if (rcv(parent) != 1) e(0);

	set_sem_op(&ops[0], 0, -3, 0);
	execute_sem_op(id, ops, 1, 0, 0);

	if (rcv(parent) != 2) e(0);

	set_sem_op(&ops[0], 2, 2, 0);
	set_sem_op(&ops[1], 1, -1, 0);
	set_sem_op(&ops[2], 0, 1, 0);
	execute_sem_op(id, ops, 3, 0, 0);

	if (rcv(parent) != 3) e(0);

	set_sem_op(&ops[0], 1, 0, 0);
	set_sem_op(&ops[1], 1, 1, 0);
	set_sem_op(&ops[2], 0, 0, 0);
	set_sem_op(&ops[3], 2, 0, 0);
	set_sem_op(&ops[4], 2, 1, 0);
	execute_sem_op(id, ops, 5, 0, 0);

	if (rcv(parent) != 4) e(0);

	set_sem_op(&ops[0], 1, -2, 0);
	set_sem_op(&ops[1], 2, 0, 0);
	execute_sem_op(id, ops, 2, 0, 0);

	if (rcv(parent) != 5) e(0);

	set_sem_op(&ops[0], 0, -1, 0);
	set_sem_op(&ops[1], 1, -1, IPC_NOWAIT);
	execute_sem_op(id, ops, 2, 0, 0);

	if (rcv(parent) != 6) e(0);

	set_sem_op(&ops[0], 1, 0, 0);
	set_sem_op(&ops[1], 0, 0, IPC_NOWAIT);
	execute_sem_op(id, ops, 2, -1, EAGAIN);

	if (rcv(parent) != 7) e(0);

	set_sem_op(&ops[0], 0, 0, 0);
	set_sem_op(&ops[1], 1, 1, 0);
	execute_sem_op(id, ops, 2, 0, 0);

	if (rcv(parent) != 8) e(0);

	set_sem_op(&ops[0], 0, -1, 0);
	set_sem_op(&ops[1], 1, 2, 0);
	execute_sem_op(id, ops, 2, -1, ERANGE);

	memset(&act, 0, sizeof(act));
	act.sa_handler = got_signal;
	sigfillset(&act.sa_mask);
	if (sigaction(SIGHUP, &act, NULL) != 0) e(0);

	if (rcv(parent) != 9) e(0);

	set_sem_op(&ops[0], 0, 0, 0);
	set_sem_op(&ops[1], 0, 1, 0);
	set_sem_op(&ops[2], 1, 0, 0);
	execute_sem_op(id, ops, 3, -1, EINTR);
	if (nr_signals != 1) e(0);

	TEST_SEM(id, 0, 0, parent->pid, 0, 0);
	TEST_SEM(id, 1, 1, parent->pid, 0, 0);

	if (rcv(parent) != 10) e(0);

	set_sem_op(&ops[0], 0, -3, 0);
	execute_sem_op(id, ops, 1, -1, EIDRM);

	id = rcv(parent);

	set_sem_op(&ops[0], 0, -1, 0);
	set_sem_op(&ops[1], 1, 1, 0);
	execute_sem_op(id, ops, 2, -1, ERANGE);

	if (rcv(parent) != 11) e(0);

	set_sem_op(&ops[0], 1, 0, 0);
	set_sem_op(&ops[1], 0, -1, 0);
	execute_sem_op(id, ops, 2, 0, 0);

	id = rcv(parent);

	set_sem_op(&ops[0], 0, -1, 0);
	set_sem_op(&ops[1], 1, 0, 0);
	execute_sem_op(id, ops, 2, 0, 0);

	snd(parent, errct);
	if (rcv(parent) != 12) e(0);

	/* The child will be killed during this call.  It should not return. */
	set_sem_op(&ops[0], 1, -1, 0);
	set_sem_op(&ops[1], 0, 3, 0);
	(void)semop(id, ops, 2);

	e(0);
}

/*
 * Test the basic semop(2) functionality.
 */
#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <signal.h>
#include <unistd.h>
#include <limits.h>

extern int subtest;
extern void e(int);
extern void TEST_SEM(int, int, int, pid_t, int, int);
extern void spawn(struct link *, void (*)(void), int);
extern void snd(struct link *, int);
extern int rcv(struct link *);
extern void terminate(struct link *);
extern void test_perm(void (*)(void), int);
extern void test88b_perm(void);
extern void test88b_child(void);
extern void *bad_ptr;
extern void *page_ptr;
extern size_t page_size;

#ifndef WAIT_USECS
#define WAIT_USECS 100000
#endif
#ifndef DROP_NONE
#define DROP_NONE 0
#endif
#ifndef IXSEQ_TO_IPCID
#define IXSEQ_TO_IPCID(seq, perm) (seq)
#endif
#ifndef IPC_NOWAIT
#define IPC_NOWAIT 0x800
#endif
#ifndef SETVAL
#define SETVAL 8
#endif
#ifndef GETVAL
#define GETVAL 7
#endif
#ifndef SETALL
#define SETALL 9
#endif
#ifndef IPC_RMID
#define IPC_RMID 0
#endif
#ifndef IPC_STAT
#define IPC_STAT 2
#endif
#ifndef IPC_INFO
#define IPC_INFO 3
#endif

enum ChildCommands {
    CMD_CHILD_SEND_SEMID = 0,
    CMD_CHILD_1,
    CMD_CHILD_2,
    CMD_CHILD_3,
    CMD_CHILD_4,
    CMD_CHILD_5,
    CMD_CHILD_6,
    CMD_CHILD_7,
    CMD_CHILD_8,
    CMD_CHILD_9,
    CMD_CHILD_10,
    CMD_CHILD_11,
    CMD_CHILD_12
};

static void
test88b(void)
{
    struct seminfo seminfo;
    struct semid_ds semds;
    struct sembuf *sops = NULL;
    size_t sops_buffer_size = 0;
    struct link child = {0};
    time_t now;
    unsigned short val[2];
    int current_sem_id = -1;

    subtest = 1;

cleanup_child:
    if (child.pid != 0) {
        terminate(&child);
        child.pid = 0;
    }
cleanup_sem_id:
    if (current_sem_id != -1) {
        (void)semctl(current_sem_id, 0, IPC_RMID);
        current_sem_id = -1;
    }
cleanup_sops:
    if (sops != NULL) {
        free(sops);
        sops = NULL;
    }
    return;

    if (semctl(0, 0, IPC_INFO, &seminfo) == -1) {
        e(0);
        goto cleanup_sops;
    }

    if (seminfo.semopm < 3 || seminfo.semopm > USHRT_MAX) {
        e(0);
        goto cleanup_sops;
    }

    sops_buffer_size = sizeof(sops[0]) * (seminfo.semopm + 1);
    sops = malloc(sops_buffer_size);
    if (sops == NULL) {
        e(0);
        goto cleanup_sops;
    }
    memset(sops, 0, sops_buffer_size);

    current_sem_id = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600);
    if (current_sem_id == -1) {
        e(0);
        goto cleanup_sops;
    }

    if (semop(current_sem_id, NULL, 0) != 0) {
        e(0);
        goto cleanup_sem_id;
    }

    if (semop(current_sem_id, NULL, 1) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != EFAULT) {
        e(0);
        goto cleanup_sem_id;
    }

    if (semop(current_sem_id, bad_ptr, 1) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != EFAULT) {
        e(0);
        goto cleanup_sem_id;
    }

    memset(page_ptr, 0, page_size);
    struct sembuf *sops_invalid_ptr_test = ((struct sembuf *)bad_ptr) - 1;
    sops_invalid_ptr_test->sem_op = 1;
    if (semop(current_sem_id, sops_invalid_ptr_test, 2) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != EFAULT) {
        e(0);
        goto cleanup_sem_id;
    }

    TEST_SEM(current_sem_id, 0, 0, 0, 0, 0);
    if (semctl(current_sem_id, 0, IPC_STAT, &semds) != 0) {
        e(0);
        goto cleanup_sem_id;
    }
    if (semds.sem_otime != 0) {
        e(0);
        goto cleanup_sem_id;
    }

    time(&now);
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_sem_id;
    }

    TEST_SEM(current_sem_id, 0, 0, getpid(), 0, 0);
    if (semctl(current_sem_id, 0, IPC_STAT, &semds) != 0) {
        e(0);
        goto cleanup_sem_id;
    }
    if (semds.sem_otime < now || semds.sem_otime >= now + 10) {
        e(0);
        goto cleanup_sem_id;
    }

    if (semop(current_sem_id, sops, seminfo.semopm) != 0) {
        e(0);
        goto cleanup_sem_id;
    }

    if (semop(current_sem_id, sops, seminfo.semopm + 1) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != E2BIG) {
        e(0);
        goto cleanup_sem_id;
    }

    if (semop(current_sem_id, sops, SIZE_MAX) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != E2BIG) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[1].sem_num = 1;
    if (semop(current_sem_id, sops, 2) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != EFBIG) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[1].sem_num = USHRT_MAX;
    if (semop(current_sem_id, sops, 2) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != EFBIG) {
        e(0);
        goto cleanup_sem_id;
    }
    sops[1].sem_num = 0;

    if (seminfo.semvmx < 3 || seminfo.semvmx > SHRT_MAX) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_num = 0;
    sops[0].sem_flg = IPC_NOWAIT;

    if (seminfo.semvmx < SHRT_MAX) {
        sops[0].sem_op = (short)(seminfo.semvmx + 1);
        if (semop(current_sem_id, sops, 1) != -1) {
            e(0);
            goto cleanup_sem_id;
        }
        if (errno != ERANGE) {
            e(0);
            goto cleanup_sem_id;
        }
        if (semctl(current_sem_id, 0, GETVAL) != 0) {
            e(0);
            goto cleanup_sem_id;
        }
    }

    sops[0].sem_op = (short)seminfo.semvmx;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_sem_id;
    }
    if (semctl(current_sem_id, 0, GETVAL) != (int)seminfo.semvmx) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = 1;
    if (semop(current_sem_id, sops, 1) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != ERANGE) {
        e(0);
        goto cleanup_sem_id;
    }
    if (semctl(current_sem_id, 0, GETVAL) != (int)seminfo.semvmx) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = (short)seminfo.semvmx;
    if (semop(current_sem_id, sops, 1) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != ERANGE) {
        e(0);
        goto cleanup_sem_id;
    }
    if (semctl(current_sem_id, 0, GETVAL) != (int)seminfo.semvmx) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = SHRT_MAX;
    if (semop(current_sem_id, sops, 1) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != ERANGE) {
        e(0);
        goto cleanup_sem_id;
    }
    if (semctl(current_sem_id, 0, GETVAL) != (int)seminfo.semvmx) {
        e(0);
        goto cleanup_sem_id;
    }

    if (seminfo.semvmx < -(int)SHRT_MIN) {
        sops[0].sem_op = (short)(-seminfo.semvmx - 1);
        if (semop(current_sem_id, sops, 1) != -1) {
            e(0);
            goto cleanup_sem_id;
        }
        if (errno != EAGAIN) {
            e(0);
            goto cleanup_sem_id;
        }
        if (semctl(current_sem_id, 0, GETVAL) != (int)seminfo.semvmx) {
            e(0);
            goto cleanup_sem_id;
        }
    }

    sops[0].sem_op = (short)(-seminfo.semvmx);
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_sem_id;
    }
    if (semctl(current_sem_id, 0, GETVAL) != 0) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = 0;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = 2;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_sem_id;
    }
    if (semctl(current_sem_id, 0, GETVAL) != 2) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = 0;
    if (semop(current_sem_id, sops, 1) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != EAGAIN) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = -3;
    if (semop(current_sem_id, sops, 1) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != EAGAIN) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = 1;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_sem_id;
    }
    if (semctl(current_sem_id, 0, GETVAL) != 3) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = -1;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_sem_id;
    }
    if (semctl(current_sem_id, 0, GETVAL) != 2) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = 0;
    if (semop(current_sem_id, sops, 1) != -1) {
        e(0);
        goto cleanup_sem_id;
    }
    if (errno != EAGAIN) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = -2;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_sem_id;
    }
    if (semctl(current_sem_id, 0, GETVAL) != 0) {
        e(0);
        goto cleanup_sem_id;
    }

    sops[0].sem_op = 0;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_sem_id;
    }

    struct sembuf *sops_invalid_read_test = ((struct sembuf *)bad_ptr) - 1;
    sops_invalid_read_test->sem_op = 0;
    sops_invalid_read_test--;
    if (semop(current_sem_id, sops_invalid_read_test, 2) != 0) {
        e(0);
        goto cleanup_sem_id;
    }

    if (semctl(current_sem_id, 0, IPC_RMID) != 0) {
        e(0);
        goto cleanup_sem_id;
    }
    current_sem_id = -1;

    if (semop(current_sem_id, NULL, 0) != -1) {
        e(0);
        goto cleanup_sops;
    }
    if (errno != EINVAL) {
        e(0);
        goto cleanup_sops;
    }

    if (semop(-1, NULL, 0) != -1) {
        e(0);
        goto cleanup_sops;
    }
    if (errno != EINVAL) {
        e(0);
        goto cleanup_sops;
    }

    if (semop(INT_MIN, NULL, 0) != -1) {
        e(0);
        goto cleanup_sops;
    }
    if (errno != EINVAL) {
        e(0);
        goto cleanup_sops;
    }

    memset(&semds, 0, sizeof(semds));
    int invalid_id_gen = IXSEQ_TO_IPCID(seminfo.semmni, semds.sem_perm);
    if (semop(invalid_id_gen, NULL, 0) != -1) {
        e(0);
        goto cleanup_sops;
    }
    if (errno != EINVAL) {
        e(0);
        goto cleanup_sops;
    }

    test_perm(test88b_perm, 0 /*owner_test*/);

    current_sem_id = semget(IPC_PRIVATE, 3, 0600);
    if (current_sem_id == -1) {
        e(0);
        goto cleanup_sops;
    }

    memset(sops, 0, sizeof(sops[0]));
    sops[0].sem_op = 1;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_sem_id;
    }

    TEST_SEM(current_sem_id, 0, 1, getpid(), 0, 0);

    spawn(&child, test88b_child, DROP_NONE);
    if (child.pid == 0) {
        e(0);
        goto cleanup_sem_id;
    }

    snd(&child, CMD_CHILD_SEND_SEMID);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 1, getpid(), 0, 1);

    sops[0].sem_op = -1;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_child;
    }

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, child.pid, 0, 0);

    sops[0].sem_op = 1;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 1, getpid(), 0, 0);

    snd(&child, CMD_CHILD_1);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 1, getpid(), 1, 0);

    sops[0].sem_op = 1;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_child;
    }

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 2, getpid(), 1, 0);

    sops[0].sem_op = 1;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_child;
    }

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, child.pid, 0, 0);

    memset(sops, 0, sizeof(sops[0]) * 2);
    sops[0].sem_num = 0;
    sops[0].sem_op = 0;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_child;
    }

    snd(&child, CMD_CHILD_2);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, getpid(), 0, 0);
    TEST_SEM(current_sem_id, 1, 0, 0, 1, 0);
    TEST_SEM(current_sem_id, 2, 0, 0, 0, 0);

    sops[0].sem_num = 1;
    sops[0].sem_op = 1;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_child;
    }

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 1, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 1, 0, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 2, 2, child.pid, 0, 0);

    snd(&child, CMD_CHILD_3);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 1, child.pid, 0, 1);
    TEST_SEM(current_sem_id, 1, 0, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 2, 2, child.pid, 0, 0);

    sops[0].sem_num = 0;
    sops[0].sem_op = -1;
    sops[1].sem_num = 2;
    sops[1].sem_op = -2;
    if (semop(current_sem_id, sops, 2) != 0) {
        e(0);
        goto cleanup_child;
    }

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 1, 1, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 2, 1, child.pid, 0, 0);

    snd(&child, CMD_CHILD_4);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 1, 1, child.pid, 1, 0);
    TEST_SEM(current_sem_id, 2, 1, child.pid, 0, 0);

    sops[0].sem_num = 1;
    sops[0].sem_op = 1;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_child;
    }

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 1, 2, getpid(), 0, 0);
    TEST_SEM(current_sem_id, 2, 1, child.pid, 0, 1);

    sops[0].sem_num = 2;
    sops[0].sem_op = -1;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_child;
    }

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 1, 0, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 2, 0, child.pid, 0, 0);

    sops[0].sem_num = 0;
    sops[0].sem_op = 0;
    sops[0].sem_flg = 0;
    sops[1].sem_num = 1;
    sops[1].sem_op = 0;
    sops[1].sem_flg = 0;
    if (semop(current_sem_id, sops, 2) != 0) {
        e(0);
        goto cleanup_child;
    }

    snd(&child, CMD_CHILD_5);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, getpid(), 1, 0);
    TEST_SEM(current_sem_id, 1, 0, getpid(), 0, 0);

    sops[0].sem_num = 0;
    sops[0].sem_op = 1;
    sops[1].sem_num = 1;
    sops[1].sem_op = 1;
    if (semop(current_sem_id, sops, 2) != 0) {
        e(0);
        goto cleanup_child;
    }

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 1, 0, child.pid, 0, 0);

    sops[0].sem_num = 0;
    sops[0].sem_op = 1;
    sops[1].sem_num = 1;
    sops[1].sem_op = 1;
    if (semop(current_sem_id, sops, 2) != 0) {
        e(0);
        goto cleanup_child;
    }

    snd(&child, CMD_CHILD_6);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 1, getpid(), 0, 0);
    TEST_SEM(current_sem_id, 1, 1, getpid(), 0, 1);

    sops[0].sem_num = 1;
    sops[0].sem_op = -1;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_child;
    }

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 1, getpid(), 0, 0);
    TEST_SEM(current_sem_id, 1, 0, getpid(), 0, 0);

    sops[0].sem_num = 0;
    sops[0].sem_op = 0;
    sops[1].sem_num = 4;
    sops[1].sem_op = 0;
    if (semop(current_sem_id, sops, 2) != -1) {
        e(0);
        goto cleanup_child;
    }
    if (errno != EFBIG) {
        e(0);
        goto cleanup_child;
    }

    sops[0].sem_num = 1;
    sops[0].sem_op = (short)seminfo.semvmx;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_child;
    }

    snd(&child, CMD_CHILD_7);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 1, getpid(), 0, 1);
    TEST_SEM(current_sem_id, 1, (int)seminfo.semvmx, getpid(), 0, 0);

    sops[0].sem_num = 0;
    sops[0].sem_op = -1;
    sops[1].sem_num = 1;
    sops[1].sem_op = -1;
    if (semop(current_sem_id, sops, 2) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 0, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 1, (int)seminfo.semvmx, child.pid, 0, 0);

    sops[0].sem_num = 1;
    sops[0].sem_op = -2;
    if (semop(current_sem_id, sops, 1) != 0) {
        e(0);
        goto cleanup_child;
    }

    snd(&child, CMD_CHILD_8);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, child.pid, 1, 0);
    TEST_SEM(current_sem_id, 1, (int)seminfo.semvmx - 2, getpid(), 0, 0);

    sops[0].sem_num = 0;
    sops[0].sem_op = 1;
    sops[1].sem_num = 1;
    sops[1].sem_op = 1;
    if (semop(current_sem_id, sops, 2) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 1, getpid(), 0, 0);
    TEST_SEM(current_sem_id, 1, (int)seminfo.semvmx - 1, getpid(), 0, 0);

    sops[0].sem_num = 0;
    sops[0].sem_op = (short)(seminfo.semvmx - 1);
    sops[1].sem_num = 0;
    sops[1].sem_op = (short)(seminfo.semvmx - 1);
    sops[2].sem_num = 0;
    sops[2].sem_op = 2;
    if (semop(current_sem_id, sops, 3) != -1) {
        e(0);
        goto cleanup_child;
    }
    if (errno != ERANGE) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 1, getpid(), 0, 0);

    if (semctl(current_sem_id, 1, SETVAL, 0) != 0) {
        e(0);
        goto cleanup_child;
    }
    sops[0].sem_num = 0;
    sops[0].sem_op = -1;
    sops[1].sem_num = 1;
    sops[1].sem_op = 1;
    if (semop(current_sem_id, sops, 2) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 0, getpid(), 0, 0);
    TEST_SEM(current_sem_id, 1, 1, getpid(), 0, 0);

    snd(&child, CMD_CHILD_9);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, getpid(), 0, 0);
    TEST_SEM(current_sem_id, 1, 1, getpid(), 0, 1);

    kill(child.pid, SIGHUP);

    snd(&child, CMD_CHILD_10);

    usleep(WAIT_USECS);

    if (semctl(current_sem_id, 0, IPC_RMID) != 0) {
        e(0);
        goto cleanup_child;
    }
    current_sem_id = -1;

    current_sem_id = semget(IPC_PRIVATE, 2, 0600);
    if (current_sem_id == -1) {
        e(0);
        goto cleanup_child;
    }

    snd(&child, CMD_CHILD_SEND_SEMID);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, 0, 1, 0);
    TEST_SEM(current_sem_id, 1, 0, 0, 0, 0);
    if (semctl(current_sem_id, 0, IPC_STAT, &semds) != 0) {
        e(0);
        goto cleanup_child;
    }
    if (semds.sem_otime != 0) {
        e(0);
        goto cleanup_child;
    }

    if (semctl(current_sem_id, 1, SETVAL, (int)seminfo.semvmx) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 0, 0, 1, 0);
    TEST_SEM(current_sem_id, 1, (int)seminfo.semvmx, 0, 0, 0);
    if (semctl(current_sem_id, 0, IPC_STAT, &semds) != 0) {
        e(0);
        goto cleanup_child;
    }
    if (semds.sem_otime != 0) {
        e(0);
        goto cleanup_child;
    }

    if (semctl(current_sem_id, 0, SETVAL, 1) != 0) {
        e(0);
        goto cleanup_child;
    }
    TEST_SEM(current_sem_id, 0, 1, 0, 0, 0);
    TEST_SEM(current_sem_id, 1, (int)seminfo.semvmx, 0, 0, 0);

    if (semctl(current_sem_id, 0, SETVAL, 0) != 0) {
        e(0);
        goto cleanup_child;
    }

    snd(&child, CMD_CHILD_11);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, 0, 0, 0);
    TEST_SEM(current_sem_id, 1, (int)seminfo.semvmx, 0, 0, 1);
    if (semctl(current_sem_id, 0, IPC_STAT, &semds) != 0) {
        e(0);
        goto cleanup_child;
    }
    if (semds.sem_otime != 0) {
        e(0);
        goto cleanup_child;
    }

    if (semctl(current_sem_id, 1, SETVAL, 0) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 0, 0, 1, 0);
    TEST_SEM(current_sem_id, 1, 0, 0, 0, 0);
    if (semctl(current_sem_id, 0, IPC_STAT, &semds) != 0) {
        e(0);
        goto cleanup_child;
    }
    if (semds.sem_otime != 0) {
        e(0);
        goto cleanup_child;
    }

    time(&now);
    if (semctl(current_sem_id, 0, SETVAL, 2) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 1, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 1, 0, child.pid, 0, 0);
    if (semctl(current_sem_id, 0, IPC_STAT, &semds) != 0) {
        e(0);
        goto cleanup_child;
    }
    if (semds.sem_otime < now || semds.sem_otime >= now + 10) {
        e(0);
        goto cleanup_child;
    }

    if (semctl(current_sem_id, 0, IPC_RMID) != 0) {
        e(0);
        goto cleanup_child;
    }
    current_sem_id = -1;

    current_sem_id = semget(IPC_PRIVATE, 2, 0600);
    if (current_sem_id == -1) {
        e(0);
        goto cleanup_child;
    }

    snd(&child, CMD_CHILD_SEND_SEMID);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, 0, 1, 0);
    TEST_SEM(current_sem_id, 1, 0, 0, 0, 0);

    val[0] = 1;
    val[1] = 1;
    if (semctl(current_sem_id, 0, SETALL, val) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 1, 0, 0, 0);
    TEST_SEM(current_sem_id, 1, 1, 0, 0, 1);

    val[0] = 0;
    val[1] = 1;
    if (semctl(current_sem_id, 0, SETALL, val) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 0, 0, 1, 0);
    TEST_SEM(current_sem_id, 1, 1, 0, 0, 0);

    val[0] = 1;
    val[1] = 1;
    if (semctl(current_sem_id, 0, SETALL, val) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 1, 0, 0, 0);
    TEST_SEM(current_sem_id, 1, 1, 0, 0, 1);

    val[0] = 0;
    val[1] = 0;
    if (semctl(current_sem_id, 0, SETALL, val) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 0, 0, 1, 0);
    TEST_SEM(current_sem_id, 1, 0, 0, 0, 0);
    if (semctl(current_sem_id, 0, IPC_STAT, &semds) != 0) {
        e(0);
        goto cleanup_child;
    }
    if (semds.sem_otime != 0) {
        e(0);
        goto cleanup_child;
    }

    time(&now);
    val[0] = 1;
    val[1] = 0;
    if (semctl(current_sem_id, 0, SETALL, val) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 0, child.pid, 0, 0);
    TEST_SEM(current_sem_id, 1, 0, child.pid, 0, 0);
    if (semctl(current_sem_id, 0, IPC_STAT, &semds) != 0) {
        e(0);
        goto cleanup_child;
    }
    if (semds.sem_otime < now || semds.sem_otime >= now + 10) {
        e(0);
        goto cleanup_child;
    }

    sops[0].sem_num = 0;
    sops[0].sem_op = 0;
    sops[0].sem_flg = 0;
    sops[1].sem_num = 1;
    sops[1].sem_op = 0;
    sops[1].sem_flg = 0;
    if (semop(current_sem_id, sops, 2) != 0) {
        e(0);
        goto cleanup_child;
    }

    TEST_SEM(current_sem_id, 0, 0, getpid(), 0, 0);
    TEST_SEM(current_sem_id, 1, 0, getpid(), 0, 0);

    if (rcv(&child) != 0) {
        e(0);
        goto cleanup_child;
    }

    snd(&child, CMD_CHILD_12);

    usleep(WAIT_USECS);

    TEST_SEM(current_sem_id, 0, 0, getpid(), 0, 0);
    TEST_SEM(current_sem_id, 1, 0, getpid(), 1, 0);

    terminate(&child);
    child.pid = 0;

    TEST_SEM(current_sem_id, 0, 0, getpid(), 0, 0);
    TEST_SEM(current_sem_id, 1, 0, getpid(), 0, 0);

    if (semctl(current_sem_id, 0, IPC_RMID) != 0) {
        e(0);
        goto cleanup_sops;
    }
    current_sem_id = -1;

    goto cleanup_sops;
}

/*
 * Test semctl(2) permission checks, part 1: regular commands.
 */
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/sem.h>

extern void e(int);
extern int rcv(struct link * parent);
extern void snd(struct link * parent, int val);
struct link; 
#ifndef __arraycount
#define __arraycount(a) (sizeof(a) / sizeof((a)[0]))
#endif

#define READ_PERM_BIT  4
#define WRITE_PERM_BIT 2

#ifndef IPCID_TO_IX
#define IPCID_TO_IX(id)		((id) & 0xffff)
#endif

static void check_semctl_no_arg(int id, int cmd, int tbit, int permission_bit) {
    int r = semctl(id, 0, cmd);
    if (r == -1 && errno != EACCES) {
        e(0);
    }
    if (((permission_bit & tbit) == permission_bit) != (r != -1)) {
        e(0);
    }
}

static void check_semctl_int_arg(int id, int cmd, int val_arg, int tbit, int permission_bit) {
    int r = semctl(id, 0, cmd, val_arg);
    if (r == -1 && errno != EACCES) {
        e(0);
    }
    if (((permission_bit & tbit) == permission_bit) != (r != -1)) {
        e(0);
    }
}

static void check_semctl_ptr_arg(int id, int cmd, void *ptr_arg, int tbit, int permission_bit) {
    int r = semctl(id, 0, cmd, ptr_arg);
    if (r == -1 && errno != EACCES) {
        e(0);
    }
    if (((permission_bit & tbit) == permission_bit) != (r != -1)) {
        e(0);
    }
}

static void check_semctl_must_fail_eacces_no_arg(int id, int cmd) {
    if (semctl(id, 0, cmd) != -1) {
        e(0);
    }
    if (errno != EACCES) {
        e(0);
    }
}

static void check_semctl_must_fail_eacces_int_arg(int id, int cmd, int val_arg) {
    if (semctl(id, 0, cmd, val_arg) != -1) {
        e(0);
    }
    if (errno != EACCES) {
        e(0);
    }
}

static void check_semctl_must_fail_eacces_ptr_arg(int id, int cmd, void *ptr_arg) {
    if (semctl(id, 0, cmd, ptr_arg) != -1) {
        e(0);
    }
    if (errno != EACCES) {
        e(0);
    }
}

static void check_semctl_always_succeed(int id, int cmd, void *ptr_arg) {
    if (semctl(id, 0, cmd, ptr_arg) == -1) {
        e(0);
    }
}

static void
test88c_perm1(struct link * parent)
{
	static const int cmds_no_arg[] = { GETVAL, GETPID, GETNCNT, GETZCNT };
	struct semid_ds semds;
	struct seminfo seminfo;
	unsigned short val[3];
	int i, tbit, id[3], cmd;
	void *ptr;

	while ((tbit = rcv(parent)) != -1) {
		id[0] = rcv(parent);
		id[1] = rcv(parent);
		id[2] = rcv(parent);

		for (i = 0; i < __arraycount(cmds_no_arg); i++) {
			cmd = cmds_no_arg[i];
			check_semctl_no_arg(id[0], cmd, tbit, READ_PERM_BIT);
			check_semctl_no_arg(id[1], cmd, tbit, READ_PERM_BIT);
			check_semctl_must_fail_eacces_no_arg(id[2], cmd);
		}

		check_semctl_int_arg(id[0], SETVAL, 0, tbit, WRITE_PERM_BIT);
		check_semctl_int_arg(id[1], SETVAL, 0, tbit, WRITE_PERM_BIT);
		check_semctl_must_fail_eacces_int_arg(id[2], SETVAL, 0);

		memset(val, 0, sizeof(val));

		for (i = 0; i < 3; i++) {
			int current_perm_bit;
			switch (i) {
			case 0:
				cmd = GETALL;
				ptr = val;
				current_perm_bit = READ_PERM_BIT;
				break;
			case 1:
				cmd = SETALL;
				ptr = val;
				current_perm_bit = WRITE_PERM_BIT;
				break;
			case 2:
				cmd = IPC_STAT;
				ptr = &semds;
				current_perm_bit = READ_PERM_BIT;
				break;
			default:
				abort();
			}

			check_semctl_ptr_arg(id[0], cmd, ptr, tbit, current_perm_bit);
			check_semctl_ptr_arg(id[1], cmd, ptr, tbit, current_perm_bit);
			check_semctl_must_fail_eacces_ptr_arg(id[2], cmd, ptr);
		}

		check_semctl_ptr_arg(IPCID_TO_IX(id[0]), SEM_STAT, &semds, tbit, READ_PERM_BIT);
		check_semctl_ptr_arg(IPCID_TO_IX(id[1]), SEM_STAT, &semds, tbit, READ_PERM_BIT);
		check_semctl_must_fail_eacces_ptr_arg(IPCID_TO_IX(id[2]), SEM_STAT, &semds);

		check_semctl_always_succeed(0, IPC_INFO, &seminfo);
		check_semctl_always_succeed(0, SEM_INFO, &seminfo);

		snd(parent, 0);
	}
}

/*
 * Test semctl(2) permission checks, part 2: the IPC_SET command.
 */
#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <string.h>
#include <errno.h>

// Forward declarations for external functions and types.
// These are assumed to be defined elsewhere in the project or included via a header.
// struct link;
// extern int rcv(struct link *parent);
// extern void snd(struct link *parent, int value);
// extern void e(int error_code); // Custom error handling function.

// Helper function to encapsulate the semctl IPC_SET call and its specific error/test logic.
// This improves maintainability by removing code duplication and centralizing the logic.
static void perform_semctl_set_perm(int sem_id, int shift_value, const struct semid_ds *sem_ds_config) {
    // Perform the semctl operation. The '0' indicates the semaphore number within the set.
    // For IPC_SET, the struct semid_ds pointed to by sem_ds_config contains the new permissions.
    // Note: While the `semctl` man page typically references `union semun` for the fourth argument,
    // many systems allow direct passing of `struct semid_ds *` for `IPC_SET` as done here,
    // which aligns with the original code's behavior.
    int result = semctl(sem_id, 0, IPC_SET, (struct semid_ds *)sem_ds_config);

    // Original error handling logic:
    // `if (r < 0 && (r != -1 || errno != EPERM)) e(0);`
    // This condition checks for two types of unexpected errors:
    // 1. `result == -1` AND `errno != EPERM`: `semctl` failed with an error other than `EPERM`.
    // 2. `result < -1`: `semctl` returned a negative value that is not -1 (uncommon but handled).
    if ((result == -1 && errno != EPERM) || result < -1) {
        // An unexpected system error occurred (not related to permissions or expected test failure).
        // Trigger the global error handler.
        e(0);
    }

    // Original test assertion logic:
    // `if ((shift == 6) != (r != -1)) e(0);`
    // This checks if the outcome of `semctl` matches the expected behavior for the current `shift_value`.
    // - If `shift_value` is 6, `semctl` is expected to fail (`result == -1`).
    // - If `shift_value` is not 6, `semctl` is expected to succeed (`result != -1`).
    // If the actual result does not match the expectation, it indicates a test failure.
    if ((shift_value == 6) != (result != -1)) {
        // The test condition failed. The semctl call did not behave as expected.
        e(0);
    }
}

static void
test88c_perm2(struct link * parent)
{
    // struct semid_ds holds semaphore set information, including permissions (sem_perm).
    // The original code's intent was to set permissions to all-zeroes (mode 0000, uid 0, gid 0).
    // Initializing the entire structure to zero achieves this effectively.
    struct semid_ds semds_config;
    int shift_value; // Represents a test condition or state, determines expected outcome.
    int sem_ids[3];  // Array to hold semaphore set identifiers.
    const int num_sem_ids = sizeof(sem_ids) / sizeof(sem_ids[0]);

    // Initialize the configuration structure once.
    // This ensures sem_perm.uid, sem_perm.gid, sem_perm.mode (and other fields) are all set to 0.
    memset(&semds_config, 0, sizeof(semds_config));

    // Loop until the parent signals termination by sending -1.
    while ((shift_value = rcv(parent)) != -1) {
        // Receive all semaphore IDs for the current test iteration.
        // The original code implicitly assumed rcv() would succeed and return valid IDs.
        for (int i = 0; i < num_sem_ids; ++i) {
            sem_ids[i] = rcv(parent);
            // No explicit error handling for rcv() is in the original code, preserving this behavior.
            // If rcv() could fail in other ways (e.g., return < 0 and not -1 for termination),
            // additional checks might be necessary for robustness.
        }

        // Apply the IPC_SET operation to all semaphore sets.
        // This loop replaces the repetitive calls in the original code, improving maintainability.
        for (int i = 0; i < num_sem_ids; ++i) {
            perform_semctl_set_perm(sem_ids[i], shift_value, &semds_config);
        }

        // Send a signal back to the parent, indicating completion of this iteration.
        snd(parent, 0);
    }
}

/*
 * Test semctl(2) permission checks, part 3: the IPC_RMID command.
 */
static void handle_semaphore_removal_and_check(int sem_id, int shift_val) {
    int r = semctl(sem_id, 0, IPC_RMID);

    if (r == -1 && errno != EPERM) {
        e(0);
    }

    if ((shift_val == 6) != (r != -1)) {
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

		handle_semaphore_removal_and_check(id[0], shift);
		handle_semaphore_removal_and_check(id[1], shift);
		handle_semaphore_removal_and_check(id[2], shift);

		snd(parent, 0);
	}
}

/*
 * Test the basic semctl(2) functionality.
 */
static int handle_semctl_error(const char *func, int line, int expected_errno) {
    if (errno != expected_errno) {
        e(0); /* Original error handling, implies exit or assert */
    }
    return -1;
}

#define CHECK_SEMCTL_ERROR(ret_val, expected_errno) \
    do { \
        if ((ret_val) == -1) { \
            if (handle_semctl_error(__func__, __LINE__, expected_errno) == -1) { \
                /* Original 'e(0)' implies termination. \
                 * If the function continues, consider returning an error code. */ \
            } \
        } else { \
            e(0); /* Should have failed, but didn't */ \
        } \
    } while(0)

#define CHECK_SEMCTL_SUCCESS(ret_val) \
    do { \
        if ((ret_val) == -1) { \
            e(0); /* Expected success, but failed */ \
        } \
    } while(0)

static void check_sem_not_updated(int id, time_t expected_ctime) {
    struct semid_ds semds;
    CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_STAT, &semds));
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime >= expected_ctime) e(0);
}

static void check_sem_updated(int id, time_t old_ctime) {
    struct semid_ds semds;
    CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_STAT, &semds));
    if (semds.sem_otime != 0) e(0);
    if (semds.sem_ctime < old_ctime || semds.sem_ctime >= old_ctime + 10) e(0);
}

static void test_invalid_sem_access(int id, int semnum, int cmd) {
    CHECK_SEMCTL_ERROR(semctl(id, semnum, cmd), EINVAL);
}

static void test_invalid_id_access(int id, int cmd) {
    CHECK_SEMCTL_ERROR(semctl(id, 0, cmd), EINVAL);
}

static void test_invalid_ptr_access(int id, int cmd, void *ptr, int expected_errno) {
    CHECK_SEMCTL_ERROR(semctl(id, 0, cmd, ptr), expected_errno);
}

static void test_semctl_commands(int id, int badid1, int badid2, time_t now, const struct seminfo *seminfo) {
    static const int cmds[] = { GETVAL, GETPID, GETNCNT, GETZCNT };
    struct semid_ds semds;
    unsigned int i, j;

    for (i = 0; i < __arraycount(cmds); i++) {
        int cmd = cmds[i];
        for (j = 0; j < 3; j++) {
            CHECK_SEMCTL_SUCCESS(semctl(id, j, cmd));
        }

        test_invalid_id_access(badid1, cmd);
        test_invalid_id_access(badid2, cmd);
        test_invalid_id_access(-1, cmd);
        test_invalid_id_access(INT_MIN, cmd);

        test_invalid_sem_access(id, -1, cmd);
        test_invalid_sem_access(id, 3, cmd);

        check_sem_not_updated(id, now);
    }
}

static void test_getall_command(int id, int badid1, int badid2, time_t now, const struct seminfo *seminfo) {
    unsigned short val[4];
    unsigned int i, j;

    for (j = 0; j < 5; j++) {
        for (i = 0; i < __arraycount(val); i++) {
            val[i] = USHRT_MAX;
        }
        CHECK_SEMCTL_SUCCESS(semctl(id, (int)j - 1, GETALL, val));
        for (i = 0; i < 3; i++) {
            if (val[i] != 0) e(0);
        }
        if (val[i] != USHRT_MAX) e(0);
    }

    for (i = 0; i < __arraycount(val); i++) {
        val[i] = USHRT_MAX;
    }

    test_invalid_id_access(badid1, GETALL);
    test_invalid_id_access(badid2, GETALL);
    test_invalid_id_access(-1, GETALL);
    test_invalid_id_access(INT_MIN, GETALL);

    for (i = 0; i < __arraycount(val); i++) {
        if (val[i] != USHRT_MAX) e(0);
    }

    test_invalid_ptr_access(id, GETALL, NULL, EFAULT);
    test_invalid_ptr_access(id, GETALL, bad_ptr, EFAULT);
    test_invalid_ptr_access(id, GETALL, ((unsigned short *)bad_ptr) - 2, EFAULT);

    CHECK_SEMCTL_SUCCESS(semctl(id, 0, GETALL, ((unsigned short *)bad_ptr) - 3));

    check_sem_not_updated(id, now);
}

static void test_ipc_stat_command(int id, int badid1, int badid2, time_t now) {
    struct semid_ds semds;
    char statbuf[sizeof(struct semid_ds) + 1];
    unsigned int i;

    memset(statbuf, 0x5a, sizeof(statbuf));

    test_invalid_id_access(badid1, IPC_STAT);
    test_invalid_id_access(badid2, IPC_STAT);
    test_invalid_id_access(-1, IPC_STAT);
    test_invalid_id_access(INT_MIN, IPC_STAT);

    for (i = 0; i < sizeof(statbuf); i++) {
        if (statbuf[i] != 0x5a) e(0);
    }

    CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_STAT, statbuf));
    if (statbuf[sizeof(statbuf) - 1] != 0x5a) e(0);

    test_invalid_ptr_access(id, IPC_STAT, NULL, EFAULT);
    test_invalid_ptr_access(id, IPC_STAT, bad_ptr, EFAULT);
    CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_STAT, ((struct semid_ds *)bad_ptr) - 1));

    CHECK_SEMCTL_SUCCESS(semctl(id, -1, IPC_STAT, &semds));
    check_sem_not_updated(id, now);
}

static void test_sem_stat_command(int id, int id2, const struct seminfo *seminfo) {
    struct semid_ds semds;
    char statbuf[sizeof(struct semid_ds) + 1];
    unsigned short seen[2];
    unsigned int i;
    int r;

    memset(statbuf, 0x5a, sizeof(statbuf));

    test_invalid_id_access(-1, SEM_STAT);
    test_invalid_id_access(seminfo->semmni, SEM_STAT);

    for (i = 0; i < sizeof(statbuf); i++) {
        if (statbuf[i] != 0x5a) e(0);
    }

    memset(seen, 0, sizeof(seen));

    for (i = 0; i < seminfo->semmni; i++) {
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

            test_invalid_ptr_access(i, SEM_STAT, NULL, EFAULT);
            test_invalid_ptr_access(i, SEM_STAT, bad_ptr, EFAULT);
        } else if (r == id2) {
            seen[1]++;
            if (semds.sem_perm.mode != (SEM_ALLOC | 0642)) e(0);
            if (semds.sem_perm.uid != geteuid()) e(0);
            if (semds.sem_perm.gid != getegid()) e(0);
            if (semds.sem_perm.cuid != semds.sem_perm.uid) e(0);
            if (semds.sem_perm.cgid != semds.sem_perm.gid) e(0);
            if (semds.sem_perm._key != KEY_A) e(0);
            if (semds.sem_nsems != seminfo->semmsl) e(0);
        }
    }

    if (seen[0] != 1) e(0);
    if (seen[1] != 1) e(0);
    if (statbuf[sizeof(statbuf) - 1] != 0x5a) e(0);
}

static void test_setval_command(int id, int badid1, int badid2, time_t *now_ptr, const struct seminfo *seminfo) {
    struct semid_ds semds;
    unsigned short val[3];

    test_invalid_id_access(badid1, SETVAL);
    test_invalid_id_access(badid2, SETVAL);
    test_invalid_id_access(-1, SETVAL);
    test_invalid_id_access(INT_MIN, SETVAL);

    test_invalid_sem_access(id, -1, SETVAL);
    test_invalid_sem_access(id, 3, SETVAL);

    CHECK_SEMCTL_ERROR(semctl(id, 0, SETVAL, -1), ERANGE);
    CHECK_SEMCTL_ERROR(semctl(id, 0, SETVAL, seminfo->semvmx + 1), ERANGE);

    TEST_SEM(id, 0, 0, 0, 0, 0);
    check_sem_not_updated(id, *now_ptr);

    CHECK_SEMCTL_SUCCESS(semctl(id, 1, SETVAL, 0));
    check_sem_updated(id, *now_ptr);
    TEST_SEM(id, 1, 0, 0, 0, 0);

    CHECK_SEMCTL_SUCCESS(semctl(id, 2, SETVAL, seminfo->semvmx));
    TEST_SEM(id, 2, seminfo->semvmx, 0, 0, 0);

    CHECK_SEMCTL_SUCCESS(semctl(id, 0, SETVAL, 1));
    TEST_SEM(id, 0, 1, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, seminfo->semvmx, 0, 0, 0);

    CHECK_SEMCTL_SUCCESS(semctl(id, 0, GETALL, val));
    if (val[0] != 1) e(0);
    if (val[1] != 0) e(0);
    if (val[2] != seminfo->semvmx) e(0);

    CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_STAT, &semds));
    while (time(now_ptr) == semds.sem_ctime)
        usleep(250000);
}

static void test_setall_command(int id, int badid1, int badid2, time_t *now_ptr, const struct seminfo *seminfo) {
    struct semid_ds semds;
    unsigned short val[3];

    test_invalid_id_access(badid1, SETALL);
    test_invalid_id_access(badid2, SETALL);
    test_invalid_id_access(-1, SETALL);
    test_invalid_id_access(INT_MIN, SETALL);

    val[0] = seminfo->semvmx + 1;
    val[1] = 0;
    val[2] = 0;
    CHECK_SEMCTL_ERROR(semctl(id, 0, SETALL, val), ERANGE);

    val[0] = 0;
    val[1] = 1;
    val[2] = seminfo->semvmx + 1;
    CHECK_SEMCTL_ERROR(semctl(id, 0, SETALL, val), ERANGE);

    test_invalid_ptr_access(id, SETALL, NULL, EFAULT);
    test_invalid_ptr_access(id, SETALL, bad_ptr, EFAULT);
    test_invalid_ptr_access(id, SETALL, ((unsigned short *)bad_ptr) - 2, EFAULT);

    TEST_SEM(id, 0, 1, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, seminfo->semvmx, 0, 0, 0);

    check_sem_not_updated(id, *now_ptr);

    val[0] = seminfo->semvmx;
    val[1] = 0;
    val[2] = 0;
    CHECK_SEMCTL_SUCCESS(semctl(id, 0, SETALL, val));
    check_sem_updated(id, *now_ptr);

    TEST_SEM(id, 0, seminfo->semvmx, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, 0, 0, 0, 0);

    val[0] = 0;
    val[1] = 1;
    val[2] = seminfo->semvmx;
    CHECK_SEMCTL_SUCCESS(semctl(id, INT_MAX, SETALL, val));

    TEST_SEM(id, 0, 0, 0, 0, 0);
    TEST_SEM(id, 1, 1, 0, 0, 0);
    TEST_SEM(id, 2, seminfo->semvmx, 0, 0, 0);

    memset(page_ptr, 0, page_size);
    CHECK_SEMCTL_SUCCESS(semctl(id, 0, SETALL, ((unsigned short *)bad_ptr) - 3));

    TEST_SEM(id, 0, 0, 0, 0, 0);
    TEST_SEM(id, 1, 0, 0, 0, 0);
    TEST_SEM(id, 2, 0, 0, 0, 0);

    CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_STAT, &semds));
    while (time(now_ptr) == semds.sem_ctime)
        usleep(250000);
}

static void test_ipc_set_command(int id, int badid1, int badid2, time_t *now_ptr) {
    struct semid_ds semds, osemds;
    unsigned int i;

    test_invalid_id_access(badid1, IPC_SET);
    test_invalid_id_access(badid2, IPC_SET);
    test_invalid_id_access(-1, IPC_SET);
    test_invalid_id_access(INT_MIN, IPC_SET);

    test_invalid_ptr_access(id, IPC_SET, NULL, EFAULT);
    test_invalid_ptr_access(id, IPC_SET, bad_ptr, EFAULT);

    CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_STAT, &osemds));
    check_sem_not_updated(id, *now_ptr);

    memset(&semds, 0x5b, sizeof(semds));
    semds.sem_perm.mode = 0712;
    semds.sem_perm.uid = UID_MAX;
    semds.sem_perm.gid = GID_MAX - 1;
    CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_SET, &semds));

    CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_STAT, &semds));
    if (semds.sem_perm.mode != (SEM_ALLOC | 0712)) e(0);
    if (semds.sem_perm.uid != UID_MAX) e(0);
    if (semds.sem_perm.gid != GID_MAX - 1) e(0);
    if (semds.sem_perm.cuid != osemds.sem_perm.cuid) e(0);
    if (semds.sem_perm.cgid != osemds.sem_perm.cgid) e(0);
    if (semds.sem_perm._seq != osemds.sem_perm._seq) e(0);
    if (semds.sem_perm._key != osemds.sem_perm._key) e(0);
    if (semds.sem_nsems != osemds.sem_nsems) e(0);
    if (semds.sem_otime != osemds.sem_otime) e(0);
    if (semds.sem_ctime < *now_ptr || semds.sem_ctime >= *now_ptr + 10) e(0);

    semds.sem_perm.uid = osemds.sem_perm.uid;
    semds.sem_perm.gid = osemds.sem_perm.gid;
    for (i = 0; i < 0777; i++) {
        semds.sem_perm.mode = i;
        CHECK_SEMCTL_SUCCESS(semctl(id, i / 2 - 1, IPC_SET, &semds));
        CHECK_SEMCTL_SUCCESS(semctl(id, i / 2 - 2, IPC_STAT, &semds));
        if (semds.sem_perm.mode != (SEM_ALLOC | i)) e(0);

        semds.sem_perm.mode = ~0777 | i;
        CHECK_SEMCTL_SUCCESS(semctl(id, i / 2 - 3, IPC_SET, &semds));
        CHECK_SEMCTL_SUCCESS(semctl(id, i / 2 - 4, IPC_STAT, &semds));
        if (semds.sem_perm.mode != (SEM_ALLOC | i)) e(0);
    }
    if (semds.sem_perm.uid != osemds.sem_perm.uid) e(0);
    if (semds.sem_perm.gid != osemds.sem_perm.gid) e(0);

    CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_SET, ((struct semid_ds *)bad_ptr) - 1));
}

static void test_ipc_rmid_command(int id, int id2, int badid1, int badid2) {
    struct semid_ds semds;

    test_invalid_id_access(badid1, IPC_RMID);
    test_invalid_id_access(badid2, IPC_RMID);
    test_invalid_id_access(-1, IPC_RMID);
    test_invalid_id_access(INT_MIN, IPC_RMID);

    CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_RMID));
    test_invalid_id_access(id, IPC_RMID);
    test_invalid_id_access(id, IPC_STAT);

    CHECK_SEMCTL_SUCCESS(semctl(id2, 1, IPC_RMID));
    test_invalid_id_access(id2, IPC_RMID);
}

static void test_ipc_info_sem_info_commands(int *id_ptr, int *id2_ptr, const struct seminfo *seminfo_initial) {
    struct seminfo seminfo;
    unsigned int i;
    int cmd;
    int r;
    int id = *id_ptr;
    int id2 = *id2_ptr;

    if ((id = semget(IPC_PRIVATE, 3, 0600)) == -1) e(0);
    if ((id2 = semget(IPC_PRIVATE, 1, 0600)) == -1) e(0);
    *id_ptr = id;
    *id2_ptr = id2;

    for (i = 0; i <= 1; i++) {
        cmd = (i == 0) ? IPC_INFO : SEM_INFO;

        memset(&seminfo, 0xff, sizeof(seminfo));

        CHECK_SEMCTL_SUCCESS(semctl(0, 0, cmd, &seminfo));

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

        CHECK_SEMCTL_SUCCESS(semctl(INT_MAX, -1, cmd, &seminfo));
        CHECK_SEMCTL_SUCCESS(semctl(-1, INT_MAX, cmd, &seminfo));

        test_invalid_ptr_access(0, cmd, NULL, EFAULT);
        test_invalid_ptr_access(0, cmd, bad_ptr, EFAULT);
        CHECK_SEMCTL_SUCCESS(semctl(0, 0, cmd, ((struct seminfo *)bad_ptr) - 1));
    }
}


static void
test88c(void)
{
	struct seminfo seminfo_initial;
	struct semid_ds semds, osemds;
	time_t now;
	int id, id2, badid1, badid2;

	subtest = 2;

	CHECK_SEMCTL_SUCCESS(semctl(0, 0, IPC_INFO, &seminfo_initial));

	test_perm(test88c_perm1, 0);
	test_perm(test88c_perm2, 1);
	test_perm(test88c_perm3, 1);

	if ((badid1 = semget(IPC_PRIVATE, 1, 0600)) < 0) e(0);
	CHECK_SEMCTL_SUCCESS(semctl(badid1, 0, IPC_RMID));

	memset(&semds, 0, sizeof(semds));
	badid2 = IXSEQ_TO_IPCID(seminfo_initial.semmni, semds.sem_perm);

	if ((id = semget(IPC_PRIVATE, 3, IPC_CREAT | 0600)) < 0) e(0);

	CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_STAT, &semds));
	if (semds.sem_otime != 0) e(0);
	if (semds.sem_ctime == 0) e(0);

	while (time(&now) == semds.sem_ctime)
		usleep(250000);

	test_semctl_commands(id, badid1, badid2, now, &seminfo_initial);
	test_getall_command(id, badid1, badid2, now, &seminfo_initial);
	test_ipc_stat_command(id, badid1, badid2, now);

	if ((id2 = semget(KEY_A, seminfo_initial.semmsl, IPC_CREAT | 0642)) < 0) e(0);
	test_sem_stat_command(id, id2, &seminfo_initial);

	CHECK_SEMCTL_SUCCESS(semctl(id, 5, IPC_STAT, &semds));
	check_sem_not_updated(id, now);

	test_setval_command(id, badid1, badid2, &now, &seminfo_initial);
	test_setall_command(id, badid1, badid2, &now, &seminfo_initial);
	test_ipc_set_command(id, badid1, badid2, &now);
	test_ipc_rmid_command(id, id2, badid1, badid2);

	test_ipc_info_sem_info_commands(&id, &id2, &seminfo_initial);

	CHECK_SEMCTL_SUCCESS(semctl(id2, 0, IPC_RMID));

	test_invalid_id_access(id, INT_MIN);
	test_invalid_id_access(id, INT_MAX);

	CHECK_SEMCTL_SUCCESS(semctl(id, 0, IPC_RMID));
}

/*
 * Test SEM_UNDO support.  Right now this functionality is missing altogether.
 * For now, we test that any attempt to use SEM_UNDO fails.
 */
static void
test88d(void)
{
	struct sembuf semaphore_operation;
	int semaphore_id;

	subtest = 3;

	semaphore_id = semget(IPC_PRIVATE, 1, 0600);
	if (semaphore_id == -1) {
		e(0);
	}

	if (!(SHRT_MAX & SEM_UNDO)) {
		e(0);
	}

	semaphore_operation.sem_num = 0;
	semaphore_operation.sem_op = 1;
	semaphore_operation.sem_flg = SHRT_MAX;

	if (semop(semaphore_id, &semaphore_operation, 1) != -1) {
		e(0);
	}

	if (errno != EINVAL) {
		e(0);
	}

	if (semctl(semaphore_id, 0, IPC_RMID) != 0) {
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
	int child;
	int id;
	int num;

	child = rcv(parent);
	id = rcv(parent);
	num = rcv(parent);

	memset(sops, 0, sizeof(sops));

	sops[2].sem_num = 0;
	sops[2].sem_op = 1;

	switch (child) {
	case 1:
		sops[0].sem_num = num;
		sops[0].sem_op = 1;
		sops[1].sem_num = num;
		sops[1].sem_op = 0;
		break;
	case 2:
		if (semctl(0, 0, IPC_INFO, &seminfo) == -1) {
			e(0);
		}
		sops[0].sem_num = num;
		sops[0].sem_op = -seminfo.semvmx;
		sops[1].sem_num = num;
		sops[1].sem_op = -seminfo.semvmx;
		break;
	default:
		e(0);
	}

	snd(parent, 0);

	if (semop(id, sops, 3) != -1) {
		e(0);
	}
	if (errno != EIDRM) {
		e(0);
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
	}

	snd(parent, 0);

	if (semop(id, sops, nsops) != expect) {
		e(0);
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
	int match;
	int id;
	int expected_semop_return_val;

	match = rcv(parent);
	id = rcv(parent);

	memset(sops, 0, sizeof(sops));

	sops[0].sem_num = 2;
	sops[0].sem_op = -1;
	sops[0].sem_flg = 0;

	nsops = 1;
	expected_semop_return_val = 0;

	switch (match) {
	case MATCH_FIRST:
		sops[1].sem_num = 0;
		sops[1].sem_op = 1;
		sops[1].sem_flg = 0;
		nsops = 2;
		expected_semop_return_val = -1;
		break;
	case MATCH_SECOND:
	case MATCH_KILL:
		break;
	case MATCH_BOTH:
	case MATCH_ALL:
		sops[1].sem_num = 3;
		sops[1].sem_op = 1;
		sops[1].sem_flg = 0;
		nsops = 2;
		break;
	case MATCH_CASCADE:
		sops[0].sem_num = 3;
		break;
	default:
		e(0);
		return;
	}

	snd(parent, 0);

	int semop_result = semop(id, sops, (unsigned short)nsops);

	if (semop_result != expected_semop_return_val ||
		(expected_semop_return_val == -1 && errno != EIDRM)) {
		e(0);
	}
}

/*
 * Third child procedure.
 */
static void
test88e_child3(struct link * parent)
{
	struct sembuf sops[1];
	size_t nsops = 1;
	int match, id;

	match = rcv(parent);
	id = rcv(parent);

	if (match != MATCH_ALL) {
		e(0);
	}

	sops[0].sem_num = 3;
	sops[0].sem_op = -2;
	sops[0].sem_flg = 0;

	snd(parent, 0);

	if (semop(id, sops, nsops) != 0) e(0);
}

/*
 * Perform one test for operations affecting multiple processes.
 */
static void
sub88e(unsigned int match, unsigned int resume, unsigned int aux)
{
	struct link aux1_link, aux2_link, child1_link, child2_link, child3_link;
	struct sembuf sop;
	unsigned short val[4];
	int sem_id;
	int inc_value = 1;
	int aux_zcnt_val = 0;
	int aux_ncnt_val = 0;

	const unsigned int AUX_FLAG_SPAWN_FIRST_CHILD = 1;
	const unsigned int AUX_FLAG_SPAWN_SECOND_CHILD = 2;
	const unsigned int AUX_FLAG_USE_MAIN_OPS_SEM_FOR_ZCNT_LOGIC = 4;

	const int SEM_IDX_NEVER_COMPLETE = 0;
	const int SEM_IDX_AUXILIARY_LOCK = 1;
	const int SEM_IDX_MAIN_OPERATIONS = 2;
	const int SEM_IDX_THIRD_MAIN_OP = 3;

	const int RESUME_TYPE_SEMOP = 0;
	const int RESUME_TYPE_SETVAL = 1;
	const int RESUME_TYPE_SETALL = 2;

	if ((sem_id = semget(IPC_PRIVATE, __arraycount(val), 0666)) == -1) {
		e(0);
	}

	if (aux & AUX_FLAG_SPAWN_FIRST_CHILD) {
		spawn(&aux1_link, test88e_childaux, DROP_ALL);
		snd(&aux1_link, 1);
		snd(&aux1_link, sem_id);
		snd(&aux1_link, (aux & AUX_FLAG_USE_MAIN_OPS_SEM_FOR_ZCNT_LOGIC) ? SEM_IDX_MAIN_OPERATIONS : SEM_IDX_AUXILIARY_LOCK);

		if (rcv(&aux1_link) != 0) {
			e(0);
		}

		if (aux & AUX_FLAG_USE_MAIN_OPS_SEM_FOR_ZCNT_LOGIC) {
			aux_zcnt_val++;
		}
	}

	spawn(&child1_link, test88e_child1, DROP_ALL);
	snd(&child1_link, match);
	snd(&child1_link, sem_id);
	if (rcv(&child1_link) != 0) {
		e(0);
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

	spawn(&child2_link, test88e_child2, DROP_NONE);
	snd(&child2_link, match);
	snd(&child2_link, sem_id);
	if (rcv(&child2_link) != 0) {
		e(0);
	}

	if (match == MATCH_ALL) {
		spawn(&child3_link, test88e_child3, DROP_USER);
		snd(&child3_link, match);
		snd(&child3_link, sem_id);
		if (rcv(&child3_link) != 0) {
			e(0);
		}
	}

	if (aux & AUX_FLAG_SPAWN_SECOND_CHILD) {
		spawn(&aux2_link, test88e_childaux, DROP_NONE);
		snd(&aux2_link, 2);
		snd(&aux2_link, sem_id);
		snd(&aux2_link, (aux & AUX_FLAG_USE_MAIN_OPS_SEM_FOR_ZCNT_LOGIC) ? SEM_IDX_MAIN_OPERATIONS : SEM_IDX_AUXILIARY_LOCK);

		if (rcv(&aux2_link) != 0) {
			e(0);
		}

		if (aux & AUX_FLAG_USE_MAIN_OPS_SEM_FOR_ZCNT_LOGIC) {
			aux_ncnt_val++;
		}
	}

	usleep(WAIT_USECS);

	switch (match) {
	case MATCH_FIRST:
	case MATCH_SECOND:
		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, 0, 2 + aux_ncnt_val, aux_zcnt_val);
		TEST_SEM(sem_id, SEM_IDX_THIRD_MAIN_OP, 0, 0, 0, 0);
		break;
	case MATCH_KILL:
		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, 0, 2 + aux_ncnt_val, aux_zcnt_val);

		terminate(&child1_link);

		usleep(WAIT_USECS);

		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, 0, 1 + aux_ncnt_val, aux_zcnt_val);
		TEST_SEM(sem_id, SEM_IDX_THIRD_MAIN_OP, 0, 0, 0, 0);
		break;
	case MATCH_BOTH:
		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, 0, 2 + aux_ncnt_val, aux_zcnt_val);
		TEST_SEM(sem_id, SEM_IDX_THIRD_MAIN_OP, 0, 0, 0, 0);
		inc_value = 2;
		break;
	case MATCH_CASCADE:
		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, 0, 1 + aux_ncnt_val, aux_zcnt_val);
		TEST_SEM(sem_id, SEM_IDX_THIRD_MAIN_OP, 0, 0, 1, 0);
		break;
	case MATCH_ALL:
		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, 0, 2 + aux_ncnt_val, aux_zcnt_val);
		TEST_SEM(sem_id, SEM_IDX_THIRD_MAIN_OP, 0, 0, 1, 0);
		inc_value = 2;
		break;
	default:
		e(0);
	}

	TEST_SEM(sem_id, SEM_IDX_NEVER_COMPLETE, 0, 0, 0, 0);
	TEST_SEM(sem_id, SEM_IDX_AUXILIARY_LOCK, 0, 0, -1, -1);

	switch (resume) {
	case RESUME_TYPE_SEMOP:
		memset(&sop, 0, sizeof(sop));
		sop.sem_num = SEM_IDX_MAIN_OPERATIONS;
		sop.sem_op = inc_value;
		sop.sem_flg = 0;
		if (semop(sem_id, &sop, 1) != 0) {
			e(0);
		}
		break;
	case RESUME_TYPE_SETVAL:
		if (semctl(sem_id, SEM_IDX_MAIN_OPERATIONS, SETVAL, inc_value) != 0) {
			e(0);
		}
		break;
	case RESUME_TYPE_SETALL:
		memset(val, 0, sizeof(val));
		val[SEM_IDX_MAIN_OPERATIONS] = inc_value;
		if (semctl(sem_id, 0, SETALL, val) != 0) {
			e(0);
		}
		break;
	default:
		e(0);
	}

	switch (match) {
	case MATCH_FIRST:
		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, child1_link.pid, 1 + aux_ncnt_val, aux_zcnt_val);
		TEST_SEM(sem_id, SEM_IDX_THIRD_MAIN_OP, 1, child1_link.pid, 0, 0);
		collect(&child1_link);
		break;
	case MATCH_SECOND:
		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, child2_link.pid, 1 + aux_ncnt_val, aux_zcnt_val);
		TEST_SEM(sem_id, SEM_IDX_THIRD_MAIN_OP, 0, 0, 0, 0);
		collect(&child2_link);
		break;
	case MATCH_KILL:
		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, child2_link.pid, aux_ncnt_val, aux_zcnt_val);
		TEST_SEM(sem_id, SEM_IDX_THIRD_MAIN_OP, 0, 0, 0, 0);
		collect(&child2_link);
		break;
	case MATCH_BOTH:
		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, -1, aux_ncnt_val, aux_zcnt_val);
		TEST_SEM(sem_id, SEM_IDX_THIRD_MAIN_OP, 2, -1, 0, 0);
		collect(&child1_link);
		collect(&child2_link);
		break;
	case MATCH_CASCADE:
		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, child1_link.pid, aux_ncnt_val, aux_zcnt_val);
		TEST_SEM(sem_id, SEM_IDX_THIRD_MAIN_OP, 0, child2_link.pid, 0, 0);
		collect(&child1_link);
		collect(&child2_link);
		break;
	case MATCH_ALL:
		TEST_SEM(sem_id, SEM_IDX_MAIN_OPERATIONS, 0, -1, aux_ncnt_val, aux_zcnt_val);
		TEST_SEM(sem_id, SEM_IDX_THIRD_MAIN_OP, 0, child3_link.pid, 0, 0);
		collect(&child1_link);
		collect(&child2_link);
		collect(&child3_link);
		break;
	default:
		e(0);
	}

	TEST_SEM(sem_id, SEM_IDX_NEVER_COMPLETE, 0, 0, 0, 0);
	TEST_SEM(sem_id, SEM_IDX_AUXILIARY_LOCK, 0, 0, -1, -1);

	if (semctl(sem_id, 0, IPC_RMID) != 0) {
		e(0);
	}

	switch (match) {
	case MATCH_FIRST:
		collect(&child2_link);
		break;
	case MATCH_SECOND:
		collect(&child1_link);
		break;
	case MATCH_KILL:
	case MATCH_BOTH:
	case MATCH_CASCADE:
	case MATCH_ALL:
		break;
	default:
		e(0);
	}

	if (aux & AUX_FLAG_SPAWN_FIRST_CHILD) {
		collect(&aux1_link);
	}
	if (aux & AUX_FLAG_SPAWN_SECOND_CHILD) {
		collect(&aux2_link);
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
#define SUBTEST_CONFIGURATION_VALUE 4U
#define AUX_LOOP_START_VALUE        1U
#define AUX_LOOP_END_VALUE          8U

static void
test88e(void)
{
	unsigned int resume;
	unsigned int match;
	unsigned int aux;

	subtest = SUBTEST_CONFIGURATION_VALUE;

	for (match = 0U; match < NR_MATCHES; match++)
	{
		for (resume = 0U; resume < NR_RESUMES; resume++)
		{
			for (aux = AUX_LOOP_START_VALUE; aux <= AUX_LOOP_END_VALUE; aux++)
			{
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
	size_t num_semaphores_to_check = 0;

	id[0] = rcv(parent);
	id[1] = rcv(parent);

	if (sysctl(mib, __arraycount(mib), NULL, &len, NULL, 0) != 0) {
		e(0);
	}

	semsi = malloc(len);
	if (semsi == NULL) {
		e(0);
	}

	size_t actual_len = len;
	if (sysctl(mib, __arraycount(mib), semsi, &actual_len, NULL, 0) != 0) {
		free(semsi);
		e(0);
	}

	if (actual_len > len) {
		free(semsi);
		e(0);
	}
	len = actual_len;

	if (len >= sizeof(struct seminfo)) {
		size_t max_semids_in_buffer = (len - sizeof(struct seminfo)) / sizeof(struct sem_semid_ds);
		if (semsi->seminfo.semmni < 0) {
		    num_semaphores_to_check = 0;
		} else {
		    num_semaphores_to_check = ((size_t)semsi->seminfo.semmni < max_semids_in_buffer) ? (size_t)semsi->seminfo.semmni : max_semids_in_buffer;
		}
	} else {
		num_semaphores_to_check = 0;
	}

	seen[0] = seen[1] = 0;
	for (i = 0; (size_t)i < num_semaphores_to_check; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
			continue;

		id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
		if (id2 == id[0])
			seen[0]++;
		else if (id2 == id[1])
			seen[1]++;
	}

	free(semsi);

	if (seen[0] != 1) e(0);
	if (seen[1] != 1) e(0);
}

/*
 * Test sysctl(2) based information retrieval.  This test aims to ensure that
 * in particular ipcs(1) and ipcrm(1) will be able to do their jobs.
 */
#include <sys/types.h>
#include <sys/sysctl.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

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
	int id[2] = { -1, -1 };
	int id2;
	int32_t i;
	int slot[2] = { -1, -1 };
	int ret = 0;

	len = sizeof(seminfo);
	if (sysctl(mib, __arraycount(mib), &seminfo, &len, NULL, 0) != 0) {
		ret = -1;
		goto cleanup;
	}
	if (len != sizeof(seminfo)) {
		ret = -1;
		goto cleanup;
	}

	if (semctl(0, 0, IPC_INFO, &seminfo2) == -1) {
		ret = -1;
		goto cleanup;
	}

	if (memcmp(&seminfo, &seminfo2, sizeof(seminfo)) != 0) {
		ret = -1;
		goto cleanup;
	}

	if (seminfo.semmni <= 0 || seminfo.semmni > SHRT_MAX) {
		ret = -1;
		goto cleanup;
	}

	size = sizeof(*semsi) + sizeof(semsi->semids[0]) * (seminfo.semmni - 1);

	len = 0;
	if (sysctl(mib, __arraycount(mib), NULL, &len, NULL, 0) != 0) {
		ret = -1;
		goto cleanup;
	}
	if (len != size) {
		ret = -1;
		goto cleanup;
	}

	if ((id[0] = semget(KEY_A, 5, IPC_CREAT | 0612)) < 0) {
		ret = -1;
		goto cleanup;
	}

	if ((id[1] = semget(IPC_PRIVATE, 3, 0650)) < 0) {
		ret = -1;
		goto cleanup;
	}

	if ((semsi = malloc(size)) == NULL) {
		ret = -1;
		goto cleanup;
	}

	len = size;
	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0) {
		ret = -1;
		goto cleanup;
	}
	if (len != size) {
		ret = -1;
		goto cleanup;
	}

	if (sizeof(semsi->seminfo) != sizeof(seminfo)) {
		ret = -1;
		goto cleanup;
	}
	if (memcmp(&semsi->seminfo, &seminfo, sizeof(semsi->seminfo)) != 0) {
		ret = -1;
		goto cleanup;
	}

	for (i = 0; i < seminfo.semmni; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
			continue;

		id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
		if (id2 == id[0]) {
			if (slot[0] != -1) {
				ret = -1;
				goto cleanup;
			}
			slot[0] = i;
		} else if (id2 == id[1]) {
			if (slot[1] != -1) {
				ret = -1;
				goto cleanup;
			}
			slot[1] = i;
		}
	}

	if (slot[0] < 0) {
		ret = -1;
		goto cleanup;
	}
	if (slot[1] < 0) {
		ret = -1;
		goto cleanup;
	}

	semds = &semsi->semids[slot[0]];
	if (semds->sem_perm.uid != geteuid()) { ret = -1; goto cleanup; }
	if (semds->sem_perm.gid != getegid()) { ret = -1; goto cleanup; }
	if (semds->sem_perm.cuid != geteuid()) { ret = -1; goto cleanup; }
	if (semds->sem_perm.cgid != getegid()) { ret = -1; goto cleanup; }
	if (semds->sem_perm.mode != (SEM_ALLOC | 0612)) { ret = -1; goto cleanup; }
	if (semds->sem_perm._key != KEY_A) { ret = -1; goto cleanup; }
	if (semds->sem_nsems != 5) { ret = -1; goto cleanup; }
	if (semds->sem_otime != 0) { ret = -1; goto cleanup; }
	if (semds->sem_ctime == 0) { ret = -1; goto cleanup; }

	semds = &semsi->semids[slot[1]];
	if (semds->sem_perm.uid != geteuid()) { ret = -1; goto cleanup; }
	if (semds->sem_perm.gid != getegid()) { ret = -1; goto cleanup; }
	if (semds->sem_perm.cuid != geteuid()) { ret = -1; goto cleanup; }
	if (semds->sem_perm.cgid != getegid()) { ret = -1; goto cleanup; }
	if (semds->sem_perm.mode != (SEM_ALLOC | 0650)) { ret = -1; goto cleanup; }
	if (semds->sem_perm._key != IPC_PRIVATE) { ret = -1; goto cleanup; }
	if (semds->sem_nsems != 3) { ret = -1; goto cleanup; }
	if (semds->sem_otime != 0) { ret = -1; goto cleanup; }
	if (semds->sem_ctime == 0) { ret = -1; goto cleanup; }

	spawn(&child, test88f_child, DROP_ALL);

	snd(&child, id[0]);
	snd(&child, id[1]);

	collect(&child);

	if (semctl(id[0], 0, IPC_RMID) != 0) {
		ret = -1;
		goto cleanup;
	}
	id[0] = -1;

	if (semctl(id[1], 0, IPC_RMID) != 0) {
		ret = -1;
		goto cleanup;
	}
	id[1] = -1;

	len = size;
	if (sysctl(mib, __arraycount(mib), semsi, &len, NULL, 0) != 0) {
		ret = -1;
		goto cleanup;
	}
	if (len != size) {
		ret = -1;
		goto cleanup;
	}

	for (i = 0; i < seminfo.semmni; i++) {
		if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
			continue;

		id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
		if (id2 == id[0]) {
			ret = -1;
			goto cleanup;
		}
		if (id2 == id[1]) {
			ret = -1;
			goto cleanup;
		}
	}

cleanup:
	if (id[0] != -1) {
		(void)semctl(id[0], 0, IPC_RMID);
	}
	if (id[1] != -1) {
		(void)semctl(id[1], 0, IPC_RMID);
	}
	if (semsi != NULL) {
		free(semsi);
	}

	if (ret != 0) {
		e(0);
	}
	return;
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

	page_size = (size_t)getpagesize();
	void *temp_page_ptr = mmap(NULL, page_size * 2, PROT_READ | PROT_WRITE,
	    MAP_ANON | MAP_PRIVATE, -1, 0);
	if (temp_page_ptr == MAP_FAILED) {
		e(0);
	}
    page_ptr = temp_page_ptr;

	bad_ptr = (char *)page_ptr + page_size;
	if (munmap(bad_ptr, page_size) != 0) {
		e(0);
	}
}

/*
 * Test program for SysV IPC semaphores.
 */
#include <stdlib.h> // For strtol
#include <errno.h>  // For errno
#include <limits.h> // For INT_MIN, INT_MAX

#define DEFAULT_TEST_MASK 0xFF

int
main(int argc, char ** argv)
{
	int m;

	start(88);

	test88_init();

	if (argc == 2)
	{
		char *endptr;
		long val;

		errno = 0;

		val = strtol(argv[1], &endptr, 0);

		if (endptr == argv[1])
		{
			m = 0;
		}
		else if (errno == ERANGE)
		{
			m = 0;
		}
		else if (val < INT_MIN || val > INT_MAX)
		{
			m = 0;
		}
		else
		{
			m = (int)val;
		}
	}
	else
	{
		m = DEFAULT_TEST_MASK;
	}

	for (int i = 0; i < ITERATIONS; i++) {
		if (m & 0x01) { test88a(); }
		if (m & 0x02) { test88b(); }
		if (m & 0x04) { test88c(); }
		if (m & 0x08) { test88d(); }
		if (m & 0x10) { test88e(); }
		if (m & 0x20) { test88f(); }
	}

	quit();
}
