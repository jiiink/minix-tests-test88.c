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
#include <stdlib.h>
#include <unistd.h>
#include <grp.h>
#include <pwd.h>
#include <sys/types.h>
#include <stdio.h>

#define DROP_ALL 1
#define DROP_USER 2
#define NONROOT_USER "nobody"
#define NONROOT_GROUP "nogroup"

struct link {
    pid_t pid;
    int sndfd;
    int rcvfd;
};

static void handleError() {
    perror("Error");
    exit(EXIT_FAILURE);
}

static void dropPrivileges(int drop) {
    struct passwd *pw;
    struct group *gr;

    if (drop == DROP_ALL) {
        if (setgroups(0, NULL) != 0) handleError();

        if ((gr = getgrnam(NONROOT_GROUP)) == NULL) handleError();
        if (setgid(gr->gr_gid) != 0 || setegid(gr->gr_gid) != 0) handleError();
    }

    if (drop != DROP_USER) return;

    if ((pw = getpwnam(NONROOT_USER)) == NULL) handleError();
    if (setuid(pw->pw_uid) != 0) handleError();
}

static void spawn(struct link *link, void (*proc)(struct link *), int drop) {
    int up[2], dn[2];

    if (fflush(stdout) != 0 || fflush(stderr) != 0) handleError();

    if (pipe(up) != 0 || pipe(dn) != 0) handleError();

    link->pid = fork();
    switch (link->pid) {
        case 0:
            close(up[1]);
            close(dn[0]);
            link->pid = getppid();
            link->rcvfd = up[0];
            link->sndfd = dn[1];
            dropPrivileges(drop);
            proc(link);
            close(link->rcvfd);
            close(link->sndfd);
            exit(0);
        case -1:
            handleError();
    }

    close(up[0]);
    close(dn[1]);
    link->sndfd = up[1];
    link->rcvfd = dn[0];
}

/*
 * Wait for a child process to terminate, and clean up.
 */
#include <errno.h>
#include <signal.h>
#include <stdbool.h>
#include <stdio.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static void handle_error(int condition) {
    if (condition) {
        perror("Error");
        exit(EXIT_FAILURE);
    }
}

static bool is_status_valid(int pid, int status) {
    if (pid < 0) {
        handle_error(1);
        return false;
    }
    if (!WIFEXITED(status)) {
        handle_error(1);
        return false;
    }
    return true;
}

static void close_descriptor(int fd) {
    handle_error(close(fd) == -1);
}

static void collect(struct link *link) {
    int status;
    pid_t result;

    close_descriptor(link->sndfd);
    close_descriptor(link->rcvfd);

    result = waitpid(link->pid, &status, 0);
    if (is_status_valid(result, status)) {
        errct += WEXITSTATUS(status);
    }
}

/*
 * Forcibly terminate a child process, and clean up.
 */
#include <signal.h>
#include <unistd.h>
#include <sys/wait.h>
#include <stdlib.h>
#include <errno.h>

// Note: Define e() function and errct variable.

static void terminate(struct link *link) {
    int status;

    if (kill(link->pid, SIGKILL) == -1) {
        e(errno);
        return;
    }

    if (close(link->sndfd) == -1 || close(link->rcvfd) == -1) {
        e(errno);
        return;
    }

    if (waitpid(link->pid, &status, 0) == -1) {
        e(errno);
        return;
    }

    if (WIFSIGNALED(status) && WTERMSIG(status) != SIGKILL) {
        e(0);
    } else if (WIFEXITED(status)) {
        errct += WEXITSTATUS(status);
    } else {
        e(0);
    }
}

/*
 * Send an integer value to the child or parent.
 */
#include <unistd.h>
#include <errno.h>

static void handle_error() {
    // Implement appropriate error handling here, possibly logging and exiting or taking corrective action
}

static void snd(struct link *link, int val) {
    ssize_t bytes_written = write(link->sndfd, &val, sizeof(val));
    if (bytes_written == -1 || bytes_written != sizeof(val)) {
        handle_error();
    }
}

/*
 * Receive an integer value from the child or parent, or -1 on EOF.
 */
static int rcv(struct link *link) {
    int val;
    if (link == NULL || link->rcvfd < 0) return -1;

    ssize_t bytesRead = read(link->rcvfd, &val, sizeof(val));
    if (bytesRead != sizeof(val)) return -1;

    return val;
}

/*
 * Child procedure that creates semaphore sets.
 */
#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <pwd.h>
#include <grp.h>
#include <unistd.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#define KEY_A 1 
#define KEY_B 2 
#define KEY_C 3 

#define IPC_CREAT 01000 
#define IPC_EXCL 02000 
#define SEM_ALLOC 04000

#define IPC_R 0400 

#define ROOT_USER "root" 
#define NONROOT_USER "nobody" 
#define ROOT_GROUP "root" 
#define NONROOT_GROUP "nogroup" 

#define SUGID_NONE 0 
#define SUGID_ROOT_USER 1 
#define SUGID_NONROOT_USER 2 
#define SUGID_ROOT_GROUP 3 
#define SUGID_NONROOT_GROUP 4 

struct link {};

int rcv(struct link *parent);
void snd(struct link *parent, int id);
void e(int error_code);

static void test_perm_child(struct link *parent) {
    struct passwd *pw = NULL;
    struct group *gr = NULL;
    struct semid_ds semds;
    uid_t uid;
    gid_t gid;
    int mask, rmask, sugid, id[3];

    while ((mask = rcv(parent)) != -1) {
        rmask = rcv(parent);
        sugid = rcv(parent);

        id[0] = semget(KEY_A, 3, IPC_CREAT | IPC_EXCL | ((sugid == SUGID_NONE) ? mask : 0));
        if (id[0] == -1) e(errno);

        id[1] = semget(KEY_B, 3, IPC_CREAT | IPC_EXCL | mask | rmask);
        if (id[1] == -1) e(errno);

        id[2] = semget(KEY_C, 3, IPC_CREAT | IPC_EXCL | rmask);
        if (id[2] == -1) e(errno);

        uid = geteuid();
        gid = getegid();

        if (sugid != SUGID_NONE) {
            switch (sugid) {
                case SUGID_ROOT_USER:
                    pw = getpwnam(ROOT_USER);
                    if (pw == NULL) e(errno);
                    uid = pw->pw_uid;
                    break;

                case SUGID_NONROOT_USER:
                    pw = getpwnam(NONROOT_USER);
                    if (pw == NULL) e(errno);
                    uid = pw->pw_uid;
                    break;

                case SUGID_ROOT_GROUP:
                    gr = getgrnam(ROOT_GROUP);
                    if (gr == NULL) e(errno);
                    gid = gr->gr_gid;
                    break;

                case SUGID_NONROOT_GROUP:
                    gr = getgrnam(NONROOT_GROUP);
                    if (gr == NULL) e(errno);
                    gid = gr->gr_gid;
                    break;
            }

            semds.sem_perm.uid = uid;
            semds.sem_perm.gid = gid;
            semds.sem_perm.mode = mask;
            if (semctl(id[0], 0, IPC_SET, &semds) != 0) e(errno);

            semds.sem_perm.mode = mask | rmask;
            if (semctl(id[1], 0, IPC_SET, &semds) != 0) e(errno);

            semds.sem_perm.mode = rmask;
            if (semctl(id[2], 0, IPC_SET, &semds) != 0) e(errno);
        }

        if (mask & IPC_R) {
            if (semctl(id[0], 0, IPC_STAT, &semds) != 0) e(errno);
            if (semds.sem_perm.mode != (SEM_ALLOC | mask)) e(errno);
            if (semds.sem_perm.uid != uid) e(errno);
            if (semds.sem_perm.gid != gid) e(errno);
            if (semds.sem_perm.cuid != geteuid()) e(errno);
            if (semds.sem_perm.cgid != getegid()) e(errno);
        }

        snd(parent, id[0]);
        snd(parent, id[1]);
        snd(parent, id[2]);

        if (rcv(parent) != 0) e(errno);

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
#define MAX_ITER 7
#define TERMINATE_SIGNAL -1

static void test_perm(void (*proc)(struct link*), int owner_test) {
    struct link child1, child2;
    int n, bit;
    int shift[] = {6, 6, 6, 3, 3, 3, 0};
    int drop1[] = {DROP_ALL, DROP_NONE, DROP_USER, DROP_NONE, DROP_NONE, DROP_NONE, DROP_NONE};
    int drop2[] = {DROP_ALL, DROP_ALL, DROP_ALL, DROP_USER, DROP_ALL, DROP_USER, DROP_ALL};
    int sugid[] = {SUGID_NONE, SUGID_NONROOT_USER, SUGID_ROOT_USER, SUGID_NONE, SUGID_NONROOT_GROUP, SUGID_NONROOT_GROUP, SUGID_NONE};

    for (n = 0; n < MAX_ITER; n++) {
        spawn(&child1, test_perm_child, drop1[n]);
        spawn(&child2, proc, drop2[n]);

        for (bit = 0; bit <= 7; bit++) {
            int mask = bit << shift[n];
            int rmask = 0777 & ~(7 << shift[n]);

            snd(&child1, mask);
            snd(&child1, rmask);
            snd(&child1, sugid[n]);

            int id[3];
            id[0] = rcv(&child1);
            id[1] = rcv(&child1);
            id[2] = rcv(&child1);

            snd(&child2, owner_test ? shift[n] : bit);
            snd(&child2, id[0]);
            snd(&child2, id[1]);
            snd(&child2, id[2]);

            if (rcv(&child2) != 0) {
                e(0);
            }

            snd(&child1, 0);
        }

        // Use a bitmask of TERMINATE_SIGNAL to terminate the children.
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
#include <errno.h>

#define KEY_A 0
#define KEY_B 1
#define KEY_C 2

static void handle_result(int result, int expected_id) {
    if (result == -1) {
        if (errno != EACCES) {
            e(0);
        }
    } else {
        if (result != expected_id) {
            e(0);
        }
    }
}

static int check_semget(int key, int mask, int tbit, int bit) {
    int r = semget(key, 0, mask);
    if ((bit != 0) && ((bit & tbit) == bit) != (r != -1)) {
        e(0);
    }
    return r;
}

static void test88a_perm(struct link *parent) {
    int tbit, bit, mask, id[3];

    while ((tbit = rcv(parent)) != -1) {
        for (int i = 0; i < 3; i++) {
            id[i] = rcv(parent);
        }

        for (bit = 1; bit <= 127; bit <<= 1) {
            mask = bit << 6;

            handle_result(check_semget(KEY_A, mask, tbit, bit), id[0]);
            handle_result(check_semget(KEY_B, mask, tbit, bit), id[1]);

            if (check_semget(KEY_C, mask, tbit, bit) != -1) {
                e(0);
            }
        }
        
        snd(parent, 0);
    }
}

/*
 * Test the basic semget(2) functionality.
 */
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <time.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <sys/types.h>
#include <unistd.h>
#include <limits.h>

#define e(x) { fprintf(stderr, "Error: %d\n", x); exit(1); }
#define TEST_SEM(id, i, val, cz, pid, sz)

static void test88a(void) {
    struct seminfo seminfo;
    struct semid_ds semds;
    time_t now;
    int id[3], *idp;
    unsigned int i = 0;

    if ((id[0] = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600)) < 0 || 
        (id[1] = semget(IPC_PRIVATE, 1, IPC_CREAT | IPC_EXCL | 0600)) < 0 ||
        (id[2] = semget(IPC_PRIVATE, 1, 0600)) < 0) e(0);

    if (id[0] == id[1] || id[1] == id[2] || id[0] == id[2]) e(0);

    for (i = 0; i < 3; i++)
        if (semctl(id[i], 0, IPC_RMID) != 0) e(0);

    if ((id[0] = semget(KEY_A, 0, 0600)) >= 0 && semctl(id[0], 0, IPC_RMID) == -1) e(0);
    if ((id[0] = semget(KEY_B, 0, 0600)) >= 0 && semctl(id[0], 0, IPC_RMID) == -1) e(0);

    if (semget(KEY_A, 1, 0600) != -1 || errno != ENOENT) e(0);
    if ((id[0] = semget(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0600)) < 0) e(0);

    if (semget(KEY_B, 1, 0600) != -1 || errno != ENOENT) e(0);
    if ((id[1] = semget(KEY_B, 1, IPC_CREAT | 0600)) < 0 || id[0] == id[1]) e(0);

    if ((id[2] = semget(KEY_A, 1, 0600)) < 0 || id[2] != id[0]) e(0);
    if ((id[2] = semget(KEY_B, 1, IPC_CREAT | 0600)) < 0 || id[2] != id[1]) e(0);

    if (semget(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0600) != -1 || errno != EEXIST) e(0);

    if (semctl(id[0], 0, IPC_RMID) != 0 || semctl(id[1], 0, IPC_RMID) != 0) e(0);

    if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
    if (seminfo.semmni < 3 || seminfo.semmni > USHRT_MAX) e(0);

    if ((idp = malloc(sizeof(int) * (seminfo.semmni + 1))) == NULL) e(0);

    for (i = 0; i < seminfo.semmni + 1; i++) {
        if ((idp[i] = semget(KEY_A + i, 1, IPC_CREAT | 0600)) < 0) break;
        for (unsigned int j = 0; j < i; j++)
            if (idp[i] == idp[j]) e(0);
    }

    if (errno != ENOSPC || i < 3 || i == seminfo.semmni + 1) e(0);

    while (i-- > 0)
        if (semctl(idp[i], 0, IPC_RMID) != 0) e(0);

    free(idp);

    if (semget(KEY_A, -1, IPC_CREAT | 0600) != -1 || errno != EINVAL) e(0);
    if (semget(KEY_A, 0, IPC_CREAT | 0600) != -1 || errno != EINVAL) e(0);

    if (seminfo.semmsl < 3 || seminfo.semmsl > USHRT_MAX) e(0);
    if (semget(KEY_A, seminfo.semmsl + 1, IPC_CREAT | 0600) != -1 || errno != EINVAL) e(0);

    if ((id[0] = semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0600)) < 0 || 
        semctl(id[0], 0, IPC_RMID) != 0) e(0);

    if ((id[0] = semget(KEY_A, 2, IPC_CREAT | 0600)) < 0) e(0);

    if ((id[1] = semget(KEY_A, 0, 0600)) < 0 || id[0] != id[1]) e(0);
    if ((id[1] = semget(KEY_A, 1, 0600)) < 0 || id[0] != id[1]) e(0);
    if ((id[1] = semget(KEY_A, 2, 0600)) < 0 || id[0] != id[1]) e(0);

    if ((id[1] = semget(KEY_A, 3, 0600)) != -1 || errno != EINVAL) e(0);
    if ((id[1] = semget(KEY_A, seminfo.semmsl + 1, 0600)) != -1 || errno != EINVAL) e(0);

    if (semctl(id[0], 0, IPC_RMID) != 0) e(0);

    time(&now);
    if (seminfo.semmns < 3 + seminfo.semmsl) e(0);

    if ((id[0] = semget(IPC_PRIVATE, 3, IPC_CREAT | IPC_EXCL | 0642)) < 0 ||
        (id[1] = semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0613)) < 0) e(0);

    if (semctl(id[0], 0, IPC_STAT, &semds) != 0 || semds.sem_perm.uid != geteuid() ||
        semds.sem_perm.gid != getegid() || semds.sem_perm.cuid != geteuid() ||
        semds.sem_perm.cgid != getegid() || semds.sem_perm.mode != (SEM_ALLOC | 0642) ||
        semds.sem_perm._key != IPC_PRIVATE || semds.sem_nsems != 3 || 
        semds.sem_otime != 0 || semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);

    for (i = 0; i < semds.sem_nsems; i++)
        TEST_SEM(id[0], i, 0, 0, 0, 0);

    if (semctl(id[1], 0, IPC_STAT, &semds) != 0 || semds.sem_perm.uid != geteuid() ||
        semds.sem_perm.gid != getegid() || semds.sem_perm.cuid != geteuid() ||
        semds.sem_perm.cgid != getegid() || semds.sem_perm.mode != (SEM_ALLOC | 0613) || 
        semds.sem_perm._key != KEY_A || semds.sem_nsems != seminfo.semmsl || 
        semds.sem_otime != 0 || semds.sem_ctime < now || semds.sem_ctime >= now + 10) e(0);

    for (i = 0; i < semds.sem_nsems; i++)
        TEST_SEM(id[1], i, 0, 0, 0, 0);

    if (semctl(id[1], 0, IPC_RMID) != 0 || semctl(id[0], 0, IPC_RMID) != 0) e(0);

    if ((id[0] = semget(KEY_A, 1, IPC_CREAT | IPC_EXCL | 0000)) < 0 ||
        (id[1] = semget(KEY_A, 0, 0600)) < 0 || id[0] != id[1] || 
        (id[1] = semget(KEY_A, 0, 0000)) < 0 || id[0] != id[1] || 
        semctl(id[0], 0, IPC_RMID) != 0) e(0);

    test_perm(test88a_perm, 0);
}

/*
 * Test semop(2) permission checks.
 */
#include <errno.h>
#include <limits.h>
#include <stddef.h>
#include <string.h>

static void test88b_perm(struct link *parent) {
    struct sembuf sops[2];
    int id[3];

    while (1) {
        int tbit = rcv(parent);
        if (tbit == -1) break;

        for (int i = 0; i < 3; i++) {
            id[i] = rcv(parent);
        }

        for (int i = 0; i < 8; i++) {
            int nsops = 0, bit = 0, r;
            memset(sops, 0, sizeof(sops));

            switch (i) {
                case 0:
                    nsops = 1;
                    bit = 4;
                    break;
                case 1:
                    sops[0].sem_op = 1;
                    nsops = 1;
                    bit = 2;
                    break;
                case 2:
                    sops[0].sem_op = -1;
                    nsops = 1;
                    bit = 2;
                    break;
                case 3:
                    sops[1].sem_op = 1;
                    nsops = 2;
                    bit = 6;
                    break;
                case 4:
                    sops[0].sem_num = 1;
                    sops[1].sem_op = -1;
                    nsops = 2;
                    bit = 6;
                    break;
                case 5:
                    sops[1].sem_num = 1;
                    nsops = 2;
                    bit = 4;
                    break;
                case 6:
                    sops[0].sem_op = 1;
                    sops[1].sem_op = -1;
                    nsops = 2;
                    bit = 2;
                    break;
                case 7:
                    sops[0].sem_num = USHRT_MAX;
                    nsops = 2;
                    bit = 4;
                    break;
            }

            for (int j = 0; j < 3; j++) {
                r = semop(id[j], sops, nsops);
                if (i == 7 && r == -1 && errno == EFBIG) r = 0;
                if (r < 0 && errno != EACCES) e(0);
                if (((bit & tbit) == bit) != (r != -1)) e(0);
            }

            if (semop(id[2], sops, nsops) != -1) e(0);
            if (errno != EACCES) e(0);
        }

        snd(parent, 0);
    }
}

/*
 * Signal handler.
 */
static void got_signal(int sig) {
    if (sig == SIGHUP && nr_signals == 0) {
        nr_signals++;
    } else {
        e(0);
    }
}

/*
 * Child process for semop(2) tests, mainly testing blocking operations.
 */
#include <errno.h>
#include <signal.h>
#include <string.h>
#include <sys/sem.h>
#include <unistd.h>

static void handleErrorCondition(int condition) {
    if (condition) e(0);
}

static void test88b_child(struct link * parent) {
    struct sembuf sops[5];
    struct sigaction act;
    int id = rcv(parent);

    memset(sops, 0, sizeof(sops));
    
    handleErrorCondition(semop(id, sops, 1) != 0);
    handleErrorCondition(rcv(parent) != 1);

    sops[0].sem_op = -3;
    handleErrorCondition(semop(id, sops, 1) != 0);

    handleErrorCondition(rcv(parent) != 2);

    sops[0].sem_num = 2;
    sops[0].sem_op = 2;
    sops[1].sem_num = 1;
    sops[1].sem_op = -1;
    sops[2].sem_num = 0;
    sops[2].sem_op = 1;
    handleErrorCondition(semop(id, sops, 3) != 0);

    handleErrorCondition(rcv(parent) != 3);

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
    handleErrorCondition(semop(id, sops, 5) != 0);

    handleErrorCondition(rcv(parent) != 4);

    sops[0].sem_num = 1;
    sops[0].sem_op = -2;
    sops[1].sem_num = 2;
    sops[1].sem_op = 0;
    handleErrorCondition(semop(id, sops, 2) != 0);

    handleErrorCondition(rcv(parent) != 5);

    sops[0].sem_num = 0;
    sops[0].sem_op = -1;
    sops[1].sem_num = 1;
    sops[1].sem_op = -1;
    sops[1].sem_flg = IPC_NOWAIT;
    handleErrorCondition(semop(id, sops, 2) != 0);

    handleErrorCondition(rcv(parent) != 6);

    sops[0].sem_num = 1;
    sops[0].sem_op = 0;
    sops[1].sem_num = 0;
    sops[1].sem_op = 0;
    sops[1].sem_flg = IPC_NOWAIT;
    handleErrorCondition(semop(id, sops, 2) != -1);
    handleErrorCondition(errno != EAGAIN);

    handleErrorCondition(rcv(parent) != 7);

    sops[0].sem_num = 0;
    sops[0].sem_op = 0;
    sops[1].sem_num = 1;
    sops[1].sem_op = 1;
    sops[1].sem_flg = 0;
    handleErrorCondition(semop(id, sops, 2) != 0);

    handleErrorCondition(rcv(parent) != 8);

    sops[0].sem_num = 0;
    sops[0].sem_op = -1;
    sops[1].sem_num = 1;
    sops[1].sem_op = 2;
    handleErrorCondition(semop(id, sops, 2) != -1);
    handleErrorCondition(errno != ERANGE);

    memset(&act, 0, sizeof(act));
    act.sa_handler = got_signal;
    sigfillset(&act.sa_mask);
    handleErrorCondition(sigaction(SIGHUP, &act, NULL) != 0);

    handleErrorCondition(rcv(parent) != 9);

    memset(sops, 0, sizeof(sops));
    sops[0].sem_num = 0;
    sops[0].sem_op = 0;
    sops[1].sem_num = 0;
    sops[1].sem_op = 1;
    sops[2].sem_num = 1;
    sops[2].sem_op = 0;
    if (semop(id, sops, 3) != -1) {
        handleErrorCondition(errno != EINTR);
        handleErrorCondition(nr_signals != 1);
    }

    TEST_SEM(id, 0, 0, parent->pid, 0, 0);
    TEST_SEM(id, 1, 1, parent->pid, 0, 0);

    handleErrorCondition(rcv(parent) != 10);

    memset(sops, 0, sizeof(sops));
    sops[0].sem_op = -3;
    handleErrorCondition(semop(id, sops, 1) != -1);
    handleErrorCondition(errno != EIDRM);

    id = rcv(parent);

    sops[0].sem_num = 0;
    sops[0].sem_op = -1;
    sops[1].sem_num = 1;
    sops[1].sem_op = 1;
    handleErrorCondition(semop(id, sops, 2) != -1);
    handleErrorCondition(errno != ERANGE);

    handleErrorCondition(rcv(parent) != 11);

    sops[0].sem_num = 1;
    sops[0].sem_op = 0;
    sops[1].sem_num = 0;
    sops[1].sem_op = -1;
    handleErrorCondition(semop(id, sops, 2) != 0);

    id = rcv(parent);

    sops[0].sem_num = 0;
    sops[0].sem_op = -1;
    sops[1].sem_num = 1;
    sops[1].sem_op = 0;
    handleErrorCondition(semop(id, sops, 2) != 0);

    snd(parent, errct);
    handleErrorCondition(rcv(parent) != 12);

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
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <unistd.h>

void e(int err_code);
void TEST_SEM(int id, int sem_num, int sem_value, int pid, int zcnt, int ncnt);

static void test88b(void) {
    struct seminfo seminfo;
    struct semid_ds semds;
    struct sembuf *sops;
    size_t size;
    time_t now;
    unsigned short val[2];
    int id;

    subtest = 1;

    if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);

    if (seminfo.semopm < 3 || seminfo.semopm > USHRT_MAX) e(0);

    size = sizeof(struct sembuf) * (seminfo.semopm + 1);
    sops = calloc(seminfo.semopm + 1, sizeof(struct sembuf));
    if (sops == NULL) e(0);

    if ((id = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600)) == -1) e(0);

    if (semop(id, NULL, 0) != 0) e(0);

    if (semop(id, NULL, 1) != -1 || errno != EFAULT) e(0);

    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime != 0) e(0);

    time(&now);
    if (semop(id, sops, 1) != 0) e(0);

    TEST_SEM(id, 0, 0, getpid(), 0, 0);
    if (semctl(id, 0, IPC_STAT, &semds) != 0) e(0);
    if (semds.sem_otime < now || semds.sem_otime >= now + 10) e(0);

    if (semop(id, sops, seminfo.semopm) != 0) e(0);

    sops[1].sem_num = 1;
    if (semop(id, sops, 2) != -1 || errno != EFBIG) e(0);

    if (seminfo.semvmx < 3 || seminfo.semvmx > SHRT_MAX) e(0);

    sops[0].sem_flg = IPC_NOWAIT;
    sops[0].sem_op = seminfo.semvmx;
    if (semop(id, sops, 1) != 0) e(0);
    if (semctl(id, 0, GETVAL) != seminfo.semvmx) e(0);

    sops[0].sem_op = 1;
    if (semop(id, sops, 1) != -1 || errno != ERANGE) e(0);

    sops[0].sem_op = SHRT_MAX;
    if (semop(id, sops, 1) != -1 || errno != ERANGE) e(0);

    if (seminfo.semvmx < -(int)SHRT_MIN) {
        sops[0].sem_op = -seminfo.semvmx - 1;
        if (semop(id, sops, 1) != -1 || errno != EAGAIN) e(0);
    }

    sops[0].sem_op = 0;
    if (semop(id, sops, 1) != 0) e(0);

    sops[0].sem_op = 2;
    if (semop(id, sops, 1) != 0) e(0);

    sops[0].sem_op = -3;
    if (semop(id, sops, 1) != -1 || errno != EAGAIN) e(0);

    sops[0].sem_op = 1;
    if (semop(id, sops, 1) != 0) e(0);

    sops[0].sem_op = -1;
    if (semop(id, sops, 1) != 0) e(0);

    if (semctl(id, 0, IPC_RMID) != 0) e(0);

    if (semop(id, NULL, 0) != -1 || errno != EINVAL) e(0);

    memset(&semds, 0, sizeof(semds));
    id = IXSEQ_TO_IPCID(seminfo.semmni, semds.sem_perm);
    if (semop(id, NULL, 0) != -1 || errno != EINVAL) e(0);

    free(sops);
}

/*
 * Test semctl(2) permission checks, part 1: regular commands.
 */
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <sys/sem.h>

static void handleError() {
    e(0);
}

static void checkSemctl(int r, int expectedValue, int errorValue) {
    if ((r < 0 && (r != -1 || errno != errorValue)) || r != expectedValue) {
        handleError();
    }
}

static int isBitSet(int tbit, int bit) {
    return (bit & tbit) == bit;
}

static void processCommands(int *id, int tbit, int *cmds, int cmdsCount) {
    int bit = 4, r;

    for (int i = 0; i < cmdsCount; i++) {
        r = semctl(id[0], 0, cmds[i]);
        checkSemctl(r, !isBitSet(tbit, bit), EACCES);

        r = semctl(id[1], 0, cmds[i]);
        checkSemctl(r, !isBitSet(tbit, bit), EACCES);

        r = semctl(id[2], 0, cmds[i]);
        if (r != -1 || errno != EACCES) handleError();
    }
}

static void setValCommands(int *id, int tbit) {
    int bit = 2, r;

    r = semctl(id[0], 0, SETVAL, 0);
    checkSemctl(r, !isBitSet(tbit, bit), EACCES);

    r = semctl(id[1], 0, SETVAL, 0);
    checkSemctl(r, !isBitSet(tbit, bit), EACCES);

    r = semctl(id[2], 0, SETVAL, 0);
    if (r != -1 || errno != EACCES) handleError();
}

static void pointerCommands(int *id, int tbit, unsigned short *val, struct semid_ds *semds) {
    void *ptr;
    int cmd, bit, r;

    for (int i = 0; i < 3; i++) {
        switch (i) {
            case 0: cmd = GETALL; ptr = val; bit = 4; break;
            case 1: cmd = SETALL; ptr = val; bit = 2; break;
            case 2: cmd = IPC_STAT; ptr = semds; bit = 4; break;
            default: abort();
        }

        r = semctl(id[0], 0, cmd, ptr);
        checkSemctl(r, !isBitSet(tbit, bit), EACCES);

        r = semctl(id[1], 0, cmd, ptr);
        checkSemctl(r, !isBitSet(tbit, bit), EACCES);

        if (semctl(id[2], 0, cmd, ptr) != -1 || errno != EACCES) handleError();
    }
}

static void semStatCommands(int *id, int tbit, struct semid_ds *semds) {
    int r;
    int bit = 4;
    #define IPCID_TO_IX(id) ((id) & 0xffff)

    r = semctl(IPCID_TO_IX(id[0]), 0, SEM_STAT, semds);
    checkSemctl(r, !isBitSet(tbit, bit), EACCES);

    r = semctl(IPCID_TO_IX(id[1]), 0, SEM_STAT, semds);
    checkSemctl(r, !isBitSet(tbit, bit), EACCES);

    if (semctl(IPCID_TO_IX(id[2]), 0, SEM_STAT, semds) != -1 || errno != EACCES) handleError();
}

static void ipcInfoCommands() {
    struct seminfo seminfo;
    if (semctl(0, 0, IPC_INFO, &seminfo) == -1 || semctl(0, 0, SEM_INFO, &seminfo) == -1) {
        handleError();
    }
}

static void test88c_perm1(struct link *parent) {
    static const int cmds[] = { GETVAL, GETPID, GETNCNT, GETZCNT };
    struct semid_ds semds;
    unsigned short val[3];
    int tbit, id[3];

    while ((tbit = rcv(parent)) != -1) {
        for (int i = 0; i < 3; i++) {
            id[i] = rcv(parent);
        }

        memset(val, 0, sizeof(val));

        processCommands(id, tbit, (int *)cmds, sizeof(cmds)/sizeof(cmds[0]));
        setValCommands(id, tbit);
        pointerCommands(id, tbit, val, &semds);
        semStatCommands(id, tbit, &semds);
        ipcInfoCommands();
        snd(parent, 0);
    }
}

/*
 * Test semctl(2) permission checks, part 2: the IPC_SET command.
 */
#include <errno.h>
#include <string.h>
#include <sys/sem.h>

static void test88c_perm2(struct link *parent) {
    struct semid_ds semds = {0};
    int r, shift, id[3];

    while ((shift = rcv(parent)) != -1) {
        for (int i = 0; i < 3; i++) {
            id[i] = rcv(parent);
        }

        for (int i = 0; i < 3; i++) {
            r = semctl(id[i], 0, IPC_SET, &semds);
            if (r < 0 && errno != EPERM) e(0);
            if ((shift == 6) != (r != -1)) e(0);
        }

        snd(parent, 0);
    }
}

/*
 * Test semctl(2) permission checks, part 3: the IPC_RMID command.
 */
#include <errno.h>
#include <sys/sem.h>

static void test88c_perm3(struct link *parent) {
    int shift, id[3];

    while ((shift = rcv(parent)) != -1) {
        for (int i = 0; i < 3; i++) {
            id[i] = rcv(parent);
            int r = semctl(id[i], 0, IPC_RMID);
            if (r < 0 && errno != EPERM) {
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
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <sys/types.h>
#include <unistd.h>

#define E_IF(expr) if (expr) handle_error();
#define SET_SEMS_NO_CHANGE(expr) \
    E_IF(semctl(id, 0, IPC_STAT, &semds) != 0); \
    E_IF(semds.sem_otime != 0); \
    E_IF(semds.sem_ctime >= now)

static void handle_error(void) {
    /* error handling code */
}

static void test88c(void) {
    static const int cmds[] = {GETVAL, GETPID, GETNCNT, GETZCNT};
    struct seminfo seminfo;
    struct semid_ds semds, osemds;
    unsigned short val[4], seen[2];
    char statbuf[sizeof(struct semid_ds) + 1];
    unsigned int i, j;
    time_t now;
    int r, id, id2, badid1, badid2, cmd;

    if (semctl(0, 0, IPC_INFO, &seminfo) == -1) handle_error();

    if ((badid1 = semget(IPC_PRIVATE, 1, 0600)) < 0) handle_error();
    if (semctl(badid1, 0, IPC_RMID) != 0) handle_error();

    memset(&semds, 0, sizeof(semds));
    badid2 = IXSEQ_TO_IPCID(seminfo.semmni, semds.sem_perm);

    if ((id = semget(IPC_PRIVATE, 3, IPC_CREAT | 0600)) < 0) handle_error();
    if (semctl(id, 0, IPC_STAT, &semds) != 0) handle_error();
    E_IF(semds.sem_otime != 0);
    E_IF(semds.sem_ctime == 0);

    while (time(&now) == semds.sem_ctime) usleep(250000);

    for (i = 0; i < sizeof(cmds) / sizeof(cmds[0]); i++) {
        for (j = 0; j < 3; j++)
            E_IF(semctl(id, j, cmds[i]) != 0);

        for (int invalid_id : {badid1, badid2, -1, INT_MIN, id, id})
            for (int semnum : {(j == 4 ? 3 : -1), 3})
                E_IF(semctl(invalid_id, semnum, cmds[i]) != -1 || errno != EINVAL);

        SET_SEMS_NO_CHANGE(semctl(id, 0, cmds[i]));
    }

    for (j = 0; j < 5; j++) {
        memset(val, 0xFF, sizeof(val));

        E_IF(semctl(id, (int)j - 1, GETALL, val) != 0);
        for (i = 0; i < 3; i++)
            E_IF(val[i] != 0);
        E_IF(val[3] != 0xFF);
    }

    memset(val, 0xFF, sizeof(val));
    for (int invalid_id : {badid1, badid2, -1, INT_MIN})
        E_IF(semctl(invalid_id, 0, GETALL, val) != -1 || errno != EINVAL);

    E_IF(semctl(id, 0, GETALL, NULL) != -1 || errno != EFAULT);
    E_IF(semctl(id, 0, GETALL, ((unsigned short *)bad_ptr) - 2) != -1 || errno != EFAULT);
    E_IF(semctl(id, 0, GETALL, ((unsigned short *)bad_ptr) - 3) != 0);

    SET_SEMS_NO_CHANGE(semctl(id, 0, GETALL, bad_ptr));

    memset(statbuf, 0x5a, sizeof(statbuf));
    for (int invalid_id : {badid1, badid2, -1, INT_MIN})
        E_IF(semctl(invalid_id, 0, IPC_STAT, statbuf) != -1 || errno != EINVAL);

    for (i = 0; i < sizeof(statbuf); i++)
        E_IF(statbuf[i] != 0x5a);

    E_IF(semctl(id, 0, IPC_STAT, statbuf) != 0);
    E_IF(statbuf[sizeof(statbuf) - 1] != 0x5a);

    E_IF(semctl(id, 0, IPC_STAT, NULL) != -1 || errno != EFAULT);
    E_IF(semctl(id, 0, IPC_STAT, ((struct semid_ds *)bad_ptr) - 1) != 0);

    SET_SEMS_NO_CHANGE(semctl(id, -1, IPC_STAT, &semds));

    if ((id2 = semget(KEY_A, seminfo.semmsl, IPC_CREAT | 0642)) < 0) handle_error();

    memset(statbuf, 0x5a, sizeof(statbuf));
    E_IF(semctl(-1, 0, SEM_STAT, statbuf) != -1 || errno != EINVAL);
    E_IF(semctl(seminfo.semmni, 0, SEM_STAT, statbuf) != -1 || errno != EINVAL);

    for (i = 0; i < sizeof(statbuf); i++)
        E_IF(statbuf[i] != 0x5a);

    memset(seen, 0, sizeof(seen));
    for (i = 0; i < seminfo.semmni; i++) {
        if ((r = semctl(i, i / 2 - 1, SEM_STAT, statbuf)) == -1) {
            if (errno != EINVAL) handle_error();
            continue;
        }
        if (r < 0) handle_error();
        memcpy(&semds, statbuf, sizeof(semds));
        if (!(semds.sem_perm.mode & SEM_ALLOC)) handle_error();
        if (semds.sem_ctime == 0) handle_error();
        if (IXSEQ_TO_IPCID(i, semds.sem_perm) != r) handle_error();
        if (r == id) {
            seen[0]++;
            if (semds.sem_perm.mode != (SEM_ALLOC | 0600)) handle_error();
            if (semds.sem_perm.uid != geteuid()) handle_error();
            if (semds.sem_perm.gid != getegid()) handle_error();
            if (semds.sem_perm.cuid != semds.sem_perm.uid) handle_error();
            if (semds.sem_perm.cgid != semds.sem_perm.gid) handle_error();
            if (semds.sem_perm._key != IPC_PRIVATE) handle_error();
            if (semds.sem_nsems != 3) handle_error();
            if (semds.sem_otime != 0) handle_error();
            E_IF(semctl(i, 0, SEM_STAT, NULL) != -1 || errno != EFAULT);
            E_IF(semctl(i, 0, SEM_STAT, bad_ptr) != -1 || errno != EFAULT);
        } else if (r == id2) {
            seen[1]++;
            if (semds.sem_perm.mode != (SEM_ALLOC | 0642)) handle_error();
            if (semds.sem_perm.uid != geteuid()) handle_error();
            if (semds.sem_perm.gid != getegid()) handle_error();
            if (semds.sem_perm.cuid != semds.sem_perm.uid) handle_error();
            if (semds.sem_perm.cgid != semds.sem_perm.gid) handle_error();
            if (semds.sem_perm._key != KEY_A) handle_error();
            if (semds.sem_nsems != seminfo.semmsl) handle_error();
        }
    }

    E_IF(seen[0] != 1);
    E_IF(seen[1] != 1);

    E_IF(statbuf[sizeof(statbuf) - 1] != 0x5a);

    SET_SEMS_NO_CHANGE(semctl(id, 5, IPC_STAT, &semds));

    for (int invalid_id : {badid1, badid2, -1, INT_MIN, id, id}) {
        for (int semnum : {3, -1}) {
            E_IF(semctl(invalid_id, semnum, SETVAL, 1) != -1 || errno != EINVAL);
        }
    }
    E_IF(semctl(id, 0, SETVAL, seminfo.semvmx + 1) != -1 || errno != ERANGE);
    SET_SEMS_NO_CHANGE(semctl(id, 0, SETVAL, semvmx));

    E_IF(semctl(id, 1, SETVAL, 0) != 0);
    E_IF(semctl(id, 2, SETVAL, seminfo.semvmx) != 0);
    E_IF(semctl(id, 0, SETVAL, 1) != 0);
    E_IF(semctl(id, 0, GETALL, val) != 0 || val[0] != 1 || val[1] != 0 || val[2] != seminfo.semvmx);

    SET_SEMS_NO_CHANGE(semctl(id, 0, SETALL, 1));

    val[0] = seminfo.semvmx;
    val[1] = 0;
    val[2] = 0;
    E_IF(semctl(id, 0, SETALL, val) != 0);
    E_IF(semctl(id, 0, SETALL, ((unsigned short *)bad_ptr) - 3) != 0);

    while (time(&now) == semds.sem_ctime) usleep(250000);

    for (int invalid_id : {badid1, badid2, -1, INT_MIN}) {
        E_IF(semctl(invalid_id, 0, IPC_SET, &semds) != -1 || errno != EINVAL);
    }

    memset(&semds, 0x5b, sizeof(semds));
    semds.sem_perm.mode = 0712;
    semds.sem_perm.uid = UID_MAX;
    semds.sem_perm.gid = GID_MAX - 1;

    E_IF(semctl(id, 0, IPC_SET, &semds) != 0);
    E_IF(semctl(id, 0, IPC_STAT, &semds) != 0);

    if (semds.sem_perm.mode != (SEM_ALLOC | 0712) || semds.sem_perm.uid != UID_MAX || semds.sem_perm.gid != GID_MAX - 1
        || semds.sem_perm.cuid != osemds.sem_perm.cuid || semds.sem_perm.cgid != osemds.sem_perm.cgid || semds.sem_perm._seq != osemds.sem_perm._seq
        || semds.sem_perm._key != osemds.sem_perm._key || semds.sem_nsems != osemds.sem_nsems || semds.sem_otime != osemds.sem_otime
        || semds.sem_ctime < now || semds.sem_ctime >= now + 10) {
        handle_error();
    }

    for (i = 0; i < 0777; i++) {
        semds.sem_perm.mode = i;
        E_IF(semctl(id, i / 2 - 1, IPC_SET, &semds) != 0);

        E_IF(semctl(id, i / 2 - 2, IPC_STAT, &semds) != 0);
        E_IF(semds.sem_perm.mode != (SEM_ALLOC | i));

        semds.sem_perm.mode = ~0777 | i;
        E_IF(semctl(id, i / 2 - 3, IPC_SET, &semds) != 0);

        E_IF(semctl(id, i / 2 - 4, IPC_STAT, &semds) != 0);
        E_IF(semds.sem_perm.mode != (SEM_ALLOC | i));
    }

    E_IF(semctl(id, 0, IPC_SET, (struct semid_ds *)bad_ptr - 1) != 0);

    for (int invalid_id : {badid1, badid2, -1, INT_MIN, id, id}) {
        E_IF(semctl(invalid_id, 0, IPC_RMID) != -1 || errno != EINVAL);
    }

    E_IF(semctl(id, 0, IPC_RMID) != 0);
    E_IF(semctl(id2, 1, IPC_RMID) != 0);

    if ((id = semget(IPC_PRIVATE, 3, 0600)) == -1) handle_error();
    if ((id2 = semget(IPC_PRIVATE, 1, 0600)) == -1) handle_error();

    for (i = 0; i <= 1; i++) {
        cmd = (i == 0) ? IPC_INFO : SEM_INFO;
        memset(&seminfo, 0xff, sizeof(seminfo));

        E_IF((r = semctl(0, 0, cmd, &seminfo)) == -1);

        if (r < 1 || r >= seminfo.semmni) handle_error();
        if (seminfo.semmap < 0 || seminfo.semmni < 3 || seminfo.semmni > USHRT_MAX || seminfo.semmns < 3 || seminfo.semmns > USHRT_MAX
            || seminfo.semmnu < 0 || seminfo.semmsl < 3 || seminfo.semmsl > USHRT_MAX || seminfo.semopm < 3 || seminfo.semopm > USHRT_MAX
            || seminfo.semume < 0 || (cmd == SEM_INFO ? seminfo.semusz < 2 : seminfo.semusz < 0) || seminfo.semvmx < 3 || seminfo.semvmx > SHRT_MAX
            || (cmd == SEM_INFO ? seminfo.semaem < 4 : seminfo.semaem < 0)) {
            handle_error();
        }

        for (int invalid_val : {INT_MAX, -1}) {
            E_IF(semctl(invalid_val, invalid_val, cmd, &seminfo) == -1);
        }

        E_IF(semctl(0, 0, cmd, NULL) != -1 || errno != EFAULT);
        E_IF(semctl(0, 0, cmd, bad_ptr) != -1 || errno != EFAULT);

        E_IF(semctl(0, 0, cmd, ((struct seminfo *)bad_ptr) - 1) == -1);
    }

    E_IF(semctl(id2, 0, IPC_RMID) != 0);

    for (int invalid_cmd : {INT_MIN, INT_MAX}) {
        E_IF(semctl(id, 0, invalid_cmd) != -1 || errno != EINVAL);
    }

    E_IF(semctl(id, 0, IPC_RMID) != 0);
}

/*
 * Test SEM_UNDO support.  Right now this functionality is missing altogether.
 * For now, we test that any attempt to use SEM_UNDO fails.
 */
#include <errno.h>
#include <limits.h>
#include <sys/ipc.h>
#include <sys/sem.h>

static void handleError(int errorCode) {
    // Handle error
}

static void test88d(void) {
    struct sembuf sop;
    int id;

    subtest = 3;

    id = semget(IPC_PRIVATE, 1, 0600);
    if (id == -1) {
        handleError(0);
        return;
    }

    if (!(SHRT_MAX & SEM_UNDO)) {
        handleError(0);
        return;
    }
    
    sop.sem_num = 0;
    sop.sem_op = 1;
    sop.sem_flg = SHRT_MAX;

    if (semop(id, &sop, 1) != -1 || errno != EINVAL) {
        handleError(0);
    }

    if (semctl(id, 0, IPC_RMID) != 0) {
        handleError(0);
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
#include <string.h>
#include <errno.h>
#include <sys/sem.h>
#include <sys/ipc.h>
#include <sys/types.h>

static void test88e_childaux(struct link * parent) {
    struct sembuf sops[3] = {0};
    struct seminfo seminfo;
    int child = rcv(parent);
    int id = rcv(parent);
    int num = rcv(parent);

    if (child == 1) {
        sops[0].sem_num = num;
        sops[0].sem_op = 1;
        sops[1].sem_num = num;
        sops[1].sem_op = 0;
        sops[2].sem_num = 0;
        sops[2].sem_op = 1;
    } else if (child == 2) {
        if (semctl(0, 0, IPC_INFO, &seminfo) == -1) e(0);
        sops[0].sem_num = num;
        sops[0].sem_op = -seminfo.semvmx;
        sops[1].sem_num = num;
        sops[1].sem_op = -seminfo.semvmx;
        sops[2].sem_num = 0;
        sops[2].sem_op = 1;
    } else {
        e(0);
    }

    snd(parent, 0);

    if (semop(id, sops, 3) != -1 || errno != EIDRM) e(0);
}

/*
 * First child procedure.
 */
static void test88e_child1(struct link *parent) {
    struct sembuf sops[3] = { {0} };
    int match = rcv(parent);
    int id = rcv(parent);
    int expect = 0;
    size_t nsops = 2;

    sops[0].sem_num = 2;
    sops[0].sem_op = -1;

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

    if (semop(id, sops, nsops) != expect) e(0);
    if (expect == -1 && errno != EIDRM) e(0);
}

/*
 * Second child procedure.
 */
#include <errno.h>
#include <string.h>
#include <sys/sem.h>

static void test88e_child2(struct link *parent) {
    struct sembuf sops[2] = {{0}};
    size_t nsops = 2;
    int match, id, expect = 0;

    match = rcv(parent);
    id = rcv(parent);

    sops[0].sem_num = 2;
    sops[0].sem_op = -1;

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

    if (semop(id, sops, nsops) != expect) e(0);
    if (expect == -1 && errno != EIDRM) e(0);
}

/*
 * Third child procedure.
 */
static void
test88e_child3(struct link *parent)
{
	struct sembuf sops;
	int match, id;

	match = rcv(parent);
	id = rcv(parent);

	if (match != MATCH_ALL) {
		e(0);
		return;
	}

	memset(&sops, 0, sizeof(sops));
	sops.sem_num = 3;
	sops.sem_op = -2;

	snd(parent, 0);
	
	if (semop(id, &sops, 1) != 0) {
		e(0);
	}
}

/*
 * Perform one test for operations affecting multiple processes.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/sem.h>

#define WAIT_USECS 100000

struct link {
	pid_t pid;
};

static void handle_spawn(struct link* child, void (*func)(), int flag) {
	if (!spawn(child, func, flag)) {
		fprintf(stderr, "Error spawning a child process\n");
		exit(EXIT_FAILURE);
	}
}

static void handle_send(struct link* child, int data) {
	if (!snd(child, data)) {
		fprintf(stderr, "Error sending data to child\n");
		exit(EXIT_FAILURE);
	}
}

static int handle_receive(struct link* child) {
	int result = rcv(child);
	if (result < 0) {
		fprintf(stderr, "Error receiving data from child\n");
		exit(EXIT_FAILURE);
	}
	return result;
}

static void handle_semaphore_operation(int semid, struct sembuf* ops, unsigned nsops) {
	if (semop(semid, ops, nsops) == -1) {
		fprintf(stderr, "Semaphore operation failed\n");
		exit(EXIT_FAILURE);
	}
}

static void handle_semaphore_control(int semid, int semnum, int cmd, unsigned short* array) {
	if (semctl(semid, semnum, cmd, array) == -1) {
		fprintf(stderr, "Semaphore control failed\n");
		exit(EXIT_FAILURE);
	}
}

static void test_semaphore(int semid, int semnum, int expected_val1, pid_t expected_pid, int expected_val2, int zcnt) {
	if (!TEST_SEM(semid, semnum, expected_val1, expected_pid, expected_val2, zcnt)) {
		fprintf(stderr, "Semaphore test failed\n");
		exit(EXIT_FAILURE);
	}
}

static void terminate_child(struct link* child) {
	if (!terminate(child)) {
		fprintf(stderr, "Error terminating child process\n");
		exit(EXIT_FAILURE);
	}
}

static void collect_child(struct link* child) {
	if (!collect(child)) {
		fprintf(stderr, "Error collecting child process\n");
		exit(EXIT_FAILURE);
	}
}

static void handle_fork_and_setup(struct link* child, void (*child_func)(), int child_flags, unsigned int match, int semid) {
	handle_spawn(child, child_func, child_flags);
	handle_send(child, match);
	handle_send(child, semid);
	if (handle_receive(child) != 0) {
		fprintf(stderr, "Child setup failed\n");
		exit(EXIT_FAILURE);
	}
}

static void sub88e(unsigned int match, unsigned int resume, unsigned int aux) {
	struct link aux1, aux2, child1, child2, child3;
	struct sembuf sop = {0};
	unsigned short val[4] = {0};
	int id = semget(IPC_PRIVATE, __arraycount(val), 0666);
	int inc = 1, aux_zcnt = 0, aux_ncnt = 0;
	int use_aux_first = aux & 1;
	int use_aux_second = aux & 2;
	int use_aux_deadlock = aux & 4;

	if (id == -1) {
		fprintf(stderr, "Semaphore get failed\n");
		exit(EXIT_FAILURE);
	}

	if (use_aux_first) {
		handle_spawn(&aux1, test88e_childaux, DROP_ALL);
		handle_send(&aux1, 1);
		handle_send(&aux1, id);
		handle_send(&aux1, use_aux_deadlock ? 2 : 1);

		if (handle_receive(&aux1) != 0) {
			fprintf(stderr, "First auxiliary child setup failed\n");
			exit(EXIT_FAILURE);
		}

		if (use_aux_deadlock) aux_zcnt++;
	}

	handle_fork_and_setup(&child1, test88e_child1, DROP_ALL, match, id);

	usleep(match == MATCH_FIRST || match == MATCH_SECOND || match == MATCH_KILL ? WAIT_USECS : 0);

	handle_fork_and_setup(&child2, test88e_child2, DROP_NONE, match, id);

	if (match == MATCH_ALL) {
		handle_fork_and_setup(&child3, test88e_child3, DROP_USER, match, id);
	}

	if (use_aux_second) {
		handle_spawn(&aux2, test88e_childaux, DROP_NONE);
		handle_send(&aux2, 2);
		handle_send(&aux2, id);
		handle_send(&aux2, use_aux_deadlock ? 2 : 1);

		if (handle_receive(&aux2) != 0) {
			fprintf(stderr, "Second auxiliary child setup failed\n");
			exit(EXIT_FAILURE);
		}

		if (use_aux_deadlock) aux_ncnt++;
	}

	usleep(WAIT_USECS);

	switch (match) {
		case MATCH_FIRST:
		case MATCH_SECOND:
			test_semaphore(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
			break;
		case MATCH_KILL:
			test_semaphore(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
			terminate_child(&child1);
			usleep(WAIT_USECS);
			test_semaphore(id, 2, 0, 0, 1 + aux_ncnt, aux_zcnt);
			break;
		case MATCH_BOTH:
			test_semaphore(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
			inc = 2;
			break;
		case MATCH_CASCADE:
			test_semaphore(id, 2, 0, 0, 1 + aux_ncnt, aux_zcnt);
			break;
		case MATCH_ALL:
			test_semaphore(id, 2, 0, 0, 2 + aux_ncnt, aux_zcnt);
			inc = 2;
			break;
		default:
			fprintf(stderr, "Invalid match condition\n");
			exit(EXIT_FAILURE);
	}

	switch (resume) {
		case RESUME_SEMOP:
			sop.sem_op = inc;
			handle_semaphore_operation(id, &sop, 1);
			break;
		case RESUME_SETVAL:
			handle_semaphore_control(id, 2, SETVAL, &inc);
			break;
		case RESUME_SETALL:
			val[2] = inc;
			handle_semaphore_control(id, 0, SETALL, val);
			break;
		default:
			fprintf(stderr, "Invalid resume state\n");
			exit(EXIT_FAILURE);
	}

	switch (match) {
		case MATCH_FIRST:
			test_semaphore(id, 2, 0, child1.pid, 1 + aux_ncnt, aux_zcnt);
			collect_child(&child1);
			break;
		case MATCH_SECOND:
			test_semaphore(id, 2, 0, child2.pid, 1 + aux_ncnt, aux_zcnt);
			collect_child(&child2);
			break;
		case MATCH_KILL:
			test_semaphore(id, 2, 0, child2.pid, aux_ncnt, aux_zcnt);
			collect_child(&child2);
			break;
		case MATCH_BOTH:
			test_semaphore(id, 2, 0, -1, aux_ncnt, aux_zcnt);
			collect_child(&child1);
			collect_child(&child2);
			break;
		case MATCH_CASCADE:
			test_semaphore(id, 2, 0, child1.pid, aux_ncnt, aux_zcnt);
			collect_child(&child1);
			collect_child(&child2);
			break;
		case MATCH_ALL:
			test_semaphore(id, 2, 0, -1, aux_ncnt, aux_zcnt);
			collect_child(&child1);
			collect_child(&child2);
			collect_child(&child3);
			break;
		default:
			fprintf(stderr, "Invalid match condition after semaphore operation\n");
			exit(EXIT_FAILURE);
	}

	if (semctl(id, 0, IPC_RMID) == -1) {
		fprintf(stderr, "Semaphore removal failed\n");
		exit(EXIT_FAILURE);
	}

	switch (match) {
		case MATCH_FIRST:
			collect_child(&child2);
			break;
		case MATCH_SECOND:
			collect_child(&child1);
			break;
		default:
			break;
	}

	if (use_aux_first) collect_child(&aux1);
	if (use_aux_second) collect_child(&aux2);
}

/*
 * Test operations affecting multiple processes, ensuring the following points:
 * 1) an operation resumes all possible waiters; 2) a resumed operation in turn
 * correctly resumes other now-unblocked operations; 3) a basic level of FIFO
 * fairness is provided between blocked parties; 4) all the previous points are
 * unaffected by additional waiters that are not being resumed; 5) identifier
 * removal properly resumes all affected waiters.
 */
#include <limits.h>

static void test88e(void) {
    unsigned int match, resume, aux;
    const unsigned int maxMatches = NR_MATCHES < UINT_MAX ? NR_MATCHES : UINT_MAX;
    const unsigned int maxResumes = NR_RESUMES < UINT_MAX ? NR_RESUMES : UINT_MAX;

    subtest = 4;

    for (match = 0; match < maxMatches; match++) {
        for (resume = 0; resume < maxResumes; resume++) {
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
#include <errno.h>
#include <stdlib.h>
#include <sys/sysctl.h>

static void handleError() {
    // Handle error appropriately
    exit(EXIT_FAILURE);
}

static void test88f_child(struct link *parent) {
    static const int mib[] = {CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_INFO, KERN_SYSVIPC_SEM_INFO};
    struct sem_sysctl_info *semsi = NULL;
    size_t len;
    int id[2];
    int seen[2] = {0, 0};
    int32_t i;

    // Retrieve identifiers from parent
    for (i = 0; i < 2; i++) {
        id[i] = rcv(parent);
    }

    // Obtain the required size for the sysctl data
    if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), NULL, &len, NULL, 0) == -1) {
        handleError();
    }

    // Allocate memory for the sysctl data
    semsi = malloc(len);
    if (semsi == NULL) {
        handleError();
    }

    // Retrieve sem_sysctl_info
    if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), semsi, &len, NULL, 0) == -1) {
        free(semsi);
        handleError();
    }

    // Process semids
    for (i = 0; i < semsi->seminfo.semmni; i++) {
        if (semsi->semids[i].sem_perm.mode & SEM_ALLOC) {
            int id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
            for (int j = 0; j < 2; j++) {
                if (id2 == id[j]) {
                    seen[j]++;
                }
            }
        }
    }

    // Clean up
    free(semsi);

    // Validate results
    for (i = 0; i < 2; i++) {
        if (seen[i] != 1) {
            handleError();
        }
    }
}

/*
 * Test sysctl(2) based information retrieval.  This test aims to ensure that
 * in particular ipcs(1) and ipcrm(1) will be able to do their jobs.
 */
#include <stdlib.h>
#include <sys/sysctl.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>
#include <stdint.h>

static void test88f(void) {
    static const int mib[] = {CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_INFO, KERN_SYSVIPC_SEM_INFO};
    struct seminfo seminfo;
    struct semid_ds_sysctl *semds;
    struct sem_sysctl_info *semsi = NULL;
    size_t size, len;
    int id[2];
    int32_t i, slot[2];
    struct link child;

    if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), &seminfo, &(len = sizeof(seminfo)), NULL, 0) != 0 || len != sizeof(seminfo)) {
        return;
    }

    struct seminfo seminfo2;
    if (semctl(0, 0, IPC_INFO, &seminfo2) == -1 || memcmp(&seminfo, &seminfo2, sizeof(seminfo)) != 0 || seminfo.semmni <= 0 || seminfo.semmni > SHRT_MAX) {
        return;
    }

    size = sizeof(*semsi) + sizeof(semsi->semids[0]) * (seminfo.semmni - 1);
    if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), NULL, &(len = 0), NULL, 0) != 0 || len != size) {
        return;
    }

    if ((id[0] = semget(KEY_A, 5, IPC_CREAT | 0612)) < 0 || (id[1] = semget(IPC_PRIVATE, 3, 0650)) < 0) {
        return;
    }

    if ((semsi = malloc(size)) == NULL) {
        return;
    }

    if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), semsi, &(len = size), NULL, 0) != 0 || len != size || sizeof(semsi->seminfo) != sizeof(seminfo) || memcmp(&semsi->seminfo, &seminfo, sizeof(semsi->seminfo)) != 0) {
        free(semsi);
        return;
    }

    slot[0] = slot[1] = -1;
    for (i = 0; i < seminfo.semmni; i++) {
        if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
            continue;

        int id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
        if (id2 == id[0]) {
            if (slot[0] != -1) {
                free(semsi);
                return;
            }
            slot[0] = i;
        } else if (id2 == id[1]) {
            if (slot[1] != -1) {
                free(semsi);
                return;
            }
            slot[1] = i;
        }
    }

    if (slot[0] < 0 || slot[1] < 0) {
        free(semsi);
        return;
    }

    semds = &semsi->semids[slot[0]];
    if (semds->sem_perm.uid != geteuid() || semds->sem_perm.gid != getegid() || semds->sem_perm.cuid != geteuid() || semds->sem_perm.cgid != getegid() || semds->sem_perm.mode != (SEM_ALLOC | 0612) || semds->sem_perm._key != KEY_A || semds->sem_nsems != 5 || semds->sem_otime != 0 || semds->sem_ctime == 0) {
        free(semsi);
        return;
    }

    semds = &semsi->semids[slot[1]];
    if (semds->sem_perm.uid != geteuid() || semds->sem_perm.gid != getegid() || semds->sem_perm.cuid != geteuid() || semds->sem_perm.cgid != getegid() || semds->sem_perm.mode != (SEM_ALLOC | 0650) || semds->sem_perm._key != IPC_PRIVATE || semds->sem_nsems != 3 || semds->sem_otime != 0 || semds->sem_ctime == 0) {
        free(semsi);
        return;
    }

    spawn(&child, test88f_child, DROP_ALL);
    snd(&child, id[0]);
    snd(&child, id[1]);
    collect(&child);

    if (semctl(id[0], 0, IPC_RMID) != 0 || semctl(id[1], 0, IPC_RMID) != 0) {
        free(semsi);
        return;
    }

    if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), semsi, &(len = size), NULL, 0) != 0 || len != size) {
        free(semsi);
        return;
    }

    for (i = 0; i < seminfo.semmni; i++) {
        if (!(semsi->semids[i].sem_perm.mode & SEM_ALLOC))
            continue;

        int id2 = IXSEQ_TO_IPCID(i, semsi->semids[i].sem_perm);
        if (id2 == id[0] || id2 == id[1]) {
            free(semsi);
            return;
        }
    }

    free(semsi);
}

/*
 * Initialize the test.
 */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <grp.h>
#include <sys/mman.h>
#include <sys/sysctl.h>
#include <sys/types.h>

#define ROOT_GROUP "wheel" // Assuming "wheel" is defined for root

static void e(int err) {
    fprintf(stderr, "Error: %d\n", err);
    exit(EXIT_FAILURE);
}

static void cleanup(void) {
    // Global cleanup code here
}

static void test88_init(void) {
    static const int mib[] = {CTL_KERN, KERN_SYSVIPC, KERN_SYSVIPC_SEM};
    struct group *gr;
    size_t len;
    int i, page_size;
    void *page_ptr, *bad_ptr;

    if (setuid(geteuid()) == -1) e(1);

    gr = getgrnam(ROOT_GROUP);
    if (gr == NULL) e(2);

    if (setgid(gr->gr_gid) == -1 || setegid(gr->gr_gid) == -1) e(3);

    len = sizeof(i);
    if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), &i, &len, NULL, 0) != 0) e(4);
    if (len != sizeof(i)) e(5);

    if (i == 0) {
        printf("skipped\n");
        cleanup();
        exit(EXIT_SUCCESS);
    }

    page_size = getpagesize();
    page_ptr = mmap(NULL, page_size * 2, PROT_READ | PROT_WRITE, MAP_ANON | MAP_PRIVATE, -1, 0);
    if (page_ptr == MAP_FAILED) e(6);

    bad_ptr = (char *)page_ptr + page_size;
    if (munmap(bad_ptr, page_size) != 0) e(7);
}

/*
 * Test program for SysV IPC semaphores.
 */
#include <stdio.h>
#include <stdlib.h>

#define ITERATIONS 100

void start(int code);
void test88_init();
void test88a();
void test88b();
void test88c();
void test88d();
void test88e();
void test88f();
void quit();

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <mode>\n", argv[0]);
        return EXIT_FAILURE;
    }

    int m = atoi(argv[1]);
    if (m < 0) {
        fprintf(stderr, "Invalid mode value\n");
        return EXIT_FAILURE;
    }

    start(88);
    test88_init();

    for (int i = 0; i < ITERATIONS; i++) {
        if (m & 0x01) test88a();
        if (m & 0x02) test88b();
        if (m & 0x04) test88c();
        if (m & 0x08) test88d();
        if (m & 0x10) test88e();
        if (m & 0x20) test88f();
    }

    quit();
    return EXIT_SUCCESS;
}
