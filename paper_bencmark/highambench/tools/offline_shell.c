/*
 * HighamBench shell launcher.
 *
 * The Codex control process needs a network connection to the model provider,
 * while commands chosen by the evaluated agent must be offline.  This small
 * launcher installs a seccomp filter in the command process and then starts
 * Bash.  Seccomp filters are inherited by every descendant, so a submitted
 * script cannot restore socket access by starting another shell or program.
 * A small supervisor answers every blocked request with EPERM and appends a
 * byte to the per-run marker named by HIGHAMBENCH_NETWORK_VIOLATION_MARKER.
 * Cross-process signal and metadata mutation calls are denied and marked.
 * kill(0, ...) is the one signal exception: the Bash child has its own process
 * group, so that form cannot reach the provider-facing app-server.  This keeps
 * ordinary in-group cleanup available without allowing guessed PIDs or process
 * groups to disrupt the trusted controller.
 *
 * Build with:
 *   cc -std=c11 -O2 -Wall -Wextra -Werror -o offline-shell offline_shell.c
 */

#define _GNU_SOURCE

#include <errno.h>
#include <dirent.h>
#include <fcntl.h>
#include <ftw.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/landlock.h>
#include <linux/seccomp.h>
#include <stddef.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#if !defined(__x86_64__)
#error "HighamBench offline_shell currently supports x86-64 only"
#endif

#define NOTIFY_SYSCALL(name)                                                  \
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_##name, 0, 1),                    \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF)

#define RELOAD_SYSCALL                                                        \
  BPF_STMT(BPF_LD | BPF_W | BPF_ABS,                                         \
           (unsigned int)offsetof(struct seccomp_data, nr))

#define HIGHAMBENCH_MAX_WRITTEN_FILE_BYTES (256ULL * 1024ULL * 1024ULL)
#define HIGHAMBENCH_MAX_WORKSPACE_BYTES (1024ULL * 1024ULL * 1024ULL)
#define HIGHAMBENCH_MAX_WORKSPACE_ENTRIES 10000ULL

#ifndef __X32_SYSCALL_BIT
#define __X32_SYSCALL_BIT 0x40000000U
#endif

#ifndef LANDLOCK_ACCESS_FS_REFER
#define LANDLOCK_ACCESS_FS_REFER (1ULL << 13)
#endif
#ifndef LANDLOCK_ACCESS_FS_TRUNCATE
#define LANDLOCK_ACCESS_FS_TRUNCATE (1ULL << 14)
#endif
#ifndef LANDLOCK_ACCESS_FS_IOCTL_DEV
#define LANDLOCK_ACCESS_FS_IOCTL_DEV (1ULL << 15)
#endif

/* kill(0, sig) is confined to the evaluated Bash process group.  Every other
 * target form, including a positive guessed PID, -1, and negative process
 * groups, is a benchmark rule violation. */
#define NOTIFY_KILL_EXCEPT_OWN_GROUP(name)                                    \
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_##name, 0, 3),                    \
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,                                     \
               (unsigned int)offsetof(struct seccomp_data, args[0])),         \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 1, 0),                          \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF), RELOAD_SYSCALL

/* Let a process create a fresh group led by itself, but prevent descendants
 * from joining the provider app-server's group before using kill(0, ...). */
#define NOTIFY_SETPGID_EXCEPT_SELF_NEW_GROUP(name)                            \
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_##name, 0, 5),                    \
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,                                     \
               (unsigned int)offsetof(struct seccomp_data, args[0])),         \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 0, 2),                          \
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,                                     \
               (unsigned int)offsetof(struct seccomp_data, args[1])),         \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 1, 0),                          \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF), RELOAD_SYSCALL

/* Permit a process to inspect or lower its own limits. Inherited hard limits
 * still prevent it from raising the file/core ceilings installed below, while
 * a nonzero PID remains a cross-process mutation and is reported. */
#define NOTIFY_PRLIMIT_EXCEPT_SELF(name)                                      \
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_##name, 0, 3),                    \
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,                                     \
               (unsigned int)offsetof(struct seccomp_data, args[0])),         \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 1, 0),                          \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF), RELOAD_SYSCALL

/* Keep ordinary descriptor flags and locks available, but block the fcntl
 * commands that arrange asynchronous signals to an arbitrary same-UID owner. */
#define NOTIFY_FCNTL_SIGNAL_OWNER_COMMANDS(name)                               \
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_##name, 0, 7),                    \
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,                                     \
               (unsigned int)offsetof(struct seccomp_data, args[1])),         \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, F_SETOWN, 0, 1),                   \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF),                     \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, F_SETSIG, 0, 1),                   \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF),                     \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, F_SETOWN_EX, 0, 1),                \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF), RELOAD_SYSCALL

#ifndef FIOASYNC
#define FIOASYNC 0x5452
#endif
#ifndef FIOSETOWN
#define FIOSETOWN 0x8901
#endif
#ifndef FIOSETOWN_EX
#define FIOSETOWN_EX 0x4008667cU
#endif
#ifndef SIOCSPGRP
#define SIOCSPGRP 0x8902
#endif
#ifndef TIOCSPGRP
#define TIOCSPGRP 0x5410
#endif

/* The equivalent ioctl ownership/job-control requests are also signal paths. */
#define NOTIFY_IOCTL_SIGNAL_OWNER_COMMANDS(name)                               \
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_##name, 0, 11),                   \
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,                                     \
               (unsigned int)offsetof(struct seccomp_data, args[1])),         \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, FIOASYNC, 0, 1),                   \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF),                     \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, FIOSETOWN, 0, 1),                  \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF),                     \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, FIOSETOWN_EX, 0, 1),               \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF),                     \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SIOCSPGRP, 0, 1),                  \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF),                     \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, TIOCSPGRP, 0, 1),                  \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF), RELOAD_SYSCALL

static int install_offline_filter(void) {
  struct sock_filter filter[] = {
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,
               (unsigned int)offsetof(struct seccomp_data, arch)),
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AUDIT_ARCH_X86_64, 1, 0),
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,
               (unsigned int)offsetof(struct seccomp_data, nr)),
      /* x32 shares AUDIT_ARCH_X86_64 but ORs this bit into syscall numbers.
       * Route the whole compatibility ABI through the denying supervisor so
       * its socket calls cannot bypass the native-number rules below. */
      BPF_JUMP(BPF_JMP | BPF_JSET | BPF_K, __X32_SYSCALL_BIT, 0, 1),
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF),
      NOTIFY_SYSCALL(socket),
      NOTIFY_SYSCALL(connect),
      NOTIFY_SYSCALL(bind),
      NOTIFY_SYSCALL(listen),
      NOTIFY_SYSCALL(accept),
      NOTIFY_SYSCALL(accept4),
      NOTIFY_SYSCALL(sendto),
      NOTIFY_SYSCALL(recvfrom),
      NOTIFY_SYSCALL(sendmsg),
      NOTIFY_SYSCALL(recvmsg),
      NOTIFY_SYSCALL(sendmmsg),
      NOTIFY_SYSCALL(recvmmsg),
      NOTIFY_SYSCALL(shutdown),
      NOTIFY_SYSCALL(io_uring_setup),
      /* The Codex control process keeps the provider connection outside the
       * command tree.  Prevent a same-UID command from inspecting that parent
       * or duplicating one of its already-open descriptors. */
      NOTIFY_SYSCALL(ptrace),
#if defined(__NR_process_vm_readv)
      NOTIFY_SYSCALL(process_vm_readv),
#endif
#if defined(__NR_process_vm_writev)
      NOTIFY_SYSCALL(process_vm_writev),
#endif
#if defined(__NR_pidfd_getfd)
      NOTIFY_SYSCALL(pidfd_getfd),
#endif
#if defined(__NR_perf_event_open)
      NOTIFY_SYSCALL(perf_event_open),
#endif
#if defined(__NR_bpf)
      NOTIFY_SYSCALL(bpf),
#endif
#if defined(__NR_kcmp)
      NOTIFY_SYSCALL(kcmp),
#endif
      NOTIFY_KILL_EXCEPT_OWN_GROUP(kill),
      NOTIFY_SETPGID_EXCEPT_SELF_NEW_GROUP(setpgid),
      NOTIFY_FCNTL_SIGNAL_OWNER_COMMANDS(fcntl),
      NOTIFY_IOCTL_SIGNAL_OWNER_COMMANDS(ioctl),
      NOTIFY_SYSCALL(tkill),
      NOTIFY_SYSCALL(tgkill),
#if defined(__NR_rt_sigqueueinfo)
      NOTIFY_SYSCALL(rt_sigqueueinfo),
#endif
#if defined(__NR_rt_tgsigqueueinfo)
      NOTIFY_SYSCALL(rt_tgsigqueueinfo),
#endif
#if defined(__NR_pidfd_open)
      NOTIFY_SYSCALL(pidfd_open),
#endif
#if defined(__NR_pidfd_send_signal)
      NOTIFY_SYSCALL(pidfd_send_signal),
#endif
      /* Generated commands may tune only their own algorithms through normal
       * computation. Cross-process rlimit, scheduler, NUMA, and I/O-priority
       * controls could otherwise target PID 1 (the provider-facing app-server)
       * inside the shared PID namespace and bias or abort a measurement. These
       * mutation syscalls are uncommon in Lean tooling, so deny all forms. */
#if defined(__NR_prlimit64)
      NOTIFY_PRLIMIT_EXCEPT_SELF(prlimit64),
#endif
      NOTIFY_SYSCALL(setpriority),
      NOTIFY_SYSCALL(sched_setaffinity),
      NOTIFY_SYSCALL(sched_setparam),
      NOTIFY_SYSCALL(sched_setscheduler),
#if defined(__NR_sched_setattr)
      NOTIFY_SYSCALL(sched_setattr),
#endif
#if defined(__NR_ioprio_set)
      NOTIFY_SYSCALL(ioprio_set),
#endif
#if defined(__NR_migrate_pages)
      NOTIFY_SYSCALL(migrate_pages),
#endif
#if defined(__NR_move_pages)
      NOTIFY_SYSCALL(move_pages),
#endif
#if defined(__NR_process_madvise)
      NOTIFY_SYSCALL(process_madvise),
#endif
#if defined(__NR_process_mrelease)
      NOTIFY_SYSCALL(process_mrelease),
#endif
      /* Landlock intentionally protects data and path topology. Current
       * Landlock ABIs do not mediate ownership, mode, xattr, or timestamp
       * changes. Deny those calls globally in generated commands so they
       * cannot corrupt the same-UID app-server control mount. */
      NOTIFY_SYSCALL(chmod),
      NOTIFY_SYSCALL(fchmod),
      NOTIFY_SYSCALL(fchmodat),
#if defined(__NR_fchmodat2)
      NOTIFY_SYSCALL(fchmodat2),
#endif
      NOTIFY_SYSCALL(chown),
      NOTIFY_SYSCALL(fchown),
      NOTIFY_SYSCALL(lchown),
      NOTIFY_SYSCALL(fchownat),
      NOTIFY_SYSCALL(setxattr),
      NOTIFY_SYSCALL(lsetxattr),
      NOTIFY_SYSCALL(fsetxattr),
      NOTIFY_SYSCALL(removexattr),
      NOTIFY_SYSCALL(lremovexattr),
      NOTIFY_SYSCALL(fremovexattr),
#if defined(__NR_utime)
      NOTIFY_SYSCALL(utime),
#endif
      NOTIFY_SYSCALL(utimes),
#if defined(__NR_futimesat)
      NOTIFY_SYSCALL(futimesat),
#endif
      NOTIFY_SYSCALL(utimensat),
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
  };
  struct sock_fprog program = {
      .len = (unsigned short)(sizeof(filter) / sizeof(filter[0])),
      .filter = filter,
  };

  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) {
    return -1;
  }
  return (int)syscall(__NR_seccomp, SECCOMP_SET_MODE_FILTER,
                      SECCOMP_FILTER_FLAG_NEW_LISTENER, &program);
}

static uint64_t handled_filesystem_rights(int abi) {
  uint64_t handled = LANDLOCK_ACCESS_FS_EXECUTE | LANDLOCK_ACCESS_FS_WRITE_FILE |
                     LANDLOCK_ACCESS_FS_READ_FILE | LANDLOCK_ACCESS_FS_READ_DIR |
                     LANDLOCK_ACCESS_FS_REMOVE_DIR |
                     LANDLOCK_ACCESS_FS_REMOVE_FILE |
                     LANDLOCK_ACCESS_FS_MAKE_CHAR |
                     LANDLOCK_ACCESS_FS_MAKE_DIR |
                     LANDLOCK_ACCESS_FS_MAKE_REG |
                     LANDLOCK_ACCESS_FS_MAKE_SOCK |
                     LANDLOCK_ACCESS_FS_MAKE_FIFO |
                     LANDLOCK_ACCESS_FS_MAKE_BLOCK |
                     LANDLOCK_ACCESS_FS_MAKE_SYM | LANDLOCK_ACCESS_FS_REFER |
                     LANDLOCK_ACCESS_FS_TRUNCATE;
  if (abi >= 5) {
    handled |= LANDLOCK_ACCESS_FS_IOCTL_DEV;
  }
  return handled;
}

static int add_landlock_path_rule(int ruleset_fd, const char *path,
                                  uint64_t allowed_access) {
  int path_fd = open(path, O_PATH | O_CLOEXEC);
  if (path_fd < 0) {
    if (errno == ENOENT) {
      return 0;
    }
    return -1;
  }
  struct landlock_path_beneath_attr rule = {
      .allowed_access = allowed_access,
      .parent_fd = path_fd,
  };
  int result = (int)syscall(__NR_landlock_add_rule, ruleset_fd,
                            LANDLOCK_RULE_PATH_BENEATH, &rule, 0);
  int saved_errno = errno;
  close(path_fd);
  errno = saved_errno;
  return result;
}

static int install_command_filesystem_filter(void) {
  int abi = (int)syscall(__NR_landlock_create_ruleset, NULL, 0,
                         LANDLOCK_CREATE_RULESET_VERSION);
  if (abi < 3) {
    errno = EOPNOTSUPP;
    return -1;
  }
  uint64_t handled = handled_filesystem_rights(abi);
  struct landlock_ruleset_attr ruleset = {
      .handled_access_fs = handled,
  };
  int ruleset_fd = (int)syscall(__NR_landlock_create_ruleset, &ruleset,
                                sizeof(ruleset), 0);
  if (ruleset_fd < 0) {
    return -1;
  }

  const uint64_t read_execute = LANDLOCK_ACCESS_FS_EXECUTE |
                                LANDLOCK_ACCESS_FS_READ_FILE |
                                LANDLOCK_ACCESS_FS_READ_DIR;
  uint64_t device_access = LANDLOCK_ACCESS_FS_READ_FILE |
                           LANDLOCK_ACCESS_FS_WRITE_FILE |
                           LANDLOCK_ACCESS_FS_READ_DIR;
  if (abi >= 5) {
    device_access |= LANDLOCK_ACCESS_FS_IOCTL_DEV;
  }
  const char *read_only_paths[] = {
      "/usr/bin",           "/usr/lib",        "/usr/lib64",
      "/usr/share/zoneinfo", "/usr/share/fonts", "/usr/share/fontconfig",
      "/usr/share/poppler", "/usr/share/mime", "/lib",
      "/lib64",             "/etc/ssl",        "/etc/ca-certificates",
      "/etc/pki",           "/etc/fonts",      "/etc/ld.so.conf.d",
      "/lean",              "/packages",       "/library",
      "/library-olean",
  };
  const char *read_only_files[] = {
      "/etc/passwd",       "/etc/group",      "/etc/resolv.conf",
      "/etc/hosts",        "/etc/nsswitch.conf", "/etc/gai.conf",
      "/etc/services",     "/etc/protocols", "/etc/localtime",
      "/etc/timezone",     "/etc/ld.so.cache", "/etc/ld.so.conf",
  };
  /* Writable scratch supports ordinary source/build files and directories,
   * but not symlinks, FIFOs, sockets, or device nodes. Keeping special nodes
   * out of host-backed workspaces makes later non-following evidence scans
   * bounded and prevents a generated path from bricking incident sealing. */
  const uint64_t write_access =
      LANDLOCK_ACCESS_FS_EXECUTE | LANDLOCK_ACCESS_FS_WRITE_FILE |
      LANDLOCK_ACCESS_FS_READ_FILE | LANDLOCK_ACCESS_FS_READ_DIR |
      LANDLOCK_ACCESS_FS_REMOVE_DIR | LANDLOCK_ACCESS_FS_REMOVE_FILE |
      LANDLOCK_ACCESS_FS_MAKE_DIR | LANDLOCK_ACCESS_FS_MAKE_REG |
      LANDLOCK_ACCESS_FS_REFER | LANDLOCK_ACCESS_FS_TRUNCATE;
  const char *write_paths[] = {"/workspace", "/tmp", "/home/bench"};

  for (size_t index = 0;
       index < sizeof(read_only_paths) / sizeof(read_only_paths[0]); ++index) {
    if (add_landlock_path_rule(ruleset_fd, read_only_paths[index],
                               read_execute) != 0) {
      close(ruleset_fd);
      return -1;
    }
  }
  for (size_t index = 0;
       index < sizeof(read_only_files) / sizeof(read_only_files[0]); ++index) {
    if (add_landlock_path_rule(ruleset_fd, read_only_files[index],
                               LANDLOCK_ACCESS_FS_READ_FILE) != 0) {
      close(ruleset_fd);
      return -1;
    }
  }
  for (size_t index = 0;
       index < sizeof(write_paths) / sizeof(write_paths[0]); ++index) {
    if (add_landlock_path_rule(ruleset_fd, write_paths[index], write_access) != 0) {
      close(ruleset_fd);
      return -1;
    }
  }
  if (add_landlock_path_rule(ruleset_fd, "/dev", device_access) != 0) {
    close(ruleset_fd);
    return -1;
  }
  if (syscall(__NR_landlock_restrict_self, ruleset_fd, 0) != 0) {
    int saved_errno = errno;
    close(ruleset_fd);
    errno = saved_errno;
    return -1;
  }
  return close(ruleset_fd);
}

static int close_inherited_fds(int keep_one, int keep_two) {
  DIR *directory = opendir("/proc/self/fd");
  if (directory == NULL) {
    long maximum = sysconf(_SC_OPEN_MAX);
    if (maximum < 0) {
      return -1;
    }
    for (int descriptor = 3; descriptor < maximum; ++descriptor) {
      if (descriptor != keep_one && descriptor != keep_two) {
        close(descriptor);
      }
    }
    return 0;
  }
  int directory_fd = dirfd(directory);
  struct dirent *entry;
  while ((entry = readdir(directory)) != NULL) {
    char *end = NULL;
    errno = 0;
    long descriptor = strtol(entry->d_name, &end, 10);
    if (errno == 0 && end != entry->d_name && *end == '\0' && descriptor >= 3 &&
        descriptor != directory_fd && descriptor != keep_one &&
        descriptor != keep_two) {
      close((int)descriptor);
    }
  }
  return closedir(directory);
}

static int enter_command_cgroup(void) {
  const char *path = getenv("HIGHAMBENCH_COMMAND_CGROUP_PROCS");
  if (path == NULL || path[0] == '\0') {
    /* The installer runs a provider-free shell canary before the measured
     * systemd scope exists. Official runs require and mount this variable. */
    return 0;
  }
  int descriptor = open(path, O_WRONLY | O_CLOEXEC | O_NOFOLLOW);
  if (descriptor < 0) {
    return -1;
  }
  char identity[32];
  int length = snprintf(identity, sizeof(identity), "%ld", (long)getpid());
  int result = 0;
  if (length <= 0 || (size_t)length >= sizeof(identity) ||
      write(descriptor, identity, (size_t)length) != length) {
    result = -1;
  }
  int saved_errno = errno;
  if (close(descriptor) != 0) {
    result = -1;
    saved_errno = errno;
  }
  if (unsetenv("HIGHAMBENCH_COMMAND_CGROUP_PROCS") != 0) {
    result = -1;
    saved_errno = errno;
  }
  errno = saved_errno;
  return result;
}

static int mark_violation(int marker_fd) {
  /* Bound the audit marker even if a command loops on a denied call. */
  struct stat status;
  if (fstat(marker_fd, &status) != 0) {
    return -1;
  }
  if (status.st_size >= 4096) {
    return 0;
  }
  for (;;) {
    ssize_t written = write(marker_fd, "N", 1);
    if (written == 1) {
      return 0;
    }
    if (written < 0 && errno == EINTR) {
      continue;
    }
    return -1;
  }
}

static int answer_one_notification(int listener_fd, int marker_fd) {
  struct seccomp_notif request;
  struct seccomp_notif_resp response;
  memset(&request, 0, sizeof(request));
  memset(&response, 0, sizeof(response));

  if (ioctl(listener_fd, SECCOMP_IOCTL_NOTIF_RECV, &request) != 0) {
    if (errno == EINTR || errno == ENOENT) {
      return 0;
    }
    return -1;
  }
  if (mark_violation(marker_fd) != 0) {
    return -1;
  }
  response.id = request.id;
  response.error = -EPERM;
  if (ioctl(listener_fd, SECCOMP_IOCTL_NOTIF_SEND, &response) != 0 &&
      errno != ENOENT) {
    return -1;
  }
  return 0;
}

static uint64_t workspace_entry_count;
static uint64_t workspace_total_bytes;

static int inspect_workspace_entry(const char *path, const struct stat *status,
                                   int type, struct FTW *position) {
  (void)path;
  if (position->level == 0) {
    return 0;
  }
  ++workspace_entry_count;
  if (workspace_entry_count > HIGHAMBENCH_MAX_WORKSPACE_ENTRIES) {
    return 1;
  }
  if (type == FTW_D) {
    if ((status->st_mode & (S_IRUSR | S_IXUSR)) != (S_IRUSR | S_IXUSR)) {
      return 1;
    }
    return 0;
  }
  if (type != FTW_F || !S_ISREG(status->st_mode) ||
      (status->st_mode & S_IRUSR) == 0 || status->st_size < 0) {
    return 1;
  }
  uint64_t size = (uint64_t)status->st_size;
  if (size > HIGHAMBENCH_MAX_WORKSPACE_BYTES - workspace_total_bytes) {
    return 1;
  }
  workspace_total_bytes += size;
  return 0;
}

static int workspace_within_limits(void) {
  workspace_entry_count = 0;
  workspace_total_bytes = 0;
  return nftw("/workspace", inspect_workspace_entry, 32, FTW_PHYS) == 0;
}

static int supervise(pid_t root_child, int listener_fd, int marker_fd) {
  int root_status = 0;
  int root_finished = 0;
  int no_children = 0;

  while (!root_finished || !no_children) {
    if (!workspace_within_limits()) {
      (void)mark_violation(marker_fd);
      /* The Bash child has PR_SET_PDEATHSIG below. Returning tears down its
       * root immediately; the app-server cleanup then reaps any descendants. */
      return 125;
    }
    struct pollfd watched = {
        .fd = listener_fd,
        .events = POLLIN,
        .revents = 0,
    };
    int ready = poll(&watched, 1, 50);
    if (ready < 0 && errno != EINTR) {
      return 125;
    }
    if (ready > 0 && (watched.revents & POLLIN) != 0 &&
        answer_one_notification(listener_fd, marker_fd) != 0) {
      return 125;
    }
    if (ready > 0 && (watched.revents & (POLLERR | POLLNVAL)) != 0) {
      return 125;
    }

    no_children = 0;
    for (;;) {
      int status = 0;
      pid_t reaped = waitpid(-1, &status, WNOHANG);
      if (reaped > 0) {
        if (reaped == root_child) {
          root_status = status;
          root_finished = 1;
        }
        continue;
      }
      if (reaped == 0) {
        break;
      }
      if (errno == EINTR) {
        continue;
      }
      if (errno == ECHILD) {
        no_children = 1;
        break;
      }
      return 125;
    }
  }

  if (WIFEXITED(root_status)) {
    return WEXITSTATUS(root_status);
  }
  if (WIFSIGNALED(root_status)) {
    return 128 + WTERMSIG(root_status);
  }
  return 125;
}

int main(int argc, char **argv) {
  char **bash_argv = calloc((size_t)argc + 3, sizeof(*bash_argv));
  if (bash_argv == NULL) {
    perror("highambench offline shell: cannot prepare bash arguments");
    return 125;
  }
  bash_argv[0] = argv[0];
  bash_argv[1] = "--noprofile";
  bash_argv[2] = "--norc";
  for (int index = 1; index < argc; ++index) {
    bash_argv[index + 2] = argv[index];
  }
  const char *marker_path = getenv("HIGHAMBENCH_NETWORK_VIOLATION_MARKER");
  if (marker_path == NULL || marker_path[0] == '\0') {
    fprintf(stderr,
            "highambench offline shell: network-violation marker is missing\n");
    free(bash_argv);
    return 125;
  }
  int marker_fd =
      open(marker_path, O_WRONLY | O_APPEND | O_CLOEXEC | O_NOFOLLOW);
  if (marker_fd < 0) {
    perror("highambench offline shell: cannot open network-violation marker");
    free(bash_argv);
    return 125;
  }
  struct stat marker_status;
  if (fstat(marker_fd, &marker_status) != 0 || !S_ISREG(marker_status.st_mode)) {
    fprintf(stderr,
            "highambench offline shell: network-violation marker is not a regular file\n");
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  if (unsetenv("HIGHAMBENCH_NETWORK_VIOLATION_MARKER") != 0) {
    perror("highambench offline shell: cannot hide network-violation marker");
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  if (enter_command_cgroup() != 0) {
    perror("highambench offline shell: cannot enter command resource cgroup");
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  if (unsetenv("CODEX_HOME") != 0 ||
      setenv("HOME", "/home/bench", 1) != 0 ||
      setenv("XDG_CACHE_HOME", "/home/bench/.cache", 1) != 0 ||
      setenv("XDG_CONFIG_HOME", "/home/bench/.config", 1) != 0 ||
      setenv("XDG_DATA_HOME", "/home/bench/.local/share", 1) != 0 ||
      setenv("TMPDIR", "/tmp", 1) != 0) {
    perror("highambench offline shell: cannot isolate command environment");
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  if (prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) != 0) {
    perror("highambench offline shell: cannot become command supervisor");
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  struct rlimit file_limit = {
      .rlim_cur = (rlim_t)HIGHAMBENCH_MAX_WRITTEN_FILE_BYTES,
      .rlim_max = (rlim_t)HIGHAMBENCH_MAX_WRITTEN_FILE_BYTES,
  };
  struct rlimit core_limit = {.rlim_cur = 0, .rlim_max = 0};
  if (setrlimit(RLIMIT_FSIZE, &file_limit) != 0 ||
      setrlimit(RLIMIT_CORE, &core_limit) != 0) {
    perror("highambench offline shell: cannot install file resource limits");
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  int listener_fd = install_offline_filter();
  if (listener_fd < 0) {
    perror("highambench offline shell: cannot install seccomp filter");
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  if (close_inherited_fds(marker_fd, listener_fd) != 0) {
    perror("highambench offline shell: cannot close inherited descriptors");
    close(listener_fd);
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  if (install_command_filesystem_filter() != 0) {
    perror("highambench offline shell: cannot install Landlock filter");
    close(listener_fd);
    close(marker_fd);
    free(bash_argv);
    return 125;
  }

  pid_t child = fork();
  if (child < 0) {
    perror("highambench offline shell: cannot start bash process");
    close(listener_fd);
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  if (child == 0) {
    pid_t supervisor = getppid();
    if (prctl(PR_SET_PDEATHSIG, SIGKILL) != 0 || getppid() != supervisor) {
      perror("highambench offline shell: cannot bind Bash lifetime to supervisor");
      _exit(126);
    }
    if (setpgid(0, 0) != 0) {
      perror("highambench offline shell: cannot isolate bash process group");
      _exit(126);
    }
    close(listener_fd);
    close(marker_fd);
    execv("/usr/bin/bash", bash_argv);
    perror("highambench offline shell: cannot start bash");
    _exit(126);
  }

  int result = supervise(child, listener_fd, marker_fd);
  close(listener_fd);
  close(marker_fd);
  free(bash_argv);
  return result;
}
