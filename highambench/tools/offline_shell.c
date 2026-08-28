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
 * Signal calls are allowed normally.  Only calls whose target is this
 * supervisor (or its process group) are denied and marked, so ordinary command
 * cleanup does not become a false benchmark violation.
 *
 * Build with:
 *   cc -std=c11 -O2 -Wall -Wextra -Werror -o offline-shell offline_shell.c
 */

#define _GNU_SOURCE

#include <errno.h>
#include <dirent.h>
#include <fcntl.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <stddef.h>
#include <poll.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
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

/* Notify for kill-like calls that name the supervisor, all permitted
 * processes (-1), or the supervisor's process group.  The Bash child enters a
 * distinct process group before exec, so its ordinary kill(0, ...) remains
 * local to the evaluated command tree. */
#define NOTIFY_SUPERVISOR_OR_GROUP(name, supervisor, negative_group)          \
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_##name, 0, 5),                    \
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,                                     \
               (unsigned int)offsetof(struct seccomp_data, args[0])),         \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (supervisor), 2, 0),               \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, UINT32_MAX, 1, 0),                 \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (negative_group), 0, 1),           \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF), RELOAD_SYSCALL

/* Notify for calls whose first argument names exactly the supervisor. */
#define NOTIFY_SUPERVISOR(name, supervisor)                                   \
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_##name, 0, 3),                    \
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,                                     \
               (unsigned int)offsetof(struct seccomp_data, args[0])),         \
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (supervisor), 0, 1),               \
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_USER_NOTIF), RELOAD_SYSCALL

static int install_offline_filter(pid_t supervisor_pid,
                                  pid_t supervisor_group) {
  unsigned int supervisor = (unsigned int)supervisor_pid;
  unsigned int negative_group =
      (unsigned int)(-(long long)supervisor_group);
  struct sock_filter filter[] = {
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,
               (unsigned int)offsetof(struct seccomp_data, arch)),
      BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AUDIT_ARCH_X86_64, 1, 0),
      BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
      BPF_STMT(BPF_LD | BPF_W | BPF_ABS,
               (unsigned int)offsetof(struct seccomp_data, nr)),
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
      NOTIFY_SUPERVISOR_OR_GROUP(kill, supervisor, negative_group),
      NOTIFY_SUPERVISOR(tkill, supervisor),
      NOTIFY_SUPERVISOR(tgkill, supervisor),
#if defined(__NR_rt_sigqueueinfo)
      NOTIFY_SUPERVISOR_OR_GROUP(rt_sigqueueinfo, supervisor, negative_group),
#endif
#if defined(__NR_rt_tgsigqueueinfo)
      NOTIFY_SUPERVISOR(rt_tgsigqueueinfo, supervisor),
#endif
#if defined(__NR_pidfd_open)
      /* Prevent creation of a descriptor that could later signal the
       * supervisor.  pidfd_send_signal for every other process stays allowed. */
      NOTIFY_SUPERVISOR(pidfd_open, supervisor),
#endif
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

static int supervise(pid_t root_child, int listener_fd, int marker_fd) {
  int root_status = 0;
  int root_finished = 0;
  int no_children = 0;

  while (!root_finished || !no_children) {
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
  if (prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) != 0) {
    perror("highambench offline shell: cannot become command supervisor");
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  pid_t supervisor_pid = getpid();
  pid_t supervisor_group = getpgrp();
  if (supervisor_pid <= 0 || supervisor_group <= 0) {
    fprintf(stderr,
            "highambench offline shell: cannot identify command supervisor\n");
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  int listener_fd =
      install_offline_filter(supervisor_pid, supervisor_group);
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

  pid_t child = fork();
  if (child < 0) {
    perror("highambench offline shell: cannot start bash process");
    close(listener_fd);
    close(marker_fd);
    free(bash_argv);
    return 125;
  }
  if (child == 0) {
    if (setpgid(0, 0) != 0) {
      perror("highambench offline shell: cannot isolate bash process group");
      _exit(126);
    }
    close(listener_fd);
    close(marker_fd);
    if (close_inherited_fds(-1, -1) != 0) {
      perror("highambench offline shell: cannot close inherited descriptors");
      _exit(126);
    }
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
