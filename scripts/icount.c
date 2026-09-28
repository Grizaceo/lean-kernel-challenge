/* icount.c — run a command and report its user-space instruction count.
 *
 * Why (2026-09-27): the Lean Kernel Challenge ranks on INSTRUCTION counts
 * (`curve_work`, contract `computation-total-v1`), and the only instrument that
 * produced them was the remote judge, which costs quota. This host has no `perf`
 * binary and `perf_event_paranoid=2`, but paranoid=2 still ALLOWS user-space
 * measurement of your own process, so PERF_TYPE_HARDWARE /
 * PERF_COUNT_HW_INSTRUCTIONS can be opened directly. That yields the official
 * metric locally and -- unlike the wall-time proxy, which has 40% run-to-run
 * spread on this host -- it is deterministic.
 *
 * Design: fork/exec the target with perf_event_open(attr, pid=child,
 * cpu=-1, group=-1, flags=PERF_FLAG_FD_CLOEXEC) so the counter is attached to
 * the child, and use PERF_FORMAT_TOTAL_TIME_ENABLED|RUNNING so a multiplexed
 * counter is scaled correctly. Prints one line:
 *   INSTR_TOTAL=<scaled instructions>  <the command's own output...>
 *
 * The judge counts the same event (PERF_COUNT_HW_INSTRUCTIONS) but with the
 * kernel included and with attestations; this is a local instrument, so treat
 * the absolute number as an indicator of magnitude, not a certified score.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <linux/perf_event.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

static long perf_event_open(struct perf_event_attr *attr, pid_t pid, int cpu,
                            int group_fd, unsigned long flags) {
  return syscall(__NR_perf_event_open, attr, pid, cpu, group_fd, flags);
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s <cmd> [args...]\n", argv[0]);
    return 2;
  }
  struct perf_event_attr attr;
  memset(&attr, 0, sizeof(attr));
  attr.size = sizeof(attr);
  attr.type = PERF_TYPE_HARDWARE;
  attr.config = PERF_COUNT_HW_INSTRUCTIONS;
  attr.disabled = 1;          /* start counting on the child's exec */
  attr.inherit = 1;           /* follow the child if it forks further */
  attr.exclude_kernel = 1;    /* user-space only, matching paranoid=2 */
  attr.exclude_hv = 1;
  attr.exclude_idle = 1;
  attr.read_format = PERF_FORMAT_TOTAL_TIME_ENABLED | PERF_FORMAT_TOTAL_TIME_RUNNING;

  pid_t pid = fork();
  if (pid < 0) {
    perror("fork");
    return 1;
  }
  if (pid == 0) {
    execvp(argv[1], &argv[1]);
    perror("execvp");
    _exit(127);
  }

  int fd = (int)perf_event_open(&attr, pid, -1, -1, 0);
  if (fd < 0) {
    /* Count without the counter rather than fail: still report the child. */
    fprintf(stderr, "icount: perf_event_open failed: %s\n", strerror(errno));
    int status = 0;
    waitpid(pid, &status, 0);
    return WEXITSTATUS(status);
  }
  ioctl(fd, PERF_EVENT_IOC_RESET, 0);
  ioctl(fd, PERF_EVENT_IOC_ENABLE, 0);

  int status = 0;
  waitpid(pid, &status, 0);

  ioctl(fd, PERF_EVENT_IOC_DISABLE, 0);
  struct { unsigned long long nr, time_enabled, time_running; } rd;
  ssize_t got = read(fd, &rd, sizeof(rd));
  if (got != (ssize_t)sizeof(rd)) {
    fprintf(stderr, "icount: read failed: %s\n", strerror(errno));
  } else {
    double scaled = (double)rd.nr;
    if (rd.time_running > 0 && rd.time_running != rd.time_enabled)
      scaled = (double)rd.nr * ((double)rd.time_enabled / (double)rd.time_running);
    fprintf(stderr, "INSTR_TOTAL=%.0f\n", scaled);
  }
  close(fd);
  return WIFEXITED(status) ? WEXITSTATUS(status) : 1;
}
