/*
 * Reproducibility experiment for Higham, Chapter 1, Section 1.15.
 *
 * The book reports MATLAB/BLAS behavior for a power-method example: the first
 * computed step has entries of order 1e-16 and, after 38 iterations, a good
 * dominant eigenpair is obtained.  The exact MATLAB version, BLAS kernel,
 * operation order, normalization convention, stopping rule, and decimal I/O
 * are not supplied, so this file is an experiment artifact, not a Lean theorem
 * target.
 *
 * Example:
 *   cc -O2 -std=c11 -fno-fast-math -o /tmp/beneficial_power_method \
 *     experiments/chapter01/beneficial_power_method.c -lm
 *   /tmp/beneficial_power_method
 *   /tmp/beneficial_power_method --left-to-right --iters 38
 */

#include <errno.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum Order {
  ORDER_RIGHT_TO_LEFT = 0,
  ORDER_LEFT_TO_RIGHT = 1
};

static const double A[3][3] = {
    {0.4, -0.6, 0.2},
    {-0.3, 0.7, -0.4},
    {-0.1, -0.4, 0.5},
};

static long parse_long(const char *text) {
  char *end = NULL;
  errno = 0;
  long value = strtol(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0' || value < 0) {
    fprintf(stderr, "invalid nonnegative integer: %s\n", text);
    exit(2);
  }
  return value;
}

static void usage(const char *argv0) {
  fprintf(stderr,
      "usage: %s [--iters N] [--right-to-left|--left-to-right]\n"
      "default: --iters 38 --right-to-left\n",
      argv0);
}

static void matvec(const double x[3], double y[3], enum Order order) {
  for (int i = 0; i < 3; ++i) {
    if (order == ORDER_LEFT_TO_RIGHT) {
      volatile double s = A[i][0] * x[0];
      s = s + A[i][1] * x[1];
      s = s + A[i][2] * x[2];
      y[i] = s;
    } else {
      volatile double s = A[i][1] * x[1];
      s = s + A[i][2] * x[2];
      s = A[i][0] * x[0] + s;
      y[i] = s;
    }
  }
}

static double dot3(const double x[3], const double y[3]) {
  volatile double s = x[0] * y[0];
  s = s + x[1] * y[1];
  s = s + x[2] * y[2];
  return s;
}

static double norm2(const double x[3]) {
  return sqrt(dot3(x, x));
}

static void print_vec(const char *label, const double x[3]) {
  printf("%s decimal: [%.17g, %.17g, %.17g]\n", label, x[0], x[1], x[2]);
  printf("%s hex:     [%a, %a, %a]\n", label, x[0], x[1], x[2]);
}

int main(int argc, char **argv) {
  long iters = 38;
  enum Order order = ORDER_RIGHT_TO_LEFT;

  for (int i = 1; i < argc; ++i) {
    if (strcmp(argv[i], "--iters") == 0) {
      if (i + 1 == argc) {
        usage(argv[0]);
        return 2;
      }
      iters = parse_long(argv[++i]);
    } else if (strcmp(argv[i], "--right-to-left") == 0) {
      order = ORDER_RIGHT_TO_LEFT;
    } else if (strcmp(argv[i], "--left-to-right") == 0) {
      order = ORDER_LEFT_TO_RIGHT;
    } else if (strcmp(argv[i], "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else {
      usage(argv[0]);
      return 2;
    }
  }

  double x[3] = {1.0, 1.0, 1.0};
  double y[3] = {0.0, 0.0, 0.0};

  printf("mode: %s\n",
      order == ORDER_RIGHT_TO_LEFT ? "right-to-left row sums" :
                                     "left-to-right row sums");
  printf("iters: %ld\n", iters);
  printf("notes: experiment only; compiler, flags, platform, libm, and decimal I/O are part of the run provenance\n");

  matvec(x, y, order);
  print_vec("first step", y);
  printf("first step norm2: %.17g\n", norm2(y));

  double nrm = norm2(y);
  if (nrm == 0.0) {
    printf("normalization stopped: first step is exactly zero in this trace\n");
    return 0;
  }
  for (int i = 0; i < 3; ++i) {
    x[i] = y[i] / nrm;
  }

  for (long k = 1; k < iters; ++k) {
    matvec(x, y, order);
    nrm = norm2(y);
    if (nrm == 0.0) {
      printf("normalization stopped at iteration %ld\n", k + 1);
      return 0;
    }
    for (int i = 0; i < 3; ++i) {
      x[i] = y[i] / nrm;
    }
  }

  matvec(x, y, order);
  double rq = dot3(x, y) / dot3(x, x);
  double residual[3] = {
      y[0] - rq * x[0],
      y[1] - rq * x[1],
      y[2] - rq * x[2],
  };

  print_vec("normalized iterate", x);
  printf("Rayleigh quotient: %.17g\n", rq);
  printf("Rayleigh quotient hex: %a\n", rq);
  printf("residual norm2: %.17g\n", norm2(residual));
  return 0;
}
