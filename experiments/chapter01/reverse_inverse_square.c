/*
 * Reproducibility experiment for Higham, Chapter 1, Section 1.12.3.
 *
 * The book reports historical single-precision Fortran output for
 *   sum_{k=1}^N 1/k^2
 * in forward and reverse order, including N = 10^9.  The exact source program,
 * compiler flags, operation trace, and decimal I/O model are not supplied, so
 * this file is an experiment artifact, not a Lean theorem target.
 *
 * Example:
 *   cc -O2 -std=c11 -fno-fast-math -o /tmp/reverse_inverse_square \
 *     experiments/chapter01/reverse_inverse_square.c
 *   /tmp/reverse_inverse_square --n 1000000 --reverse
 *   /tmp/reverse_inverse_square --n 1000000000 --reverse
 */

#include <errno.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static uint64_t parse_u64(const char *text) {
  char *end = NULL;
  errno = 0;
  unsigned long long value = strtoull(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0') {
    fprintf(stderr, "invalid integer: %s\n", text);
    exit(2);
  }
  return (uint64_t)value;
}

static uint32_t float_bits(float x) {
  uint32_t bits = 0;
  memcpy(&bits, &x, sizeof(bits));
  return bits;
}

static float inverse_square_term(uint64_t k) {
  volatile float fk = (float)k;
  volatile float denom = fk * fk;
  return 1.0f / denom;
}

static float sum_forward(uint64_t n, uint64_t *first_no_change) {
  volatile float s = 0.0f;
  *first_no_change = 0;

  for (uint64_t k = 1; k <= n; ++k) {
    volatile float next = s + inverse_square_term(k);
    if (*first_no_change == 0 && next == s) {
      *first_no_change = k;
    }
    s = next;
  }

  return s;
}

static float sum_reverse(uint64_t n) {
  volatile float s = 0.0f;

  for (uint64_t k = n; k >= 1; --k) {
    s = s + inverse_square_term(k);
    if (k == 1) {
      break;
    }
  }

  return s;
}

static void usage(const char *argv0) {
  fprintf(stderr,
      "usage: %s [--n N] [--forward|--reverse]\n"
      "default: --n 1000000 --reverse\n",
      argv0);
}

int main(int argc, char **argv) {
  uint64_t n = 1000000;
  int reverse = 1;

  for (int i = 1; i < argc; ++i) {
    if (strcmp(argv[i], "--n") == 0) {
      if (i + 1 == argc) {
        usage(argv[0]);
        return 2;
      }
      n = parse_u64(argv[++i]);
    } else if (strcmp(argv[i], "--forward") == 0) {
      reverse = 0;
    } else if (strcmp(argv[i], "--reverse") == 0) {
      reverse = 1;
    } else if (strcmp(argv[i], "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else {
      usage(argv[0]);
      return 2;
    }
  }

  clock_t start = clock();
  uint64_t first_no_change = 0;
  float result =
      reverse ? sum_reverse(n) : sum_forward(n, &first_no_change);
  clock_t stop = clock();

  printf("mode: %s\n", reverse ? "reverse" : "forward");
  printf("n: %" PRIu64 "\n", n);
  printf("float result decimal: %.9g\n", result);
  printf("float result fixed8: %.8f\n", result);
  printf("float result hex: 0x%08" PRIx32 "\n", float_bits(result));
  if (!reverse) {
    printf("first no-change k: %" PRIu64 "\n", first_no_change);
    printf("first plateau attained at k: %" PRIu64 "\n",
        first_no_change > 0 ? first_no_change - 1 : 0);
  }
  printf("clock seconds: %.3f\n",
      (double)(stop - start) / (double)CLOCKS_PER_SEC);
  printf("notes: experiment only; compiler, flags, platform, and decimal I/O are part of the run provenance\n");
  return 0;
}
