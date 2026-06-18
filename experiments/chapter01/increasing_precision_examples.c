/*
 * Advisory experiments for Higham, Chapter 1, Section 1.13.
 *
 * The book reports increasing-precision plots and named Fortran 90 workstation
 * behavior, but it does not supply a complete machine/routine/display model.
 * This file is therefore a reproducibility artifact, not a Lean theorem target.
 *
 * Example:
 *   cc -O2 -std=c11 -fno-fast-math -o /tmp/increasing_precision_examples \
 *     experiments/chapter01/increasing_precision_examples.c -lm
 *   /tmp/increasing_precision_examples
 */

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static uint32_t float_bits(float x) {
  uint32_t bits = 0;
  memcpy(&bits, &x, sizeof(bits));
  return bits;
}

static uint64_t double_bits(double x) {
  uint64_t bits = 0;
  memcpy(&bits, &x, sizeof(bits));
  return bits;
}

static double round_to_binary_digits(double x, int t) {
  if (!isfinite(x) || x == 0.0) {
    return x;
  }

  int exp2 = 0;
  double mant = frexp(x, &exp2);
  double scaled = ldexp(mant, t);
  double rounded = nearbyint(scaled);
  return ldexp(rounded, exp2 - t);
}

static double sine_precision_model(int t) {
  double x = round_to_binary_digits(1.0 / 7.0, t);
  double a = round_to_binary_digits(1.0e-8, t);
  double b = round_to_binary_digits(ldexp(1.0, 24), t);
  double bx = round_to_binary_digits(b * x, t);
  double s = round_to_binary_digits(sin(bx), t);
  double as = round_to_binary_digits(a * s, t);
  return round_to_binary_digits(x + as, t);
}

static void run_sine_sweep(void) {
  const double x = 1.0 / 7.0;
  const double perturb = 1.0e-8 * sin(ldexp(1.0, 24) * x);
  const double exact_ref = x + perturb;
  double previous = NAN;

  printf("sine example: x + 1e-8*sin(2^24*x), x = 1/7\n");
  printf("host perturbation: %.17g\n", perturb);
  printf("host exact-ref approximation: %.17g\n", exact_ref);
  printf("t, rounded-value, abs-error, same-as-previous\n");
  for (int t = 10; t <= 40; ++t) {
    double y = sine_precision_model(t);
    double err = fabs(y - exact_ref);
    printf("%2d, %.17g, %.17g, %s\n",
        t, y, err, (t > 10 && y == previous) ? "yes" : "no");
    previous = y;
  }
  printf("\n");
}

static void run_branch_example(void) {
  volatile float xf = 2.0f / 3.0f;
  volatile float yf = fabsf(3.0f * (xf - 0.5f) - 0.5f) / 25.0f;
  volatile float ef = expf(yf);
  volatile float zf = yf == 0.0f ? 1.0f : (ef - 1.0f) / yf;

  volatile double xd = 2.0 / 3.0;
  volatile double yd = fabs(3.0 * (xd - 0.5) - 0.5) / 25.0;
  volatile double ed = exp(yd);
  volatile double zd = yd == 0.0 ? 1.0 : (ed - 1.0) / yd;

  printf("branch example: stored x = 2/3, z = (exp(y)-1)/y if y != 0\n");
  printf("float  x: %.9g hex-bits: 0x%08x\n", xf, float_bits(xf));
  printf("float  y: %.9g exp(y): %.9g z: %.9g\n", yf, ef, zf);
  printf("double x: %.17g hex-bits: 0x%016llx\n",
      xd, (unsigned long long)double_bits(xd));
  printf("double y: %.17g exp(y): %.17g z: %.17g\n", yd, ed, zd);
  printf("\n");
}

int main(void) {
  printf("notes: experiment only; compiler, flags, platform, libm, rounding mode, and decimal I/O are run provenance\n\n");
  run_sine_sweep();
  run_branch_example();
  return 0;
}
