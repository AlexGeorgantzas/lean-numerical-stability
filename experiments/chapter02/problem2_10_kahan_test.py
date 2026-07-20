"""Advisory local replay for Higham Chapter 2, Problem 2.10.

Problem 2.10 quotes Kahan's theorem for binary IEEE rounded arithmetic and then
asks the reader to test the theorem on their computer.  This script is that
kind of experiment artifact: it is not a Lean theorem and it is not evidence for
the full quantified theorem.

The replay uses the host Python `float` path for a small source-prefix sample of
allowable denominators and integer numerators satisfying the binary64
`|m| < 2^(t-1)` side condition.  Machine-independent finite-selector subclaims
from earlier work are archived in `NumStability/Analysis/Problem2_10.lean`
and the Chapter 2 ledgers, but this computer-test exercise is closed as an
experiment rather than a theorem gate.
"""

from __future__ import annotations

import platform
import sys


BINARY64_T = 53

ALLOWABLE_DENOMINATORS = [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20]

TEST_NUMERATORS = [
    0,
    1,
    -1,
    2,
    -2,
    3,
    -3,
    5,
    -5,
    2**10 + 1,
    -(2**10 + 1),
    2**20 + 12345,
    -(2**20 + 12345),
    2**52 - 1,
    -(2**52 - 1),
]


def kahan_float_trial(m: int, n: int) -> tuple[bool, float, float, float]:
    """Run the host float expression `(m / n) * n` and compare with `m`."""

    fm = float(m)
    fn = float(n)
    quotient = fm / fn
    product = quotient * fn
    return product == fm, quotient, product, fm


def main() -> int:
    failures: list[tuple[int, int, float, float]] = []

    print("Advisory local replay for Higham Chapter 2, Problem 2.10")
    print("This is an experiment artifact, not a proof.")
    print(f"python: {platform.python_implementation()} {platform.python_version()}")
    print(f"platform: {platform.platform()}")
    print(f"float_info: mant_dig={sys.float_info.mant_dig}, radix={sys.float_info.radix}")
    print(f"sample_denominators: {ALLOWABLE_DENOMINATORS}")
    print(f"sample_numerators: {TEST_NUMERATORS}")
    print()
    print("n,m,quotient_hex,product_hex,expected_hex,passed")

    for n in ALLOWABLE_DENOMINATORS:
        for m in TEST_NUMERATORS:
            if abs(m) >= 2 ** (BINARY64_T - 1):
                raise ValueError(f"test numerator violates source side condition: {m}")
            passed, quotient, product, expected = kahan_float_trial(m, n)
            print(
                f"{n},{m},{quotient.hex()},{product.hex()},"
                f"{expected.hex()},{str(passed).lower()}"
            )
            if not passed:
                failures.append((n, m, product, expected))

    print()
    print(f"trials={len(ALLOWABLE_DENOMINATORS) * len(TEST_NUMERATORS)}")
    print(f"failures={len(failures)}")
    if failures:
        for n, m, product, expected in failures:
            print(
                "failure:"
                f" n={n} m={m} product={product.hex()} expected={expected.hex()}"
            )
        return 1

    print("all sampled host-float trials matched")
    print("lean_formal_subclaim=problem2_10_ieeeDouble_signed_one_third_times_three")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
