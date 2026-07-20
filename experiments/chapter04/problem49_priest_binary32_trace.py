"""Advisory binary32 replay for Higham Chapter 4, Problem 4.10.

This file is an experiment artifact, not a Lean theorem and not evidence for
the historical Priest/Higham printed machine output.  It replays Algorithm 4.2
using Python's standard-library conversion to IEEE-like binary32 after each
displayed primitive operation.

The corresponding theorem-bearing Lean facts are recorded in
NumStability/Algorithms/CompensatedSum.lean and in the Chapter 4 ledgers.
"""

from __future__ import annotations

import struct


def f32(x: float) -> float:
    """Round a Python float through the platform C binary32 conversion."""

    return struct.unpack(">f", struct.pack(">f", float(x)))[0]


def priest_problem410_inputs(t: int = 24) -> list[float]:
    return [
        f32(2.0 ** (t + 1)),
        f32(2.0 ** (t + 1) - 2.0),
        f32(-(2.0**t - 1.0)),
        f32(-(2.0**t - 1.0)),
        f32(-(2.0**t - 1.0)),
        f32(-(2.0**t - 1.0)),
    ]


def kahan_trace_binary32(xs: list[float]) -> list[tuple[int, float, float, float, float, float]]:
    s = f32(0.0)
    e = f32(0.0)
    rows: list[tuple[int, float, float, float, float, float]] = []

    for i, x in enumerate(xs, start=1):
        x = f32(x)
        temp = s
        y = f32(x + e)
        s = f32(temp + y)
        e = f32(f32(temp - s) + y)
        rows.append((i, x, temp, y, s, e))

    return rows


def main() -> None:
    xs = priest_problem410_inputs()
    rows = kahan_trace_binary32(xs)

    print("Advisory binary32 replay for Higham Chapter 4, Problem 4.10")
    print("This is an experiment artifact, not a proof.")
    print()
    print("i,x,temp,y,s,e")
    for row in rows:
        print(",".join([str(row[0]), *(format(value, ".9g") for value in row[1:])]))

    final_s = rows[-1][4]
    final_e = rows[-1][5]
    exact_sum = sum([2.0**25, 2.0**25 - 2.0] + [-(2.0**24 - 1.0)] * 4)

    print()
    print(f"final_s={format(final_s, '.9g')}")
    print(f"final_e={format(final_e, '.9g')}")
    print(f"exact_sum={format(exact_sum, '.9g')}")
    print("lean_formal_subclaim=problem410PriestInput_t24_first_sum_ieeeSingle_rounds_to_67108864")


if __name__ == "__main__":
    main()
