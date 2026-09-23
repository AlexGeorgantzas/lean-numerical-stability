# Pilot 23 first-pair review (2026-09-23)

Pilot 23's Titan output root is
`/hdd/alexgeorgantzas/highambench/pilot23-dev3-20260923-a`.
Its controller is frozen at `46c7dc8643b8d69a02ce63cd6f23a4d78f95a228`.
The first `FAB19-EQ3.5` pair report SHA-256 is
`465ab519fae90e7b01f4626a801e12fa1a284155e39a94bb94a9e1fb01da491e`.
The first-review gate was `PAUSED_FIRST_REVIEW`, then released through that
same frozen controller at 10:34:56 UTC to run the two remaining admitted
canaries concurrently in separate B/C lanes. Pilot 22's incident result was
not scored or resumed.

| Metric | N / R0, Mathlib | L / R1, NumStability | L / N |
| --- | ---: | ---: | ---: |
| Audited faithfulness | faithful-stronger | faithful-stronger | both accepted |
| Submissions | 1 | 1 | 1 |
| Contestant-active seconds | 179.893 | 146.161 | 0.812 |
| Contestant system-wall seconds, including retrieval | 194.506 | 171.642 | 0.882 |
| Retrieval seconds | 14.613 | 25.481 | 1.744 |
| Net-new provider tokens | 24,434 | 49,164 | 2.012 |
| Candidate lines | 70 | 56 | 0.800 |
| Audit wall seconds, excluded | 384.929 | 378.691 | — |
| Sampled peak RAM bytes | 910,999,552 | 511,766,528 | — |
| Sampled peak one-second CPU mean, cores | 1.002 | 0.823 | — |

Both conditions had 8 logical CPUs and a 24-GiB cgroup limit, with no OOM
events. The CPU figure is an interval mean, not an instantaneous peak. R1
imported `NumStability.Algorithms.Summation.Recursive.Core`; its compiled
statement directly reached `fl_recursiveSum`,
`fl_higherPrecisionRecursiveSum`, `FPModel`, `gamma`, and `gammaValid`.
The composition router reported `DIRECT_OR_COMPOSITION` for R1 and `NO_ROUTE`
for R0. This is real treatment uptake, not an import-only proxy.

For each condition, the independent blind and direct judges accounted for
every recursively expanded dependency (70 N; 65 L). Direct and round-trip
judges each returned all 16 semantic checklist items and explicit
candidate-implies-source/source-implies-candidate assessments. They agreed
`faithful-stronger`: both candidates retain all positive block sizes,
recursive working-precision block sums, extended recursive accumulation,
final working-precision rounding, and a per-input backward-error
representation. Their finite-u gamma majorants imply the selected
`b*u + O(u²)` first-order coefficient. No adjudication was needed.

This is **one exploratory development pair**, not a general library-effect
estimate. L saved about 23 seconds of contestant system-wall time and 14
statement lines, while using about twice the net-new provider tokens and
roughly 11 more seconds of retrieval. Keep all four measures rather than
reporting only the favorable one.
