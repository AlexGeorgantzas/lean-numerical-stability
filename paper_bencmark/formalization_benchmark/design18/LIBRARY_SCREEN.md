# NumStability component screen — draft, before candidate results

The frozen Design-17 schema-v3 NumStability atlas was independently copied
from Titan and SHA-256 checked against its `atlas.json`. Its declaration file
hash is `1f978f116073cb02dd1f22abadbe00099bd389b1c7b8866565df39e9422cc1f2`.
This screen is **not** a proof that no disguised target theorem exists: a
semantic declaration-by-declaration collision review is still required before
the twelve tasks are admitted. It is deliberately completed before any
Design-18 candidate exists.

| Proposed tasks | Verifiable lower-level NumStability components | Unclosed bridge |
|---|---|---|
| `HM19-2-4` | `FPModel`, `FiniteProbability.eventProb`, `StatisticalRoundingErrorModel`, expectation/event lemmas | Independent mean-zero operation errors, signed reciprocal products, and the exact Higham–Mary exponential tail coefficient. This is foundational and may have the smallest reuse benefit. |
| `HM19-3-1`, `HM19-3-2` | `fl_dotProduct`, rounded scalar operators, deterministic dot-product backward-error lemmas, finite probability | Link each stochastic execution's scalar trace to the existing deterministic algorithm; derive simultaneous high-probability perturbation events. |
| `HM19-3-3`, `HM19-3-4` | `fl_matVec`, `fl_matMul`, rectangular matrix and componentwise error infrastructure | Stochastic execution/row-column trace bridge and union of per-row/column events; no direct probabilistic matrix theorem may be exposed. |
| `HM19-3-5` | `fl_forwardSub`, `fl_backSub`, `triangularSolve_backward_error` | Full-domain random substitution trace and joint perturbation event. |
| `HM19-3-6`, `HM19-3-7` | `DoolittleLU`, `doolittle_backward_error`, `doolittle_solve_backward_error`, triangular solvers | Probabilistic operation trace and exact Higham–Mary event/coefficient; deterministic result families are components only if they do not imply the target probabilistic event. |
| `HM19-3-8` | `fl_cholesky`, `CholeskyBackwardError`, `fl_cholesky_backward_error` | Stochastic Cholesky trace, square-root operation, and event aggregation. |
| `HALL21-3-3` | `fl_recursiveSum`, exact partial sums, `FiniteProbability` event/expectation lemmas | Independent mean-zero rounded recurrence, maximal concentration, and all-orders product factor. |
| `CASTRO24-4-1` | `SumTree`, `fl_pairwiseSum`, balanced-tree deterministic error bounds, `SumTree.statisticalRunningErrorContribution_rms_le` | SR execution with martingale concentration and the source's exact high-probability coefficient. RMS alone does not imply that conclusion. |
| `CASTRO24-4-2` | `fl_hornerDesc`, polynomial evaluation and deterministic Horner bounds | SR/Horner trace, martingale length, condition number, and high-probability conclusion. |

Exact names above were found in the frozen declaration atlas. No name/signature
screen found a theorem already joining these selected algorithm families to
the respective source-specific high-probability conclusions; this negative
search is not sufficient for final admission. In particular, the library's
`StatisticalRoundingErrorModel` and SumTree RMS theorems are **not** substitutes
for the selected tail-probability theorems.

A reproducible co-occurrence probe on the frozen `declarations.jsonl` also
returned zero records whose name/signature contained both one of the selected
algorithm names (`dotProduct`, `fl_recursiveSum`, `fl_hornerDesc`,
`fl_pairwiseSum`, `fl_matVec`, `fl_matMul`, `fl_forwardSub`, `fl_backSub`,
`DoolittleLU`, `fl_cholesky`) and one of `eventProb`, `FiniteProbability`,
`probability`, `stochastic`, `independent`, `martingale`, or `hoeffding`
(case-insensitive). This is a lexical check, **not** a semantic collision
certificate; it cannot rule out a theorem whose name/signature hides the
algorithm behind an abstraction.

The largest predictable risk is representation: `FPModel` and most algorithms
are deterministic, while the new papers quantify random execution traces.
The exposed `StatisticalRoundingErrorModel` is defined over a finite sample
space (`[Fintype Ω]`); the selected paper statements do not all impose that
restriction. It may serve as inspiration or a partial bridge, but a candidate
that restricts the source domain to finite probability spaces merely to use it
is unfaithful. R0 and R1 therefore both receive Mathlib's general `Measure`
and `iIndepFun` foundations from the same catalog.
If constructing this bridge dominates both conditions, a weak R1 advantage
would be an explainable limit of the present library, not evidence that the
target result was leaked or that the benchmark may assume the bridge for free.
