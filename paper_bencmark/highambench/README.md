# HighamBench P01--P02 pilot

This directory contains a two-paper benchmark for testing whether access to the
NumStability Lean library helps an agent finish fixed Lean proofs. A fixed proof
means that the theorem statement is chosen before a run and the agent may change
only the proof.

This pilot contains exactly P01 and P02. No other candidate paper is included:

> Nicholas J. Higham, "The Accuracy of Floating Point Summation," *SIAM Journal
> on Scientific Computing* 14(4), 783--799, July 1993.
> <https://doi.org/10.1137/0914050>

> Takeshi Ogita, Siegfried M. Rump, and Shin'ichi Oishi, "Accurate Sum and Dot
> Product," *SIAM Journal on Scientific Computing* 26(6), 1955--1988, 2005.
> <https://doi.org/10.1137/030601818>

The local paper PDF is used only as the recorded source copy. It is covered by
the publisher's terms. The benchmark metadata uses short paraphrases rather than
copying long passages from the paper.

## The six tasks

Both papers support all three task types in the HighamBench 0.2 specification.

| Task | Type | Chosen result | Exact paper location |
| --- | --- | --- | --- |
| `P01-T1` | T1, direct use | Pairwise summation bound for nonnegative inputs | Equation (3.6), journal p. 788 / PDF p. 6; nonnegative observation after (2.6), journal p. 785 / PDF p. 3 |
| `P01-T2` | T2, combine | Pairwise and recursive bounds, including the comparison of their bound factors | Equation (2.6), journal p. 785 / PDF p. 3; equation (3.6) and the following comparison, journal p. 788 / PDF p. 6 |
| `P01-T3` | T3, extend | Recursive-summation running-error bound under the no-guard-digit model | Equations (5.1), (5.2), and (5.3), journal p. 793 / PDF p. 11 |
| `P02-T1` | T1, direct use | `VecSum` preserves the exact sum | Equation (4.7)(i) and Algorithm 4.3, journal p. 1965 / PDF p. 11 |
| `P02-T2` | T2, combine | `Sum2` doubled-working-precision absolute-error bound | Proposition 4.5, equation (4.8), journal p. 1965 / PDF p. 11; proof on journal pp. 1966--1967 / PDF pp. 12--13 |
| `P02-T3` | T3, extend | Optimized `DotK` K-fold absolute-error bound without multiplication underflow | Algorithm 5.10, journal p. 1977 / PDF p. 23; equation (5.10) and Proposition 5.11, journal p. 1978 / PDF p. 24 |

T1 is close to one existing NumStability theorem. T2 needs several existing
results and extra arithmetic. T3 formalizes equation (5.3), whose right side
uses the actual computed prefix sums from recursive summation. NumStability has
no accumulated no-guard running-budget theorem of this form. A condition-L
proof can reuse pieces such as `NumStability.noGuardAddWitness_error_eq` and
the generic `NumStability.runningError_bound_from_local_errors`, but it must
still connect them to the no-guard recursive state, witnesses, indices, and the
exact computed-prefix budget, or construct the full induction directly.

The T1 and T2 statements use an exact `gamma` bound. Here `gamma` is the usual
closed formula that safely collects several small rounding errors. T3 instead
uses the exact finite bound printed in (5.3), so it needs no `gamma` condition
and no informal `O(u^2)` term.

For P02, T1 is a direct iteration of the local error-free `TwoSum` identity.
T2 combines that invariant with the low-component budget, ordinary recursive
summation, final rounding, and gamma arithmetic. T3 adds error-free products,
iterated `VecSum`, a transformed dot-product mass estimate, and the gamma
comparisons in Proposition 5.11. NumStability has nearby compensated-summation
and extended-dot-product ingredients, but no `VecSum`, `SumK`, or `DotK`
theorem. The T3 statement selects the paper's no-multiplication-underflow
absolute bound; this keeps the shared setting neutral and avoids adding an
underflow-unit and rounded-division model that the selected claim does not need.

## Two conditions

- `N` means no NumStability library. No source, compiled library file,
  documentation, search index, declaration-name list, or cache from the library
  may be visible.
- `L` means the frozen NumStability source and compiled files are available for
  local use and local search.

Both conditions use the same fixed statement, source material, shared task
definitions, Lean version, mathlib revision, agent prompt, tools, time limit,
token limit, and machine class. Each attempt starts in a new bubblewrap
namespace, meaning a fresh restricted view of files and processes, and a new
conversation. Model-generated shell commands cannot create network sockets.
The shell supervisor records denied socket activity in a per-run marker. The
outer runner watches that marker with a separate kernel event queue, so deleting
or clearing the file cannot hide an earlier change. Any recorded attempt is a
failure, even when the Lean proof itself is valid. It is labeled
`RULE_VIOLATION` unless a time limit, token limit, or missing submission has the
higher-priority failure label. The launcher also blocks attempts to signal its
supervisor and closes inherited file handles before starting Bash.
Both conditions see the same separately staged package runtime: mathlib Lean
source files plus each package's base `.olean` files and the matching
`.olean.server`, `.olean.private`, and `.ir` support files needed by Lean 4.29.
No other package-build files are staged. The original `.lake/packages`
checkout, its Git data, build traces, and caches are not mounted in an attempt.

The Codex control process still needs its provider connection. This setup uses
no frozen OCI container image, so its measurements must be labeled as an
observational pilot rather than an official reference-protocol score.

The fixed limit is 900 seconds and 120,000 total model tokens per run. A model
token is a small piece of text counted by the model service. Failed runs receive
900 seconds in the main time comparison, while their real stop time is also kept.
The frozen Codex binary lists the `rollout_budget` feature. Strict configuration
turns it on with the 120,000-token limit and weight 1 for both input and
generated tokens; adapter tests check that each setting is supplied once.

## Repetitions and run order

Each task-condition pair is repeated three times. The IDs `rep-01`, `rep-02`,
and `rep-03` are repetition IDs, not model random seeds. No backend seed is
claimed because this repository does not currently have proof that the selected
agent backend accepts and obeys a seed. If a backend with real seed support is
used later, its seed values must be added to the raw run record before evaluation.

There are 36 planned runs:

`6 tasks x 3 repetitions x 2 conditions = 36 runs`.

The first condition in each pair was selected by the fixed SHA-256 rule recorded
in `metadata/run_order.json`. SHA-256 is a repeatable text-to-number calculation.
It makes the order reproducible without presenting repetition IDs as random
seeds.

## Files

- `IMPLEMENTATION_PLAN.md` explains the construction decisions and the checks
  required before measured runs.
- `metadata/manifest.json` records exactly two papers, their hashes, the
  specification hash, all six tasks, and their exact source locations.
- `metadata/config.json` freezes the environment and run limits.
- `metadata/run_order.json` fixes the order of N and L for every paired
  repetition.
- `metadata/reviews/reviewer_1.json` and `reviewer_2.json` are the historical
  P01 reviews.
- `metadata/reviews/P02_reviewer_1.json` and `P02_reviewer_2.json` are the two
  current Codex review passes for the new paper entry.

The review files distinguish completed checks from pending checks. A pending
check is not a pass. The expanded shared setting and all six public target
skeletons have been rebuilt in both isolated conditions, and condition N was
rescanned after complete controlled staging. The six P01 private N/L proofs
also passed fresh hidden validation against the expanded shared file; that
regression record is `metadata/evidence/construction_validation_P01_shared_regression.json`.
Fresh private construction proofs for P02 and a complete twelve-proof,
six-task construction record are still required before release. The complete
measured matrix is also still required.

## Frozen source versions

- Lean: `leanprover/lean4:v4.29.0-rc3`
- mathlib: `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`
- NumStability source baseline:
  `45813a95dacf577461bae13f033af0dbc985a225`
- P01 paper PDF SHA-256:
  `d5ad99fac5022da54dbe02721ea57116df3cec15badddd7c96c344328718fea7`
- P02 paper PDF SHA-256:
  `e7b8523c793ad7345dfc76f681c44d1afbbc3a810fb948912451432ae616512d`
- Specification PDF SHA-256:
  `25a8a72d62e2ad9d131004b871f5ccc58438d488dbd64afcd0a8839e9e4d78a8`

## What a result may say

This pilot may show whether library access changed proof success, time, token
use, or actual library use for these six fixed tasks and one fixed agent setup.
It does not test translation from English into Lean, and two papers cannot stand
for all numerical analysis papers. Any 95 percent range made by resampling only
these two whole papers has very limited resolution and must not be presented as
broad certainty.
