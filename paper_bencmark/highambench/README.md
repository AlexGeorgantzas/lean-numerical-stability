# HighamBench P01 pilot

This directory contains a one-paper benchmark for testing whether access to the
NumStability Lean library helps an agent finish fixed Lean proofs. A fixed proof
means that the theorem statement is chosen before a run and the agent may change
only the proof.

This pilot contains only P01:

> Nicholas J. Higham, "The Accuracy of Floating Point Summation," *SIAM Journal
> on Scientific Computing* 14(4), 783--799, July 1993.
> <https://doi.org/10.1137/0914050>

The local paper PDF is used only as the recorded source copy. It is covered by
the publisher's terms. The benchmark metadata uses short paraphrases rather than
copying long passages from the paper.

## The three tasks

The paper supports all three task types in the HighamBench 0.2 specification.

| Task | Type | Chosen result | Exact paper location |
| --- | --- | --- | --- |
| `P01-T1` | T1, direct use | Pairwise summation bound for nonnegative inputs | Equation (3.6), journal p. 788 / PDF p. 6; nonnegative observation after (2.6), journal p. 785 / PDF p. 3 |
| `P01-T2` | T2, combine | Pairwise and recursive bounds, including the comparison of their bound factors | Equation (2.6), journal p. 785 / PDF p. 3; equation (3.6) and the following comparison, journal p. 788 / PDF p. 6 |
| `P01-T3` | T3, extend | Recursive-summation running-error bound under the no-guard-digit model | Equations (5.1), (5.2), and (5.3), journal p. 793 / PDF p. 11 |

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

There are 18 planned runs:

`3 tasks x 3 repetitions x 2 conditions = 18 runs`.

The first condition in each pair was selected by the fixed SHA-256 rule recorded
in `metadata/run_order.json`. SHA-256 is a repeatable text-to-number calculation.
It makes the order reproducible without presenting repetition IDs as random
seeds.

## Files

- `IMPLEMENTATION_PLAN.md` explains the construction decisions and the checks
  required before measured runs.
- `metadata/manifest.json` records the one paper, its hash, the specification
  hash, all three tasks, and their exact source locations.
- `metadata/config.json` freezes the environment and run limits.
- `metadata/run_order.json` fixes the order of N and L for every paired
  repetition.
- `metadata/reviews/reviewer_1.json` is the source-and-mathematics review.
- `metadata/reviews/reviewer_2.json` is the formal-interface-and-protocol review.

The review files distinguish completed checks from pending checks. A pending
check is not a pass. The fixed Lean files now build in both conditions and their
hashes are in the manifest. Final reviewer approval and the complete measured
matrix are still required before the benchmark report is complete.

## Frozen source versions

- Lean: `leanprover/lean4:v4.29.0-rc3`
- mathlib: `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`
- NumStability source baseline:
  `45813a95dacf577461bae13f033af0dbc985a225`
- Paper PDF SHA-256:
  `d5ad99fac5022da54dbe02721ea57116df3cec15badddd7c96c344328718fea7`
- Specification PDF SHA-256:
  `25a8a72d62e2ad9d131004b871f5ccc58438d488dbd64afcd0a8839e9e4d78a8`

## What a result may say

This pilot may show whether library access changed proof success, time, token
use, or actual library use for these three fixed tasks and one fixed agent setup.
It does not test translation from English into Lean, and one paper cannot stand
for all numerical analysis papers. A 95 percent range made by resampling whole
papers has no useful spread with only one paper; the analysis must say this
plainly rather than suggesting that the range gives broad certainty.
