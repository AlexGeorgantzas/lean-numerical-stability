# HighamBench construction corpus

This directory contains a 20-paper construction corpus for testing whether
access to the NumStability Lean library helps an agent finish fixed Lean proofs.
A fixed proof means that the theorem statement is chosen before a run and the
agent may change only the proof.

The current corpus contains 60 tasks drawn from papers P01--P20. It may still
change before the measurement-ready snapshot is created.

## Task types

Each paper contributes one task of each type used by the HighamBench 0.2
specification:

- T1, direct use: apply or specialize a close existing NumStability result.
- T2, combine: join multiple existing results with additional reasoning.
- T3, extend: prove a result requiring material not already supplied as a
  complete NumStability theorem.

The manifest and per-task records contain each selected result, source tag,
paper location, fixed Lean statement, and task-specific rationale.

## Papers

| ID | Authors | Paper | Year |
| --- | --- | --- | --- |
| `P01` | Nicholas J. Higham | [The Accuracy of Floating Point Summation](https://doi.org/10.1137/0914050) | 1993 |
| `P02` | Takeshi Ogita, Siegfried M. Rump, and Shin'ichi Oishi | [Accurate Sum and Dot Product](https://doi.org/10.1137/030601818) | 2005 |
| `P03` | Erin Carson and Nicholas J. Higham | [Accelerating the Solution of Linear Systems by Iterative Refinement in Three Precisions](https://doi.org/10.1137/17M1140819) | 2018 |
| `P04` | Pierre Blanchard, Nicholas J. Higham, Florent Lopez, Theo Mary, and Srikara Pranesh | [Mixed Precision Block Fused Multiply-Add: Error Analysis and Application to GPU Tensor Cores](https://doi.org/10.1137/19M1289546) | 2020 |
| `P05` | Siegfried M. Rump and Claude-Pierre Jeannerod | [Improved Backward Error Bounds for LU and Cholesky Factorizations](https://doi.org/10.1137/130927231) | 2014 |
| `P06` | Michael P. Connolly and Nicholas J. Higham | [Probabilistic Rounding Error Analysis of Householder QR Factorization](https://doi.org/10.1137/22M1514817) | 2023 |
| `P07` | Maike Meier, Yuji Nakatsukasa, Alex Townsend, and Marcus Webb | [Are Sketch-and-Precondition Least Squares Solvers Numerically Stable?](https://doi.org/10.1137/23M1551973) | 2024 |
| `P08` | Robert D. Skeel | [Iterative Refinement Implies Numerical Stability for Gaussian Elimination](https://www.jstor.org/stable/2006197) | 1980 |
| `P09` | George U. Ramos | [Roundoff Error Analysis of the Fast Fourier Transform](https://doi.org/10.1090/S0025-5718-1971-0300488-0) | 1971 |
| `P10` | James Demmel, Ioana Dumitriu, and Olga Holtz | [Fast linear algebra is stable](https://doi.org/10.1007/s00211-007-0114-x) | 2007 |
| `P11` | Alicja Smoktunowicz, Jesse L. Barlow, and Julien Langou | [A note on the error analysis of classical Gram–Schmidt](https://doi.org/10.1007/s00211-006-0042-1) | 2006 |
| `P12` | Marko Lange and Shin'ichi Oishi | [A note on Dekker's FastTwoSum algorithm](https://doi.org/10.1007/s00211-020-01114-2) | 2020 |
| `P13` | Nicholas J. Higham | [The numerical stability of barycentric Lagrange interpolation](https://doi.org/10.1093/imanum/24.4.547) | 2004 |
| `P14` | Pierre Blanchard, Desmond J. Higham, and Nicholas J. Higham | [Accurately computing the log-sum-exp and softmax functions](https://doi.org/10.1093/imanum/draa038) | 2021 |
| `P15` | Nicholas J. Higham and Theo Mary | [Solving block low-rank linear systems by LU factorization is numerically stable](https://doi.org/10.1093/imanum/drab020) | 2022 |
| `P16` | Alfredo Buttari, Nicholas J. Higham, Theo Mary, and Bastien Vieublé | [A modular framework for the backward error analysis of GMRES](https://doi.org/10.1093/imanum/draf049) | 2026 |
| `P17` | El-Mehdi El Arar, Massimiliano Fasi, Silviu-Ioan Filip, and Mantas Mikaitis | [Probabilistic Error Analysis of Limited-Precision Stochastic Rounding](https://doi.org/10.1137/24M1681458) | 2025 |
| `P18` | Zachary J. Grant | [Perturbed Runge–Kutta Methods for Mixed Precision Applications](https://doi.org/10.1007/s10915-022-01801-2) | 2022 |
| `P19` | Alfredo Buttari, Xin Liu, Theo Mary, and Bastien Vieublé | [Mixed precision strategies for preconditioned GMRES: a comprehensive analysis](https://hal.science/hal-05071696v2) | 2026 |
| `P20` | Theo Mary and Mantas Mikaitis | [Error Analysis of Matrix Multiplication with Narrow Range Floating-Point Arithmetic](https://doi.org/10.1137/24M1685109) | 2025 |

The local paper PDFs are recorded source copies and remain subject to their
publishers' terms. The benchmark metadata records source locators and hashes and
uses short paraphrases instead of copying long passages from the papers.

## One construction workflow for every paper

P01, P02, and every later P0X entry use the same task schema, source-tag rules,
construction checker, run-order rule, report builder, and hash refresh command.
No paper ID is special-cased by an operational script.

The Lean setting is also uniform without making all papers share all
definitions. `shared/HighamBench/Core.lean` contains only definitions used by
more than one paper. `P01Definitions.lean` and `P02Definitions.lean` contain
only their own paper's extra models and algorithms. Each controlled task
contains the core plus its own paper file. Each trusted compiled bundle follows
the same rule, so a P01 run cannot import the P02 module and a P02 run cannot
import the P01 module.

While the corpus is being built, every paper and task has
`classification_frozen_before_runs` set to `false`. This means its metadata may
be reviewed and corrected. The selected P01 and P02 results and their Lean
statements have not been changed.

After any paper or task edit, refresh all derived metadata with:

```text
python3 paper_bencmark/highambench/tools/refresh_snapshot.py \
  --benchmark-root paper_bencmark/highambench --phase construction
```

Only after the complete corpus, proofs, and reviews are ready should the same
command be run with `--phase measurement-ready`. The benchmark runner rejects
construction-state tasks, so a partial corpus cannot be measured accidentally.

## Two conditions

- `N` means no NumStability library. No source, compiled library file,
  documentation, search index, declaration-name list, or cache from the library
  may be visible.
- `L` means the frozen NumStability source and compiled files are available for
  local use and local search.

Both conditions for a task use the same fixed statement, source material,
paper-scoped task definitions, Lean version, mathlib revision, agent prompt, tools, time limit,
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

There are 360 planned runs:

`60 tasks x 3 repetitions x 2 conditions = 360 runs`.

The first condition in each pair was selected by the fixed SHA-256 rule recorded
in `metadata/run_order.json`. SHA-256 is a repeatable text-to-number calculation.
It makes the order reproducible without presenting repetition IDs as random
seeds.

## Files

- `../TASK_SOURCE_TAGS.md` defines the mandatory source-presentation tags for
  every task. `../AGENTS.md` makes that policy persistent across Codex
  sessions, and `tools/task_tags.py` checks every current task record.
- `tools/refresh_snapshot.py` validates the corpus and regenerates its derived
  metadata: each task's controlled files and hashes, condition order, corpus
  counts, and snapshot and environment identifiers.
- `shared/HighamBench/Core.lean` is the small cross-paper core.
  `shared/HighamBench/P*Definitions.lean` files add only one paper's models and
  algorithms. Manifest scopes and separate compiled bundles keep them isolated.
- `IMPLEMENTATION_PLAN.md` explains the construction decisions and the checks
  required before measured runs.
- `metadata/manifest.json` records all 20 papers, their source hashes, the
  specification hash, all 60 tasks, and their exact source locations.
- `metadata/config.json` freezes the environment and run limits.
- `metadata/run_order.json` fixes the order of N and L for every paired
  repetition.
- `metadata/reviews/` contains construction-stage review records. They are
  evidence from earlier snapshots, not final immutable approvals; final review
  records must be regenerated for every task before measurement.

The review files distinguish completed checks from pending checks. A pending
check is not a pass. Measurement readiness requires current full-corpus
construction evidence and two current final reviews for every task. The
complete measured matrix is also still required.

## Frozen source versions

- Lean: `leanprover/lean4:v4.29.0-rc3`
- mathlib: `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`
- NumStability source baseline:
  `45813a95dacf577461bae13f033af0dbc985a225`
- Paper PDF SHA-256 values and lawful source locators are recorded for every
  corpus paper in `metadata/manifest.json`.
- Specification PDF SHA-256:
  `25a8a72d62e2ad9d131004b871f5ccc58438d488dbd64afcd0a8839e9e4d78a8`

## What a result may say

This pilot may show whether library access changed proof success, time, token
use, or actual library use for these 60 fixed tasks and one fixed agent setup.
It does not test translation from English into Lean or human proof development.
Any uncertainty interval obtained by resampling the 20 papers describes this
corpus and must not be presented as certainty about all numerical analysis
papers.
