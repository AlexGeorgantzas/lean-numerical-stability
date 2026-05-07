# External-Source Pilot Run: May 7, 2026

Draft status: benchmark result note.

This file records the first controlled solver run on the external-source task
suite.  The run is not the final thesis benchmark; it is a pilot datapoint
used to validate task design and harness behavior.

## Run

### E01

- Task: `E01_LapackBerrBackward`
- Run id: `20260507-184135`
- Result root:
  `benchmark/results/E01_LapackBerrBackward/20260507-184135`
- Timeout: 1200 seconds per condition.
- Conditions: A and C used byte-identical task files.
- Generated workspaces were removed after archive.

## Outcome

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver left the original `sorry`; public messages identify the missing residual-error theorem for `fl_residual` as the blocker. |
| Condition C | pass | no | Solver used `conventional_residual_error` and `oettli_prager_sufficient`; final file validated with no placeholders or forbidden declarations. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T15:42:09Z	2026-05-07T15:46:11Z	47	0	5	1	0
condition_c	0	0	no	2026-05-07T15:46:11Z	2026-05-07T15:50:18Z	85	51	44	0	0
```

## Interpretation

This is a valid pilot separation for E01:

- Condition A did not fail due to a timeout or harness error.  It stopped with
  the proof placeholder still present.
- Condition A's public messages point to the intended missing infrastructure:
  the residual-computation error theorem connecting `fl_residual` to the exact
  residual.
- Condition C passed by using public library theorems rather than task-specific
  hidden notes.
- The proof route matches the theorem-truth audit:
  `conventional_residual_error` gives the exact residual bound, then
  `oettli_prager_sufficient` constructs the componentwise perturbations.

This result should not yet be generalized to the whole external suite.  The
next step is to run more external tasks under the same protocol and inspect
failure modes task by task.

## E02 Pilot, First Attempt With Timing Caveat

- Task: `E02_TemplatesResidualStop`
- Run id: `20260507-185210`
- Result root:
  `benchmark/results/E02_TemplatesResidualStop/20260507-185210`
- Timeout setting: 1200 seconds per condition.

Outcome:

| Condition | Validation | Timeout marker | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver left a `sorry`; public messages identify the missing residual soundness theorem as the blocker. |
| Condition C | pass | no | Solver used residual soundness plus forward-error/norm infrastructure and passed validation. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T15:52:37Z	2026-05-07T17:11:46Z	71	7	4	1	0
condition_c	0	0	no	2026-05-07T17:11:46Z	2026-05-07T17:15:25Z	80	69	62	0	0
```

Important caveat:

The E02 Condition A attempt reports `timeout_seconds = 1200` but ran for much
longer than 1200 seconds and did not produce `timeout.txt`.  Therefore E02 is
not an official timing-valid datapoint.  It is still useful qualitatively
because the archived final file, public solver messages, and validation result
show the same intended failure mode as E01.

Follow-up:

`benchmark/scripts/run_codex_attempt.sh` was changed after this run to use
`benchmark/scripts/run_with_timeout.py`, a process-group timeout wrapper.  The
wrapper was tested on a command that sleeps for 5 seconds with a 1-second
timeout and returned exit code 124 with a timeout marker.

## E02 Pilot, Timing-Valid Rerun

- Task: `E02_TemplatesResidualStop`
- Run id: `20260507-201754`
- Result root:
  `benchmark/results/E02_TemplatesResidualStop/20260507-201754`
- Timeout setting: 1200 seconds per condition.
- Runner: fixed process-group timeout wrapper.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver left the original `sorry`; public messages again identify the missing residual soundness theorem as the blocker. |
| Condition C | pass | no | Solver used the library residual/forward-error/norm infrastructure and passed validation. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T17:18:21Z	2026-05-07T17:23:48Z	80	0	5	1	0
condition_c	0	0	no	2026-05-07T17:23:48Z	2026-05-07T17:28:21Z	101	74	67	0	0
```

Interpretation:

This is the timing-valid E02 pilot datapoint.  It confirms the same separation
as the first E02 attempt without the timeout anomaly.

## E03 Pilot

- Task: `E03_LapackFerrForward`
- Run id: `20260507-202911`
- Result root:
  `benchmark/results/E03_LapackFerrForward/20260507-202911`
- Timeout setting: 1200 seconds per condition.
- Runner: fixed process-group timeout wrapper.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver left the original `sorry`; public messages identify the missing floating residual error lemma as the blocker. |
| Condition C | pass | no | Solver used `conventional_residual_error`, `forward_error_from_residual`, and norm/supremum reasoning; final file validated. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T17:29:34Z	2026-05-07T17:37:09Z	87	7	4	1	0
condition_c	0	0	no	2026-05-07T17:37:09Z	2026-05-07T17:40:08Z	79	56	49	0	0
```

Interpretation:

E03 is a timing-valid pilot separation.  It is slightly more algebraic than
E01/E02 because the theorem divides the infinity-norm forward error by
`||xhat||_inf`, but the public messages and final validation still point to
the same library-dependent route.

## E04 Pilot

- Task: `E04_LapackLevel3Matmul`
- Run id: `20260507-204055`
- Result root:
  `benchmark/results/E04_LapackLevel3Matmul/20260507-204055`
- Timeout setting: 1200 seconds per condition.
- Runner: fixed process-group timeout wrapper.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver left the original `sorry`; public messages identify the missing dot-product/matrix-multiplication error theorem as the blocker. |
| Condition C | pass | no | Solver used `matMul_error_bound`, then proved the rectangular infinity-norm row-sum estimate locally; final file validated. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T17:41:17Z	2026-05-07T17:46:37Z	56	0	4	1	0
condition_c	0	0	no	2026-05-07T17:46:37Z	2026-05-07T17:49:14Z	79	50	44	0	0
```

Interpretation:

E04 is a timing-valid pilot separation.  It differs from E01-E03 because it is
a matrix multiplication stability theorem rather than a residual-certificate
theorem.  Condition A's public messages show that it recognized the need to
derive dot-product/matrix-multiplication error bounds from the bare model and
did not complete that derivation.  Condition C found the library's
componentwise matrix multiplication error theorem and supplied the remaining
finite-sum and supremum reasoning in the task file.

## E05 Pilot, Pre-Isolation-Hardening Attempt

- Task: `E05_LapackTriangularResidual`
- Run id: `20260507-205025`
- Result root:
  `benchmark/results/E05_LapackTriangularResidual/20260507-205025`
- Timeout setting: 1200 seconds per condition.
- Runner: fixed process-group timeout wrapper, before the temporary
  `HOME`/`XDG_CACHE_HOME` hardening.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver produced a proof that referenced `backSub_backward_error`; validation rejected it because that theorem is not present in the Condition A stub. |
| Condition C | pass | no | Solver used `backSub_backward_error`, `infNormVec_matMulVec_le`, and norm reasoning; final file validated. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T17:50:47Z	2026-05-07T18:07:22Z	131	68	62	0	0
condition_c	0	0	no	2026-05-07T18:07:22Z	2026-05-07T18:09:46Z	69	55	49	0	0
```

Important caveat:

The Condition A validator did its job: the attempted proof failed because it
used a theorem that the bare stub does not provide.  However, the public solver
messages say the solver discovered a compiled companion library in a local
cache and manually tested the proof with that extra search path.  That means
this first E05 run should not be cited as an isolation-clean datapoint.

Follow-up:

After this run, the harness prompt was tightened to forbid manually discovered
external paths, and `run_codex_attempt.sh` was updated to run Codex with a
temporary `HOME` and `XDG_CACHE_HOME`.  E05 should be rerun after that hardening
before it is treated as an official pilot datapoint.

## E05 Pilot, First Hardened Rerun With Solver-Build Caveat

- Task: `E05_LapackTriangularResidual`
- Run id: `20260507-211235`
- Result root:
  `benchmark/results/E05_LapackTriangularResidual/20260507-211235`
- Timeout setting: 1200 seconds per condition.
- Runner: process-group timeout wrapper, temporary `CODEX_HOME`, temporary
  `HOME`/`XDG_CACHE_HOME`, hardened prompt; before adding the shared Lake
  package cache as a Codex `--add-dir`.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver left the original `sorry`; public messages did not mention external full-library cache discovery. |
| Condition C | pass | no | Solver used `backSub_backward_error` and norm reasoning; final file validated. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T18:12:54Z	2026-05-07T18:16:11Z	35	0	4	1	0
condition_c	0	0	no	2026-05-07T18:16:11Z	2026-05-07T18:23:18Z	78	59	53	0	0
```

Important caveat:

The Condition A isolation looked cleaner in this rerun: the final file was
unchanged and no public message reported finding a compiled full-library
companion module.  However, both conditions reported that solver-side
`lake build BenchmarkTask` could not use dependencies cleanly and tried to
resolve GitHub.  The post-run validator still built the archived final files,
so the Lean pass/fail result is meaningful, but this is not yet the cleanest
solver-experience datapoint.

Follow-up:

After this rerun, `run_codex_attempt.sh` was updated to pass the shared
third-party Lake package cache to Codex through `--add-dir`.  This should let
the solver run `lake build BenchmarkTask` without network or lock-file
artifacts while still keeping the full `LeanFpAnalysis` snapshot out of
Condition A.

## E05 Pilot, Package-Cache Add-Dir Rerun With Toolchain Caveat

- Task: `E05_LapackTriangularResidual`
- Run id: `20260507-212519`
- Result root:
  `benchmark/results/E05_LapackTriangularResidual/20260507-212519`
- Timeout setting: 1200 seconds per condition.
- Runner: process-group timeout wrapper, temporary `CODEX_HOME`, temporary
  `HOME`/`XDG_CACHE_HOME`, hardened prompt, shared third-party Lake package
  cache as Codex `--add-dir`; before passing host `ELAN_HOME`.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver left the original `sorry`; public messages did not mention external full-library cache discovery. |
| Condition C | fail | no | Solver guessed residual-bound theorem names and validation rejected the final file because the guessed theorem was absent. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T18:25:39Z	2026-05-07T18:45:42Z	34	0	4	1	0
condition_c	0	1	no	2026-05-07T18:45:42Z	2026-05-07T18:47:49Z	47	25	19	0	0
```

Important caveat:

This run is not a valid C-failure datapoint.  The public messages show that
the solver still could not use `lean`/`lake` normally because Elan was looking
for the Lean toolchain under the temporary `HOME` and attempted to download
from GitHub.  The prompt also made the solver hesitant to inspect the
Condition C public-library snapshot because the Lake file records the snapshot
as an absolute path.

Follow-up:

The prompt was clarified: files and symlinks already present in the current
workspace, such as `public_library`, `README.md`, `docs`, and `examples`, are
allowed.  `run_codex_attempt.sh` was also updated to pass host `ELAN_HOME`
explicitly while keeping `HOME` and `XDG_CACHE_HOME` temporary.

## E05 Pilot, Isolation-Clean Datapoint

- Task: `E05_LapackTriangularResidual`
- Run id: `20260507-214953`
- Result root:
  `benchmark/results/E05_LapackTriangularResidual/20260507-214953`
- Timeout setting: 1200 seconds per condition.
- Runner: process-group timeout wrapper, temporary `CODEX_HOME`, temporary
  `HOME`/`XDG_CACHE_HOME`, host `ELAN_HOME`, hardened prompt allowing
  workspace-provided public-library symlinks, shared third-party Lake package
  cache as Codex `--add-dir`.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver left the original `sorry`; public messages report that the local stub exposes definitions but no triangular-solve residual theorem. |
| Condition C | pass | no | Solver found `backSub_backward_error`, rewrote the residual as `-ΔU * xhat`, and used `infNormVec_matMulVec_le`; final file validated. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T18:50:14Z	2026-05-07T18:54:11Z	39	0	4	1	0
condition_c	0	0	no	2026-05-07T18:54:11Z	2026-05-07T18:56:51Z	69	66	60	0	0
```

Interpretation:

This is the E05 datapoint to cite.  It is a clean A/C separation on a
triangular-solve residual stability theorem.  The remaining caveat is that the
solver's own `lake build BenchmarkTask` still reported an external Mathlib
lock-file sandbox error; the post-run validator then built the archived final
file successfully and is the authoritative pass/fail check.

## E06 Pilot, First Attempt

- Task: `E06_OettliPragerForward`
- Run id: `20260507-215812`
- Result root:
  `benchmark/results/E06_OettliPragerForward/20260507-215812`
- Timeout setting: 1200 seconds per condition.
- Runner: same corrected harness as the E05 isolation-clean datapoint.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver wrote a local finite-sum perturbation proof, but validation rejected Lean errors. |
| Condition C | fail | no | Solver also wrote a local proof and failed on Lean algebra details instead of applying the existing standard componentwise forward-error theorem. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T18:58:32Z	2026-05-07T19:01:36Z	52	94	88	0	0
condition_c	0	1	no	2026-05-07T19:01:36Z	2026-05-07T19:03:50Z	56	105	99	0	0
```

Interpretation:

This is an informative C failure, not a theorem-truth failure.  The intended
library route is to unpack `opBackwardCompatible` and apply
`componentwise_forward_error_standard`.  The failure exposed a public lookup
gap: the guide listed the more generic `componentwise_forward_error` but not
the standard specialization most relevant to this task.  The lookup table and
example checks were updated after this run; E06 should be rerun with the
updated Condition C snapshot.

## E06 Pilot, Lookup-Updated Rerun

- Task: `E06_OettliPragerForward`
- Run id: `20260507-220547`
- Result root:
  `benchmark/results/E06_OettliPragerForward/20260507-220547`
- Timeout setting: 1200 seconds per condition.
- Runner: corrected harness plus rebuilt Condition C snapshot containing the
  updated lookup table and example checks.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver wrote a non-building local finite-sum proof. |
| Condition C | fail | no | Solver again wrote a local proof and failed on Lean details instead of applying `componentwise_forward_error_standard`. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T19:07:04Z	2026-05-07T19:10:47Z	59	130	124	0	0
condition_c	0	1	no	2026-05-07T19:10:47Z	2026-05-07T19:13:53Z	74	114	108	0	0
```

Interpretation:

This remains an informative C failure.  The task statement is still supported
by the library, but the agent did not discover or choose the short theorem
application route.  This suggests the public guide may need a stronger general
"proof pattern" section for perturbation-transfer theorems, or E06 should be
placed later in the difficulty ordering.

## E07 Pilot

- Task: `E07_TemplatesStationaryResidual`
- Run id: `20260507-221510`
- Result root:
  `benchmark/results/E07_TemplatesStationaryResidual/20260507-221510`
- Timeout setting: 1200 seconds per condition.
- Runner: corrected harness and lookup-updated Condition C snapshot.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | pass | no | Solver derived the stationary residual recurrence and scalar contraction locally from the task-visible definitions. |
| Condition C | pass | no | Solver bridged the task-local error definition to `ComputedIteration` and applied `normwise_residual_bound`. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	0	no	2026-05-07T19:15:29Z	2026-05-07T19:23:00Z	76	218	212	0	0
condition_c	0	0	no	2026-05-07T19:23:00Z	2026-05-07T19:24:36Z	43	17	11	0	0
```

Interpretation:

E07 is not a useful pass/fail separation task in its current form.  It is still
a stability proof, but the statement exposes enough exact stationary-iteration
structure for Condition A to complete a long local derivation.  It may be
useful as an efficiency-gap datapoint, or it should be redesigned/replaced if
the benchmark requires Condition A to fail.

## E08 Pilot

- Task: `E08_LapackLSQRForward`
- Run id: `20260507-222525`
- Result root:
  `benchmark/results/E08_LapackLSQRForward/20260507-222525`
- Timeout setting: 1200 seconds per condition.
- Runner: corrected harness and lookup-updated Condition C snapshot.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver attempted a long local least-squares perturbation proof and failed on finite-sum/absolute-value Lean details. |
| Condition C | pass | no | Solver extracted `DeltaG`/`Deltag` from `LSQRSolveBackwardError` and applied `ls_qr_forward_error`; final file validated. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T19:25:45Z	2026-05-07T19:28:06Z	51	104	98	0	0
condition_c	0	0	no	2026-05-07T19:28:07Z	2026-05-07T19:29:50Z	63	13	7	0	0
```

Interpretation:

E08 is a clean pass/fail separation on a least-squares QR forward-error
certificate.  It is still a specification-transfer task rather than a full QR
algorithm analysis from raw floating-point operations, but it is a sourced
stability proof and exercises library theorem discovery effectively.

## E09 Pilot

- Task: `E09_LapackNormalEquations`
- Run id: `20260507-223046`
- Result root:
  `benchmark/results/E09_LapackNormalEquations/20260507-223046`
- Timeout setting: 1200 seconds per condition.
- Runner: corrected harness and lookup-updated Condition C snapshot.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver attempted a long local normal-equations perturbation proof and failed on Lean details such as an unavailable `abs_add` name. |
| Condition C | fail | no | Solver found `ls_normal_equations_forward_error`, but validation rejected a small finite-sum normalization step in the wrapper bound. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T19:31:07Z	2026-05-07T19:34:32Z	54	104	98	0	0
condition_c	0	1	no	2026-05-07T19:34:32Z	2026-05-07T19:36:28Z	62	31	25	0	0
```

Interpretation:

E09 is an informative C failure, not a theorem-truth failure.  Condition C did
discover the intended theorem, `ls_normal_equations_forward_error`, and reduced
the task to a local inequality converting
`epsG * |ATA j k| * |xhat k|` into
`epsG * (|ATA j k| * |xhat k|)` inside a finite sum.  Validation rejected the
file at that normalization step.

The run also shows why the remaining solver-side Lake lock-file artifact
matters.  The post-run validator reached the real Lean error and archived it,
but the solver reported that `lake build BenchmarkTask` was blocked by the
external Mathlib lock file before it could receive normal compiler feedback.
The archived pass/fail result is valid, but future runs should fix this
solver-feedback artifact before treating C failures as strong evidence about
library usability.

## E10 Pilot

- Task: `E10_OgitaSumKCertificate`
- Run id: `20260507-224508`
- Result root:
  `benchmark/results/E10_OgitaSumKCertificate/20260507-224508`
- Timeout setting: 1200 seconds per condition.
- Runner: corrected harness with workspace-local solver-side Lake wrapper.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | pass | no | Solver used the certificate's visible stage and final-rounding assumptions, then closed the remaining real arithmetic locally. |
| Condition C | pass | no | Solver followed essentially the same certificate-arithmetic route and passed validation. |

Metrics from `metrics.tsv`:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	0	no	2026-05-07T19:45:29Z	2026-05-07T19:46:59Z	31	51	45	0	0
condition_c	0	0	no	2026-05-07T19:46:59Z	2026-05-07T19:48:23Z	33	68	62	0	0
```

Interpretation:

E10 is not a useful pass/fail separation task in its current form.  It is a
sourced stability-certificate theorem, but the hard numerical-analysis content
is already encoded in the task-local certificate assumptions.  The remaining
proof is real-arithmetic composition of those assumptions.  That makes it too
easy for Condition A and means E10 should be redesigned or replaced if the
final benchmark needs the last task to be one where Condition A plausibly
fails and Condition C plausibly succeeds.

Harness note:

This is the first run after adding the workspace-local solver-side Lake
wrapper.  The public solver messages show normal `lake build BenchmarkTask`
success reports rather than the previous external Mathlib lock-file artifact.
Post-run validation still used the real Lake build and passed in both
conditions.

## Aggregate Snapshot

Plots and aggregate metrics for the latest May 7 run per external task were
generated at:

```text
benchmark/results/plots/pass_at_1_20260507_external/
```

Latest-run pass/fail pattern:

- Clean A-fail/C-pass separations: E01, E02, E03, E04, E05, E08.
- Both conditions failed: E06, E09.
- Both conditions passed: E07, E10.

Current design consequence:

The external-source suite is useful as a pilot, but it is not yet the final
thesis benchmark.  E07 and E10 are too solvable in Condition A for a
pass/fail-separation benchmark.  E06 and E09 are theorem-supported but still
failed in Condition C, so they need either better public-library guidance,
minor theorem-wrapper support, or replacement depending on the final protocol.
