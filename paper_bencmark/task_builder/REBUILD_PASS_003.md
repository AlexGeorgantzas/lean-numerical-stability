# HighamBench rebuild pass 3

## Scope

- Baseline audit: `audit_002`
- Baseline status: completed, with 59 fully validated eligible results
- Pass-3 scope: the 25 fully validated Audit 2 results that were not accepted
- Processing order: the order in the ledger below
- Active task: none; Builder work is complete
- Rebuilds started: 25/25
- Rebuilds committed and pushed: 25/25
- Corrected-source audit exclusions: 2 (`P07-T2`, `P16-T2`)
- Pass-3 audits accepted: 0/23 eligible tasks

All 25 tasks have dedicated rebuild commits on the remote branch. The project
owner resolved the three former source blocks: `P07-T2` and `P16-T2` retain
their cited results as explicitly project-corrected tasks and are excluded from
ordinary faithfulness scoring, while `P10-T3` was reselected to the valid exact
block-inverse reduction in the proof of Theorem 3.3. The decisions and source
evidence are documented below.

## Operating rules

1. Work on one task at a time unless the project owner explicitly changes the
   order or authorizes parallel rebuilding.
2. Before editing, run the Builder's `audit_context.py` for the task and read
   the complete Audit 2 decision and report. Also read the source contract,
   direct judgment, round-trip judgment, adjudication, and every recorded minor
   or unclear finding when those artifacts exist.
3. Verify the audited target and PDF hashes. If the current target has changed,
   inspect the intervening commits and establish which audit findings still
   apply before rebuilding.
4. Reconstruct the selected paper result from the PDF and imported declarations;
   do not repair only the headline audit classification.
5. Complete the task-local Builder checks in `WORKFLOW.md`. Corpus-wide snapshot
   hashes remain deferred until the stable end-of-cycle checkpoint.
6. After each rebuild, update this ledger, create a task-scoped commit, and push
   it to `benchmark_faithfulness_audit` before starting the next task.
7. Mark a task `accepted` only after an independent pass-3 faithfulness audit
   returns `faithful-equivalent` or `faithful-stronger` and its bundle validates.
8. Source reselection, a paper-level tier reassignment, or a contradicted source
   claim still requires explicit project-owner approval.

## Status vocabulary

- `pending`: no pass-3 rebuild has started.
- `in-progress`: the Builder is actively reconstructing the task.
- `blocked`: progress requires source clarification or project-owner approval.
- `rebuilt-pushed`: the rebuilt task has a dedicated commit on the remote branch.
- `audit-pending`: an independent pass-3 audit has been requested or started.
- `accepted`: the validated pass-3 audit accepted the rebuilt task.
- `rebuild-again`: the validated pass-3 audit did not accept the rebuilt task.
- `excluded-source-defect`: the owner-retained corrected task is outside the
  ordinary faithfulness denominator under a source-validity record.

## Ledger

The evidence commit pins the exact Audit 2 task bundle. The linked task-local
decision and report are convenient views; if a later audit replaces them, use
the evidence commit and the hashes in `audit_002/results.json` to recover the
Audit 2 versions.

| # | Task | Audit 2 result | Implications L->P / P->L | Evidence commit | Audit 2 notes | Pass-3 status | Rebuild commit | Pass-3 audit |
|---:|---|---|---|---|---|---|---|---|
| 1 | `P04-T1` | `not-faithful-weaker` | `no / yes` | `0ab5d3555a22` | [decision](../highambench/tasks/P04/T1/faithfulness/decision.json), [report](../highambench/tasks/P04/T1/faithfulness/report.md) | `rebuilt-pushed` | `1d1dea9e3` | - |
| 2 | `P04-T2` | `not-faithful-different` | `no / no` | `340f64c844ff` | [decision](../highambench/tasks/P04/T2/faithfulness/decision.json), [report](../highambench/tasks/P04/T2/faithfulness/report.md) | `rebuilt-pushed` | `74a1dffee` | - |
| 3 | `P05-T1` | `not-faithful-different` | `no / no` | `c75077eefad7` | [decision](../highambench/tasks/P05/T1/faithfulness/decision.json), [report](../highambench/tasks/P05/T1/faithfulness/report.md) | `rebuilt-pushed` | `0402e4ec3` | - |
| 4 | `P05-T2` | `not-faithful-different` | `no / no` | `eb1f4d90e3fd` | [decision](../highambench/tasks/P05/T2/faithfulness/decision.json), [report](../highambench/tasks/P05/T2/faithfulness/report.md) | `rebuilt-pushed` | `5eff63450` | - |
| 5 | `P05-T3` | `not-faithful-weaker` | `no / yes` | `406fab50515a` | [decision](../highambench/tasks/P05/T3/faithfulness/decision.json), [report](../highambench/tasks/P05/T3/faithfulness/report.md) | `rebuilt-pushed` | `47d060c99` | - |
| 6 | `P06-T1` | `not-faithful-weaker` | `no / yes` | `be015f6d50ce` | [decision](../highambench/tasks/P06/T1/faithfulness/decision.json), [report](../highambench/tasks/P06/T1/faithfulness/report.md) | `rebuilt-pushed` | `23ca8a94f` | - |
| 7 | `P07-T2` | `not-faithful-weaker` | `no / yes` | `cef9fdfaa43e` | [decision](../highambench/tasks/P07/T2/faithfulness/decision.json), [report](../highambench/tasks/P07/T2/faithfulness/report.md) | `rebuilt-pushed` | `dab184314` | `excluded-source-defect` |
| 8 | `P08-T3` | `not-faithful-different` | `no / no` | `b172c68f6218` | [decision](../highambench/tasks/P08/T3/faithfulness/decision.json), [report](../highambench/tasks/P08/T3/faithfulness/report.md) | `rebuilt-pushed` | `e2fcbfdcb` | - |
| 9 | `P09-T2` | `not-faithful-different` | `no / no` | `d184164e2187` | [decision](../highambench/tasks/P09/T2/faithfulness/decision.json), [report](../highambench/tasks/P09/T2/faithfulness/report.md) | `rebuilt-pushed` | `89fa203cc` | - |
| 10 | `P09-T3` | `not-faithful-different` | `no / no` | `6b8ca8416867` | [decision](../highambench/tasks/P09/T3/faithfulness/decision.json), [report](../highambench/tasks/P09/T3/faithfulness/report.md) | `rebuilt-pushed` | `85d54831c` | - |
| 11 | `P10-T1` | `not-faithful-weaker` | `no / yes` | `624ef97f4f9f` | [decision](../highambench/tasks/P10/T1/faithfulness/decision.json), [report](../highambench/tasks/P10/T1/faithfulness/report.md) | `rebuilt-pushed` | `c49e920af` | - |
| 12 | `P10-T2` | `not-faithful-different` | `no / no` | `ceb4251350f7` | [decision](../highambench/tasks/P10/T2/faithfulness/decision.json), [report](../highambench/tasks/P10/T2/faithfulness/report.md) | `rebuilt-pushed` | `3e42b5a31` | - |
| 13 | `P10-T3` | `not-faithful-different` | `no / no` | `c985025981ec` | [decision](../highambench/tasks/P10/T3/faithfulness/decision.json), [report](../highambench/tasks/P10/T3/faithfulness/report.md) | `rebuilt-pushed` | `a484b0274` | - |
| 14 | `P11-T1` | `not-faithful-weaker` | `no / yes` | `fd63257e85de` | [decision](../highambench/tasks/P11/T1/faithfulness/decision.json), [report](../highambench/tasks/P11/T1/faithfulness/report.md) | `rebuilt-pushed` | `b8e484e7f` | - |
| 15 | `P11-T3` | `not-faithful-different` | `no / no` | `9e89faf58c92` | [decision](../highambench/tasks/P11/T3/faithfulness/decision.json), [report](../highambench/tasks/P11/T3/faithfulness/report.md) | `rebuilt-pushed` | `34773e2fa` | - |
| 16 | `P12-T2` | `not-faithful-weaker` | `no / yes` | `b7d3d843d9a0` | [decision](../highambench/tasks/P12/T2/faithfulness/decision.json), [report](../highambench/tasks/P12/T2/faithfulness/report.md) | `rebuilt-pushed` | `deff8248e` | - |
| 17 | `P12-T3` | `not-faithful-weaker` | `no / yes` | `c3afb57814be` | [decision](../highambench/tasks/P12/T3/faithfulness/decision.json), [report](../highambench/tasks/P12/T3/faithfulness/report.md) | `rebuilt-pushed` | `16d97346f` | - |
| 18 | `P15-T3` | `not-faithful-different` | `no / no` | `74f8c0a42173` | [decision](../highambench/tasks/P15/T3/faithfulness/decision.json), [report](../highambench/tasks/P15/T3/faithfulness/report.md) | `rebuilt-pushed` | `779eb38a8` | - |
| 19 | `P16-T2` | `not-faithful-weaker` | `no / yes` | `e2edb9b4c0cd` | [decision](../highambench/tasks/P16/T2/faithfulness/decision.json), [report](../highambench/tasks/P16/T2/faithfulness/report.md) | `rebuilt-pushed` | `10590dee8` | `excluded-source-defect` |
| 20 | `P16-T3` | `not-faithful-different` | `no / no` | `40fd4df778a1` | [decision](../highambench/tasks/P16/T3/faithfulness/decision.json), [report](../highambench/tasks/P16/T3/faithfulness/report.md) | `rebuilt-pushed` | `d5b6f62e8` | - |
| 21 | `P18-T1` | `undetermined` | `unclear / no` | `ec13f9585b76` | [decision](../highambench/tasks/P18/T1/faithfulness/decision.json), [report](../highambench/tasks/P18/T1/faithfulness/report.md) | `rebuilt-pushed` | `266f923d6` | - |
| 22 | `P18-T3` | `not-faithful-weaker` | `no / yes` | `b1616ce83dca` | [decision](../highambench/tasks/P18/T3/faithfulness/decision.json), [report](../highambench/tasks/P18/T3/faithfulness/report.md) | `rebuilt-pushed` | `ae1521f6b` | - |
| 23 | `P19-T2` | `not-faithful-different` | `no / no` | `a88a277ace1e` | [decision](../highambench/tasks/P19/T2/faithfulness/decision.json), [report](../highambench/tasks/P19/T2/faithfulness/report.md) | `rebuilt-pushed` | `3e66be0df` | - |
| 24 | `P19-T3` | `not-faithful-weaker` | `no / yes` | `01678017bf60` | [decision](../highambench/tasks/P19/T3/faithfulness/decision.json), [report](../highambench/tasks/P19/T3/faithfulness/report.md) | `rebuilt-pushed` | `fc9da3a86` | - |
| 25 | `P20-T3` | `not-faithful-different` | `no / no` | `d1ca8c6b6626` | [decision](../highambench/tasks/P20/T3/faithfulness/decision.json), [report](../highambench/tasks/P20/T3/faithfulness/report.md) | `rebuilt-pushed` | `1475db430` | - |

## Resolved Source Decisions

### P07-T2

Theorem 3.5 on PDF page 16, printed page 920, contains two incompatible
perturbed-solution claims. Its statement prints
`(A + DeltaA) xHat = b + deltaB`, while its proof identifies
`xHat = (A + DeltaA)^dagger (b + deltaB)`. For a tall least-squares problem,
the latter does not imply the former unless the perturbed right-hand side is
in the range of the perturbed matrix. The proof's product-pseudoinverse step
also requires perturbed full column rank (or an equivalent product rule), but
equation (3.9) places no bound on `DeltaYHat` and the paper states neither
condition.

Audit 2 consequently rejected the normal-equation formalization as strictly
weaker than both printed claims. The project owner approved retaining Theorem
3.5 as a corrected source result. Commit `dab184314` adds perturbed full-column
rank and perturbed-right-hand-side consistency, proves the actual product
pseudoinverse and exact perturbed system, and preserves the four-term norm
budget. Its [source-validity record](../faithfulness_audit/source_validity/P07-T2.md)
documents the correction; ordinary faithfulness scoring is excluded.

### P10-T3

The selected result includes the four displayed SylR block-error estimates,
their recurrence, equation (20), and the resulting logarithmic-stability claim
on PDF page 28, printed page 86. The displayed simplification for `R12` replaces
the already accumulated total errors in `R11` and `R22` by the unaugmented
smaller-problem error. Substituting the paper's immediately preceding `R11`
and `R22` inequalities does not justify that step.

More concretely, write
`alpha = ||A||/sep(A,B)` and `beta = ||B||/sep(A,B)`. The four inequalities
before simplification yield an error coefficient containing
`4 + 2*alpha + 2*beta + 2*alpha*beta`, together with propagated forcing terms
from the `R11` and `R22` right-hand-side errors. The printed recurrence contains
only `4 + 2*alpha + 2*beta`. The omitted terms are first order in the rounding
error, so the paper's stated suppression of higher-order terms does not remove
them. The published paper, the authors' final copy, and the arXiv version all
print the same step; no correction was found.

A sound operational rebuild could use a corrected recurrence, but it could not
retain equation (20). The project owner instead approved source reselection.
Commit `a484b0274` selects the valid unnumbered block inverse in the converse
proof of Theorem 3.3, PDF page 12 / printed page 70. The new target proves both
inverse directions and extracts `A*B` from the upper-right block. It does not
overlap P10-T1 or P10-T2, which both select first-order content from equation
(8). The rebuilt task remains eligible for an independent pass-3 audit.

### P16-T2

The backward-error clause of Lemma 4.2 uses
`||xHat_i||_2 lesssim ||xHat_(i+1)||_2` in the proof after equation (4.18), but
does not state that comparison as a hypothesis. Without it, the displayed
first-order recurrence (4.15) is false even for a one-dimensional nonsingular
system satisfying the printed residual, update, and correction models.

For any fixed `0 < epsilonR < 1`, take `A = [1]`, `b = [1]`,
`xHat_i = [1/epsilonR - 1]`, `xHat_(i+1) = [0]`, `deltaR_i = [-1]`,
`correctionHat_i = [-(1/epsilonR - 1)]`, `deltaX_i = [0]`, and
`epsilonU = w_i = omega_i = 0`. Equations (4.1) and (4.2) hold, the correction
residual in (4.14) is zero, and every required coefficient is nonnegative.
Equation (4.15), however, reduces to `1 lesssim epsilonR`, which is not a
first-order consequence as `epsilonR` becomes small.

Audit 2 rejected the previous target as weaker because it already depended on
this unprinted condition and imposed one particular asymptotic interpretation.
The project owner approved retaining Lemma 4.2 as a corrected source result.
Commit `10590dee8` removes the comparison from the printed-step certificate and
makes it an explicit theorem premise, then derives exact identity (4.18) and
recurrence (4.15). Its
[source-validity record](../faithfulness_audit/source_validity/P16-T2.md)
documents the correction; ordinary faithfulness scoring is excluded.

## End-of-pass checkpoint

The Builder phase ended with all 25 tasks rebuilt and pushed. Independent
pass-3 audits remain pending for the 23 eligible tasks; `P07-T2` and `P16-T2`
are excluded under their source-validity records.

Corpus-wide controlled manifests, release hashes, environment identity, and
run order remain intentionally stale during this rebuild/audit cycle. After
the independent audits and any resulting repairs are settled, use
`WORKFLOW.md` to reconcile semantic metadata, regenerate those hashes once,
validate the construction snapshot, and commit the generated metadata
separately. Benchmark measurements remain forbidden before that checkpoint.
