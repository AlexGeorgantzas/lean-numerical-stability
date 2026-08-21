# HighamBench rebuild pass 3

## Scope

- Baseline audit: `audit_002`
- Baseline status: completed, with 59 fully validated eligible results
- Pass-3 scope: the 25 fully validated Audit 2 results that were not accepted
- Processing order: the order in the ledger below
- Active task: `P09-T2`
- Rebuilds started: 9/25
- Rebuilds committed and pushed: 7/25
- Pass-3 audits accepted: 0/25

`P04-T1`, `P04-T2`, `P05-T1`, `P05-T2`, `P05-T3`, and `P06-T1` have been
rebuilt and pushed. `P07-T2` is blocked on source clarification; `P08-T3` has
also been rebuilt and pushed, and `P09-T2` is in progress.

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
| 7 | `P07-T2` | `not-faithful-weaker` | `no / yes` | `cef9fdfaa43e` | [decision](../highambench/tasks/P07/T2/faithfulness/decision.json), [report](../highambench/tasks/P07/T2/faithfulness/report.md) | `blocked` | - | source contradiction documented below |
| 8 | `P08-T3` | `not-faithful-different` | `no / no` | `b172c68f6218` | [decision](../highambench/tasks/P08/T3/faithfulness/decision.json), [report](../highambench/tasks/P08/T3/faithfulness/report.md) | `rebuilt-pushed` | `e2fcbfdcb` | - |
| 9 | `P09-T2` | `not-faithful-different` | `no / no` | `d184164e2187` | [decision](../highambench/tasks/P09/T2/faithfulness/decision.json), [report](../highambench/tasks/P09/T2/faithfulness/report.md) | `in-progress` | - | - |
| 10 | `P09-T3` | `not-faithful-different` | `no / no` | `6b8ca8416867` | [decision](../highambench/tasks/P09/T3/faithfulness/decision.json), [report](../highambench/tasks/P09/T3/faithfulness/report.md) | `pending` | - | - |
| 11 | `P10-T1` | `not-faithful-weaker` | `no / yes` | `624ef97f4f9f` | [decision](../highambench/tasks/P10/T1/faithfulness/decision.json), [report](../highambench/tasks/P10/T1/faithfulness/report.md) | `pending` | - | - |
| 12 | `P10-T2` | `not-faithful-different` | `no / no` | `ceb4251350f7` | [decision](../highambench/tasks/P10/T2/faithfulness/decision.json), [report](../highambench/tasks/P10/T2/faithfulness/report.md) | `pending` | - | - |
| 13 | `P10-T3` | `not-faithful-different` | `no / no` | `c985025981ec` | [decision](../highambench/tasks/P10/T3/faithfulness/decision.json), [report](../highambench/tasks/P10/T3/faithfulness/report.md) | `pending` | - | - |
| 14 | `P11-T1` | `not-faithful-weaker` | `no / yes` | `fd63257e85de` | [decision](../highambench/tasks/P11/T1/faithfulness/decision.json), [report](../highambench/tasks/P11/T1/faithfulness/report.md) | `pending` | - | - |
| 15 | `P11-T3` | `not-faithful-different` | `no / no` | `9e89faf58c92` | [decision](../highambench/tasks/P11/T3/faithfulness/decision.json), [report](../highambench/tasks/P11/T3/faithfulness/report.md) | `pending` | - | - |
| 16 | `P12-T2` | `not-faithful-weaker` | `no / yes` | `b7d3d843d9a0` | [decision](../highambench/tasks/P12/T2/faithfulness/decision.json), [report](../highambench/tasks/P12/T2/faithfulness/report.md) | `pending` | - | - |
| 17 | `P12-T3` | `not-faithful-weaker` | `no / yes` | `c3afb57814be` | [decision](../highambench/tasks/P12/T3/faithfulness/decision.json), [report](../highambench/tasks/P12/T3/faithfulness/report.md) | `pending` | - | - |
| 18 | `P15-T3` | `not-faithful-different` | `no / no` | `74f8c0a42173` | [decision](../highambench/tasks/P15/T3/faithfulness/decision.json), [report](../highambench/tasks/P15/T3/faithfulness/report.md) | `pending` | - | - |
| 19 | `P16-T2` | `not-faithful-weaker` | `no / yes` | `e2edb9b4c0cd` | [decision](../highambench/tasks/P16/T2/faithfulness/decision.json), [report](../highambench/tasks/P16/T2/faithfulness/report.md) | `pending` | - | - |
| 20 | `P16-T3` | `not-faithful-different` | `no / no` | `40fd4df778a1` | [decision](../highambench/tasks/P16/T3/faithfulness/decision.json), [report](../highambench/tasks/P16/T3/faithfulness/report.md) | `pending` | - | - |
| 21 | `P18-T1` | `undetermined` | `unclear / no` | `ec13f9585b76` | [decision](../highambench/tasks/P18/T1/faithfulness/decision.json), [report](../highambench/tasks/P18/T1/faithfulness/report.md) | `pending` | - | - |
| 22 | `P18-T3` | `not-faithful-weaker` | `no / yes` | `b1616ce83dca` | [decision](../highambench/tasks/P18/T3/faithfulness/decision.json), [report](../highambench/tasks/P18/T3/faithfulness/report.md) | `pending` | - | - |
| 23 | `P19-T2` | `not-faithful-different` | `no / no` | `a88a277ace1e` | [decision](../highambench/tasks/P19/T2/faithfulness/decision.json), [report](../highambench/tasks/P19/T2/faithfulness/report.md) | `pending` | - | - |
| 24 | `P19-T3` | `not-faithful-weaker` | `no / yes` | `01678017bf60` | [decision](../highambench/tasks/P19/T3/faithfulness/decision.json), [report](../highambench/tasks/P19/T3/faithfulness/report.md) | `pending` | - | - |
| 25 | `P20-T3` | `not-faithful-different` | `no / no` | `d1ca8c6b6626` | [decision](../highambench/tasks/P20/T3/faithfulness/decision.json), [report](../highambench/tasks/P20/T3/faithfulness/report.md) | `pending` | - | - |

## Blocked Task Evidence

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

Audit 2 consequently rejected the current normal-equation formalization as
strictly weaker than both printed claims. Rebuilding either printed claim
would require adding an unprinted range/rank hypothesis; retaining the valid
factorization and norm estimate would require narrowing the selected source.
Both choices require project-owner approval under operating rule 8. No P07-T2
construction files were changed in pass 3.

## End-of-pass checkpoint

After all reachable pass-3 rebuilds and audits finish, use `WORKFLOW.md` to
reconcile semantic metadata, regenerate corpus-wide hashes once, validate the
settled construction snapshot, and commit the generated metadata separately.
