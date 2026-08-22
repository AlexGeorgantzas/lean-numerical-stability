# HighamBench rebuild pass 4

## Scope

- Baseline audit: finalized `audit_003`
- Audit history commit:
  `a06728e225be6348dcd72754114d0c9af1b5d4eb`
- Latest task-audit commit:
  `cbfd683407c8fbbfc990511c00e7d1c2e542f91d`
- Ordinary audit scope: 57 tasks after three source-validity exclusions
- Baseline accepted: 45/57
- Pass-4 scope: the 12 Audit 3 results that were not accepted
- Processing order: the order in the ledger below
- Active task: `P09-T2`
- Reviews started: 3/12
- Rebuilds committed and pushed: 2/12
- Pass-4 audits accepted: 0/12

This is the final currently planned rebuild pass. `P10-T3` is not in scope: its
fresh audit classified the reselected block-inverse task as
`faithful-equivalent`, bringing the ordinary accepted count to 45/57.

The audit protocol is deliberately strict but is not treated as an infallible
oracle. An unaccepted classification is diagnostic evidence, not by itself
proof that the target is mathematically unfaithful. Before changing a task, the
Builder must check the complete audit reasoning against the primary paper,
the exact Lean proposition, and every imported declaration. A task must not be
distorted merely to satisfy an audit judgment.

## Baseline integrity

The finalized Audit 3 history records:

- `results.json` SHA-256:
  `68867273fbb7ace037910b58eab24f3b5ecdf63fd0905d15dc608609a7d3f491`;
- `summary.md` SHA-256:
  `a62d9d8c261e4fa76cfdcb0c0460d761e0704408e781cdf61d208dcd1c789aae`;
- seven `not-faithful-weaker` results with implications `no / yes`; and
- five `not-faithful-different` results with implications `no / no`.

Each ledger row records the task-specific evidence commit and audited target
hash. Those values pin the exact Audit 3 diagnosis even after a later audit
replaces the task-local `faithfulness/` files.

## Operating rules

1. Work on one task at a time unless the project owner explicitly changes the
   order or authorizes parallel rebuilding.
2. Start by running the Builder's `audit_context.py` for the task. Verify the
   Audit 3 result, target hash, PDF hash, decision hash, and report hash before
   relying on any finding.
3. Read the final decision, complete report, source contract, direct judgment,
   round-trip judgment, and adjudication output when present. Inspect every
   major, minor, note, uncertainty, and failed or unclear semantic check.
4. Independently classify the audit diagnosis as a genuine target defect, a
   defensible formalization choice, or unresolved source ambiguity. Record the
   conclusion in this ledger before editing.
5. For a genuine defect, reconstruct the selected result from the paper rather
   than patching only the audit's headline complaint. Preserve all binders,
   hypotheses, conclusions, constants, algorithm linkage, error semantics,
   dimensions, norms, and quantifier dependencies.
6. If the current target is defensibly faithful and the rejection appears to
   be an audit false negative, do not change the proposition merely to obtain
   acceptance. Record primary evidence and use `audit-finding-disputed` for
   owner review.
7. Source reselection, tier reassignment, or treatment of a contradicted or
   materially ambiguous source claim requires explicit project-owner approval.
8. Complete the task-local Builder validations in `WORKFLOW.md`. Do not edit
   prior audit artifacts or Audit 3 history.
9. Once execution of this pass is authorized, give each rebuilt task its own
   commit and push before beginning the next task. Mark it `accepted` only
   after an independent validated Pass 4 audit returns
   `faithful-equivalent` or `faithful-stronger`.
10. Keep corpus-wide controlled manifests, release hashes, environment
    identity, and run order deferred until the rebuild and re-audit cycle is
    settled. Benchmark measurements remain forbidden before that checkpoint.

## Status vocabulary

- `pending-review`: no Pass 4 Builder review has started.
- `review-in-progress`: the Builder is checking the audit against the source
  and elaborated Lean proposition.
- `repair-required`: the Builder confirmed a genuine target defect and has a
  source-grounded repair contract.
- `audit-finding-disputed`: primary evidence supports the existing target or
  exposes an audit false negative; project-owner review is required.
- `needs-owner-decision`: source reselection, tier reassignment, or another
  project-level decision is required.
- `rebuild-in-progress`: an approved repair is being implemented.
- `rebuilt-pushed`: the rebuilt task has a dedicated remote commit.
- `audit-pending`: an independent Pass 4 audit has been requested or started.
- `accepted`: a validated Pass 4 audit accepted the rebuilt task.
- `unaccepted-final`: the final validated audit did not accept the task and no
  further rebuild pass is currently planned.

## Ledger

The diagnosis column is a compact description of the Audit 3 finding, not a
Builder endorsement. The Builder assessment column must be completed from
primary evidence before a task moves to `repair-required`,
`audit-finding-disputed`, or `needs-owner-decision`.

| # | Task | Tier | Audit 3 result | L->P / P->L | Evidence commit | Target SHA-256 | Audit 3 notes | Audit diagnosis | Builder assessment | Pass-4 status | Rebuild commit | Pass-4 audit |
|---:|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `P04-T2` | T2 | `not-faithful-weaker` | `no / yes` | `7bf69e8ca6a7` | `deb0f26432df` | [decision](../highambench/tasks/P04/T2/faithfulness/decision.json), [report](../highambench/tasks/P04/T2/faithfulness/report.md) | Output precision is unnecessarily restricted to `uLow` or `uHigh`. | Confirmed from C127--C128: only `uFma` is restricted to the low/high formats; Algorithm 3.1's final working/output precision is independent. Removed exactly that unsupported premise and validated a run with a distinct third precision. | `rebuilt-pushed` | `de2a3c719` | - |
| 2 | `P06-T1` | T1 | `not-faithful-weaker` | `no / yes` | `679d7f4b104d` | `582a7ed4a777` | [decision](../highambench/tasks/P06/T1/faithfulness/decision.json), [report](../highambench/tasks/P06/T1/faithfulness/report.md) | Per-column certificates assume major theorem content, the QR run is not linked to the stochastic trace, and the pointwise higher-order witnesses can be vacuous. | Confirmed from Lemmas 4.2--4.3 and Theorem 4.4: the current `perColumn` premise supplies conclusions that the paper derives from Model 1.5 and the probability-one local bound. The frozen library has no theorem closing that matrix-concentration argument, so a faithful repair of the full selected theorem would require formalizing the missing probabilistic proof stack. The clean alternative is to reselect the paper's explicit implication sentence immediately before (4.20), with simultaneous (4.17) as its premise, but that source narrowing requires owner approval. | `needs-owner-decision` | - | - |
| 3 | `P08-T3` | T3 | `not-faithful-weaker` | `no / yes` | `9611bc6846c7` | `2e0ed250d2dc` | [decision](../highambench/tasks/P08/T3/faithfulness/decision.json), [report](../highambench/tasks/P08/T3/faithfulness/report.md) | The run adds unsupported `m = 0` correction and update requirements, specializes implementation details, and does not encode dimension-only uniformity. | Confirmed the first two defects from printed page 824: the actual loop starts at `m=1`, while `x_0`, `r_0`, and `d_0` are auxiliary. Removed the invented zero-index solve and rounded subtraction, replaced the underspecified operational elimination trace with page 823's solve interface, and encoded the exact `h_(m+1)` update equation and bound used in Lemma 4.2. The dimension-only package still supplies functions of `n` and checks every named constant; the paper specifies neither the functions nor a matrix comparison relation, so the audit's demand for a separately quantified all-problem family is disputed rather than strengthened beyond the source. | `rebuilt-pushed` | `9572883f8` | - |
| 4 | `P09-T2` | T2 | `not-faithful-weaker` | `no / yes` | `c0f50d60c4cf` | `6bfa09c58a63` | [decision](../highambench/tasks/P09/T2/faithfulness/decision.json), [report](../highambench/tasks/P09/T2/faithfulness/report.md) | The RMS asymptotic theorem is supplied as a certificate instead of derived for the modeled FFT execution. | - | `pending-review` | - | - |
| 5 | `P11-T1` | T1 | `not-faithful-weaker` | `no / yes` | `f5f038d149f4` | `d288077fb173` | [decision](../highambench/tasks/P11/T1/faithfulness/decision.json), [report](../highambench/tasks/P11/T1/faithfulness/report.md) | The inherited all-k condition uses an incorrectly grouped `c1` formula that narrows applicability. | - | `pending-review` | - | - |
| 6 | `P12-T3` | T3 | `not-faithful-weaker` | `no / yes` | `4100a7522add` | `d2835574e18a` | [decision](../highambench/tasks/P12/T3/faithfulness/decision.json), [report](../highambench/tasks/P12/T3/faithfulness/report.md) | The second TwoProduct call uses a half-`beta^p` raw-input grid bound where the paper permits half-`beta^(2p)`. | - | `pending-review` | - | - |
| 7 | `P15-T3` | T3 | `not-faithful-different` | `no / no` | `364b6d1c9548` | `1877c9100346` | [decision](../highambench/tasks/P15/T3/faithfulness/decision.json), [report](../highambench/tasks/P15/T3/faithfulness/report.md) | The execution and BLR domains are simultaneously narrower and broader than the paper, while perturbation and triangular-solve content is pre-certified. | - | `pending-review` | - | - |
| 8 | `P16-T3` | T3 | `not-faithful-different` | `no / no` | `c3398249f31c` | `f4fd7fadeb50` | [decision](../highambench/tasks/P16/T3/faithfulness/decision.json), [report](../highambench/tasks/P16/T3/faithfulness/report.md) | Restart records assume convergence content, MGS-GMRES linkage is incomplete, and dimension factors, remainders, and attainable levels differ from the source. | - | `pending-review` | - | - |
| 9 | `P18-T3` | T3 | `not-faithful-different` | `no / no` | `690121f03c46` | `49f3c1f801a3` | [decision](../highambench/tasks/P18/T3/faithfulness/decision.json), [report](../highambench/tasks/P18/T3/faithfulness/report.md) | The exact tableau is not linked to Method 4s3pC, and the regularity regimes, local orders, exact-flow semantics, and global propagation are largely assumed. | - | `pending-review` | - | - |
| 10 | `P19-T2` | T2 | `not-faithful-different` | `no / no` | `010928845658` | `93526540f05f` | [decision](../highambench/tasks/P19/T2/faithfulness/decision.json), [report](../highambench/tasks/P19/T2/faithfulness/report.md) | The target admits singular bases, leaves first-order semantics and dimension constants arbitrary, and assumes MGS and Appendix-A conclusions. | - | `pending-review` | - | - |
| 11 | `P19-T3` | T3 | `not-faithful-different` | `no / no` | `2adfcd920235` | `951ad8781d52` | [decision](../highambench/tasks/P19/T3/faithfulness/decision.json), [report](../highambench/tasks/P19/T3/faithfulness/report.md) | Appendix bounds are premises, the two uses of `u_g` are disconnected, constants and first-order semantics are uncontrolled, and singular bases can pass the encoded condition. | - | `pending-review` | - | - |
| 12 | `P20-T3` | T3 | `not-faithful-weaker` | `no / yes` | `e826151e14e4` | `dcc89a9a1a76` | [decision](../highambench/tasks/P20/T3/faithfulness/decision.json), [report](../highambench/tasks/P20/T3/faithfulness/report.md) | The substantive Section 4 derivation is assumed, first-order semantics are unconstrained, and the second bound regroups equation (4.32) instead of representing equation (4.33). | - | `pending-review` | - | - |

## End-of-pass checkpoint

Do not refresh the complete benchmark snapshot while this ledger is active.
After all 12 tasks have final dispositions and no Builder or Auditor is writing
task files, follow `WORKFLOW.md` to reconcile semantic metadata, regenerate the
deferred hashes once, validate the construction snapshot, and commit generated
metadata separately. Only then can the corpus move toward measurement-ready
status.
