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
- Active task: none; all 12 reviews have final Builder dispositions
- Reviews started: 12/12
- Rebuilds committed and pushed: 7/12
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
| 2 | `P06-T1` | T1 | `not-faithful-weaker` | `no / yes` | `679d7f4b104d` | `582a7ed4a777` | [decision](../highambench/tasks/P06/T1/faithfulness/decision.json), [report](../highambench/tasks/P06/T1/faithfulness/report.md) | Per-column certificates assume major theorem content, the QR run is not linked to the stochastic trace, and the pointwise higher-order witnesses can be vacuous. | The owner approved the source reselection proposed after primary review. P06-T1 now selects exactly the sentence preceding (4.20): simultaneous column bounds (4.17) imply the Frobenius bound (4.20). The rebuilt target retains the exact `c6*lambda*sqrt(n)*gammaTilde_m(lambda,u)` coefficient and aggregates genuine `O(u^2)` functions on the punctured physical neighborhood `0<u<1`; it no longer claims Theorem 4.4 or accepts its probabilistic conclusions as certificates. P06-T2 and P06-T3 remain independent accepted source selections. | `rebuilt-pushed` | `80aaad807` | - |
| 3 | `P08-T3` | T3 | `not-faithful-weaker` | `no / yes` | `9611bc6846c7` | `2e0ed250d2dc` | [decision](../highambench/tasks/P08/T3/faithfulness/decision.json), [report](../highambench/tasks/P08/T3/faithfulness/report.md) | The run adds unsupported `m = 0` correction and update requirements, specializes implementation details, and does not encode dimension-only uniformity. | Confirmed the first two defects from printed page 824: the actual loop starts at `m=1`, while `x_0`, `r_0`, and `d_0` are auxiliary. Removed the invented zero-index solve and rounded subtraction, replaced the underspecified operational elimination trace with page 823's solve interface, and encoded the exact `h_(m+1)` update equation and bound used in Lemma 4.2. The dimension-only package still supplies functions of `n` and checks every named constant; the paper specifies neither the functions nor a matrix comparison relation, so the audit's demand for a separately quantified all-problem family is disputed rather than strengthened beyond the source. | `rebuilt-pushed` | `9572883f8` | - |
| 4 | `P09-T2` | T2 | `not-faithful-weaker` | `no / yes` | `c0f50d60c4cf` | `6bfa09c58a63` | [decision](../highambench/tasks/P09/T2/faithfulness/decision.json), [report](../highambench/tasks/P09/T2/faithfulness/report.md) | The RMS asymptotic theorem is supplied as a certificate instead of derived for the modeled FFT execution. | Disputed. The selected page-768 result is explicitly a corollary of Theorem 1(a), and `paper.json` deliberately selects only that fictional-input construction while exposing the immediately preceding theorem as an inherited result. Removing the premise would broaden this task into the full forward-error derivation on pages 759--763. The remainder coefficient and radius are fixed after the complete operational family and before `eps`, matching a local asymptotic result for that fixed family; the paper does not state uniformity across all input families or implementations. | `audit-finding-disputed` | - | - |
| 5 | `P11-T1` | T1 | `not-faithful-weaker` | `no / yes` | `f5f038d149f4` | `d288077fb173` | [decision](../highambench/tasks/P11/T1/faithfulness/decision.json), [report](../highambench/tasks/P11/T1/faithfulness/report.md) | The inherited all-k condition uses an incorrectly grouped `c1` formula that narrows applicability. | Confirmed visually from equation (2), printed page 302. For `k >= 2`, the source coefficient is `2*sqrt(2*m*k)+2*sqrt(k)`, while the shared definition put `m*k` outside the first square root. Corrected `p11C1`; every other adjudicated audit item was already accepted as a faithful local abstraction. The controlled target text is unchanged, but its elaborated run condition now has the source coefficient. | `rebuilt-pushed` | `e88b6512a` | - |
| 6 | `P12-T3` | T3 | `not-faithful-weaker` | `no / yes` | `4100a7522add` | `d2835574e18a` | [decision](../highambench/tasks/P12/T3/faithfulness/decision.json), [report](../highambench/tasks/P12/T3/faithfulness/report.md) | The second TwoProduct call uses a half-`beta^p` raw-input grid bound where the paper permits half-`beta^(2p)`. | Confirmed from equation (17) and printed page 397, including the audit's `7*7*7` counterexample. The second call now uses the local least-exponent grid of `th`, and the displayed `0.5*beta^(2p)` bounds for `a2` and `a3` are represented on the original three-input grid. The private proof replaces its former use of the false small bound with a nearest-rounding radix-lattice argument for the merge error, including exponent-boundary cases. The controlled target text is unchanged, but the elaborated execution domain now admits the source scale. | `rebuilt-pushed` | `4de5158d5` | - |
| 7 | `P15-T3` | T3 | `not-faithful-different` | `no / no` | `364b6d1c9548` | `1877c9100346` | [decision](../highambench/tasks/P15/T3/faithfulness/decision.json), [report](../highambench/tasks/P15/T3/faithfulness/report.md) | The execution and BLR domains are simultaneously narrower and broader than the paper, while perturbation and triangular-solve content is pre-certified. | Confirmed and repaired the concrete domain defects from equations (2.3)--(2.4), (4.3), and (4.22): input and intermediate compressions now require the orientation-specific orthonormal truncated-SVD form and minimum threshold-satisfying rank; factor updates perturb the input and product contributions separately; dense LU and block solves use Lemmas 2.2--2.3; triangular traces require nonsingular diagonal blocks; and their aggregate errors use `c_tri=b+r^(3/2)+p`. The controlled theorem text remains unchanged. The precision family and component Theorem 4.2--4.4 interfaces are intentionally retained because printed page 975 explicitly begins from those theorems and the two big-O conclusions require cross-precision quantification. The exact meaning of “safely smaller” and the source's `Atilde`/`A` notation remain documented source ambiguities rather than invented numeric or object identifications. | `rebuilt-pushed` | `f5c3f4178` | - |
| 8 | `P16-T3` | T3 | `not-faithful-different` | `no / no` | `c3398249f31c` | `f4fd7fadeb50` | [decision](../highambench/tasks/P16/T3/faithfulness/decision.json), [report](../highambench/tasks/P16/T3/faithfulness/report.md) | Restart records assume convergence content, MGS-GMRES linkage is incomplete, and dimension factors, remainders, and attainable levels differ from the source. | Confirmed the concrete defects from Theorem 6.3 and printed pages 1978--1979. Removed the stored Theorem 4.1 one-step recurrences, fixed-precision remainder certificates, geometric `1/(1-Lambda)` envelopes, and unprinted `uHigh <= uLow` restriction. The cast residual is now linked to the first MGS basis vector; every factor is a dimension-only polynomial evaluated at the actual restart key `k_i`; and the target concludes only the two source-scale affine contractions. The exact inequalities are an explicit strengthening of `lesssim`. The correction-level estimates remain the documented interface to the earlier MGS-GMRES analysis invoked by the source, but neither selected global recurrence is an input. New target SHA-256: `b2fbda0cd4a2`. | `rebuilt-pushed` | `7b9403370` | - |
| 9 | `P18-T3` | T3 | `not-faithful-different` | `no / no` | `690121f03c46` | `49f3c1f801a3` | [decision](../highambench/tasks/P18/T3/faithfulness/decision.json), [report](../highambench/tasks/P18/T3/faithfulness/report.md) | The exact tableau is not linked to Method 4s3pC, and the regularity regimes, local orders, exact-flow semantics, and global propagation are largely assumed. | Confirmed a source-level blocker on printed page 18. The paper identifies Method 4s3pC only by 15-decimal coefficients, while its asymptotic claim relies on exact order identities; the literal decimals fail at least `btilde*c^epsilon=0`, and neither the paper nor later primary material supplies the unrounded tableau or proves that one exists. Replacing it by an arbitrary exact tableau changes the method, while a tolerance cannot preserve an exact `h -> 0` order claim. A faithful rebuild therefore needs owner-approved source reselection, an author-supplied exact tableau, or exclusion as source-ambiguous. The audit's additional regularity, exact-flow, and asymptotic-semantics findings would still need reconstruction if exact coefficients became available. | `needs-owner-decision` | - | - |
| 10 | `P19-T2` | T2 | `not-faithful-different` | `no / no` | `010928845658` | `93526540f05f` | [decision](../highambench/tasks/P19/T2/faithfulness/decision.json), [report](../highambench/tasks/P19/T2/faithfulness/report.md) | The target admits singular bases, leaves first-order semantics and dimension constants arbitrary, and assumes MGS and Appendix-A conclusions. | Confirmed. Positivity of `sigma_min(VHat)` is missing; the arbitrary static predicates do not give a mathematical meaning to first-order notation; and (A.1) must use `c(n,k)*u_g + epsilon_c`, not one free scalar multiplying both terms. More fundamentally, the selected Theorem 3.1 proof imports the MGS result [11, (5.15)--(5.17)], omits the first two parts of [11, Thm. 3.1], and performs four pages of Appendix-A perturbation analysis. The current `P19MGSSelectionLaw` and `P19StaticAppendixATheory` assume that content instead of deriving it. Repairing only the local defects would leave a conclusion-bearing certificate task. A faithful rebuild therefore requires either T3 reassignment and formalization of the missing cited/Appendix stack, or owner-approved reselection to a narrower exact result that does not overlap P19-T1/T3. | `needs-owner-decision` | - | - |
| 11 | `P19-T3` | T3 | `not-faithful-different` | `no / no` | `2adfcd920235` | `951ad8781d52` | [decision](../highambench/tasks/P19/T3/faithfulness/decision.json), [report](../highambench/tasks/P19/T3/faithfulness/report.md) | Appendix bounds are premises, the two uses of `u_g` are disconnected, constants and first-order semantics are uncontrolled, and singular bases can pass the encoded condition. | Confirmed from Theorems 3.3--3.4 and Appendices C--D. The same `u_g` must govern MGS selection, condition (3.16), and the final envelopes; `c(n,k)` must remain a low-degree polynomial factor; `sigma_min(VHat)` must be positive; and the static qualitative predicates are not adequate first-order semantics. More importantly, Appendices C--D derive (C.1)--(C.15), (D.1)--(D.2), the Algorithm-2 parameter identifications, and applicability of Theorem 3.1, while the target supplies their propagated consequences as structures. A faithful repair depends on first resolving P19-T2 and then formalizing these Appendix applications, or on owner-approved reselection/tier redesign. The exact Remark-4 envelope identity is valid only as an algebraic supplement and does not repair the two theorem claims. | `needs-owner-decision` | - | - |
| 12 | `P20-T3` | T3 | `not-faithful-weaker` | `no / yes` | `e826151e14e4` | `dcc89a9a1a76` | [decision](../highambench/tasks/P20/T3/faithfulness/decision.json), [report](../highambench/tasks/P20/T3/faithfulness/report.md) | The substantive Section 4 derivation is assumed, first-order semantics are unconstrained, and the second bound regroups equation (4.32) instead of representing equation (4.33). | Confirmed from printed pages B793--B795. The paper itself derives the word-decomposition identities and bounds (4.8)--(4.26), then combines the range-free accumulation estimate imported from [7, Thm. 2.1] with its own underflow analysis to obtain (4.27)--(4.32). `P20StaticSection4Derivation` instead asks the caller to supply all of those local decompositions and estimates, and `P20FirstOrderSemantics` does not require asymptotic smallness. Equation (4.33) is a distinct external range-unrestricted result, not a second bound for the narrow-range run; the current second conjunct merely reassociates (4.32). A faithful repair therefore requires either formalizing the complete Section 4 derivation with a narrowly scoped interface for the imported Fasi estimate, or owner-approved reselection/scope reduction. | `needs-owner-decision` | - | - |

## End-of-pass checkpoint

Do not refresh the complete benchmark snapshot while this ledger is active.
After all 12 tasks have final dispositions and no Builder or Auditor is writing
task files, follow `WORKFLOW.md` to reconcile semantic metadata, regenerate the
deferred hashes once, validate the construction snapshot, and commit generated
metadata separately. Only then can the corpus move toward measurement-ready
status.
