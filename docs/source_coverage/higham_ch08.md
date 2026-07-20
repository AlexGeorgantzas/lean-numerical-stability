# Higham Chapter 8 Formalization Report — "Triangular Systems"

> **Fresh strict audit (2026-07-19, corrected): gate PASS; the remaining
> asymptotic compression is policy-deferred.**
> The audit re-read the chapter PDF and rebuilt the dependency
> path from the literal `fl_matMul`/`fl_matVec` fan-in executor.  Equations
> (8.14)--(8.20) are now connected by exact all-orders theorems: the seven
> rounded operations have forward coefficient `((1 + gamma_n)^7 - 1)`, that
> envelope transfers to the residual, to a constructed rank-one backward
> perturbation, and through `|L^{-1}|` to a forward bound.  No relative bound
> on a cancellation-prone intermediate product is assumed.
>
> The formerly missing exact source objects are now constructed:
> `higham8_13_lowerColumnInverseFactor` is proved to be the two-sided inverse
> `M_k=L_k^{-1}`, its reverse product is a two-sided inverse of `L`, the
> balanced seven-factor fan-in application is proved to solve `Lx=b`, and
> `higham8_18_fanIn7AbsMatrix_eq_comparisonInverse` proves the source identity
> `|M_7|...|M_1|=M(L)^{-1}`.
>
> The previous audit incorrectly proposed reducing the executor's *global raw*
> first-order majorant directly to the five-factor cube. That reduction is not
> in Higham and is false: the exact order-seven certificate
> `higham8_15_raw_inverse_factor_envelope_not_le_source_cube` has raw entry
> `32` and five-factor entry `24`, using the literal inverse column factors and
> genuine `L^{-1}`. Higham instead expands the local perturbations before
> discarding their cross terms into `O(u^2)`.
>
> The scalar asymptotic bookkeeping for the exact all-orders substitute is
> explicit: `higham8_18_fanIn7CoefficientRemainder` splits
> `((1+gamma_n)^7-1)` exactly into `7 n u` plus a named nonnegative
> quadratic-and-higher remainder, and the split is propagated to the actual
> residual.  The module also proves a concrete 2-by-2
> cancellation witness showing why the older relative-factor bridge cannot
> supply the source's local expansion by division through an exact intermediate
> product.
> The source does not specify `d_n` or the hidden `O(u²)` constant/family, so
> that local first-order compression is
> **DEFER–MISSING-PRECISE-STATEMENT** under the audit policy, with the literal
> all-orders executor theorem recorded as its exact substitute. No other
> missing chapter bridge was found.
> See `AUDIT_ch01-28_2026-07-18.md`.

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 8, "Triangular Systems" (printed pp. 139–154).
- Source file: `higham-split/sources/chapter-pdfs/1.9780898718027.ch8.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7–12).
- Fresh selected-scope gate: **PASS**. The exact inverse-factor/product/solve
  bridge is closed. The unparameterized `d_n/O(u²)` local first-order clause is
  **DEFER–MISSING-PRECISE-STATEMENT**, with an exact all-orders substitute.
  All named primary labels remain closed. The older 2026-07-11 PASS
  certification predated literal-producer/source-bridge checking and is
  superseded by this strict audit.  A separate **policy flag on
  benchmark-reserved Problems** remains recorded below.

Primary Lean module: `NumStability/Algorithms/HighamChapter8.lean`
(7.4k lines); proofs in the focused modules TriangularSolve, ForwardSub,
TriangularSolveCombined, TriangularForwardBound, InverseBounds,
TriangularForwardComparison, TriangularArbitraryOrder, TriangularNoGuard,
MMatrix.

## Primary labels (14) — all CLOSED
| Source label | Lean declaration(s) | Notes |
|---|---|---|
| Algorithm 8.1 (back substitution) | `higham8_1_backSub` | wraps `fl_backSub` |
| Lemma 8.2 | `higham8_2_backSub_row_spec`, `higham8_2_backSub_row_tight` | |
| Theorem 8.3 | `higham8_3_backSub_backward_error` | |
| Lemma 8.4 (order-independent) | `higham8_4_anyOrder_backwardError` | |
| Theorem 8.5 | `higham8_5_backSub_backward_error` (+`_anyOrder`, forwardSub variants) | 4 specializations |
| Lemma 8.6 | `higham8_6_inv_abs_mul_bound_diagDom` | |
| Theorem 8.7 | `higham8_7_backSub_forward_error_diagDom` | |
| Lemma 8.8 | `higham8_8_rowDiagDominantUpper_condSkeel_bound` | condSkeel ≤ 2n−1 |
| Lemma 8.9 | `higham8_9_condAtSolution_le_comparisonMatrix` (+ eq/specialization cluster) | |
| Theorem 8.10 | `higham8_10_forwardSub_forward_error_mu_bound` | exact μ recurrence |
| Corollary 8.11 (M-matrix) | `higham8_11_mmatrix_forwardSub_relative_error` | |
| Theorem 8.12 | `higham8_12_abs_inv_le_comparison_inv` + `higham8_12_{infNorm,oneNorm,opNorm2,absolute_norm_vector}_chain`, `higham8_12_comparisonInv_le_WInv`, `higham8_12_WInv_le_ZInvFormula` | |
| Algorithm 8.13 | `higham8_13_inverse_bound_from_comparison` + `higham8_13_mu`/`_y`/recurrence | |
| Theorem 8.14 | `higham8_14_full_norm_chain` + six upper/lower bound pieces | |

## Equations (8.1)–(8.20)
All 20 have Lean surfaces under the `higham8_N_*` convention.  The fresh
producer/bridge audit gives the following finer status for the fan-in chain:

| Source row | Fresh status | Literal bridge / evidence |
|---|---|---|
| (8.1)--(8.13) | **CLOSED** | Existing chapter surfaces; (8.12)--(8.13) now include the exact lower-column product, literal two-sided inverse factors `M_k=L_k^{-1}`, their reverse-product inverse, the fan-in parenthesization, and an exact fan-in solve producer. |
| (8.14) | **CLOSED** | `higham8_14_fanIn7Executor`, `higham8_14_fanIn7Executor_eq_roundedApply`; all five displayed perturbations are produced by the literal rounded tree with local envelopes. |
| (8.15) | **DEFER–MISSING-PRECISE-STATEMENT at printed asymptotic form; exact substitute CLOSED** | `higham8_15_fanIn7Executor_residual_componentwise_bound` proves the actual all-orders raw residual envelope and `_first_order_remainder_bound` gives an exact `7 n u` split with named nonnegative remainder. The exact inverse-column identities are closed. Higham leaves `d_n` and `O(u²)` unparameterized and reaches the cube by a local perturbation expansion, not by the formally refuted global-raw reduction. |
| (8.16) | **CLOSED exact substitute / printed asymptotic deferred** | `higham8_16_fanIn7Executor_residual_infNorm_bound`; the exact scalar first-order/remainder split is available from (8.15). |
| (8.17) | **CLOSED** | `higham8_17_fanIn7Executor_backward_error_bound` constructs the backward perturbation from the literal residual bound. |
| (8.18) | **CLOSED** | `higham8_18_fanIn7Executor_forward_componentwise_bound` proves `|xhat-x| <= ((1+gamma_n)^7-1)|M7|...|M1||b|`, retaining all higher-order terms. |
| (8.19) | **CLOSED** | `higham8_19_fanIn7Executor_forward_relative_infNorm_bound`. |
| (8.20) | **CLOSED exact transfer / printed asymptotic deferred** | `higham8_20_fanIn7Executor_forward_from_residual_componentwise_bound` and `_relative_infNorm_bound` connect the actual residual through `|L^{-1}|`; `higham8_20_condition_cubing_*` proves the exact five-factor-to-condition-cube transfer. The unparameterized `d_n/O(u²)` producer form inherited from (8.15) is policy-deferred. |

The sharp obstruction to reusing the older relative-intermediate-product
route is formalized by
`higham8_14_local_envelope_not_relative_after_cancellation`: its exact product
entry is zero, its product-of-absolute-matrices entry is two, and a nonzero
local perturbation obeys the latter envelope while obeying no scalar relative
bound by the former.  This does not refute Higham's asymptotic argument; it
pinpoints the missing formal object, namely the first-order expansion that
places cross terms in an explicit second-order remainder.  The stronger
order-seven certificate in `HighamChapter8FanInClosure` additionally proves
that the formerly proposed global-raw reduction is false (`32 > 24`); this
corrects the audit plan and does not contradict Higham's local expansion.

## Naming caveat (informational)
The `higham8_N_` prefix is overloaded across item kinds sharing the number N
(Lemma 8.2 vs eq (8.2) vs Problem 8.2, etc.); only docstrings disambiguate.
No numeric mismatches found: every `higham8_N_*` docstring cites label N.

## Benchmark-reserved — POLICY FLAG (coordinator decision needed)
Pre-existing declarations formalize several end-of-chapter Problems as genuine
exercise content (not general-fact wrappers):
- explicit prefix: `higham8_problem8_1_*` (4 decls, no-guard variants),
  `higham8_problem8_3_*` (1), `higham8_problem8_9_*` (35, Kahan matrix
  second-smallest singular value);
- bare-prefix (docstring-labeled "Problem 8.N"): Problems 8.2, 8.4, 8.5, 8.6,
  8.7, 8.8 under `higham8_N_*` names.

These predate the split project's benchmark-reserved-exercise ban (the ch8
formalization is one of the oldest in the repo). They are recorded here as
identifiers + locations only. **They are NOT counted toward the chapter's
selected-scope coverage above**, and none of the primary rows depends on
them (spot-checked: the primary-label declarations live in the shared
triangular/M-matrix modules or wrap them directly). Options for the
coordinator: (a) grandfather as pre-existing work, (b) quarantine/rename if
the affected Problems are wanted as clean benchmark items. No unilateral
deletion performed.

## Skipped items (reason codes)
| Source location | Summary | Reason |
|---|---|---|
| §8.4 numerical experiments, Tables 8.1–8.3 | machine outputs | empirical |
| §8.5 Notes and References, LAPACK notes | history/software | non-mathematical |
| epigraphs, motivating prose | quotations | editorial |

## Verification (fresh 2026-07-18 audit)
- Direct `lake env lean NumStability/Algorithms/HighamChapter8.lean`:
  **PASS** after the literal inverse-factor bridge additions.
- Direct
  `lake env lean NumStability/Algorithms/HighamChapter8FanInClosure.lean`:
  **PASS**, including the exact order-seven honesty certificate.
- `lake build NumStability.Algorithms.HighamChapter8`: **PASS**.
- Hygiene: no `sorry`/`admit`/new `axiom` in `HighamChapter8.lean`.
- `#print axioms` on the literal executor, inverse-factor/reverse-product
  producers, coefficient remainder split, actual (8.15)--(8.20) bridge
  theorems, and both honesty witnesses: `[propext, Classical.choice,
  Quot.sound]` only.

## Open selected-scope items
None. The unparameterized `d_n/O(u²)` local first-order compression is
**DEFER–MISSING-PRECISE-STATEMENT** and is not an additional producer
obligation. Its exact all-orders substitute, the inverse-column-factor
identities, and the exact five-factor-to-condition-cube transfer are all
closed. The previously requested global raw-majorant reduction is formally
false and was never a source claim.

The benchmark-reserved Problem formalizations flagged above remain a separate
policy decision, not proof work.
