# Higham Chapter 21 Source Coverage Ledger

## Source and Scope

- Source: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
  2nd ed., Chapter 21, "Underdetermined Systems".
- Local source: `References/1.9780898718027.ch21.pdf`, printed pages 407-414.
- Assigned partition: Chapter 21 ONLY.
- Mode: core.
- Core primary labels: Theorem 21.1, Lemma 21.2, Theorem 21.3, and
  Theorem 21.4.
- Core numbered equations: (21.1)-(21.11).
- Current aggregate status: **PASS** under the strict source-strength audit.
  All 21 selected rows are verified. Theorem 21.4 now has source-facing
  Householder and retained-trace Givens producers that derive computed
  triangular nonbreakdown, and the Givens producer also derives replay
  smallness, from full row rank, gamma validity, and the printed-form smallness
  condition. Both methods in (21.11) and the corrected-MGS recurrence are
  represented; its qualitative stability sentence is classified separately
  below.

Status language in this ledger:

- **VERIFIED**: the corresponding declarations compile through the Chapter 21
  umbrella and passed the final source/axiom/hygiene audit.
- **PRESENT**: the numbered source identity or construction is represented by
  compiled declarations; no stronger analytic status is implied.
- **EXCLUDED**: an intentional empirical, editorial, qualitative, or optional
  source row outside the selected core proof obligations.

## Primary Contracts

| Source label | Status | Lean coverage | Exact scope notes |
| --- | --- | --- | --- |
| Theorem 21.1 | **VERIFIED** | `higham21_theorem21_1_relative_asymptotic_bound_of_gram_det_ne_zero`, `higham21_theorem21_1_finite_error_relative_bound`, and the first-order majorant theorems in `Higham21Perturbation.lean`; rank preservation in `Higham21RankStability.lean`; Holder attainability in `Higham21Attainability.lean` | The arbitrary absolute-norm coefficient in (21.6) is represented, and the remainder is proved `O(t^2)` through an explicit fixed-radius bound on perturbed Gram inverses. The caller-facing finite theorem derives perturbed full row rank from `||Aplus DeltaA||_2 < 1`. The local inverse bound used to make the quadratic constant finite is explicit rather than hidden in big-O notation. |
| Lemma 21.2 | **VERIFIED** | `undetLemma21_2SinglePerturbation`, `higham21_lemma21_2_rowwise_backward_error_bound_of_pseudoinverse_products`, `higham21_lemma21_2_single_perturbation_frob_bound`, and `higham21_lemma21_2_single_perturbation_op_bound` | Covers the two perturbed equations, the printed `3 * max` pseudoinverse-product smallness condition, the zero/nonzero construction of one perturbation, minimum-norm recovery, and the printed `p = 2, F` square-sum norm bounds. Row-wise bounds used by Theorem 21.4 are also present. |
| Theorem 21.3 | **VERIFIED (documented source correction)** | `higham21_theorem21_3_nonzero_normwise_backward_error_formula`, `higham21_theorem21_3_normwise_backward_error_formula`, and `Higham21Theorem21_3Attainment.lean` | The printed unconditional `min` is not valid in the zero-system boundary case. Lean proves the mathematically correct Sun-Sun infimum formula, including `eta_F(0) = theta ||b||_2`, the nonzero branch with `sigma_m(A(I-yy+))`, the lower bound for every feasible perturbation, and an epsilon-attaining upper construction. Exact attainment is proved under the sharp nonzero-pairing condition, and closure attainment is unconditional. A verified scalar example witnesses nonattainment. |
| Theorem 21.4 | **VERIFIED** | `Higham21QMethodFullRowRankComputedQRDomain.of_source_smallness`, `higham21_theorem21_4_computed_qhat_rowwise_backward_stable_source`, `Higham21GivensActualReplayEtaQ_lt_one_of_operational_gammaValid`, `higham21_givens_actual_topBlock_nonbreakdown_of_source_smallness`, and `higham21_theorem21_4_givens_actual_rounded_rowwise_backward_stable_source` in `Higham21Theorem214SourceClosure.lean` | For Householder QR, the source wrapper combines the Chapter 19 rowwise QR perturbation with the Chapter 21 right inverse and rank-stability bridge to prove the computed top block nonsingular, then supplies the formerly hidden `lsTheorem20_4ComputedQRNonbreakdown` field. For retained-trace Givens QR, one operational gamma-validity index supplies the local kernels and solve, bounds the complete replay recurrence below one, and the same perturbation/rank argument derives every top diagonal entry nonzero. Thus neither `hdiag` nor `hQsmall` remains a caller-supplied execution conclusion. |

## Equation Ledger

| Equation | Status | Formalized content |
| --- | --- | --- |
| (21.1) | **PRESENT** | `higham21_eq21_1_qr_transpose_block_mulVec` and `higham21_qr_transpose_system_eq` formalize the `[R;0]` block algebra under a supplied orthogonal QR certificate. QR existence and rounding are imported from Chapter 19 interfaces. |
| (21.2) | **PRESENT** | `higham21_eq21_2_qr_block_transpose_coordinates` proves `[R^T 0][y1;y2] = R^T y1`, with the full `A x = b` coordinate handoff in `higham21_qr_transpose_system_eq`. |
| (21.3) | **PRESENT** | The `higham21_eq21_3_*` family proves the zero-free-coordinate minimum-norm choice and the exact Q-method solution, with inverse, determinant, and nonzero triangular-diagonal entry points. |
| (21.4) | **PRESENT** | The `higham21_eq21_4_*` declarations in `UnderdeterminedSpec.lean` prove the transpose-form minimum-norm characterization, `Aplus = A^T (A A^T)^-1`, right-inverse and Moore-Penrose properties, and the determinant-facing formula. |
| (21.5) | **PRESENT** | `higham21_eq21_5_qr_sne_gram_eq` identifies `A A^T = R^T R`; the associated solve and minimum-norm handoffs formalize the exact SNE algebra. |
| (21.6) | **VERIFIED** | `Higham21Perturbation.lean` gives the exact arbitrary absolute-norm first-order coefficient, a finite `|t|^2` remainder coefficient, and an `O(t^2)` relative form. The fixed-radius inverse envelope is an explicit hypothesis. |
| (21.7) | **VERIFIED** | `higham21Eq21_7_exact_expansion` and its determinant wrapper prove the exact one-parameter first-order expansion. `higham21Eq21_7_exactRemainder_vecNorm2_isBigO` and the absolute-norm counterpart prove the quadratic remainder. The two printed first-order source vectors are also proved orthogonal. |
| (21.8) | **VERIFIED** | `Higham21Eq21_8.lean` proves the exact coefficient `min {3, n-m+2} * max {||H||_2, 1} * cond2(A)`, including the square/strict-underdetermined split and an explicit fixed-radius quadratic remainder. |
| (21.9) | **VERIFIED** | `Higham21Eq21_9.lean` proves the printed coefficient `min {3, n-m+2} * sqrt(m*n) * kappa2(A)`, first for the exact first-order vector and then with an explicit fixed-radius quadratic remainder. |
| (21.10) | **PRESENT** | The `higham21_eq21_10_*` family converts the computed `Q_hat = Q + DeltaQ` accumulation certificate and Frobenius bound into the exact formed-vector action bound. Householder-panel, closed-form, and gamma-coefficient wrappers are present; `higham21_givens_actual_rounded_action_error` supplies the actual retained-trace Givens action theorem. |
| (21.11), Q method | **VERIFIED** | `higham21_eq21_11_computed_qhat_relative_forward_error_quadratic` composes the actual Theorem 21.4 output with (21.7). For `n = m+k` it proves `||x_hat-x||_2/||x||_2 <= n * eta * cond2(A) + eta^2*C/||x||_2`, with an explicit normalized perturbation direction, rank-stable perturbed Gram matrix, and finite quadratic coefficient. `higham21_eq21_11_computed_qhat_relative_forward_error_quadratic_scalar` in `Higham21Equation21_11Scalar.lean` closes the remaining square scalar case (`m+k <= 1`), complementing the uniform dimension-at-least-two theorem. |
| (21.11), SNE paragraph | **VERIFIED** | `higham21_sne_householder_actual_output_source_relative_q_uniform` proves the fixed-radius relative bound for the actual Householder panel, two rounded triangular solves, and rounded `A^T y_hat` formation, comparing the actual `xhat` with canonical `x = Aplus*b` and retaining the original `cond2(A)` first-order coefficient. `higham21_sne_householder_actual_output_source_relative_unit_roundoff_sq` converts the uniform quadratic remainder to `fp.u^2 * higham21SNEQUniformUnitRoundoffSecondOrderCoefficient A b tau`; this coefficient depends only on `A`, `b`, the dimensions, and `tau`, not on the active QR direction, nearby factors, or rounded normal solution. No SNE backward-stability or general residual theorem is claimed. |

## Source Prose Obligations

### Rank Stability

**VERIFIED.**
`higham21_theorem21_1_perturbed_transpose_injective_of_right_inverse` proves
that `A + DeltaA` has full row rank from a right inverse for `A` and
`||Aplus DeltaA||_2 <= c < 1`. The determinant-facing wrappers supply the
perturbed Gram nonsingularity used by Theorem 21.1 and equation (21.11).

### Holder Attainability

**VERIFIED.**
`higham21_theorem21_1_holder_firstOrder_upper_and_attainment` proves the
first-order Holder `p`-norm upper bound for every admissible componentwise
perturbation and constructs sign perturbations attaining it within

`2 * n^(1/p) * n^|1/p - 1/2|`.

This is an explicit dimension-only realization of the source phrase
"within a constant factor depending on n."

### Row Scaling

**VERIFIED.**
`higham21Cond2With_row_scaling` proves
`cond2(D A) = cond2(A)` for a nonsingular diagonal row scaling and the
correspondingly transformed pseudoinverse. The same module proves preservation
of the right-inverse and Moore-Penrose certificates.

### Q Method and SNE

- The actual rounded Q-method output has a Theorem 21.4 row-wise backward
  stability certificate for both Householder and retained-trace Givens QR.
  `Higham21QMethodFullRowRankComputedQRDomain.of_source_smallness` derives the
  complete Householder domain, and
  `higham21_theorem21_4_givens_actual_rounded_rowwise_backward_stable_source`
  derives the Givens nonbreakdown and replay-smallness guards rather than
  accepting them from the caller.
  Equation (21.11) is closed by the dimension-at-least-two theorem together
  with the square scalar theorem in `Higham21Equation21_11Scalar.lean`.
- The SNE analysis reaches the actual two-triangular-solve normal vector and
  final rounded `A^T y_hat` output. The theorem
  `higham21_sne_householder_actual_output_source_relative_q_uniform` closes the
  relative forward bound against the canonical solution with the original
  `cond2(A)` in the first-order term and a fixed-radius quadratic coefficient.
  Its corollary
  `higham21_sne_householder_actual_output_source_relative_unit_roundoff_sq`
  makes the remainder explicitly proportional to `fp.u^2`, with a coefficient
  depending only on `A`, `b`, the dimensions, and `tau`.
- In that endpoint, `hm`, `hn`, `hdet`, and `hb` are source/domain assumptions;
  `hvalidQR` and `hmGamma` are `gammaValid` floating-point validity premises;
  `hdiag` is triangular nonbreakdown; and `hrho_pos` asserts positivity of the
  Householder perturbation scale. The uniform neighborhood requires
  `gamma_m + rho ≤ tau < 1`, Gram contraction below one, and
  `tau * higham21SNEQUniformSolveMultiplier A tau ≤ 1/2`. The explicit
  `fp.u²` corollary adds the half-radius bounds for `m * fp.u` and the
  Householder QR index times `fp.u`.
- The source statement that SNE has no analogue of Theorem 21.4 and no general
  small residual guarantee is respected by absence of such a theorem. The
  negative impossibility claim itself is not formalized.

### Corrected MGS solver

**RECURRENCE VERIFIED; STABILITY PROSE `SKIP-QUALITATIVE`.** The reverse
corrected recurrence is precise and is formalized in `Higham21MGS.lean` and
`Higham21MGSRounded.lean`, including its exact repair algebra and rounded local
operations. The source says only that the algorithm satisfies "essentially"
Theorem 21.4, without an exact coefficient or theorem surface. Under the core
selection policy this does not define a selected theorem. The conditional
row-scaled handoffs in `Higham21MGSRounded.lean` are retained as non-core
extension work and are not counted as end-to-end source stability.

### Givens variants

**VERIFIED CORE BRANCH.** Higham's Theorem 21.4 discussion permits Householder
or Givens QR. `Higham21GivensClosure.lean` reconstructs the source-bearing
rotation trace from the staged QR tasks, uses the same exact rotation product
for the QR certificate and actual rounded transpose replay, proves the
equation-(21.10) action estimate, and derives both the row-wise theorem and its
`omegaR` bound. No supplied replay/application certificate or target-equivalence
bridge is used. `Higham21Theorem214SourceClosure.lean` closes the remaining
source bridge: `Higham21GivensActualReplayEtaQ_lt_one_of_operational_gammaValid`
bounds the actual replay recurrence below one, while
`higham21_givens_actual_topBlock_nonbreakdown_of_source_smallness` derives the
computed diagonal nonbreakdown from full row rank and the QR perturbation
smallness. The source-facing row-wise endpoint consumes both derived facts.

## Module Map

- `UnderdeterminedSpec.lean`: minimum-norm specification and equation (21.4).
- `UnderdeterminedSolve.lean`: equations (21.1)-(21.5), equation (21.7),
  Lemma 21.2, Theorems 21.3-21.4, and equation (21.10).
- `Higham21QRFoundations.lean`: full-row-rank QR consequences for
  equations (21.1)-(21.4).
- `Higham21RankStability.lean`: Theorem 21.1 rank preservation.
- `Higham21Perturbation.lean`: Theorem 21.1 and equation (21.6).
- `Higham21PerturbationRadius.lean`: concrete fixed-radius inverse and
  remainder certificates for Theorem 21.1.
- `Higham21Attainability.lean`: Holder first-order upper and lower witnesses.
- `Higham21Theorem21_3Attainment.lean`: exact/closure attainment and the
  scalar nonattainment witness for Theorem 21.3.
- `Higham21Condition.lean`: row-scaling invariance of `cond2`.
- `Higham21Eq21_8.lean`: equation (21.8).
- `Higham21Eq21_9.lean`: equation (21.9).
- `Higham21ProjectorNorm.lean`: exact complement-projector norm identities
  used by equations (21.8)-(21.9).
- `Higham21Equation21_11.lean`: Q-method equation (21.11) with explicit
  quadratic remainder.
- `Higham21Eq21_11Uniform.lean`: uniform fixed-radius refinement of the
  Q-method equation (21.11).
- `Higham21Equation21_11Scalar.lean`: square scalar closure for the Q-method
  equation (21.11), covering the remaining `m+k <= 1` boundary.
- `Higham21SNEForward.lean` and `Higham21SNEActualOutput.lean`: rounded SNE
  solve envelopes and the actual two-solve/final-formation output.
- `Higham21SNEEnvelopeTransfer.lean`: retained aggregate compatibility
  interface; it is not the evidence used for the final source-facing endpoint.
- `Higham21SNESigned.lean`: cancellation-preserving signed SNE identities and
  quantitative Demmel--Higham factor bounds.
- `Higham21SNEConditionTransfer.lean`: honest fixed-radius pseudoinverse,
  dual-solution, condition-number, and solution-norm transfers.
- `Higham21SNEQRMajorant.lean`: componentwise QR-action majorants that retain
  the source cancellation structure.
- `Higham21SNERemainderBounds.lean`: explicit factor-difference, signed
  remainder, source-action, QR-action, and formation quadratic estimates.
- `Higham21SNEClosure.lean`: concrete Householder SNE instantiation and final
  active-computation relative forward endpoint for equation (21.11).
- `Higham21SNEUniform.lean`: source-defined fixed-radius majorants for the
  active QR factors, rounded normal solution, and signed remainder; final
  relative `theta²` theorem and explicit `fp.u²` source-facing corollary.
- `Higham21Givens.lean`, `Higham21GivensRounded.lean`, and
  `Higham21GivensClosure.lean`: Givens Q-method construction, rounded replay,
  actual retained-trace action estimate, Theorem 21.4, and `omegaR` closure.
- `Higham21Theorem214SourceClosure.lean`: source-level Householder/Givens
  Theorem 21.4 producers, including derived top-block nonbreakdown and actual
  retained-trace replay smallness.
- `Higham21MGS.lean` and `Higham21MGSRounded.lean`: the stable corrected
  MGS recurrence and its rounded transfer interfaces.
- `Higham21RowwiseMeasure.lean`: the printed row-wise backward-error measure.
- `Higham21.lean`: Chapter 21 umbrella module importing the complete module
  set above.

## Honest Scope Exclusions

- The Householder and Givens branches of Theorem 21.4 are selected verified
  rows, not exclusions. Their source-facing producers derive the operational
  nonbreakdown/replay guards; the square scalar Q-method case and SNE
  equation-(21.11) endpoint are likewise selected verified rows.
- The qualitative warning that SNE has no Theorem-21.4 analogue and no general
  small-residual guarantee is `SKIP-QUALITATIVE`. Consistently, no stronger SNE
  backward-stability or residual theorem is claimed.
- The statement that corrected reverse MGS has "essentially" Theorem-21.4
  stability is `SKIP-QUALITATIVE`: no exact coefficient or theorem surface is
  printed. The corrected recurrence itself is verified.
- The Section 21.3 Vandermonde experiment is `SKIP-EMPIRICAL`: the printed
  `cond2(A) = 7.6e12`, `||Qhat^T Qhat-I||2 = 9e-3`, and Table 21.1 backward
  errors (`1.6e-17`, `1.8e-3`, `3.4e-17`, `4.7e-14`) depend on an unspecified
  historical execution environment. The symbolic algorithms and stability
  claims are inventoried separately; reproducing these outputs is not a core
  proof obligation.
- Section 21.4.1 LAPACK routine descriptions are documentation, not selected
  proof obligations.
- Problem 21.1 and its Appendix A solution are
  `OPTIONAL-PROBLEM-NOT-SELECTED`. They characterize the block system (21.12)
  as the optimality conditions for the generalized least-squares objective
  (21.13) and constrained minimum-distance problem (21.14). They are useful
  future benchmark targets but do not block the Chapter 21 core gate.

## Current Verification Ledger

- Focused compile of `Higham21SNEUniform.lean`, including the fixed-radius
  relative endpoint and explicit `fp.u²` corollary: **PASS**.
- Compile `Higham21GivensClosure.lean` and its actual retained-trace action,
  row-wise, and `omegaR` theorems through the umbrella: **PASS**.
- Focused build of `Higham21Theorem214SourceClosure.lean`, including the
  Householder and Givens source producers and their derived guards:
  **PASS** (3,084 jobs).
- Compile `Higham21Equation21_11Scalar.lean`,
  `Higham21SNEConditionTransfer.lean`, `Higham21SNEQRMajorant.lean`, and
  `Higham21SNERemainderBounds.lean` through the umbrella: **PASS**.
- Scan the new Chapter 21 modules, including `Higham21SNEUniform.lean`, for
  `sorry`, `admit`, new axioms, unsafe shortcuts, and opaque placeholders:
  **PASS**.
- Build the Chapter 21 umbrella: **PASS** (3,108 jobs).
- Build `LeanFpAnalysis.FP.Algorithms`: **PASS** (3,848 jobs).
- Build the full repository: **PASS** (3,901 jobs). Replayed warnings are
  inherited from pre-existing modules; the new Chapter 21 modules are clean.
- `#print axioms` for
  `higham21_sne_householder_actual_output_source_relative_unit_roundoff_sq`:
  **PASS**, with only `[propext, Classical.choice, Quot.sound]`.
- The Chapter 21 selected-scope gate is **PASS**: all 21 selected rows are
  source-closed, with six intentional exclusions recorded separately.
