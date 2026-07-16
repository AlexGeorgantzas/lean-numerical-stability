import LeanFpAnalysis.FP.Algorithms.LeastSquares.Higham20Theorem20_7QdR
import LeanFpAnalysis.FP.Algorithms.QR.Higham19Thm6RowSpecific

namespace LeanFpAnalysis.FP

open scoped BigOperators

namespace Theorem20_7

/-!
# Theorem 20.7 assembly at the Split 3B numerical contract

The least-squares part of Theorem 20.7 needs only three numerical facts from
the Cox--Higham column-pivoted QR analysis (Split 3B): a rowwise estimate for
the concrete accumulated matrix residual, the corresponding estimate for the
concrete right-hand-side residual, and a rowwise estimate for transporting an
admissible triangular back-substitution perturbation through the concrete
accumulated orthogonal factor.

The contract below states exactly those facts for the literal traces.  It has
no least-squares minimizer, returned solution, or final backward-error
conclusion as an input.  In particular it does not mention the refuted strict
rounded-trace pivot-scale history or `PivotedStoredQRRawReady`.
-/

/-- Pure numerical interface exported by the Split 3B Cox--Higham QR
analysis.

The matrix residual is kept in pivot-position coordinates, where its sharp
`(j+1)^2` factor is meaningful.  The RHS and triangular-transport bounds use
the permutation-independent `n^2` envelope needed by the source-facing
least-squares statement. -/
structure PivotedStoredQRSplit3BNumericalContract (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (alpha betaScale : Fin m → ℝ)
    (qrCoeff rhsCoeff backSubCoeff : ℝ) : Prop where
  alpha_nonneg : ∀ i, 0 ≤ alpha i
  betaScale_nonneg : ∀ i, 0 ≤ betaScale i
  qrCoeff_nonneg : 0 ≤ qrCoeff
  rhsCoeff_nonneg : 0 ≤ rhsCoeff
  backSubCoeff_nonneg : 0 ≤ backSubCoeff
  qr_accumulated_pivot_row : ∀ i j,
    |pivotDAacc (pivotedStoredQRPseq fp hmn A)
        (pivotedStoredQRSwapSeq fp hmn A)
        (pivotedStoredQREseq fp hmn A) n i j| ≤
      ((j.val : ℝ) + 1) ^ 2 * qrCoeff * alpha i
  rhs_accumulated_source_row : ∀ i,
    |pivotedStoredQRRhsDelta fp hmn A b i| ≤
      (n : ℝ) ^ 2 * rhsCoeff * betaScale i
  backSub_transport_source_row :
    ∀ dR : Fin n → Fin n → ℝ,
      (∀ i j,
        |dR i j| ≤ gamma fp n * |pivotedStoredQRTopR fp hmn A i j|) →
      ∀ i j,
        |matMulRect m m n
            (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
            (rectTopBlock (m := m) dR) i
            ((pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n).symm j)| ≤
          (n : ℝ) ^ 2 * backSubCoeff * alpha i

/-! ## Concrete Cox--Higham producer data

The following definitions are the literal finite-trace versions of the three
scales printed in Higham, Theorem 20.7.  They depend only on the source data and
the forward rounded matrix/RHS traces; none mentions a backward perturbation.
-/

/-- Printed numerator `max_{j,k} |aᵢⱼ^(k)|`, represented as the maximum row
infinity norm over the `n+1` recorded states of the literal pivoted trace. -/
noncomputable def pivotedStoredQRPrintedAlphaScale (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  Wave18D.rowInftyGrowthFactor (fl_pivotedStoredQRMatrixSeq fp hmn A) n i

/-- Dimensionless printed row-growth ratio `alpha_i`.  The producer and the
contract use its numerator directly, avoiding a spurious division-by-zero side
condition when an initial source row is zero. -/
noncomputable def pivotedStoredQRPrintedAlpha (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  pivotedStoredQRPrintedAlphaScale fp hmn A i /
    Wave18D.rowInftyNorm A i

/-- Printed RHS history numerator `max_k |b_i^(k)|`. -/
noncomputable def pivotedStoredQRRhsRowGrowthScale (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (i : Fin m) : ℝ :=
  ⨆ t : Fin (n + 1), |fl_pivotedStoredQRRhsSeq fp hmn A b t.val i|

/-- Higham's printed
`phi = max_k ‖b^(k)(k:m)‖₂ / ‖a_k^(k)(k:m)‖₂` for the literal common-reflector
trace.  The denominator is the named executed pivot scale. -/
noncomputable def pivotedStoredQRPrintedPhi (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : ℝ :=
  ⨆ k : Fin n,
    vecNorm2
        (householderTrailingPart m (pivotedQRActiveRow hmn k.val k.isLt)
          (fl_pivotedStoredQRRhsSeq fp hmn A b k.val)) /
      |pivotedStoredQRSigma fp hmn A k.val|

/-- Printed beta numerator
`max(phi * max_{j,k}|a_ij^(k)|, max_k |b_i^(k)|)`. -/
noncomputable def pivotedStoredQRPrintedBetaScale (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (i : Fin m) : ℝ :=
  max
    (pivotedStoredQRPrintedPhi fp hmn A b *
      pivotedStoredQRPrintedAlphaScale fp hmn A i)
    (pivotedStoredQRRhsRowGrowthScale fp hmn A b i)

/-- Dimensionless printed `beta_i`. -/
noncomputable def pivotedStoredQRPrintedBeta (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (i : Fin m) : ℝ :=
  pivotedStoredQRPrintedBetaScale fp hmn A b i /
    max
      (pivotedStoredQRPrintedPhi fp hmn A b * Wave18D.rowInftyNorm A i)
      |b i|

theorem pivotedStoredQRPrintedAlphaScale_nonneg
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    0 ≤ pivotedStoredQRPrintedAlphaScale fp hmn A i := by
  let j0 : Fin n := ⟨0, hn⟩
  exact Wave18D.rowInftyGrowthFactor_nonneg
    (fl_pivotedStoredQRMatrixSeq fp hmn A) n i j0

/-- The final leading factor already satisfies the literal printed-alpha row
bound: its entries are entries of the last state included in the defining
finite trace maximum.  Thus this part of the Cox--Higham row policy is data,
not an additional numerical hypothesis. -/
theorem pivotedStoredQRTopR_abs_le_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (i j : Fin n) :
    |pivotedStoredQRTopR fp hmn A i j| ≤
      pivotedStoredQRPrintedAlphaScale fp hmn A
        ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ := by
  exact Wave18D.abs_entry_le_rowInftyGrowthFactor
    (fl_pivotedStoredQRMatrixSeq fp hmn A) n
    ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ n le_rfl j

theorem pivotedStoredQRRhsRowGrowthScale_nonneg
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (i : Fin m) :
    0 ≤ pivotedStoredQRRhsRowGrowthScale fp hmn A b i := by
  have h0 : 0 ≤ |fl_pivotedStoredQRRhsSeq fp hmn A b 0 i| := abs_nonneg _
  exact h0.trans (le_ciSup
    (Finite.bddAbove_range
      (fun t : Fin (n + 1) => |fl_pivotedStoredQRRhsSeq fp hmn A b t.val i|))
    (0 : Fin (n + 1)))

theorem pivotedStoredQRPrintedPhi_nonneg
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    0 ≤ pivotedStoredQRPrintedPhi fp hmn A b := by
  let k0 : Fin n := ⟨0, hn⟩
  have h0 : 0 ≤
      vecNorm2
          (householderTrailingPart m (pivotedQRActiveRow hmn k0.val k0.isLt)
            (fl_pivotedStoredQRRhsSeq fp hmn A b k0.val)) /
        |pivotedStoredQRSigma fp hmn A k0.val| :=
    div_nonneg (vecNorm2_nonneg _) (abs_nonneg _)
  exact h0.trans (le_ciSup
    (Finite.bddAbove_range (fun k : Fin n =>
      vecNorm2
          (householderTrailingPart m (pivotedQRActiveRow hmn k.val k.isLt)
            (fl_pivotedStoredQRRhsSeq fp hmn A b k.val)) /
        |pivotedStoredQRSigma fp hmn A k.val|)) k0)

theorem pivotedStoredQRPrintedBetaScale_nonneg
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (i : Fin m) :
    0 ≤ pivotedStoredQRPrintedBetaScale fp hmn A b i := by
  apply le_max_of_le_right
  exact pivotedStoredQRRhsRowGrowthScale_nonneg fp hmn A b i

/-- Each literal RHS iterate is bounded by the printed RHS-history scale. -/
theorem abs_fl_pivotedStoredQRRhsSeq_le_rowGrowthScale
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (t : ℕ) (ht : t ≤ n) (i : Fin m) :
    |fl_pivotedStoredQRRhsSeq fp hmn A b t i| ≤
      pivotedStoredQRRhsRowGrowthScale fp hmn A b i := by
  have hlt : t < n + 1 := Nat.lt_succ_of_le ht
  exact le_ciSup
    (Finite.bddAbove_range
      (fun q : Fin (n + 1) => |fl_pivotedStoredQRRhsSeq fp hmn A b q.val i|))
    (⟨t, hlt⟩ : Fin (n + 1))

/-- The definition of `phi` supplies the active-tail bound at every nonzero
executed pivot. -/
theorem pivotedStoredQRRhs_tail_le_printedPhi_mul_sigma
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < |pivotedStoredQRSigma fp hmn A k|) :
    vecNorm2
        (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
          (fl_pivotedStoredQRRhsSeq fp hmn A b k)) ≤
      pivotedStoredQRPrintedPhi fp hmn A b *
        |pivotedStoredQRSigma fp hmn A k| := by
  let kf : Fin n := ⟨k, hk⟩
  have hratio :
      vecNorm2
          (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
            (fl_pivotedStoredQRRhsSeq fp hmn A b k)) /
          |pivotedStoredQRSigma fp hmn A k| ≤
        pivotedStoredQRPrintedPhi fp hmn A b := by
    exact le_ciSup
      (Finite.bddAbove_range (fun q : Fin n =>
        vecNorm2
            (householderTrailingPart m
              (pivotedQRActiveRow hmn q.val q.isLt)
              (fl_pivotedStoredQRRhsSeq fp hmn A b q.val)) /
          |pivotedStoredQRSigma fp hmn A q.val|)) kf
  exact (div_le_iff₀ hsigma).mp hratio

/-- Explicit local arithmetic budget for one stored RHS update.  It is the
repository's dot/multiply/subtract component budget, masked to the active tail;
in particular it is not an accumulated RHS perturbation. -/
noncomputable def pivotedStoredQRRhsComponentBudget (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (i : Fin m) : ℝ :=
  if i.val < k then 0
  else householderCompactComponentBudget fp m
    (pivotedStoredQRRawVector fp hmn A k)
    (pivotedStoredQRBeta fp hmn A k)
    (fl_pivotedStoredQRRhsSeq fp hmn A b k) i

/-- The actual RHS stage residual is controlled by the explicit local compact
budget. -/
theorem pivotedStoredQRRhsEseq_abs_le_componentBudget
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m) (k : ℕ) (hk : k < n) (i : Fin m) :
    |pivotedStoredQRRhsEseq fp hmn A b k i| ≤
      pivotedStoredQRRhsComponentBudget fp hmn A b k i := by
  let v := pivotedStoredQRRawVector fp hmn A k
  let beta := pivotedStoredQRBeta fp hmn A k
  let bk := fl_pivotedStoredQRRhsSeq fp hmn A b k
  have hprefix : ∀ r : Fin m, r.val < k →
      matMulVec m (householder m v beta) bk r = bk r := by
    intro r hr
    have hvzero : v r = 0 :=
      pivotedStoredQRRawVector_zero_prefix fp hmn A k hk r hr
    have hform := congrFun (householder_matMulVec_eq m v beta bk) r
    rw [hform, hvzero]
    ring
  have hbound := fl_householderStoredRhsStep_componentwise_error_bound
    fp m k v beta bk hm hprefix i
  rw [pivotedStoredQRRhsEseq,
    fl_pivotedStoredQRRhsSeq_succ_of_lt fp hmn A b k hk]
  simpa [pivotedStoredQRPseq, pivotedStoredQRRhsComponentBudget,
    v, beta, bk] using hbound

/-- Norm form of the explicit RHS component budget. -/
theorem pivotedStoredQRRhsEseq_norm_le_componentBudget
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m) (k : ℕ) (hk : k < n) :
    vecNorm2 (pivotedStoredQRRhsEseq fp hmn A b k) ≤
      vecNorm2 (fun i => pivotedStoredQRRhsComponentBudget fp hmn A b k i) := by
  apply vecNorm2_le_of_abs_le
  intro i
  exact pivotedStoredQRRhsEseq_abs_le_componentBudget
    fp hmn A b hm k hk i

/-- Primitive forward row policy used by the concrete producer.

Its fields are properties of the literal forward trace: nonzero executed
pivots, the raw-reflector row bound of Cox--Higham (2.10), the executed-prefix
row bound behind (2.12), and final `R` row/tail growth used in (3.7)--(3.11).
RHS transport uses a separate mixed alpha/beta component budget below; it does
not pretend that the reflector vector is beta-scaled.  This core policy is
independent of the optional initial-row sorting cap.  No field mentions `pivotDAacc`,
`pivotedStoredQRRhsDelta`, `Q[dR;0]`, or a least-squares result. -/
structure PivotedStoredQRCoxHighamRowPolicy (fp : FPModel) {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) : Prop where
  sigma_pos : ∀ k, k < n → 0 < |pivotedStoredQRSigma fp hmn A k|
  raw_vector_row : ∀ k, k < n → ∀ i,
    |pivotedStoredQRRawVector fp hmn A k i| ≤
      2 * pivotedStoredQRPrintedAlphaScale fp hmn A i
  prefix_vector_row : ∀ k, k < n → ∀ i,
    |Wave19.applyProd
        (fun q => householder m
          (pivotedStoredQRRawVector fp hmn A q)
          (pivotedStoredQRBeta fp hmn A q)) 0 k
        (pivotedStoredQRRawVector fp hmn A k) i| ≤
      (1 + 4 * (k : ℝ)) * 2 *
        pivotedStoredQRPrintedAlphaScale fp hmn A i
  topR_row : ∀ i j,
    |pivotedStoredQRTopR fp hmn A i j| ≤
      pivotedStoredQRPrintedAlphaScale fp hmn A
        ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩
  topR_tail : ∀ k (hk : k < n) (j : Fin n),
    vecNorm2
        (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
          (fun i => rectTopBlock (m := m)
            (pivotedStoredQRTopR fp hmn A) i j)) ≤
      |pivotedStoredQRSigma fp hmn A k|

/-- Build the primitive row policy from its genuinely numerical trace
obligations.  The final-`R` row bound is discharged internally from the
definition of the printed alpha scale. -/
theorem PivotedStoredQRCoxHighamRowPolicy.of_trace_core
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hsigma : ∀ k, k < n → 0 < |pivotedStoredQRSigma fp hmn A k|)
    (hraw : ∀ k, k < n → ∀ i,
      |pivotedStoredQRRawVector fp hmn A k i| ≤
        2 * pivotedStoredQRPrintedAlphaScale fp hmn A i)
    (hprefix : ∀ k, k < n → ∀ i,
      |Wave19.applyProd
          (fun q => householder m
            (pivotedStoredQRRawVector fp hmn A q)
            (pivotedStoredQRBeta fp hmn A q)) 0 k
          (pivotedStoredQRRawVector fp hmn A k) i| ≤
        (1 + 4 * (k : ℝ)) * 2 *
          pivotedStoredQRPrintedAlphaScale fp hmn A i)
    (htail : ∀ k (hk : k < n) (j : Fin n),
      vecNorm2
          (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
            (fun i => rectTopBlock (m := m)
              (pivotedStoredQRTopR fp hmn A) i j)) ≤
        |pivotedStoredQRSigma fp hmn A k|) :
    PivotedStoredQRCoxHighamRowPolicy fp hn hmn A where
  sigma_pos := hsigma
  raw_vector_row := hraw
  prefix_vector_row := hprefix
  topR_row := pivotedStoredQRTopR_abs_le_printedAlphaScale fp hmn A
  topR_tail := htail

/-- Optional source-row caps supplied by a common row-sorting/growth policy.
They convert the exact printed forward numerators into the initial-data form;
they are not needed for the literal-trace numerical contract itself. -/
structure PivotedStoredQRCoxHighamRowSortingCaps (fp : FPModel) {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (rowSortCoeff : ℝ) : Prop where
  rowSortCoeff_nonneg : 0 ≤ rowSortCoeff
  alpha_row_sorted : ∀ i,
    pivotedStoredQRPrintedAlphaScale fp hmn A i ≤
      rowSortCoeff * Wave18D.rowInftyNorm A i
  beta_row_sorted : ∀ i,
    pivotedStoredQRPrintedBetaScale fp hmn A b i ≤
      rowSortCoeff *
        max (pivotedStoredQRPrintedPhi fp hmn A b *
          Wave18D.rowInftyNorm A i) |b i|
  rowSortCoeff_le_printed :
    rowSortCoeff ≤ Real.sqrt (m : ℝ) *
      (1 + Real.sqrt 2) ^ (n - 1)

/-- Primitive local compact-operation obligations.  They bound the explicit
matrix/RHS component budgets at each stage.  Matrix transport uses the (2.12)
norm ratio.  RHS transport keeps the reflector's forward alpha scale separate
from the RHS beta scale through the mixed product
`alpha_i * (‖f_k‖₂ / ‖v_q‖₂)`.  These are local arithmetic/source hypotheses,
not an accumulated QR/RHS perturbation or a contract field. -/
structure PivotedStoredQRCoxHighamComponentBudgets (fp : FPModel) {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (gammaTilde : ℝ) : Prop where
  gamma_nonneg : 0 ≤ gammaTilde
  matrix_component_row : ∀ k, k < n → ∀ i j,
    pivotedStoredQRComponentBudget fp hmn A k i j ≤
      gammaTilde * pivotedStoredQRPrintedAlphaScale fp hmn A i
  matrix_component_transport : ∀ k, k < n → ∀ q, q < k + 1 → ∀ j,
    vecNorm2 (fun i => pivotedStoredQRComponentBudget fp hmn A k i j) /
        vecNorm2 (pivotedStoredQRRawVector fp hmn A q) ≤ gammaTilde
  rhs_component_row : ∀ k, k < n → ∀ i,
    pivotedStoredQRRhsComponentBudget fp hmn A b k i ≤
      gammaTilde * pivotedStoredQRPrintedBetaScale fp hmn A b i
  rhs_component_transport : ∀ k, k < n → ∀ q, q < k + 1 → ∀ i,
    pivotedStoredQRPrintedAlphaScale fp hmn A i *
        (vecNorm2 (fun r => pivotedStoredQRRhsComponentBudget fp hmn A b k r) /
          vecNorm2 (pivotedStoredQRRawVector fp hmn A q)) ≤
      gammaTilde * pivotedStoredQRPrintedBetaScale fp hmn A b i

/-- One actual matrix residual transported through the already executed
reflector prefix, derived from the primitive compact budgets and row policy. -/
theorem pivotedStoredQR_stageImage_entrywise_le_of_componentBudgets
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (gammaTilde : ℝ) (hm : gammaValid fp m)
    (policy : PivotedStoredQRCoxHighamRowPolicy fp hn hmn A)
    (budgets : PivotedStoredQRCoxHighamComponentBudgets
      fp hn hmn A b gammaTilde)
    (k : ℕ) (hk : k < n) (i : Fin m) (j : Fin n) :
    |matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) (k + 1))
        (pivotedStoredQREseq fp hmn A k) i j| ≤
      (1 + 4 * ((k + 1 : ℕ) : ℝ)) * gammaTilde *
        pivotedStoredQRPrintedAlphaScale fp hmn A i := by
  rw [qacc_matMulRect_eq_applyProd
    (pivotedStoredQRPseq fp hmn A)
    (fun q => householder_symmetric m
      (pivotedStoredQRRawVector fp hmn A q)
      (pivotedStoredQRBeta fp hmn A q))
    (k + 1) (pivotedStoredQREseq fp hmn A k) i j]
  apply applyProd_rawHouseholder_entrywise_le
    (fun q => pivotedStoredQRRawVector fp hmn A q)
    (fun q => pivotedStoredQRBeta fp hmn A q)
    (fun s => pivotedStoredQREseq fp hmn A k s j)
    (pivotedStoredQRPrintedAlphaScale fp hmn A)
    gammaTilde (k + 1) i budgets.gamma_nonneg
    (pivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A)
    (fun q => pivotedStoredQRPseq_orthogonal fp hmn A q)
  · intro q hq
    have hqn : q < n := by omega
    have hlower := pivotedStoredQRRawVector_sigma_sign_bound fp hmn A q hqn
    have hscale : 0 < Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A q| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (policy.sigma_pos q hqn)
    linarith
  · intro q hq
    apply householderBetaSpec_mul_vecNorm2_sq_eq_two_of_pos
    have hqn : q < n := by omega
    have hlower := pivotedStoredQRRawVector_sigma_sign_bound fp hmn A q hqn
    have hscale : 0 < Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A q| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (policy.sigma_pos q hqn)
    linarith
  · intro q hq r
    exact policy.raw_vector_row q (by omega) r
  · intro q hq
    have hqn : q < n := by omega
    have hlower := pivotedStoredQRRawVector_sigma_sign_bound fp hmn A q hqn
    have hscale : 0 < Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A q| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (policy.sigma_pos q hqn)
    have hden : 0 < vecNorm2 (pivotedStoredQRRawVector fp hmn A q) := by
      linarith
    have hnorm := pivotedStoredQREseq_norm_le_componentBudget
      fp hmn A hm k hk (policy.sigma_pos k hk) j
    exact (div_le_div_of_nonneg_right hnorm hden.le).trans
      (budgets.matrix_component_transport k hk q hq j)
  · exact (pivotedStoredQREseq_abs_le_componentBudget
      fp hmn A hm k hk (policy.sigma_pos k hk) i j).trans
        (budgets.matrix_component_row k hk i j)

/-- One actual RHS residual transported through the same reflector prefix. -/
theorem pivotedStoredQRRhs_stageImage_entrywise_le_of_componentBudgets
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (gammaTilde : ℝ) (hm : gammaValid fp m)
    (policy : PivotedStoredQRCoxHighamRowPolicy fp hn hmn A)
    (budgets : PivotedStoredQRCoxHighamComponentBudgets
      fp hn hmn A b gammaTilde)
    (k : ℕ) (hk : k < n) (i : Fin m) :
    |matMulVec m
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) (k + 1))
        (pivotedStoredQRRhsEseq fp hmn A b k) i| ≤
      (1 + 4 * ((k + 1 : ℕ) : ℝ)) * gammaTilde *
        pivotedStoredQRPrintedBetaScale fp hmn A b i := by
  rw [congrFun (qacc_matMulVec_eq_applyProd
    (pivotedStoredQRPseq fp hmn A)
    (fun q => householder_symmetric m
      (pivotedStoredQRRawVector fp hmn A q)
      (pivotedStoredQRBeta fp hmn A q))
    (k + 1) (pivotedStoredQRRhsEseq fp hmn A b k)) i]
  apply applyProd_rawHouseholder_entrywise_le_two_scales
    (fun q => pivotedStoredQRRawVector fp hmn A q)
    (fun q => pivotedStoredQRBeta fp hmn A q)
    (pivotedStoredQRRhsEseq fp hmn A b k)
    (pivotedStoredQRPrintedAlphaScale fp hmn A)
    (pivotedStoredQRPrintedBetaScale fp hmn A b)
    gammaTilde (k + 1) i budgets.gamma_nonneg
    (pivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A)
    (pivotedStoredQRPrintedBetaScale_nonneg fp hmn A b)
    (fun q => pivotedStoredQRPseq_orthogonal fp hmn A q)
  · intro q hq
    have hqn : q < n := by omega
    have hlower := pivotedStoredQRRawVector_sigma_sign_bound fp hmn A q hqn
    have hscale : 0 < Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A q| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (policy.sigma_pos q hqn)
    linarith
  · intro q hq
    apply householderBetaSpec_mul_vecNorm2_sq_eq_two_of_pos
    have hqn : q < n := by omega
    have hlower := pivotedStoredQRRawVector_sigma_sign_bound fp hmn A q hqn
    have hscale : 0 < Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A q| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (policy.sigma_pos q hqn)
    linarith
  · intro q hq r
    exact policy.raw_vector_row q (by omega) r
  · intro q hq
    have hqn : q < n := by omega
    have hlower := pivotedStoredQRRawVector_sigma_sign_bound fp hmn A q hqn
    have hscale : 0 < Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A q| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (policy.sigma_pos q hqn)
    have hden : 0 < vecNorm2 (pivotedStoredQRRawVector fp hmn A q) := by
      linarith
    have hnorm := pivotedStoredQRRhsEseq_norm_le_componentBudget
      fp hmn A b hm k hk
    have hratio := div_le_div_of_nonneg_right hnorm hden.le
    exact (mul_le_mul_of_nonneg_left hratio
      (pivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A i)).trans
        (budgets.rhs_component_transport k hk q hq i)
  · exact (pivotedStoredQRRhsEseq_abs_le_componentBudget
      fp hmn A b hm k hk i).trans (budgets.rhs_component_row k hk i)

/-- Printed pivot-position matrix envelope for the actual swap-aware residual
accumulator, derived entirely from local component budgets. -/
theorem pivotedStoredQR_pivotDAacc_rowwise_bound_of_componentBudgets
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (gammaTilde : ℝ) (hm : gammaValid fp m)
    (policy : PivotedStoredQRCoxHighamRowPolicy fp hn hmn A)
    (budgets : PivotedStoredQRCoxHighamComponentBudgets
      fp hn hmn A b gammaTilde)
    (i : Fin m) (j : Fin n) :
    |pivotDAacc (pivotedStoredQRPseq fp hmn A)
        (pivotedStoredQRSwapSeq fp hmn A)
        (pivotedStoredQREseq fp hmn A) n i j| ≤
      ((j.val : ℝ) + 1) ^ 2 * (5 * gammaTilde) *
        pivotedStoredQRPrintedAlphaScale fp hmn A i := by
  apply pivotDAacc_coxHigham_rowwise_bound
    (pivotedStoredQRPseq fp hmn A)
    (pivotedStoredQRSwapSeq fp hmn A)
    (pivotedStoredQREseq fp hmn A)
    (pivotedStoredQRPrintedAlphaScale fp hmn A) gammaTilde
    budgets.gamma_nonneg
    (pivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A)
    (fun k j hj => pivotedStoredQRSwapSeq_fix_prefix fp hmn A k j hj)
    (fun k j hj => pivotedStoredQRSwapSeq_maps_active fp hmn A k j hj)
    (fun k r c hc =>
      pivotedStoredQR_QaccE_completed_column_zero fp hmn A k r c hc)
  · intro k r c
    by_cases hk : k < n
    · simpa [Nat.cast_add, Nat.cast_one] using
        pivotedStoredQR_stageImage_entrywise_le_of_componentBudgets
          fp hn hmn A b gammaTilde hm policy budgets k hk r c
    · have hkge : n ≤ k := Nat.le_of_not_gt hk
      have hc : c.val < k := lt_of_lt_of_le c.isLt hkge
      have hzero : matMulRect m m n
          (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) (k + 1))
          (pivotedStoredQREseq fp hmn A k) r c = 0 := by
        unfold matMulRect
        apply Finset.sum_eq_zero
        intro s _hs
        rw [pivotedStoredQREseq_completed_column_zero fp hmn A k s c hc]
        ring
      rw [hzero, abs_zero]
      exact mul_nonneg
        (mul_nonneg (by positivity) budgets.gamma_nonneg)
        (pivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A r)

/-- Printed `n²` RHS envelope for the literal paired RHS trace. -/
theorem pivotedStoredQRRhsDelta_rowwise_bound_of_componentBudgets
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (gammaTilde : ℝ) (hm : gammaValid fp m)
    (policy : PivotedStoredQRCoxHighamRowPolicy fp hn hmn A)
    (budgets : PivotedStoredQRCoxHighamComponentBudgets
      fp hn hmn A b gammaTilde)
    (i : Fin m) :
    |pivotedStoredQRRhsDelta fp hmn A b i| ≤
      (n : ℝ) ^ 2 * (5 * gammaTilde) *
        pivotedStoredQRPrintedBetaScale fp hmn A b i := by
  have h := Wave19.entrywise_residual_telescope_bound n
    (pivotedStoredQRPseq fp hmn A)
    (pivotedStoredQRRhsEMatrixSeq fp hmn A b)
    (fun k r => (1 + 4 * ((k : ℝ) + 1)) * gammaTilde *
      pivotedStoredQRPrintedBetaScale fp hmn A b r)
    (fun k hk r _j => by
      simpa [pivotedStoredQRRhsEMatrixSeq, matMulRect, matMulVec,
        Nat.cast_add, Nat.cast_one] using
        pivotedStoredQRRhs_stageImage_entrywise_le_of_componentBudgets
          fp hn hmn A b gammaTilde hm policy budgets k hk r)
    i (0 : Fin 1)
  have hfactor :
      (∑ k ∈ Finset.range n,
          (1 + 4 * ((k : ℝ) + 1)) * gammaTilde *
            pivotedStoredQRPrintedBetaScale fp hmn A b i) =
        (∑ k ∈ Finset.range n, (1 + 4 * ((k : ℝ) + 1))) *
          gammaTilde * pivotedStoredQRPrintedBetaScale fp hmn A b i := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hfactor] at h
  have hsum := Wave19.stage_sum_le_five_j_sq n
  have hscale : 0 ≤ gammaTilde *
      pivotedStoredQRPrintedBetaScale fp hmn A b i :=
    mul_nonneg budgets.gamma_nonneg
      (pivotedStoredQRPrintedBetaScale_nonneg fp hmn A b i)
  calc
    |pivotedStoredQRRhsDelta fp hmn A b i| ≤
        (∑ k ∈ Finset.range n, (1 + 4 * ((k : ℝ) + 1))) *
          gammaTilde * pivotedStoredQRPrintedBetaScale fp hmn A b i := by
            simpa [pivotedStoredQRRhsDelta] using h
    _ = (∑ k ∈ Finset.range n, (1 + 4 * ((k : ℝ) + 1))) *
          (gammaTilde * pivotedStoredQRPrintedBetaScale fp hmn A b i) := by ring
    _ ≤ (5 * (n : ℝ) ^ 2) *
          (gammaTilde * pivotedStoredQRPrintedBetaScale fp hmn A b i) :=
      mul_le_mul_of_nonneg_right hsum hscale
    _ = (n : ℝ) ^ 2 * (5 * gammaTilde) *
          pivotedStoredQRPrintedBetaScale fp hmn A b i := by ring

/-- A componentwise-admissible triangular-solve perturbation satisfies the
prefix-policy obligations needed to transport `Q [dR;0]`.  This is derived
from the literal final `R`, its active-tail policy, and the actual executed
reflector-prefix policy; it does not assume a transported perturbation bound. -/
theorem pivotedStoredQR_qdRPrefixReady_of_componentwise_topR
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (hgammaN : gammaValid fp n)
    (policy : PivotedStoredQRCoxHighamRowPolicy fp hn hmn A)
    (dR : Fin n → Fin n → ℝ)
    (hdR : ∀ i j,
      |dR i j| ≤ gamma fp n * |pivotedStoredQRTopR fp hmn A i j|) :
    PivotedStoredQRQdRPrefixReady fp hmn A
      (pivotedStoredQRPrintedAlphaScale fp hmn A) (gamma fp n) dR := by
  have hgamma0 : 0 ≤ gamma fp n := gamma_nonneg fp hgammaN
  refine
    { eta_nonneg := hgamma0
      correction_row := ?_
      prefix_vector_row := policy.prefix_vector_row
      correction_tail_norm := ?_ }
  · intro i j
    by_cases hi : i.val < n
    · have hrelative := hdR ⟨i.val, hi⟩ j
      have hRrow := policy.topR_row ⟨i.val, hi⟩ j
      rw [rectTopBlock_top dR i j hi]
      exact hrelative.trans
        (mul_le_mul_of_nonneg_left hRrow hgamma0)
    · have hle : n ≤ i.val := Nat.le_of_not_gt hi
      rw [rectTopBlock_bottom dR i j hle, abs_zero]
      exact mul_nonneg hgamma0
        (pivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A i)
  · intro k hk j
    let p : Fin m := pivotedQRActiveRow hmn k hk
    let dTail : Fin m → ℝ :=
      householderTrailingPart m p
        (fun i => rectTopBlock (m := m) dR i j)
    let rTail : Fin m → ℝ :=
      householderTrailingPart m p
        (fun i => rectTopBlock (m := m)
          (pivotedStoredQRTopR fp hmn A) i j)
    have hpoint : ∀ i : Fin m, |dTail i| ≤ gamma fp n * |rTail i| := by
      intro i
      by_cases hik : i.val < k
      · simp [dTail, rTail, householderTrailingPart, p,
          pivotedQRActiveRow, hik]
      · by_cases hin : i.val < n
        · have hrelative := hdR ⟨i.val, hin⟩ j
          simpa [dTail, rTail, householderTrailingPart, p,
            pivotedQRActiveRow, hik, rectTopBlock_top, hin] using hrelative
        · have hle : n ≤ i.val := Nat.le_of_not_gt hin
          simp [dTail, rTail, householderTrailingPart, p,
            pivotedQRActiveRow, hik, rectTopBlock_bottom, hle]
    have hnorm : vecNorm2 dTail ≤
        vecNorm2 (fun i => gamma fp n * |rTail i|) :=
      vecNorm2_le_of_abs_le dTail
        (fun i => gamma fp n * |rTail i|) hpoint
    have hscaled : vecNorm2 (fun i => gamma fp n * |rTail i|) =
        gamma fp n * vecNorm2 rTail := by
      rw [vecNorm2_smul, abs_of_nonneg hgamma0, vecNorm2_abs]
    calc
      vecNorm2
          (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
            (fun i => rectTopBlock (m := m) dR i j)) = vecNorm2 dTail := by
              rfl
      _ ≤ gamma fp n * vecNorm2 rTail := by
        rw [← hscaled]
        exact hnorm
      _ ≤ gamma fp n * |pivotedStoredQRSigma fp hmn A k| :=
        mul_le_mul_of_nonneg_left (policy.topR_tail k hk j) hgamma0

/-- Concrete Split 3B producer for the literal rounded pivoted-stored-QR and
paired-RHS traces.

The coefficient `5 * gammaTilde` is obtained by summing the explicit compact
matrix/RHS component budgets through the (2.10)--(2.14) rowwise core.  The
coefficient `16 * gamma fp n` is obtained by applying the Cox--Higham
(3.7)--(3.11) prefix argument to every componentwise back-substitution
perturbation.  The exact forward alpha/beta numerators are used here without
row sorting; sorting is only the optional initial-scale corollary below.  Thus
no field of the resulting contract, no final minimizer, and no accumulated
backward error is assumed. -/
theorem pivotedStoredQR_split3B_numericalContract_of_coxHigham
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (gammaTilde : ℝ)
    (hm : gammaValid fp m) (hgammaN : gammaValid fp n)
    (policy : PivotedStoredQRCoxHighamRowPolicy fp hn hmn A)
    (budgets : PivotedStoredQRCoxHighamComponentBudgets
      fp hn hmn A b gammaTilde) :
    PivotedStoredQRSplit3BNumericalContract fp hmn A b
      (pivotedStoredQRPrintedAlphaScale fp hmn A)
      (pivotedStoredQRPrintedBetaScale fp hmn A b)
      (5 * gammaTilde) (5 * gammaTilde) (16 * gamma fp n) := by
  refine
    { alpha_nonneg := pivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A
      betaScale_nonneg :=
        pivotedStoredQRPrintedBetaScale_nonneg fp hmn A b
      qrCoeff_nonneg := mul_nonneg (by norm_num) budgets.gamma_nonneg
      rhsCoeff_nonneg := mul_nonneg (by norm_num) budgets.gamma_nonneg
      backSubCoeff_nonneg :=
        mul_nonneg (by norm_num) (gamma_nonneg fp hgammaN)
      qr_accumulated_pivot_row := ?_
      rhs_accumulated_source_row := ?_
      backSub_transport_source_row := ?_ }
  · intro i j
    exact pivotedStoredQR_pivotDAacc_rowwise_bound_of_componentBudgets
      fp hn hmn A b gammaTilde hm policy budgets i j
  · intro i
    exact pivotedStoredQRRhsDelta_rowwise_bound_of_componentBudgets
      fp hn hmn A b gammaTilde hm policy budgets i
  · intro dR hdR i j
    have qdr := pivotedStoredQR_qdRPrefixReady_of_componentwise_topR
      fp hn hmn A hgammaN policy dR hdR
    exact pivotedStoredQR_QdR_source_n_sq_le_of_prefixReady
      fp hmn A (pivotedStoredQRPrintedAlphaScale fp hmn A)
      (pivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A)
      policy.sigma_pos qdr i j

/-- Zero-safe source-row form of the concrete producer.  The exact printed
growth numerators are replaced by the row-policy caps
`rowSortCoeff * max_j |aᵢⱼ|` and
`rowSortCoeff * max (phi * max_j |aᵢⱼ|) |bᵢ|`; the separate sorting certificate records
the printed Cox--Higham cap on `rowSortCoeff`. -/
theorem pivotedStoredQR_split3B_sourceRowContract_of_coxHigham
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (gammaTilde rowSortCoeff : ℝ)
    (hm : gammaValid fp m) (hgammaN : gammaValid fp n)
    (policy : PivotedStoredQRCoxHighamRowPolicy fp hn hmn A)
    (sorting : PivotedStoredQRCoxHighamRowSortingCaps
      fp hn hmn A b rowSortCoeff)
    (budgets : PivotedStoredQRCoxHighamComponentBudgets
      fp hn hmn A b gammaTilde) :
    PivotedStoredQRSplit3BNumericalContract fp hmn A b
      (fun i => rowSortCoeff * Wave18D.rowInftyNorm A i)
      (fun i => rowSortCoeff *
        max (pivotedStoredQRPrintedPhi fp hmn A b *
          Wave18D.rowInftyNorm A i) |b i|)
      (5 * gammaTilde) (5 * gammaTilde) (16 * gamma fp n) := by
  have base := pivotedStoredQR_split3B_numericalContract_of_coxHigham
    fp hn hmn A b gammaTilde hm hgammaN policy budgets
  refine
    { alpha_nonneg := ?_
      betaScale_nonneg := ?_
      qrCoeff_nonneg := base.qrCoeff_nonneg
      rhsCoeff_nonneg := base.rhsCoeff_nonneg
      backSubCoeff_nonneg := base.backSubCoeff_nonneg
      qr_accumulated_pivot_row := ?_
      rhs_accumulated_source_row := ?_
      backSub_transport_source_row := ?_ }
  · intro i
    exact mul_nonneg sorting.rowSortCoeff_nonneg
      (Wave18D.rowInftyNorm_nonneg A i ⟨0, hn⟩)
  · intro i
    have hmax : 0 ≤ max
        (pivotedStoredQRPrintedPhi fp hmn A b *
          Wave18D.rowInftyNorm A i) |b i| :=
      (abs_nonneg (b i)).trans (le_max_right _ _)
    exact mul_nonneg sorting.rowSortCoeff_nonneg hmax
  · intro i j
    have h := base.qr_accumulated_pivot_row i j
    have hcoeff : 0 ≤ (((j.val : ℝ) + 1) ^ 2 * (5 * gammaTilde)) :=
      mul_nonneg (sq_nonneg _) base.qrCoeff_nonneg
    calc
      |pivotDAacc (pivotedStoredQRPseq fp hmn A)
          (pivotedStoredQRSwapSeq fp hmn A)
          (pivotedStoredQREseq fp hmn A) n i j| ≤
          ((j.val : ℝ) + 1) ^ 2 * (5 * gammaTilde) *
            pivotedStoredQRPrintedAlphaScale fp hmn A i := h
      _ = (((j.val : ℝ) + 1) ^ 2 * (5 * gammaTilde)) *
            pivotedStoredQRPrintedAlphaScale fp hmn A i := by ring
      _ ≤ (((j.val : ℝ) + 1) ^ 2 * (5 * gammaTilde)) *
            (rowSortCoeff * Wave18D.rowInftyNorm A i) :=
        mul_le_mul_of_nonneg_left (sorting.alpha_row_sorted i) hcoeff
      _ = ((j.val : ℝ) + 1) ^ 2 * (5 * gammaTilde) *
            (rowSortCoeff * Wave18D.rowInftyNorm A i) := by ring
  · intro i
    have h := base.rhs_accumulated_source_row i
    have hcoeff : 0 ≤ (n : ℝ) ^ 2 * (5 * gammaTilde) :=
      mul_nonneg (sq_nonneg _) base.rhsCoeff_nonneg
    calc
      |pivotedStoredQRRhsDelta fp hmn A b i| ≤
          (n : ℝ) ^ 2 * (5 * gammaTilde) *
            pivotedStoredQRPrintedBetaScale fp hmn A b i := h
      _ = ((n : ℝ) ^ 2 * (5 * gammaTilde)) *
            pivotedStoredQRPrintedBetaScale fp hmn A b i := by ring
      _ ≤ ((n : ℝ) ^ 2 * (5 * gammaTilde)) *
            (rowSortCoeff *
              max (pivotedStoredQRPrintedPhi fp hmn A b *
                Wave18D.rowInftyNorm A i) |b i|) :=
        mul_le_mul_of_nonneg_left (sorting.beta_row_sorted i) hcoeff
      _ = (n : ℝ) ^ 2 * (5 * gammaTilde) *
            (rowSortCoeff *
              max (pivotedStoredQRPrintedPhi fp hmn A b *
                Wave18D.rowInftyNorm A i) |b i|) := by ring
  · intro dR hdR i j
    have h := base.backSub_transport_source_row dR hdR i j
    have hcoeff : 0 ≤ (n : ℝ) ^ 2 * (16 * gamma fp n) :=
      mul_nonneg (sq_nonneg _) base.backSubCoeff_nonneg
    calc
      |matMulRect m m n
          (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
          (rectTopBlock (m := m) dR) i
          ((pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n).symm j)| ≤
          (n : ℝ) ^ 2 * (16 * gamma fp n) *
            pivotedStoredQRPrintedAlphaScale fp hmn A i := h
      _ = ((n : ℝ) ^ 2 * (16 * gamma fp n)) *
            pivotedStoredQRPrintedAlphaScale fp hmn A i := by ring
      _ ≤ ((n : ℝ) ^ 2 * (16 * gamma fp n)) *
            (rowSortCoeff * Wave18D.rowInftyNorm A i) :=
        mul_le_mul_of_nonneg_left (sorting.alpha_row_sorted i) hcoeff
      _ = (n : ℝ) ^ 2 * (16 * gamma fp n) *
            (rowSortCoeff * Wave18D.rowInftyNorm A i) := by ring

/-! ## Executable common-row-permutation wrapper

The literal stored-QR loop has no row swaps.  A source-level common row
permutation is therefore applied to both `A` and `b` before running the same
executable matrix/RHS/back-substitution traces.  Perturbations are pulled back
by the inverse row permutation below. -/

/-- Returned vector of the literal algorithm after a common source row
permutation of `A` and `b`. -/
noncomputable def pivotedStoredQRCommonRowPermutedReturnedX
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (σ : Fin m ≃ Fin m) :
    Fin n → ℝ :=
  pivotedStoredQRReturnedX fp hmn
    (rectPermuteRows σ A) (vecPermute σ b)

/-- Pullback to source rows of the matrix perturbation produced after the
common row permutation. -/
noncomputable def pivotedStoredQRCommonRowPermutedBackSubSourceDelta
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (σ : Fin m ≃ Fin m)
    (dR : Fin n → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => pivotedStoredQRBackSubSourceDelta fp hmn
    (rectPermuteRows σ A) dR (σ.symm i) j

/-- Pullback to source rows of the paired RHS perturbation produced after the
same common row permutation. -/
noncomputable def pivotedStoredQRCommonRowPermutedRhsDelta
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (σ : Fin m ≃ Fin m) :
    Fin m → ℝ :=
  fun i => pivotedStoredQRRhsDelta fp hmn
    (rectPermuteRows σ A) (vecPermute σ b) (σ.symm i)

/-- Literal column-pivoted QR, paired RHS transformation, and floating-point
back substitution satisfy the source-facing Theorem 20.7 conclusion once the
Split 3B numerical contract is available.

The proof runs the repository's `fl_backSub`, obtains its concrete `dR`, and
then reconstructs the exact least-squares problem from the literal matrix and
RHS telescopes.  The total matrix perturbation includes both the accumulated
QR residual and `Q [dR;0]`.  Unpermuting uses the valid uniform `n^2` source
factor; no pivot-position factor is incorrectly relabeled as a source-column
factor. -/
theorem fl_pivotedStoredQR_returnedX_exactMinimizer_of_split3B
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (alpha betaScale : Fin m → ℝ)
    (qrCoeff rhsCoeff backSubCoeff : ℝ)
    (contract : PivotedStoredQRSplit3BNumericalContract fp hmn A b
      alpha betaScale qrCoeff rhsCoeff backSubCoeff)
    (hdiag : ∀ i : Fin n, pivotedStoredQRTopR fp hmn A i i ≠ 0)
    (hgamma : gammaValid fp n) :
    ∃ dR : Fin n → Fin n → ℝ,
      (∀ i j,
        |dR i j| ≤ gamma fp n * |pivotedStoredQRTopR fp hmn A i j|) ∧
      IsLeastSquaresMinimizer
        (fun i j => A i j +
          pivotedStoredQRBackSubSourceDelta fp hmn A dR i j)
        (fun i => b i + pivotedStoredQRRhsDelta fp hmn A b i)
        (pivotedStoredQRReturnedX fp hmn A b) ∧
      (∀ i j,
        |pivotedStoredQRBackSubSourceDelta fp hmn A dR i j| ≤
          (n : ℝ) ^ 2 * (qrCoeff + backSubCoeff) * alpha i) ∧
      ∀ i,
        |pivotedStoredQRRhsDelta fp hmn A b i| ≤
          (n : ℝ) ^ 2 * rhsCoeff * betaScale i := by
  let Pseq := pivotedStoredQRPseq fp hmn A
  let Sseq := pivotedStoredQRSwapSeq fp hmn A
  let Eseq := pivotedStoredQREseq fp hmn A
  let pi := pivotPermAcc Sseq n
  let Q := Wave19.Qacc Pseq n
  let Rfull := fl_pivotedStoredQRMatrixSeq fp hmn A n
  let Rtop := pivotedStoredQRTopR fp hmn A
  let cfull := fl_pivotedStoredQRRhsSeq fp hmn A b n
  let ctop := pivotedStoredQRTopRhs fp hmn A b
  let dA := pivotDAacc Pseq Sseq Eseq n
  let db := pivotedStoredQRRhsDelta fp hmn A b
  let xPivot := pivotedStoredQRReturnedPivotX fp hmn A b
  have hP : ∀ k, IsOrthogonal m (Pseq k) := by
    intro k
    exact pivotedStoredQRPseq_orthogonal fp hmn A k
  have hQ : IsOrthogonal m Q := Wave19.Qacc_orthogonal Pseq hP n
  have hRupper : IsUpperTrapezoidal m n Rfull :=
    fl_pivotedStoredQRMatrixSeq_upperTrapezoidal fp hmn A
  have hRtopUpper : ∀ i j : Fin n, j.val < i.val → Rtop i j = 0 := by
    intro i j hji
    exact hRupper ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j hji
  rcases backSub_backward_error fp n Rtop ctop
      (by simpa [Rtop] using hdiag) hRtopUpper hgamma with
    ⟨dR, hdR, hsolve⟩
  have hdR' : ∀ i j,
      |dR i j| ≤ gamma fp n * |pivotedStoredQRTopR fp hmn A i j| := by
    simpa [Rtop] using hdR
  refine ⟨dR, hdR', ?_, ?_, contract.rhs_accumulated_source_row⟩
  · let topdR := rectTopBlock (m := m) dR
    let APivot : Fin m → Fin n → ℝ := fun i j =>
      Wave13.columnPermuteMatrix A pi i j + dA i j
    let APivotTotal : Fin m → Fin n → ℝ := fun i j =>
      APivot i j + matMulRect m m n Q topdR i j
    let Atrans : Fin m → Fin n → ℝ := fun i j => Rfull i j + topdR i j
    let bPert : Fin m → ℝ := fun i => b i + db i
    have hAhat : Rfull = matMulRect m m n (matTranspose Q) APivot := by
      funext i j
      simpa [Pseq, Sseq, Eseq, Q, Rfull, pi, dA, APivot,
        fl_pivotedStoredQRMatrixSeq] using
        pivoted_entrywise_residual_telescope n
          (fl_pivotedStoredQRMatrixSeq fp hmn A) Pseq Sseq Eseq hP
          (fun k _hk r s =>
            pivotedStoredQR_step_with_residual fp hmn A k r s) i j
    have hbhat : cfull = matMulVec m (matTranspose Q) bPert := by
      funext i
      simpa [Pseq, Q, cfull, db, bPert] using
        pivotedStoredQRRhs_telescope fp hmn A b i
    have hQTQ : matMul m (matTranspose Q) Q = idMatrix m :=
      funext fun i => funext fun j => hQ.left_inv i j
    have hpull :
        matMulRect m m n (matTranspose Q)
            (matMulRect m m n Q topdR) = topdR := by
      rw [← matMulRect_assoc_square_left, hQTQ, matMulRect_id_left]
    have hAtrans : Atrans =
        matMulRect m m n (matTranspose Q) APivotTotal := by
      rw [show APivotTotal = fun i j =>
          APivot i j + matMulRect m m n Q topdR i j by rfl,
        matMulRect_add_right, ← hAhat, hpull]
    have hA_top : ∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
        Atrans i j = (fun r s => Rtop r s + dR r s) ⟨i.val, hi⟩ j := by
      intro i j hi
      have hRi : Rfull i j = Rtop ⟨i.val, hi⟩ j := by
        simp [Rfull, Rtop]
        congr 2
      have hdi : topdR i j = dR ⟨i.val, hi⟩ j := by
        simpa [topdR] using rectTopBlock_top dR i j hi
      simpa [Atrans] using congrArg₂ (· + ·) hRi hdi
    have hA_bottom : ∀ (i : Fin m) (j : Fin n), n ≤ i.val →
        Atrans i j = 0 := by
      intro i j hi
      have htopzero : topdR i j = 0 := by
        simpa [topdR] using rectTopBlock_bottom dR i j hi
      rw [show Atrans i j = Rfull i j + topdR i j by rfl,
        hRupper i j (lt_of_lt_of_le j.isLt hi), htopzero]
      ring
    have hb_top : ∀ (i : Fin m) (hi : i.val < n),
        cfull i = ctop ⟨i.val, hi⟩ := by
      intro i hi
      congr 1
    have hsolve' : ∀ r : Fin n,
        matMulVec n (fun i j => Rtop i j + dR i j) xPivot r = ctop r := by
      intro r
      simpa [matMulVec, xPivot, pivotedStoredQRReturnedPivotX,
        Rtop, ctop] using hsolve r
    have hNEtrans : RectLSNormalEquations Atrans cfull xPivot :=
      RectLSNormalEquations.of_top_solve_zero_bottom
        Atrans cfull (fun i j => Rtop i j + dR i j) ctop xPivot
        hA_top hA_bottom hb_top hsolve'
    have hNEPivot : RectLSNormalEquations APivotTotal bPert xPivot :=
      RectLSNormalEquations.of_orthogonal_left
        (matTranspose Q) APivotTotal Atrans bPert cfull xPivot hQ.transpose
        hAtrans hbhat hNEtrans
    have hMinPivot : IsLeastSquaresMinimizer APivotTotal bPert xPivot :=
      hNEPivot.isLeastSquaresMinimizer
    have hPermData : rectPermuteCols pi
        (fun i j => A i j +
          pivotedStoredQRBackSubSourceDelta fp hmn A dR i j) =
        APivotTotal := by
      funext i j
      simp [rectPermuteCols, pivotedStoredQRBackSubSourceDelta,
        pivotedStoredQRBackSubPivotDelta, Pseq, Sseq, Eseq, pi, Q, dA,
        APivotTotal, APivot, topdR, Wave13.columnPermuteMatrix]
      ring
    have hMinPerm : IsLeastSquaresMinimizer
        (rectPermuteCols pi
          (fun i j => A i j +
            pivotedStoredQRBackSubSourceDelta fp hmn A dR i j))
        bPert xPivot := by
      rw [hPermData]
      exact hMinPivot
    have hMinSource := IsLeastSquaresMinimizer.of_permuteCols pi
      (fun i j => A i j +
        pivotedStoredQRBackSubSourceDelta fp hmn A dR i j)
      bPert xPivot hMinPerm
    simpa [bPert, db, xPivot, pivotedStoredQRReturnedX, pi, Sseq] using
      hMinSource
  · intro i j
    have hqrPivot := contract.qr_accumulated_pivot_row i (pi.symm j)
    have hfactor := pivotPositionFactor_le_sourceDimensionFactor pi j
    have hqrScale : 0 ≤ qrCoeff * alpha i :=
      mul_nonneg contract.qrCoeff_nonneg (contract.alpha_nonneg i)
    have hqrSource :
        |dA i (pi.symm j)| ≤ (n : ℝ) ^ 2 * qrCoeff * alpha i := by
      calc
        |dA i (pi.symm j)| ≤
            (((pi.symm j).val : ℝ) + 1) ^ 2 * qrCoeff * alpha i := by
              simpa [Pseq, Sseq, Eseq, pi, dA] using hqrPivot
        _ = (((pi.symm j).val : ℝ) + 1) ^ 2 *
              (qrCoeff * alpha i) := by ring
        _ ≤ (n : ℝ) ^ 2 * (qrCoeff * alpha i) :=
          mul_le_mul_of_nonneg_right hfactor hqrScale
        _ = (n : ℝ) ^ 2 * qrCoeff * alpha i := by ring
    have htransport := contract.backSub_transport_source_row dR hdR' i j
    calc
      |pivotedStoredQRBackSubSourceDelta fp hmn A dR i j| =
          |dA i (pi.symm j) +
            matMulRect m m n Q (rectTopBlock (m := m) dR) i
              (pi.symm j)| := by
            simp [pivotedStoredQRBackSubSourceDelta,
              pivotedStoredQRBackSubPivotDelta, Pseq, Sseq, Eseq, pi, Q,
              dA]
      _ ≤ |dA i (pi.symm j)| +
            |matMulRect m m n Q (rectTopBlock (m := m) dR) i
              (pi.symm j)| := abs_add_le _ _
      _ ≤ (n : ℝ) ^ 2 * qrCoeff * alpha i +
            (n : ℝ) ^ 2 * backSubCoeff * alpha i :=
        add_le_add hqrSource (by simpa [Pseq, Sseq, pi, Q] using htransport)
      _ = (n : ℝ) ^ 2 * (qrCoeff + backSubCoeff) * alpha i := by ring

/-- Direct Cox--Higham endpoint for the actual executable pivoted stored-QR,
paired RHS, and `fl_backSub` traces.  The numerical contract is constructed
internally from the forward row policy and primitive compact-operation
budgets, so this theorem has no contract, accumulated perturbation, returned-x
correctness, or minimizer hypothesis. -/
theorem fl_pivotedStoredQR_returnedX_exactMinimizer_of_coxHigham
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (gammaTilde : ℝ)
    (hm : gammaValid fp m) (hgammaN : gammaValid fp n)
    (policy : PivotedStoredQRCoxHighamRowPolicy fp hn hmn A)
    (budgets : PivotedStoredQRCoxHighamComponentBudgets
      fp hn hmn A b gammaTilde)
    (hdiag : ∀ i : Fin n, pivotedStoredQRTopR fp hmn A i i ≠ 0) :
    ∃ dR : Fin n → Fin n → ℝ,
      (∀ i j,
        |dR i j| ≤ gamma fp n * |pivotedStoredQRTopR fp hmn A i j|) ∧
      IsLeastSquaresMinimizer
        (fun i j => A i j +
          pivotedStoredQRBackSubSourceDelta fp hmn A dR i j)
        (fun i => b i + pivotedStoredQRRhsDelta fp hmn A b i)
        (pivotedStoredQRReturnedX fp hmn A b) ∧
      (∀ i j,
        |pivotedStoredQRBackSubSourceDelta fp hmn A dR i j| ≤
          (n : ℝ) ^ 2 *
            ((5 * gammaTilde) + (16 * gamma fp n)) *
              pivotedStoredQRPrintedAlphaScale fp hmn A i) ∧
      ∀ i,
        |pivotedStoredQRRhsDelta fp hmn A b i| ≤
          (n : ℝ) ^ 2 * (5 * gammaTilde) *
            pivotedStoredQRPrintedBetaScale fp hmn A b i := by
  let contract := pivotedStoredQR_split3B_numericalContract_of_coxHigham
    fp hn hmn A b gammaTilde hm hgammaN policy budgets
  exact fl_pivotedStoredQR_returnedX_exactMinimizer_of_split3B
    fp hmn A b
      (pivotedStoredQRPrintedAlphaScale fp hmn A)
      (pivotedStoredQRPrintedBetaScale fp hmn A b)
      (5 * gammaTilde) (5 * gammaTilde) (16 * gamma fp n)
      contract hdiag hgammaN

/-- Optional initial-data form of the direct endpoint.  This is a corollary of
the forward-alpha/beta endpoint plus a separate common row-sorting/growth cap;
row sorting is not used in the Cox--Higham (2.10)--(2.14) core itself. -/
theorem fl_pivotedStoredQR_returnedX_sourceRows_of_coxHigham
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (gammaTilde rowSortCoeff : ℝ)
    (hm : gammaValid fp m) (hgammaN : gammaValid fp n)
    (policy : PivotedStoredQRCoxHighamRowPolicy fp hn hmn A)
    (sorting : PivotedStoredQRCoxHighamRowSortingCaps
      fp hn hmn A b rowSortCoeff)
    (budgets : PivotedStoredQRCoxHighamComponentBudgets
      fp hn hmn A b gammaTilde)
    (hdiag : ∀ i : Fin n, pivotedStoredQRTopR fp hmn A i i ≠ 0) :
    ∃ dR : Fin n → Fin n → ℝ,
      (∀ i j,
        |dR i j| ≤ gamma fp n * |pivotedStoredQRTopR fp hmn A i j|) ∧
      IsLeastSquaresMinimizer
        (fun i j => A i j +
          pivotedStoredQRBackSubSourceDelta fp hmn A dR i j)
        (fun i => b i + pivotedStoredQRRhsDelta fp hmn A b i)
        (pivotedStoredQRReturnedX fp hmn A b) ∧
      (∀ i j,
        |pivotedStoredQRBackSubSourceDelta fp hmn A dR i j| ≤
          (n : ℝ) ^ 2 *
            ((5 * gammaTilde) + (16 * gamma fp n)) *
              (rowSortCoeff * Wave18D.rowInftyNorm A i)) ∧
      ∀ i,
        |pivotedStoredQRRhsDelta fp hmn A b i| ≤
          (n : ℝ) ^ 2 * (5 * gammaTilde) *
            (rowSortCoeff *
              max (pivotedStoredQRPrintedPhi fp hmn A b *
                Wave18D.rowInftyNorm A i) |b i|) := by
  let contract := pivotedStoredQR_split3B_sourceRowContract_of_coxHigham
    fp hn hmn A b gammaTilde rowSortCoeff hm hgammaN
      policy sorting budgets
  exact fl_pivotedStoredQR_returnedX_exactMinimizer_of_split3B
    fp hmn A b
      (fun i => rowSortCoeff * Wave18D.rowInftyNorm A i)
      (fun i => rowSortCoeff *
        max (pivotedStoredQRPrintedPhi fp hmn A b *
          Wave18D.rowInftyNorm A i) |b i|)
      (5 * gammaTilde) (5 * gammaTilde) (16 * gamma fp n)
      contract hdiag hgammaN

/-- Source-transported endpoint for the executable common-row-permutation
wrapper.  The algorithm is run on `(A ∘ σ, b ∘ σ)` and the two perturbations
are pulled back with `σ⁻¹`; row-permutation invariance then gives an exact
least-squares minimizer for the original source row order. -/
theorem fl_pivotedStoredQR_commonRowPermuted_exactMinimizer_of_coxHigham
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (σ : Fin m ≃ Fin m)
    (gammaTilde : ℝ) (hm : gammaValid fp m)
    (hgammaN : gammaValid fp n)
    (policy : PivotedStoredQRCoxHighamRowPolicy fp hn hmn
      (rectPermuteRows σ A))
    (budgets : PivotedStoredQRCoxHighamComponentBudgets fp hn hmn
      (rectPermuteRows σ A) (vecPermute σ b) gammaTilde)
    (hdiag : ∀ i : Fin n,
      pivotedStoredQRTopR fp hmn (rectPermuteRows σ A) i i ≠ 0) :
    ∃ dR : Fin n → Fin n → ℝ,
      (∀ i j,
        |dR i j| ≤ gamma fp n *
          |pivotedStoredQRTopR fp hmn (rectPermuteRows σ A) i j|) ∧
      IsLeastSquaresMinimizer
        (fun i j => A i j +
          pivotedStoredQRCommonRowPermutedBackSubSourceDelta
            fp hmn A σ dR i j)
        (fun i => b i +
          pivotedStoredQRCommonRowPermutedRhsDelta fp hmn A b σ i)
        (pivotedStoredQRCommonRowPermutedReturnedX fp hmn A b σ) ∧
      (∀ i j,
        |pivotedStoredQRCommonRowPermutedBackSubSourceDelta
            fp hmn A σ dR i j| ≤
          (n : ℝ) ^ 2 *
            ((5 * gammaTilde) + (16 * gamma fp n)) *
              pivotedStoredQRPrintedAlphaScale fp hmn
                (rectPermuteRows σ A) (σ.symm i)) ∧
      ∀ i,
        |pivotedStoredQRCommonRowPermutedRhsDelta fp hmn A b σ i| ≤
          (n : ℝ) ^ 2 * (5 * gammaTilde) *
            pivotedStoredQRPrintedBetaScale fp hmn
              (rectPermuteRows σ A) (vecPermute σ b) (σ.symm i) := by
  rcases fl_pivotedStoredQR_returnedX_exactMinimizer_of_coxHigham
      fp hn hmn (rectPermuteRows σ A) (vecPermute σ b) gammaTilde
      hm hgammaN policy budgets hdiag with
    ⟨dR, hdR, hmin, hmatrix, hrhs⟩
  refine ⟨dR, hdR, ?_, ?_, ?_⟩
  · apply IsLeastSquaresMinimizer.of_permuteRows σ
      (fun i j => A i j +
        pivotedStoredQRCommonRowPermutedBackSubSourceDelta
          fp hmn A σ dR i j)
      (fun i => b i +
        pivotedStoredQRCommonRowPermutedRhsDelta fp hmn A b σ i)
      (pivotedStoredQRCommonRowPermutedReturnedX fp hmn A b σ)
    have hAeq : rectPermuteRows σ
        (fun i j => A i j +
          pivotedStoredQRCommonRowPermutedBackSubSourceDelta
            fp hmn A σ dR i j) =
        fun i j => rectPermuteRows σ A i j +
          pivotedStoredQRBackSubSourceDelta fp hmn
            (rectPermuteRows σ A) dR i j := by
      funext i j
      simp [rectPermuteRows,
        pivotedStoredQRCommonRowPermutedBackSubSourceDelta]
    have hbeq : vecPermute σ
        (fun i => b i +
          pivotedStoredQRCommonRowPermutedRhsDelta fp hmn A b σ i) =
        fun i => vecPermute σ b i +
          pivotedStoredQRRhsDelta fp hmn
            (rectPermuteRows σ A) (vecPermute σ b) i := by
      funext i
      simp [vecPermute, pivotedStoredQRCommonRowPermutedRhsDelta]
    rw [hAeq, hbeq]
    simpa [pivotedStoredQRCommonRowPermutedReturnedX] using hmin
  · intro i j
    exact hmatrix (σ.symm i) j
  · intro i
    exact hrhs (σ.symm i)

end Theorem20_7

end LeanFpAnalysis.FP
