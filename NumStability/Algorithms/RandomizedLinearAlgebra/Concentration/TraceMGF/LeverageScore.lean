import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Gram
import NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge
import NumStability.Analysis.FunctionalCalculus.OperatorLog.Monotonicity
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixConcentration
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.TraceMGF.LeverageScore

W11 canonical reusable randomized linear algebra destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.RowSamplingLeverageMGF`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/RowSamplingLeverageMGF.lean
--
-- One-step matrix-CGF prerequisites for Algorithm 2 leverage-score sampling.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602





namespace NumStability

open scoped BigOperators ComplexOrder

/-!
## Centered leverage covariance log-CGF

This file instantiates the repository's generic centered C-star Bernstein
log-CGF theorem with Algorithm 2's one-step leverage covariance observable

`X_i = rowOuterGramSample U i - I`.

It is a source-sharp concentration prerequisite: it proves the one-step
matrix-CGF bound needed before applying the row-trace product-law MGF adapter
and the final rank-one tail conversion.
-/

/-- Row outer-product estimators are symmetric finite real matrices. -/
theorem rowOuterGramSample_symmetric {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) :
    IsSymmetricFiniteMatrix (fun j k : Fin n => rowOuterGramSample U i j k) := by
  intro j k
  unfold rowOuterGramSample
  ring

/-- The centered one-step row outer-product estimator `X_i - I` is symmetric. -/
theorem rowOuterGramSample_centered_symmetric {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) :
    IsSymmetricFiniteMatrix
      (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k) := by
  intro j k
  have hrow := rowOuterGramSample_symmetric U i j k
  change rowOuterGramSample U i j k = rowOuterGramSample U i k j at hrow
  change
    rowOuterGramSample U i j k - finiteIdMatrix j k =
      rowOuterGramSample U i k j - finiteIdMatrix k j
  rw [hrow]
  by_cases h : j = k
  · subst h
    simp [finiteIdMatrix]
  · have hk : k ≠ j := Ne.symm h
    simp [finiteIdMatrix, h, hk]

/-- C-star self-adjointness of the centered one-step leverage covariance
observable. -/
theorem leverage_rowOuterGramSample_centered_cstar_selfAdjoint {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) :
    IsSelfAdjoint
      (finiteComplexCStarMatrix
        (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k)) := by
  exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
    (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k)
    (rowOuterGramSample_centered_symmetric U i)

































































/-- The centered one-step leverage covariance observable is bounded above by
`n I` in finite Loewner order.  This conservative upper bound is enough to
instantiate the generic one-step Bernstein log-CGF theorem. -/
theorem leverage_rowOuterGramSample_centered_finiteLoewnerLe_nat
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (i : Fin m) :
    finiteLoewnerLe
      (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k)
      (fun j k : Fin n => (n : ℝ) * finiteIdMatrix j k) := by
  intro x
  have hY :=
    leverage_rowOuterGramSample_finiteLoewnerLe_nat U hU hn i x
  rw [finiteQuadraticForm_smul_finiteIdMatrix] at hY
  rw [finiteQuadraticForm_sub, finiteQuadraticForm_finiteIdMatrix,
    finiteQuadraticForm_smul_finiteIdMatrix]
  exact (sub_le_self _ (finiteVecNorm2Sq_nonneg x)).trans hY

/-- Real spectrum upper bound for the centered leverage covariance observable,
obtained from the finite Loewner bound after embedding in complex C-star
matrices. -/
theorem leverage_rowOuterGramSample_centered_spectrum_le_nat {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) (i : Fin m) {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (fun j k : Fin n =>
            rowOuterGramSample U i j k - finiteIdMatrix j k))) :
    x ≤ (n : ℝ) := by
  classical
  let M : Fin n → Fin n → ℝ :=
    fun j k => rowOuterGramSample U i j k - finiteIdMatrix j k
  let N : Fin n → Fin n → ℝ :=
    fun j k => (n : ℝ) * finiteIdMatrix j k
  have hMsym : IsSymmetricFiniteMatrix M := by
    simpa [M] using rowOuterGramSample_centered_symmetric U i
  have hNsym : IsSymmetricFiniteMatrix N := by
    simpa [N] using smulFiniteIdMatrix_symmetric (n : ℝ)
  have hLe : finiteLoewnerLe M N := by
    simpa [M, N] using
      leverage_rowOuterGramSample_centered_finiteLoewnerLe_nat U hU hn i
  have hCLe :
      finiteComplexCStarMatrix M ≤
        ((n : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
    have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M N hMsym hNsym hLe
    simpa [N, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hxM :
      x ∈ spectrum ℝ (finiteComplexCStarMatrix M) := by
    simpa [M] using hx
  exact cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxM

/-- For leverage-score probabilities, the one-step rank-one estimator squares
to `n` times itself. -/
theorem leverage_finiteMatMul_rowOuterGramSample_self_eq_nat_smul
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (i : Fin m) :
    finiteMatMul
        (fun j k : Fin n => rowOuterGramSample U i j k)
        (fun j k : Fin n => rowOuterGramSample U i j k) =
      fun j k : Fin n => (n : ℝ) * rowOuterGramSample U i j k := by
  classical
  ext j k
  let p : ℝ := rowSqNormProb U i
  have hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  by_cases hpzero : p = 0
  · have hzero := rowOuterGramSample_eq_zero_of_prob_zero U hden i hpzero
    simp [finiteMatMul, hzero]
  · have hp_nonneg : 0 ≤ p := rowSqNormProb_nonneg U hden i
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hrow_pos : 0 < rowNormSq U i := by
      unfold p rowSqNormProb at hp_pos
      exact (div_pos_iff_of_pos_right hden).mp hp_pos
    have hprob_eq : p = rowNormSq U i / (n : ℝ) := by
      unfold p rowSqNormProb
      rw [rowSqNormProbDen_eq_nat_of_orthonormal_columns U hU]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    unfold finiteMatMul rowOuterGramSample
    calc
      ∑ l : Fin n,
          (U i j * U i l / rowSqNormProb U i) *
            (U i l * U i k / rowSqNormProb U i)
          =
        (U i j * U i k / p ^ 2) *
          ∑ l : Fin n, U i l ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            unfold p
            field_simp [hpzero]
      _ =
        (U i j * U i k / p ^ 2) * rowNormSq U i := by
            simp [rowNormSq]
      _ =
        (n : ℝ) * (U i j * U i k / p) := by
            rw [hprob_eq]
            field_simp [hrow_pos.ne', hnR]
      _ =
        (n : ℝ) * (U i j * U i k / rowSqNormProb U i) := by
            rfl

/-- Entrywise square identity for the centered leverage covariance observable. -/
theorem leverage_finiteMatMul_centered_rowOuterGramSample_self_eq
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (i : Fin m) :
    finiteMatMul
        (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k)
        (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k) =
      fun j k : Fin n =>
        ((n : ℝ) - 2) * rowOuterGramSample U i j k + finiteIdMatrix j k := by
  classical
  ext j k
  have hsq :=
    congrFun (congrFun
      (leverage_finiteMatMul_rowOuterGramSample_self_eq_nat_smul U hU hn i)
      j) k
  unfold finiteMatMul
  change
    (∑ l : Fin n,
      rowOuterGramSample U i j l * rowOuterGramSample U i l k) =
      (n : ℝ) * rowOuterGramSample U i j k at hsq
  calc
    ∑ l : Fin n,
        (rowOuterGramSample U i j l - finiteIdMatrix j l) *
          (rowOuterGramSample U i l k - finiteIdMatrix l k)
        =
      (∑ l : Fin n,
        rowOuterGramSample U i j l * rowOuterGramSample U i l k) -
        rowOuterGramSample U i j k -
        rowOuterGramSample U i j k +
        finiteIdMatrix j k := by
          calc
            ∑ l : Fin n,
                (rowOuterGramSample U i j l - finiteIdMatrix j l) *
                  (rowOuterGramSample U i l k - finiteIdMatrix l k)
                =
              ∑ l : Fin n,
                (rowOuterGramSample U i j l *
                    rowOuterGramSample U i l k -
                  rowOuterGramSample U i j l * finiteIdMatrix l k -
                  finiteIdMatrix j l * rowOuterGramSample U i l k +
                  finiteIdMatrix j l * finiteIdMatrix l k) := by
                  apply Finset.sum_congr rfl
                  intro l _
                  ring
            _ =
              (∑ l : Fin n,
                  rowOuterGramSample U i j l *
                    rowOuterGramSample U i l k) -
                (∑ l : Fin n,
                  rowOuterGramSample U i j l * finiteIdMatrix l k) -
                (∑ l : Fin n,
                  finiteIdMatrix j l * rowOuterGramSample U i l k) +
                (∑ l : Fin n,
                  finiteIdMatrix j l * finiteIdMatrix l k) := by
                  rw [Finset.sum_add_distrib]
                  rw [Finset.sum_sub_distrib]
                  rw [Finset.sum_sub_distrib]
            _ =
              (∑ l : Fin n,
                rowOuterGramSample U i j l * rowOuterGramSample U i l k) -
                rowOuterGramSample U i j k -
                rowOuterGramSample U i j k +
                finiteIdMatrix j k := by
                  simp [finiteIdMatrix]
    _ =
      ((n : ℝ) - 2) * rowOuterGramSample U i j k + finiteIdMatrix j k := by
        rw [hsq]
        ring

























































































































































































/-- The negative centered leverage covariance observable `I - Y_i` is bounded
above by `I` in finite Loewner order. -/
theorem leverage_rowOuterGramSample_neg_centered_finiteLoewnerLe_one
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (i : Fin m) :
    finiteLoewnerLe
      (fun j k : Fin n => -(rowOuterGramSample U i j k - finiteIdMatrix j k))
      (fun j k : Fin n => finiteIdMatrix j k) := by
  intro x
  have hpsd := leverage_rowOuterGramSample_finitePSD U hU hn i x
  rw [show
      (fun j k : Fin n =>
        -(rowOuterGramSample U i j k - finiteIdMatrix j k)) =
        fun j k : Fin n => finiteIdMatrix j k - rowOuterGramSample U i j k by
        ext j k
        ring]
  rw [finiteQuadraticForm_sub, finiteQuadraticForm_finiteIdMatrix]
  linarith

/-- Real spectrum upper bound for `-(Y_i-I)`, using PSD of the row
outer-product estimator. -/
theorem leverage_rowOuterGramSample_neg_centered_spectrum_le_one {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) (i : Fin m) {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (fun j k : Fin n =>
            rowOuterGramSample U i j k - finiteIdMatrix j k) :
          CStarMatrix (Fin n) (Fin n) ℂ)) :
    x ≤ 1 := by
  classical
  let M : Fin n → Fin n → ℝ :=
    fun j k => -(rowOuterGramSample U i j k - finiteIdMatrix j k)
  let N : Fin n → Fin n → ℝ := fun j k => finiteIdMatrix j k
  have hMsym : IsSymmetricFiniteMatrix M := by
    intro j k
    dsimp [M]
    have hsym := rowOuterGramSample_centered_symmetric U i j k
    simpa using congrArg Neg.neg hsym
  have hNsym : IsSymmetricFiniteMatrix N := by
    intro j k
    by_cases h : j = k
    · subst h
      simp [N, finiteIdMatrix]
    · have hk : k ≠ j := Ne.symm h
      simp [N, finiteIdMatrix, h, hk]
  have hLe : finiteLoewnerLe M N := by
    simpa [M, N] using
      leverage_rowOuterGramSample_neg_centered_finiteLoewnerLe_one U hU hn i
  have hCLe :
      finiteComplexCStarMatrix M ≤
        (1 : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
    have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M N hMsym hNsym hLe
    simpa [N, finiteComplexCStarMatrix_finiteIdMatrix] using hC
  have hMembed :
      finiteComplexCStarMatrix M =
        -finiteComplexCStarMatrix
          (fun j k : Fin n =>
            rowOuterGramSample U i j k - finiteIdMatrix j k) := by
    ext j k
    simp [M]
  have hxM :
      x ∈ spectrum ℝ (finiteComplexCStarMatrix M) := by
    simpa [hMembed] using hx
  exact cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxM
























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Positive `gammaValid` horizons imply the unit roundoff is below one.

This small adapter lets concrete square-root denominator certificates use the
same sample-count roundoff guard as the downstream dot-product analysis. -/
theorem unitRoundoff_lt_one_of_pos_gammaValid
    (fp : FPModel) {s : ℕ} (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) :
    fp.u < 1 := by
  have hsNat : 0 < s := by exact_mod_cast hs
  have hone_le_s_nat : 1 ≤ s := Nat.succ_le_iff.mpr hsNat
  have hone_le_s : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hone_le_s_nat
  have hu_le_su : fp.u ≤ (s : ℝ) * fp.u := by
    simpa using mul_le_mul_of_nonneg_right hone_le_s fp.u_nonneg
  have hsu_lt_one : (s : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hγ
  exact lt_of_le_of_lt hu_le_su hsu_lt_one

/-- Concrete leverage-score denominator routine for Algorithm 2 equation (7).

The probability table remains the exact leverage-score law by project
convention.  The non-probability denominator used by the implementation is the
rounded routine `fl_sqrt (fl_mul s p_i)`, and the constructor below carries the
proved absolute denominator-error bound for that routine. -/
noncomputable def leverageFlMulThenSqrtRowScaleDen
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s) :
    ComputedRowScaleDen fp s (rowSqNormProb U) :=
  ComputedRowScaleDen.flMulThenSqrt fp s (rowSqNormProb U)
    (rowSqNormProb_nonneg U
      (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn))
    hs (unitRoundoff_lt_one_of_pos_gammaValid fp hs hγ)

@[simp] theorem leverageFlMulThenSqrtRowScaleDen_den
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s) :
    (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den =
      fun i => fp.fl_sqrt (fp.fl_mul (s : ℝ) (rowSqNormProb U i)) := rfl
























































end NumStability
