-- Algorithms/LeastSquares/LSPerturbation.lean
--
-- Perturbation theory for the least squares problem (Higham §20.1).
--
-- Theorem 20.1 (Wedin): Normwise perturbation bounds for the LS solution.
--   ‖x−y‖/‖x‖ ≤ κ₂(A)ε/(1−κ₂(A)ε) · (2 + (κ₂(A)+1)‖r‖/(‖A‖‖x‖))
--   ‖r−s‖/‖b‖ ≤ (1+2κ₂(A))ε
--
-- Theorem 20.2: Componentwise perturbation via the augmented system
--   [I A; Aᵀ 0][r; x] = [b; 0].
--
-- The full Wedin theorem still requires the project-local SVD, pseudoinverse,
-- and projector perturbation route.  The scalar source right-hand sides below
-- are proved infrastructure, while the older structures remain only as legacy
-- contract packages.

import Mathlib.Data.Real.Basic
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Analysis.Norms

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §20.1  Theorem 20.1 (Wedin): Normwise LS perturbation
-- ============================================================

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1):
    scalar right-hand side of Wedin's relative solution perturbation bound. -/
noncomputable def wedinTheorem20_1SolutionRelativeRHS
    (kappa eps A_norm x_norm r_norm : ℝ) : ℝ :=
  (kappa * eps) / (1 - kappa * eps) *
    (2 + (kappa + 1) * r_norm / (A_norm * x_norm))

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    scalar right-hand side of Wedin's relative residual perturbation bound. -/
def wedinTheorem20_1ResidualRelativeRHS (kappa eps : ℝ) : ℝ :=
  (1 + 2 * kappa) * eps

/-- The small-perturbation condition in Theorem 20.1 makes the denominator in
    equation (20.1) positive. -/
theorem wedinTheorem20_1_denominator_pos {kappa eps : ℝ}
    (hsmall : kappa * eps < 1) :
    0 < 1 - kappa * eps := by
  linarith

/-- The denominator in Wedin's equation (20.1) is nonzero under the printed
    small-perturbation hypothesis. -/
theorem wedinTheorem20_1_denominator_ne_zero {kappa eps : ℝ}
    (hsmall : kappa * eps < 1) :
    1 - kappa * eps ≠ 0 :=
  (wedinTheorem20_1_denominator_pos hsmall).ne'

/-- Under the natural norm-domain assumptions, Wedin's equation (20.1)
    right-hand side is a nonnegative scalar bound. -/
theorem wedinTheorem20_1_solutionRelativeRHS_nonneg {kappa eps A_norm x_norm r_norm : ℝ}
    (hkappa : 0 ≤ kappa) (heps : 0 ≤ eps) (hsmall : kappa * eps < 1)
    (hA : 0 < A_norm) (hx : 0 < x_norm) (hr : 0 ≤ r_norm) :
    0 ≤ wedinTheorem20_1SolutionRelativeRHS kappa eps A_norm x_norm r_norm := by
  unfold wedinTheorem20_1SolutionRelativeRHS
  have hnum : 0 ≤ kappa * eps := mul_nonneg hkappa heps
  have hden_pos : 0 < 1 - kappa * eps :=
    wedinTheorem20_1_denominator_pos hsmall
  have hfrac : 0 ≤ (kappa * eps) / (1 - kappa * eps) :=
    div_nonneg hnum (le_of_lt hden_pos)
  have hAx_pos : 0 < A_norm * x_norm := mul_pos hA hx
  have hkappa_one_nonneg : 0 ≤ kappa + 1 := by linarith
  have hterm : 0 ≤ (kappa + 1) * r_norm / (A_norm * x_norm) :=
    div_nonneg (mul_nonneg hkappa_one_nonneg hr) (le_of_lt hAx_pos)
  have hparen : 0 ≤ 2 + (kappa + 1) * r_norm / (A_norm * x_norm) := by
    linarith
  exact mul_nonneg hfrac hparen

/-- Under the natural condition-number and roundoff-domain assumptions,
    Wedin's equation (20.2) right-hand side is nonnegative. -/
theorem wedinTheorem20_1_residualRelativeRHS_nonneg {kappa eps : ℝ}
    (hkappa : 0 ≤ kappa) (heps : 0 ≤ eps) :
    0 ≤ wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  unfold wedinTheorem20_1ResidualRelativeRHS
  have hfactor : 0 ≤ 1 + 2 * kappa := by nlinarith
  exact mul_nonneg hfactor heps

/-- With zero data perturbation budget, the scalar RHS of Wedin's equation
    (20.1) vanishes. -/
@[simp] theorem wedinTheorem20_1_solutionRelativeRHS_zero_eps
    (kappa A_norm x_norm r_norm : ℝ) :
    wedinTheorem20_1SolutionRelativeRHS kappa 0 A_norm x_norm r_norm = 0 := by
  simp [wedinTheorem20_1SolutionRelativeRHS]

/-- With zero data perturbation budget, the scalar RHS of Wedin's equation
    (20.2) vanishes. -/
@[simp] theorem wedinTheorem20_1_residualRelativeRHS_zero_eps (kappa : ℝ) :
    wedinTheorem20_1ResidualRelativeRHS kappa 0 = 0 := by
  simp [wedinTheorem20_1ResidualRelativeRHS]

/-- In the zero-residual case, Wedin's equation (20.1) loses the residual
    amplification term and reduces to the `2 κ ε / (1 - κ ε)` factor. -/
theorem wedinTheorem20_1_solutionRelativeRHS_of_zero_residual
    (kappa eps A_norm x_norm : ℝ) :
    wedinTheorem20_1SolutionRelativeRHS kappa eps A_norm x_norm 0 =
      2 * ((kappa * eps) / (1 - kappa * eps)) := by
  simp [wedinTheorem20_1SolutionRelativeRHS, mul_comm]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    the smallness hypothesis `η < 1` makes the reciprocal denominator positive. -/
theorem wedinLemma20_11_denominator_pos {eta : ℝ} (hsmall : eta < 1) :
    0 < 1 - eta := by
  linarith

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    column-side least singular value for a real rectangular matrix with
    nonempty column dimension, viewed through the repository's complexified
    singular-value API. -/
noncomputable def wedinLemma20_11_sigmaMinCol
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ) : ℝ :=
  complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    the column-side least singular value is nonnegative. -/
theorem wedinLemma20_11_sigmaMinCol_nonneg
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ) :
    0 ≤ wedinLemma20_11_sigmaMinCol A := by
  simpa [wedinLemma20_11_sigmaMinCol] using
    complexMatrixSingularValue_nonneg (realRectToCMatrix A) (Fin.last k)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    the least singular value gives the lower vector-action radius for a real
    rectangular matrix with nonempty column dimension. -/
theorem wedinLemma20_11_sigmaMinCol_mul_vecNorm2_le_rectMatMulVec
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    (x : Fin (k + 1) → ℝ) :
    wedinLemma20_11_sigmaMinCol A * vecNorm2 x ≤
      vecNorm2 (rectMatMulVec A x) := by
  have h :=
    complexMatrixSingularValue_last_mul_norm_le_norm_euclideanLin
      (realRectToCMatrix A) (realVecToEuclidean x)
  rw [realVecToEuclidean_norm] at h
  rw [realRectToCMatrix_euclideanLin_realVecToEuclidean_norm] at h
  simpa [wedinLemma20_11_sigmaMinCol] using h

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    injectivity of the real rectangular action makes the full-column
    `sigma_min` positive. -/
theorem wedinLemma20_11_sigmaMinCol_pos_of_rectMatMulVec_injective
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    (hinj : Function.Injective (rectMatMulVec A)) :
    0 < wedinLemma20_11_sigmaMinCol A := by
  by_contra hnot
  have hsigma_zero : wedinLemma20_11_sigmaMinCol A = 0 :=
    le_antisymm (le_of_not_gt hnot) (wedinLemma20_11_sigmaMinCol_nonneg A)
  obtain ⟨x, hx_ne, hsq⟩ :=
    realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq A
  have hsing_zero :
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) = 0 := by
    simpa [wedinLemma20_11_sigmaMinCol] using hsigma_zero
  have hx_action_zero : rectMatMulVec A x = 0 := by
    apply funext
    apply (vecNorm2_eq_zero_iff (rectMatMulVec A x)).1
    apply (sq_eq_zero_iff).1
    rw [vecNorm2_sq, hsq, hsing_zero]
    ring
  have hx_zero : x = 0 := by
    have h0 : rectMatMulVec A x = rectMatMulVec A (fun _j => 0) := by
      rw [hx_action_zero]
      ext i
      simp [rectMatMulVec]
    exact hinj h0
  exact hx_ne hx_zero

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    triangle-inequality core behind the singular-value perturbation step.

    If `A` has lower action radius `sigma` and the perturbation `Delta` has
    rectangular operator-2 radius `delta`, then `A + Delta` has lower action
    radius `sigma - delta`.  This is a proved local adapter toward the source
    line `sigma_r(B) >= sigma_r(A) - ||A-B||_2`; it does not by itself identify
    `sigma` with a singular value or prove rank preservation. -/
theorem wedinLemma20_11_lowerActionBound_of_rectOpNorm2Le
    {m n : ℕ} (A Delta : Fin m → Fin n → ℝ) {sigma delta : ℝ}
    (hlower : ∀ x : Fin n → ℝ,
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x))
    (hDelta : rectOpNorm2Le Delta delta) :
    ∀ x : Fin n → ℝ,
      (sigma - delta) * vecNorm2 x ≤
        vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) := by
  intro x
  have hsplit :
      rectMatMulVec (fun i j => A i j + Delta i j) x =
        fun i => rectMatMulVec A x i + rectMatMulVec Delta x i :=
    rectMatMulVec_mat_add A Delta x
  have hA_decomp :
      rectMatMulVec A x =
        fun i =>
          rectMatMulVec (fun i j => A i j + Delta i j) x i -
            rectMatMulVec Delta x i := by
    ext i
    rw [congrFun hsplit i]
    ring
  have htri :
      vecNorm2 (rectMatMulVec A x) ≤
        vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) +
          vecNorm2 (rectMatMulVec Delta x) := by
    calc
      vecNorm2 (rectMatMulVec A x)
          = vecNorm2
              (fun i =>
                rectMatMulVec (fun i j => A i j + Delta i j) x i -
                  rectMatMulVec Delta x i) := by
            rw [hA_decomp]
      _ ≤ vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) +
            vecNorm2 (fun i => -rectMatMulVec Delta x i) := by
            have h := vecNorm2_add_le
              (rectMatMulVec (fun i j => A i j + Delta i j) x)
              (fun i => -rectMatMulVec Delta x i)
            simpa [sub_eq_add_neg] using h
      _ = vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) +
            vecNorm2 (rectMatMulVec Delta x) := by
            rw [vecNorm2_neg]
  have hlower_x := hlower x
  have hDelta_x := hDelta x
  have hleft :
      sigma * vecNorm2 x - delta * vecNorm2 x ≤
        vecNorm2 (rectMatMulVec A x) -
          vecNorm2 (rectMatMulVec Delta x) := by
    linarith
  have hright :
      vecNorm2 (rectMatMulVec A x) -
          vecNorm2 (rectMatMulVec Delta x) ≤
        vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) := by
    linarith
  calc
    (sigma - delta) * vecNorm2 x =
        sigma * vecNorm2 x - delta * vecNorm2 x := by
          ring
    _ ≤ vecNorm2 (rectMatMulVec A x) -
          vecNorm2 (rectMatMulVec Delta x) := hleft
    _ ≤ vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) := hright

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    source-shaped lower action perturbation with `B - A` as the perturbation.

    This is the same triangle-inequality step as
    `wedinLemma20_11_lowerActionBound_of_rectOpNorm2Le`, rewritten in the
    orientation used in the source proof of Lemma 20.11. -/
theorem wedinLemma20_11_lowerActionBound_of_sub_rectOpNorm2Le
    {m n : ℕ} (A B : Fin m → Fin n → ℝ) {sigma delta : ℝ}
    (hlower : ∀ x : Fin n → ℝ,
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta) :
    ∀ x : Fin n → ℝ,
      (sigma - delta) * vecNorm2 x ≤ vecNorm2 (rectMatMulVec B x) := by
  intro x
  have h :=
    wedinLemma20_11_lowerActionBound_of_rectOpNorm2Le
      A (fun i j => B i j - A i j) hlower hDelta x
  have hmat : (fun i j => A i j + (B i j - A i j)) = B := by
    ext i j
    ring
  simpa [hmat] using h

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column singular-value perturbation line.

    For real rectangular matrices with nonempty column dimension, a rectangular
    operator-2 bound on `B - A` gives
    `sigma_min(A) - delta <= sigma_min(B)`.  This is the source line
    `sigma_r(B) >= sigma_r(A) - ||A-B||_2` specialized to the full-column-rank
    indexing surface used by least-squares applications. -/
theorem wedinLemma20_11_sigmaMinCol_sub_le_sigmaMinCol_of_sub_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta) :
    wedinLemma20_11_sigmaMinCol A - delta ≤
      wedinLemma20_11_sigmaMinCol B := by
  by_cases hnonneg : 0 ≤ wedinLemma20_11_sigmaMinCol A - delta
  · obtain ⟨x, hx_ne, hsq⟩ :=
      realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq B
    have hx_norm_ne : vecNorm2 x ≠ 0 := by
      intro hx_norm
      apply hx_ne
      ext j
      exact (vecNorm2_eq_zero_iff x).mp hx_norm j
    have hx_norm_pos : 0 < vecNorm2 x :=
      lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hx_norm_ne)
    have hB_lower :=
      wedinLemma20_11_lowerActionBound_of_sub_rectOpNorm2Le
        A B (wedinLemma20_11_sigmaMinCol_mul_vecNorm2_le_rectMatMulVec A)
        hDelta x
    have hB_norm_eq :
        vecNorm2 (rectMatMulVec B x) =
          wedinLemma20_11_sigmaMinCol B * vecNorm2 x := by
      apply (sq_eq_sq₀
        (vecNorm2_nonneg (rectMatMulVec B x))
        (mul_nonneg (wedinLemma20_11_sigmaMinCol_nonneg B)
          (vecNorm2_nonneg x))).mp
      calc
        vecNorm2 (rectMatMulVec B x) ^ 2 =
            vecNorm2Sq (rectMatMulVec B x) := vecNorm2_sq _
        _ = (wedinLemma20_11_sigmaMinCol B) ^ 2 * vecNorm2Sq x := by
            simpa [wedinLemma20_11_sigmaMinCol] using hsq
        _ = (wedinLemma20_11_sigmaMinCol B) ^ 2 * vecNorm2 x ^ 2 := by
            rw [← vecNorm2_sq x]
        _ = (wedinLemma20_11_sigmaMinCol B * vecNorm2 x) ^ 2 := by
            ring
    have hmul :
        (wedinLemma20_11_sigmaMinCol A - delta) * vecNorm2 x ≤
          wedinLemma20_11_sigmaMinCol B * vecNorm2 x := by
      simpa [hB_norm_eq] using hB_lower
    nlinarith
  · have hB_nonneg := wedinLemma20_11_sigmaMinCol_nonneg B
    linarith

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    a strict full-column perturbation below `sigma_min(A)` makes
    `sigma_min(B)` positive. -/
theorem wedinLemma20_11_sigmaMinCol_pos_of_sub_rectOpNorm2Le_lt
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hsmall : delta < wedinLemma20_11_sigmaMinCol A) :
    0 < wedinLemma20_11_sigmaMinCol B := by
  have hgap :=
    wedinLemma20_11_sigmaMinCol_sub_le_sigmaMinCol_of_sub_rectOpNorm2Le
      A B hDelta
  have hpos : 0 < wedinLemma20_11_sigmaMinCol A - delta := by
    linarith
  exact lt_of_lt_of_le hpos hgap

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    strict perturbations below a lower action radius preserve injectivity.

    This is a full-column-rank consequence of the source singular-value
    perturbation line.  It is not the general equal-rank pseudoinverse theorem,
    but it gives the rank-preservation bridge needed by full-rank LS uses of
    Wedin's theorem. -/
theorem wedinLemma20_11_rectMatMulVec_injective_of_sub_rectOpNorm2Le_lt
    {m n : ℕ} (A B : Fin m → Fin n → ℝ) {sigma delta : ℝ}
    (hlower : ∀ x : Fin n → ℝ,
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hsmall : delta < sigma) :
    Function.Injective (rectMatMulVec B) := by
  have h :=
    rectMatMulVec_injective_of_lower_bound_and_rectOpNorm2Le_lt
      (M := A) (Delta := fun i j => B i j - A i j)
      hlower hDelta hsmall
  have hmat : (fun i j => A i j + (B i j - A i j)) = B := by
    ext i j
    ring
  simpa [hmat] using h

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    scalar rearrangement step from the singular-value perturbation lower bound.

    The missing spectral input is the hypothesis `sigmaA - delta <= sigmaB`,
    where `delta = ||A - B||₂`, `sigmaA = ||A⁺||₂⁻¹`, and
    `sigmaB = ||B⁺||₂⁻¹`.  This theorem proves only the source's final
    reciprocal algebra, not the singular-value perturbation theorem itself. -/
theorem wedinLemma20_11_pinvNorm_le_of_singularValue_gap
    {Aplus_norm Bplus_norm delta eta sigmaA sigmaB : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hsigmaA : sigmaA = 1 / Aplus_norm)
    (hBplus : Bplus_norm = 1 / sigmaB)
    (hgap : sigmaA - delta ≤ sigmaB) :
    Bplus_norm ≤ Aplus_norm / (1 - eta) := by
  subst eta
  have hden_pos : 0 < 1 - Aplus_norm * delta :=
    wedinLemma20_11_denominator_pos hsmall
  have hdelta_lt : delta < 1 / Aplus_norm := by
    rw [lt_div_iff₀ hAplus_pos]
    simpa [mul_comm] using hsmall
  have hgap_pos : 0 < sigmaA - delta := by
    rw [hsigmaA]
    linarith
  have hrecip : 1 / sigmaB ≤ 1 / (sigmaA - delta) :=
    one_div_le_one_div_of_le hgap_pos hgap
  rw [hBplus]
  calc
    1 / sigmaB ≤ 1 / (sigmaA - delta) := hrecip
    _ = Aplus_norm / (1 - Aplus_norm * delta) := by
      rw [hsigmaA]
      field_simp [ne_of_gt hAplus_pos, ne_of_gt hden_pos]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column specialization of the pseudoinverse norm bound.

    Compared with `wedinLemma20_11_pinvNorm_le_of_singularValue_gap`, this
    theorem proves the singular-value perturbation step locally for real
    rectangular matrices with nonempty column dimension.  The remaining
    assumptions are exactly the reciprocal identifications between the
    column-side `sigma_min` values and the displayed pseudoinverse norms. -/
theorem wedinLemma20_11_fullColumn_pinvNorm_le_of_sub_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    {Aplus_norm Bplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_sigma :
      wedinLemma20_11_sigmaMinCol A = 1 / Aplus_norm)
    (hBplus_sigma :
      Bplus_norm = 1 / wedinLemma20_11_sigmaMinCol B) :
    Bplus_norm ≤ Aplus_norm / (1 - eta) :=
  wedinLemma20_11_pinvNorm_le_of_singularValue_gap
    (Aplus_norm := Aplus_norm) (Bplus_norm := Bplus_norm)
    (delta := delta) (eta := eta)
    (sigmaA := wedinLemma20_11_sigmaMinCol A)
    (sigmaB := wedinLemma20_11_sigmaMinCol B)
    hAplus_pos heta hsmall hAplus_sigma hBplus_sigma
    (wedinLemma20_11_sigmaMinCol_sub_le_sigmaMinCol_of_sub_rectOpNorm2Le
      A B hDelta)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column injectivity and the reciprocal identification make the
    displayed pseudoinverse norm positive. -/
theorem wedinLemma20_11_Aplus_norm_pos_of_injective_sigmaMinCol_recip
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ) {Aplus_norm : ℝ}
    (hAinj : Function.Injective (rectMatMulVec A))
    (hAplus_sigma :
      wedinLemma20_11_sigmaMinCol A = 1 / Aplus_norm) :
    0 < Aplus_norm := by
  apply one_div_pos.mp
  rw [← hAplus_sigma]
  exact wedinLemma20_11_sigmaMinCol_pos_of_rectMatMulVec_injective A hAinj

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    under the full-column reciprocal identification, `η = ||A⁺||₂ delta`
    and `η < 1` imply `delta < sigma_min(A)`. -/
theorem wedinLemma20_11_delta_lt_sigmaMinCol_of_injective_eta_lt_one
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAinj : Function.Injective (rectMatMulVec A))
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hAplus_sigma :
      wedinLemma20_11_sigmaMinCol A = 1 / Aplus_norm) :
    delta < wedinLemma20_11_sigmaMinCol A := by
  have hAplus_pos :
      0 < Aplus_norm :=
    wedinLemma20_11_Aplus_norm_pos_of_injective_sigmaMinCol_recip
      A hAinj hAplus_sigma
  have hdelta_lt : delta < 1 / Aplus_norm := by
    rw [lt_div_iff₀ hAplus_pos]
    rw [heta] at hsmall
    simpa [mul_comm] using hsmall
  simpa [hAplus_sigma] using hdelta_lt

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    the source smallness condition preserves positivity of the perturbed
    full-column lower singular value. -/
theorem wedinLemma20_11_sigmaMinCol_B_pos_of_injective_eta_lt_one
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAinj : Function.Injective (rectMatMulVec A))
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_sigma :
      wedinLemma20_11_sigmaMinCol A = 1 / Aplus_norm) :
    0 < wedinLemma20_11_sigmaMinCol B :=
  wedinLemma20_11_sigmaMinCol_pos_of_sub_rectOpNorm2Le_lt A B hDelta
    (wedinLemma20_11_delta_lt_sigmaMinCol_of_injective_eta_lt_one
      A hAinj heta hsmall hAplus_sigma)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column source-shaped pseudoinverse norm perturbation wrapper.

    This version derives the pseudoinverse-norm positivity side condition from
    full-column injectivity of `A` and the reciprocal `sigma_min(A)` identity.
    The still-open pseudoinverse foundations remain explicit as the reciprocal
    norm/singular-value identifications for `A` and `B`. -/
theorem wedinLemma20_11_fullColumn_pinvNorm_le_of_injective_sub_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    {Aplus_norm Bplus_norm delta eta : ℝ}
    (hAinj : Function.Injective (rectMatMulVec A))
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_sigma :
      wedinLemma20_11_sigmaMinCol A = 1 / Aplus_norm)
    (hBplus_sigma :
      Bplus_norm = 1 / wedinLemma20_11_sigmaMinCol B) :
    Bplus_norm ≤ Aplus_norm / (1 - eta) :=
  wedinLemma20_11_fullColumn_pinvNorm_le_of_sub_rectOpNorm2Le
    A B
    (wedinLemma20_11_Aplus_norm_pos_of_injective_sigmaMinCol_recip
      A hAinj hAplus_sigma)
    heta hsmall hDelta hAplus_sigma hBplus_sigma

/-- **Theorem 20.1 (Wedin)**: Normwise perturbation of the LS solution.

    Let A ∈ ℝ^{m×n} (m ≥ n) and A + ΔA both be of full rank, with
    ‖ΔA‖₂ ≤ ε‖A‖₂ and ‖Δb‖₂ ≤ ε‖b‖₂. Then:

    ‖x−y‖₂/‖x‖₂ ≤ κ₂(A)·ε/(1−κ₂(A)·ε) · (2 + (κ₂(A)+1)·‖r‖₂/(‖A‖₂·‖x‖₂))
    ‖r−s‖₂/‖b‖₂ ≤ (1 + 2κ₂(A))·ε

    where r = b − Ax, s = b + Δb − (A+ΔA)y.

    The bound shows sensitivity is κ₂(A) when the residual is small
    (nearly consistent system) and κ₂(A)² when the residual is large.

    Legacy contract package only: the source-exact Wedin theorem still remains
    open until the SVD, pseudoinverse, and projector perturbation foundations
    are closed. -/
structure WedinPerturbationBound (n : ℕ)
    (x y : Fin n → ℝ) (kappa eps : ℝ)
    (sol_bound res_bound : ℝ) : Prop where
  /-- κ₂(A) > 0. -/
  kappa_pos : 0 < kappa
  /-- The perturbation is small enough: κ₂(A)·ε < 1. -/
  small_pert : kappa * eps < 1
  /-- Solution perturbation bound (eq 20.1):
      ‖x−y‖ ≤ sol_bound where sol_bound depends on κ₂(A), ε, ‖r‖, ‖A‖, ‖x‖. -/
  solution : ∀ i, |y i - x i| ≤ sol_bound
  /-- Residual perturbation bound (eq 20.2):
      ‖r−s‖ ≤ res_bound where res_bound ≤ (1+2κ₂(A))·ε·‖b‖. -/
  residual_bound_val : res_bound ≤ (1 + 2 * kappa) * eps

-- ============================================================
-- §20.1  Theorem 20.2: Componentwise LS perturbation
-- ============================================================

/-- **Augmented system for the LS problem** (Higham eq 20.3).

    The LS solution x and residual r = b − Ax satisfy the
    (m+n)×(m+n) augmented system:

    [I  A ][r]   [b]
    [Aᵀ 0 ][x] = [0]

    This is equivalent to the normal equations AᵀAx = Aᵀb.

    The inverse of the augmented system matrix has blocks
    involving A⁺ and (AᵀA)⁻¹ (eq 19.6), enabling componentwise
    perturbation analysis.

    We capture the componentwise perturbation result (Theorem 20.2)
    in terms of the n×n Gram inverse (AᵀA)⁻¹, which is representable
    in the library's square-matrix framework. -/
structure LSAugmentedPerturbation (n : ℕ)
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (eps : ℝ)
    (bound_vec : Fin n → ℝ) : Prop where
  /-- (AᵀA)⁻¹ is the inverse of the Gram matrix. -/
  gram_inv : IsInverse n ATA ATA_inv
  /-- The perturbation ε is nonneg. -/
  eps_nonneg : 0 ≤ eps
  /-- Componentwise bound on the solution perturbation (eq 19.8):
      |y_i − x_i| ≤ ε · bound_vec_i
      where bound_vec captures the |(AᵀA)⁻¹|-weighted perturbation. -/
  solution_bound : ∀ i, |y i - x i| ≤ eps * bound_vec i

end LeanFpAnalysis.FP
