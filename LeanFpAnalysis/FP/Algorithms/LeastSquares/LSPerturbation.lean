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
import LeanFpAnalysis.FP.Analysis.HighamChapter7

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

/-- Conservative scalar right-hand side produced by the current one-sided
    Lemma 20.12 route toward Wedin's equation (20.1).

The second residual term keeps the extra `1 / (1 - κ ε)` factor that remains
until the full Lemma 20.12 equality/min surface is formalized. -/
noncomputable def wedinTheorem20_1SolutionRelativeRHSConservative
    (kappa eps A_norm x_norm r_norm : ℝ) : ℝ :=
  (kappa * eps) / (1 - kappa * eps) *
    (2 + r_norm / (A_norm * x_norm)) +
  (kappa ^ 2 * eps) / (1 - kappa * eps) ^ 2 *
    (r_norm / (A_norm * x_norm))

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

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1), scalar
    normalization for the currently proved one-sided Wedin vector route.

This theorem converts the vector estimate with forcing radii
`DeltaA_norm <= eps*A_norm` and
`Deltab_norm <= eps*(A_norm*x_norm + r_norm)` into the conservative relative
RHS above.  It deliberately does not collapse to the printed (20.1) RHS; that
requires the remaining full Lemma 20.12 equality/min step. -/
theorem wedinTheorem20_1_solutionRelativeRHSConservative_of_vector_bound
    {sol_norm Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm x_norm
      r_norm eta : ℝ}
    (hAplus_nonneg : 0 ≤ Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (hx_norm_pos : 0 < x_norm)
    (hkappa : kappa = Aplus_norm * A_norm)
    (heta : eta = kappa * eps)
    (hsmall : kappa * eps < 1)
    (hDeltaA_norm : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm : Deltab_norm ≤ eps * (A_norm * x_norm + r_norm))
    (hvec :
      sol_norm ≤
        (Aplus_norm / (1 - eta)) *
            (DeltaA_norm * x_norm + Deltab_norm) +
          (eta * Aplus_norm / (1 - eta) ^ 2) * r_norm) :
    sol_norm / x_norm ≤
      wedinTheorem20_1SolutionRelativeRHSConservative
        kappa eps A_norm x_norm r_norm := by
  have hden_eta_pos : 0 < 1 - eta := by
    rw [heta]
    exact wedinTheorem20_1_denominator_pos hsmall
  have hcoef_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg hAplus_nonneg (le_of_lt hden_eta_pos)
  have hDeltaA_x :
      DeltaA_norm * x_norm ≤ (eps * A_norm) * x_norm :=
    mul_le_mul_of_nonneg_right hDeltaA_norm (le_of_lt hx_norm_pos)
  have hinside :
      DeltaA_norm * x_norm + Deltab_norm ≤
        (eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm) :=
    add_le_add hDeltaA_x hDeltab_norm
  have hforcing :
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * x_norm + Deltab_norm) ≤
        (Aplus_norm / (1 - eta)) *
          ((eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm)) :=
    mul_le_mul_of_nonneg_left hinside hcoef_nonneg
  have hvec_scalar :
      sol_norm ≤
        (Aplus_norm / (1 - eta)) *
            ((eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm)) +
          (eta * Aplus_norm / (1 - eta) ^ 2) * r_norm :=
    hvec.trans (add_le_add hforcing (le_refl _))
  calc
    sol_norm / x_norm
        ≤ ((Aplus_norm / (1 - eta)) *
            ((eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm)) +
          (eta * Aplus_norm / (1 - eta) ^ 2) * r_norm) / x_norm :=
            div_le_div_of_nonneg_right hvec_scalar (le_of_lt hx_norm_pos)
    _ = wedinTheorem20_1SolutionRelativeRHSConservative
        kappa eps A_norm x_norm r_norm := by
          unfold wedinTheorem20_1SolutionRelativeRHSConservative
          rw [heta, hkappa]
          field_simp [ne_of_gt hA_norm_pos, ne_of_gt hx_norm_pos,
            ne_of_gt hden_eta_pos]
          ring

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

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    any proved full-column lower action radius is bounded above by the
    repository's column-side `sigma_min`. -/
theorem wedinLemma20_11_lowerActionBound_le_sigmaMinCol
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ) {sigma : ℝ}
    (hlower : ∀ x : Fin (k + 1) → ℝ,
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x)) :
    sigma ≤ wedinLemma20_11_sigmaMinCol A := by
  by_cases hsigma_nonneg : 0 ≤ sigma
  · obtain ⟨x, hx_ne, hsq⟩ :=
      realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq A
    have hx_norm_ne : vecNorm2 x ≠ 0 := by
      intro hx_norm
      apply hx_ne
      ext j
      exact (vecNorm2_eq_zero_iff x).mp hx_norm j
    have hx_norm_pos : 0 < vecNorm2 x :=
      lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hx_norm_ne)
    have hA_norm_eq :
        vecNorm2 (rectMatMulVec A x) =
          wedinLemma20_11_sigmaMinCol A * vecNorm2 x := by
      apply (sq_eq_sq₀
        (vecNorm2_nonneg (rectMatMulVec A x))
        (mul_nonneg (wedinLemma20_11_sigmaMinCol_nonneg A)
          (vecNorm2_nonneg x))).mp
      calc
        vecNorm2 (rectMatMulVec A x) ^ 2 =
            vecNorm2Sq (rectMatMulVec A x) := vecNorm2_sq _
        _ = (wedinLemma20_11_sigmaMinCol A) ^ 2 * vecNorm2Sq x := by
            simpa [wedinLemma20_11_sigmaMinCol] using hsq
        _ = (wedinLemma20_11_sigmaMinCol A) ^ 2 * vecNorm2 x ^ 2 := by
            rw [← vecNorm2_sq x]
        _ = (wedinLemma20_11_sigmaMinCol A * vecNorm2 x) ^ 2 := by
            ring
    have hmul :
        sigma * vecNorm2 x ≤
          wedinLemma20_11_sigmaMinCol A * vecNorm2 x := by
      simpa [hA_norm_eq] using hlower x
    nlinarith
  · have hA_nonneg := wedinLemma20_11_sigmaMinCol_nonneg A
    linarith

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    an explicit left inverse `Aplus A = I` and an operator-norm bound on
    `Aplus` give the lower action radius `1 / Aplus_norm` for `A`. -/
theorem wedinLemma20_11_lowerActionBound_of_left_inverse_rectOpNorm2Le
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    {Aplus_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (hleft : rectMatMul Aplus A = idMatrix n)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm) :
    ∀ x : Fin n → ℝ,
      (1 / Aplus_norm) * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x) := by
  intro x
  have hleft_vec :
      rectMatMulVec Aplus (rectMatMulVec A x) = x := by
    rw [← rectMatMulVec_rectMatMul Aplus A x]
    rw [hleft]
    rw [rectMatMulVec_idMatrix]
  have hbound := hAplus (rectMatMulVec A x)
  have hx_bound :
      vecNorm2 x ≤ Aplus_norm * vecNorm2 (rectMatMulVec A x) := by
    simpa [hleft_vec] using hbound
  have hrec_nonneg : 0 ≤ 1 / Aplus_norm :=
    le_of_lt (one_div_pos.mpr hAplus_pos)
  calc
    (1 / Aplus_norm) * vecNorm2 x
        ≤ (1 / Aplus_norm) *
            (Aplus_norm * vecNorm2 (rectMatMulVec A x)) :=
          mul_le_mul_of_nonneg_left hx_bound hrec_nonneg
    _ = vecNorm2 (rectMatMulVec A x) := by
          field_simp [ne_of_gt hAplus_pos]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    source-shaped singular-value lower bound obtained from an explicit left
    inverse of `A` and a perturbation bound for `B - A`. -/
theorem wedinLemma20_11_recip_sub_le_sigmaMinCol_of_left_inverse_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus : Fin (k + 1) → Fin m → ℝ) {Aplus_norm delta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (hleft : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta) :
    1 / Aplus_norm - delta ≤ wedinLemma20_11_sigmaMinCol B := by
  have hlowerA :
      ∀ x : Fin (k + 1) → ℝ,
        (1 / Aplus_norm) * vecNorm2 x ≤
          vecNorm2 (rectMatMulVec A x) :=
    wedinLemma20_11_lowerActionBound_of_left_inverse_rectOpNorm2Le
      A Aplus hAplus_pos hleft hAplus
  have hlowerB :
      ∀ x : Fin (k + 1) → ℝ,
        (1 / Aplus_norm - delta) * vecNorm2 x ≤
          vecNorm2 (rectMatMulVec B x) :=
    wedinLemma20_11_lowerActionBound_of_sub_rectOpNorm2Le
      A B hlowerA hDelta
  exact wedinLemma20_11_lowerActionBound_le_sigmaMinCol B hlowerB

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column pseudoinverse norm perturbation from an explicit left inverse
    of `A` and an operator-norm bound on that left inverse.

    This removes the separate assumption
    `sigma_min(A) = 1 / ||Aplus||_2`; the remaining reciprocal identification
    is the perturbed-side norm identity for `Bplus`. -/
theorem wedinLemma20_11_fullColumn_pinvNorm_le_of_left_inverse_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm Bplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleft : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus_sigma :
      Bplus_norm = 1 / wedinLemma20_11_sigmaMinCol B) :
    Bplus_norm ≤ Aplus_norm / (1 - eta) :=
  wedinLemma20_11_pinvNorm_le_of_singularValue_gap
    (Aplus_norm := Aplus_norm) (Bplus_norm := Bplus_norm)
    (delta := delta) (eta := eta)
    (sigmaA := 1 / Aplus_norm)
    (sigmaB := wedinLemma20_11_sigmaMinCol B)
    hAplus_pos heta hsmall rfl hBplus_sigma
    (wedinLemma20_11_recip_sub_le_sigmaMinCol_of_left_inverse_rectOpNorm2Le
      A B Aplus hAplus_pos hleft hAplus hDelta)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    a lower action radius for `B`, together with the Moore-Penrose range-side
    projection conditions, bounds the rectangular operator norm of `Bplus`.

    The hypotheses `Bplus B = I` and symmetry of `B Bplus` are exactly the
    full-column Penrose fields needed to make the range projection
    nonexpansive. -/
theorem wedinLemma20_11_rectOpNorm2Le_left_inverse_of_lowerActionBound
    {m n : ℕ} (B : Fin m → Fin n → ℝ) (Bplus : Fin n → Fin m → ℝ)
    {sigma : ℝ}
    (hsigma_pos : 0 < sigma)
    (hlower : ∀ x : Fin n → ℝ,
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec B x))
    (hleft : rectMatMul Bplus B = idMatrix n)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (1 / sigma) := by
  intro y
  have hproj :=
    rectOpNorm2Le_rangeProjection_of_symmetric_left_inverse B Bplus
      hleft hSym y
  have hproj' :
      vecNorm2 (rectMatMulVec B (rectMatMulVec Bplus y)) ≤ vecNorm2 y := by
    simpa [rectMatMulVec_rectMatMul] using hproj
  have hlower_y := hlower (rectMatMulVec Bplus y)
  have hbound :
      sigma * vecNorm2 (rectMatMulVec Bplus y) ≤ vecNorm2 y :=
    le_trans hlower_y hproj'
  have hrec_nonneg : 0 ≤ 1 / sigma :=
    le_of_lt (one_div_pos.mpr hsigma_pos)
  calc
    vecNorm2 (rectMatMulVec Bplus y)
        = (1 / sigma) * (sigma * vecNorm2 (rectMatMulVec Bplus y)) := by
            field_simp [ne_of_gt hsigma_pos]
    _ ≤ (1 / sigma) * vecNorm2 y :=
            mul_le_mul_of_nonneg_left hbound hrec_nonneg

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column predicate-form pseudoinverse norm perturbation bound.

    This is the source Lemma 20.11 route in the repository's
    `rectOpNorm2Le` API: an explicit left inverse for `A`, the perturbation
    bound for `B - A`, and the full-column Penrose range-projection fields for
    `Bplus` imply `||Bplus||₂ <= ||Aplus||₂ / (1 - eta)`. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_left_inverse_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) := by
  subst eta
  have hden_pos : 0 < 1 - Aplus_norm * delta :=
    wedinLemma20_11_denominator_pos hsmall
  have hdelta_lt : delta < 1 / Aplus_norm := by
    rw [lt_div_iff₀ hAplus_pos]
    simpa [mul_comm] using hsmall
  have hmu_pos : 0 < 1 / Aplus_norm - delta := by
    linarith
  have hlowerA :
      ∀ x : Fin (k + 1) → ℝ,
        (1 / Aplus_norm) * vecNorm2 x ≤
          vecNorm2 (rectMatMulVec A x) :=
    wedinLemma20_11_lowerActionBound_of_left_inverse_rectOpNorm2Le
      A Aplus hAplus_pos hleftA hAplus
  have hlowerB :
      ∀ x : Fin (k + 1) → ℝ,
        (1 / Aplus_norm - delta) * vecNorm2 x ≤
          vecNorm2 (rectMatMulVec B x) :=
    wedinLemma20_11_lowerActionBound_of_sub_rectOpNorm2Le
      A B hlowerA hDelta
  have hBplus :
      rectOpNorm2Le Bplus (1 / (1 / Aplus_norm - delta)) :=
    wedinLemma20_11_rectOpNorm2Le_left_inverse_of_lowerActionBound
      B Bplus hmu_pos hlowerB hleftB hSymB
  have hcoeff :
      (Aplus_norm⁻¹ - delta)⁻¹ =
        Aplus_norm / (1 - Aplus_norm * delta) := by
    field_simp [ne_of_gt hAplus_pos, ne_of_gt hmu_pos, ne_of_gt hden_pos]
  simpa [one_div, hcoeff] using hBplus

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column predicate-form pseudoinverse perturbation bound with the
    perturbed-side left inverse derived from the first Penrose equation.

    The Chapter 7 Moore-Penrose bridge turns `B Bplus B = B` plus injectivity
    of `x ↦ B*x` into `Bplus B = I`, leaving the same range-projection
    symmetry condition used by the direct operator-bound theorem above. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_injective_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hBinj : Function.Injective (rectMatMulVec B))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) := by
  have hleftB : rectMatMul Bplus B = idMatrix (k + 1) := by
    ext i j
    simpa [rectMatMul, idMatrix] using
      theorem7_5_rect_left_inverse_of_penrose1_rectMatMulVec_injective
        B Bplus hBpenrose1 hBinj i j
  exact
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_left_inverse_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hleftB hSymB

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column predicate-form pseudoinverse perturbation bound with the
    perturbed-side injectivity derived from the smallness condition.

    The A-side left inverse and operator bound supply the lower action radius
    `1 / Aplus_norm`; the source smallness condition `eta = Aplus_norm * delta
    < 1` makes the perturbation strict enough to preserve injectivity of `B`.
    The first Penrose equation for `Bplus` then supplies the remaining
    perturbed-side left-inverse field. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_small_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) := by
  have hsmall_mul : Aplus_norm * delta < 1 := by
    simpa [heta] using hsmall
  have hdelta_lt : delta < 1 / Aplus_norm := by
    rw [lt_div_iff₀ hAplus_pos]
    simpa [mul_comm] using hsmall_mul
  have hlowerA :
      ∀ x : Fin (k + 1) → ℝ,
        (1 / Aplus_norm) * vecNorm2 x ≤
          vecNorm2 (rectMatMulVec A x) :=
    wedinLemma20_11_lowerActionBound_of_left_inverse_rectOpNorm2Le
      A Aplus hAplus_pos hleftA hAplus
  have hBinj : Function.Injective (rectMatMulVec B) :=
    wedinLemma20_11_rectMatMulVec_injective_of_sub_rectOpNorm2Le_lt
      A B hlowerA hDelta hdelta_lt
  exact
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_injective_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hBpenrose1 hBinj hSymB

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column predicate-form pseudoinverse perturbation bound with both
    rectangular left-inverse fields derived from Penrose1 data.

    On the `A` side, Penrose1 plus injectivity gives `Aplus A = I`; the
    smallness condition then preserves injectivity for `B`, and Penrose1 plus
    the Chapter 7 bridge gives `Bplus B = I`. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_Apenrose1_Bpenrose1_small_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hApenrose1 : rectMatMul (rectMatMul A Aplus) A = A)
    (hAinj : Function.Injective (rectMatMulVec A))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) := by
  have hleftA : rectMatMul Aplus A = idMatrix (k + 1) := by
    ext i j
    simpa [rectMatMul, idMatrix] using
      theorem7_5_rect_left_inverse_of_penrose1_rectMatMulVec_injective
        A Aplus hApenrose1 hAinj i j
  exact
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_small_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hBpenrose1 hSymB

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    matrix-rank source wrapper for the full-column predicate-form
    pseudoinverse perturbation bound.

    Full column rank of `A` is represented by `(Matrix.of A).rank = k + 1`;
    Chapter 7 turns that rank hypothesis and A-side Penrose1 into the explicit
    left inverse needed by the operator-bound route. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_Apenrose1_rank_Bpenrose1_small_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hApenrose1 : rectMatMul (rectMatMul A Aplus) A = A)
    (hArank : (Matrix.of A).rank = k + 1)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) :=
  wedinLemma20_11_rectOpNorm2Le_Bplus_of_Apenrose1_Bpenrose1_small_rectOpNorm2Le
    A B Aplus Bplus hAplus_pos heta hsmall hApenrose1
    (ch7_rectMatMulVec_injective_of_matrix_rank_eq_width A hArank)
    hAplus hDelta hBpenrose1 hSymB

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    applying the complement of a square projection is the vector residual
    `x - P*x`. -/
theorem wedinLemma20_12_rectMatMulVec_projectionComplement
    {m : ℕ} (P : Fin m → Fin m → ℝ) (x : Fin m → ℝ) :
    rectMatMulVec (fun i j => idMatrix m i j - P i j) x =
      fun i => x i - rectMatMulVec P x i := by
  ext i
  unfold rectMatMulVec
  calc
    (∑ j : Fin m, (idMatrix m i j - P i j) * x j)
        = (∑ j : Fin m, idMatrix m i j * x j) -
            ∑ j : Fin m, P i j * x j := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = x i - ∑ j : Fin m, P i j * x j := by
          have hid :
              (∑ j : Fin m, idMatrix m i j * x j) = x i := by
            simpa [rectMatMulVec] using
              congrFun (rectMatMulVec_idMatrix x) i
          rw [hid]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a symmetric Moore-Penrose range projection has a nonexpansive complement
    `I - A Aplus`. -/
theorem wedinLemma20_12_rectOpNorm2Le_projectionComplement_of_symmetric_left_inverse
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (hleft : rectMatMul Aplus A = idMatrix n)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul A Aplus)) :
    rectOpNorm2Le (fun i j => idMatrix m i j - rectMatMul A Aplus i j) 1 := by
  intro y
  have hbest :=
    rectMatMulVec_rangeProjection_residual_norm_le_range_residual_of_symmetric_left_inverse
      A Aplus hleft hSym y (fun _ : Fin n => 0)
  have hzero :
      (fun i : Fin m => y i - rectMatMulVec A (fun _ : Fin n => 0) i) = y := by
    ext i
    simp [rectMatMulVec]
  simpa [wedinLemma20_12_rectMatMulVec_projectionComplement, hzero] using hbest

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    reversing a matrix difference preserves a rectangular operator-2 bound. -/
theorem wedinLemma20_12_rectOpNorm2Le_sub_rev
    {m n : ℕ} (A B : Fin m → Fin n → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta) :
    rectOpNorm2Le (fun i j => A i j - B i j) delta := by
  intro x
  have hmul :
      rectMatMulVec (fun i j => A i j - B i j) x =
        fun i => -rectMatMulVec (fun i j => B i j - A i j) x i := by
    ext i
    unfold rectMatMulVec
    calc
      (∑ j : Fin n, (A i j - B i j) * x j)
          = ∑ j : Fin n, -((B i j - A i j) * x j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = -(∑ j : Fin n, (B i j - A i j) * x j) := by
              rw [Finset.sum_neg_distrib]
  rw [hmul]
  simpa [vecNorm2_neg] using hDelta x

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    one-sided projection perturbation bound from the source proof.

    This proves the elementary half
    `||(I - P_A) P_B||_2 <= ||A - B||_2 ||Bplus||_2` in the repository's
    predicate API.  The nontrivial CS-decomposition equality
    `||P_A(I-P_B)||_2 = ||P_B(I-P_A)||_2` is not claimed here. -/
theorem wedinLemma20_12_rectOpNorm2Le_complement_rangeProjection_mul_rangeProjection
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Bplus_norm : ℝ}
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j)
        (rectMatMul B Bplus))
      (delta * Bplus_norm) := by
  let IPA : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - rectMatMul A Aplus i j
  have hIPA :
      rectOpNorm2Le IPA 1 :=
    wedinLemma20_12_rectOpNorm2Le_projectionComplement_of_symmetric_left_inverse
      A Aplus hleftA hSymA
  have hIPA_A_zero : ∀ z : Fin (k + 1) → ℝ,
      rectMatMulVec IPA (rectMatMulVec A z) = 0 := by
    intro z
    have hfix :=
      rectMatMulVec_rangeProjection_apply_range_of_left_inverse A Aplus
        hleftA z
    rw [wedinLemma20_12_rectMatMulVec_projectionComplement]
    rw [hfix]
    ext i
    simp
  have hdelta_nonneg : 0 ≤ delta :=
    rectOpNorm2Le_radius_nonneg (M := fun i j => B i j - A i j) hDelta
  intro y
  let z : Fin (k + 1) → ℝ := rectMatMulVec Bplus y
  have hB_decomp :
      rectMatMulVec B z =
        fun i : Fin m =>
          rectMatMulVec (fun i j => B i j - A i j) z i +
            rectMatMulVec A z i := by
    ext i
    unfold rectMatMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hvec :
      rectMatMulVec
          (rectMatMul IPA (rectMatMul B Bplus)) y =
        rectMatMulVec IPA
          (rectMatMulVec (fun i j => B i j - A i j) z) := by
    calc
      rectMatMulVec (rectMatMul IPA (rectMatMul B Bplus)) y
          = rectMatMulVec IPA (rectMatMulVec (rectMatMul B Bplus) y) := by
              rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec IPA (rectMatMulVec B z) := by
              rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec IPA
            (fun i : Fin m =>
              rectMatMulVec (fun i j => B i j - A i j) z i +
                rectMatMulVec A z i) := by
              rw [hB_decomp]
      _ = fun i : Fin m =>
            rectMatMulVec IPA
                (rectMatMulVec (fun i j => B i j - A i j) z) i +
              rectMatMulVec IPA (rectMatMulVec A z) i := by
              rw [rectMatMulVec_add]
      _ = rectMatMulVec IPA
            (rectMatMulVec (fun i j => B i j - A i j) z) := by
              rw [hIPA_A_zero z]
              ext i
              simp
  have hproj :=
    hIPA (rectMatMulVec (fun i j => B i j - A i j) z)
  have hDelta_y := hDelta z
  have hBplus_y := hBplus y
  calc
    vecNorm2 (rectMatMulVec (rectMatMul IPA (rectMatMul B Bplus)) y)
        = vecNorm2
            (rectMatMulVec IPA
              (rectMatMulVec (fun i j => B i j - A i j) z)) := by
            rw [hvec]
    _ ≤ vecNorm2 (rectMatMulVec (fun i j => B i j - A i j) z) := by
            simpa using hproj
    _ ≤ delta * vecNorm2 z := hDelta_y
    _ ≤ delta * (Bplus_norm * vecNorm2 y) :=
            mul_le_mul_of_nonneg_left hBplus_y hdelta_nonneg
    _ = (delta * Bplus_norm) * vecNorm2 y := by ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    swapped one-sided projection perturbation bound from the source proof.

    This is the companion elementary half
    `||(I - P_B) P_A||_2 <= ||A - B||_2 ||Aplus||_2` in the repository's
    predicate API.  As above, this does not claim the nontrivial equality of
    the two cross-projection operator norms. -/
theorem wedinLemma20_12_rectOpNorm2Le_complement_rangeProjection_mul_rangeProjection_swapped
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Aplus_norm : ℝ}
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (fun i j => idMatrix m i j - rectMatMul B Bplus i j)
        (rectMatMul A Aplus))
      (delta * Aplus_norm) :=
  wedinLemma20_12_rectOpNorm2Le_complement_rangeProjection_mul_rangeProjection
    B A Bplus Aplus hleftB hSymB
    (wedinLemma20_12_rectOpNorm2Le_sub_rev A B hDelta)
    hAplus

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the complement of a symmetric projection is symmetric. -/
theorem wedinLemma20_12_projectionComplement_symmetric
    {m : ℕ} (P : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P) :
    IsSymmetricFiniteMatrix (fun i j => idMatrix m i j - P i j) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [idMatrix]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [idMatrix, hij, hji, hP i j]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    transposing a product of symmetric square matrices reverses the product
    order. -/
theorem wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q) :
    finiteTranspose (rectMatMul P Q) = rectMatMul Q P := by
  ext i j
  unfold finiteTranspose rectMatMul
  apply Finset.sum_congr rfl
  intro l _
  rw [hP j l, hQ l i]
  ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    source-oriented projection perturbation bound.

    This transposes the swapped one-sided half into the printed orientation
    `P_A (I - P_B)`, giving
    `||P_A(I-P_B)||_2 <= ||A-B||_2 ||Aplus||_2` in the repository predicate
    API.  The equality with the opposite cross-projection norm is still not
    claimed. -/
theorem wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Aplus_norm : ℝ}
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_norm_nonneg : 0 ≤ Aplus_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (rectMatMul A Aplus)
        (fun i j => idMatrix m i j - rectMatMul B Bplus i j))
      (delta * Aplus_norm) := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let IPB : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - rectMatMul B Bplus i j
  have hIPB_sym : IsSymmetricFiniteMatrix IPB :=
    wedinLemma20_12_projectionComplement_symmetric
      (rectMatMul B Bplus) hSymB
  have hhalf :
      rectOpNorm2Le (rectMatMul IPB PA) (delta * Aplus_norm) := by
    simpa [PA, IPB] using
      wedinLemma20_12_rectOpNorm2Le_complement_rangeProjection_mul_rangeProjection_swapped
        A B Aplus Bplus hleftB hSymB hDelta hAplus
  have hdelta_nonneg : 0 ≤ delta :=
    rectOpNorm2Le_radius_nonneg (M := fun i j => B i j - A i j) hDelta
  have htrans :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (rectMatMul IPB PA)
      (mul_nonneg hdelta_nonneg hAplus_norm_nonneg)
      hhalf
  have htranspose :
      finiteTranspose (rectMatMul IPB PA) = rectMatMul PA IPB :=
    wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric
      IPB PA hIPB_sym (by simpa [PA] using hSymA)
  rw [htranspose] at htrans
  simpa [PA, IPB] using htrans

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    source-oriented swapped projection perturbation bound.

    This transposes the direct one-sided half into the printed orientation
    `P_B (I - P_A)`, giving
    `||P_B(I-P_A)||_2 <= ||A-B||_2 ||Bplus||_2` in the repository predicate
    API. -/
theorem wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Bplus_norm : ℝ}
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (rectMatMul B Bplus)
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
      (delta * Bplus_norm) := by
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPA : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - rectMatMul A Aplus i j
  have hIPA_sym : IsSymmetricFiniteMatrix IPA :=
    wedinLemma20_12_projectionComplement_symmetric
      (rectMatMul A Aplus) hSymA
  have hhalf :
      rectOpNorm2Le (rectMatMul IPA PB) (delta * Bplus_norm) := by
    simpa [PB, IPA] using
      wedinLemma20_12_rectOpNorm2Le_complement_rangeProjection_mul_rangeProjection
        A B Aplus Bplus hleftA hSymA hDelta hBplus
  have hdelta_nonneg : 0 ≤ delta :=
    rectOpNorm2Le_radius_nonneg (M := fun i j => B i j - A i j) hDelta
  have htrans :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (rectMatMul IPA PB)
      (mul_nonneg hdelta_nonneg hBplus_norm_nonneg)
      hhalf
  have htranspose :
      finiteTranspose (rectMatMul IPA PB) = rectMatMul PB IPA :=
    wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric
      IPA PB hIPA_sym (by simpa [PB] using hSymB)
  rw [htranspose] at htrans
  simpa [PB, IPA] using htrans

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    the source-oriented Lemma 20.12 projector estimate controls `Bplus*r`
    whenever `r` is orthogonal to the range of `A`.

This is the local algebra behind `B⁺r = B⁺P_B(I-P_A)r`.  It deliberately
keeps the one-sided projector radius already proved above and does not claim
the missing CS-decomposition equality from the printed Lemma 20.12. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_residual_le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Bplus_norm : ℝ} (r : Fin m → ℝ)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2 (rectMatMulVec Bplus r) ≤
      (delta * Bplus_norm * Bplus_norm) * vecNorm2 r := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPA : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - PA i j
  have hBplusPB : rectMatMul Bplus PB = Bplus := by
    calc
      rectMatMul Bplus PB = rectMatMul Bplus (rectMatMul B Bplus) := by
        rfl
      _ = rectMatMul (rectMatMul Bplus B) Bplus := by
        rw [rectMatMul_assoc]
      _ = rectMatMul (idMatrix (k + 1)) Bplus := by
        rw [hleftB]
      _ = Bplus := rectMatMul_id_left Bplus
  have hIPA_r : rectMatMulVec IPA r = r := by
    rw [show IPA = (fun i j => idMatrix m i j - rectMatMul A Aplus i j) by
      ext i j
      rfl]
    rw [wedinLemma20_12_rectMatMulVec_projectionComplement]
    rw [hrangeA_residual]
    ext i
    simp
  have hfactor :
      rectMatMulVec Bplus r =
        rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r) := by
    symm
    calc
      rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r)
          = rectMatMulVec Bplus
              (rectMatMulVec PB (rectMatMulVec IPA r)) := by
              rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec Bplus (rectMatMulVec PB r) := by
              rw [hIPA_r]
      _ = rectMatMulVec (rectMatMul Bplus PB) r := by
              rw [← rectMatMulVec_rectMatMul]
      _ = rectMatMulVec Bplus r := by
              rw [hBplusPB]
  have hPBIPA :
      rectOpNorm2Le (rectMatMul PB IPA) (delta * Bplus_norm) := by
    simpa [PA, PB, IPA] using
      wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped
        A B Aplus Bplus hleftA hSymA hSymB hDelta
        hBplus_norm_nonneg hBplus
  have hBplus_y := hBplus (rectMatMulVec (rectMatMul PB IPA) r)
  have hPBIPA_r := hPBIPA r
  calc
    vecNorm2 (rectMatMulVec Bplus r)
        = vecNorm2
            (rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r)) := by
            rw [hfactor]
    _ ≤ Bplus_norm * vecNorm2 (rectMatMulVec (rectMatMul PB IPA) r) :=
            hBplus_y
    _ ≤ Bplus_norm * ((delta * Bplus_norm) * vecNorm2 r) :=
            mul_le_mul_of_nonneg_left hPBIPA_r hBplus_norm_nonneg
    _ = (delta * Bplus_norm * Bplus_norm) * vecNorm2 r := by ring

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    `η`-scaled form of the `Bplus*r` residual bound.

When Lemma 20.11 has supplied
`||Bplus||₂ <= ||Aplus||₂ / (1 - η)` and `η = ||Aplus||₂ * delta`, the
one-sided Lemma 20.12 route gives the displayed residual-transfer scale
`η ||Aplus||₂ / (1 - η)^2`. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_residual_le_eta
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ} (r : Fin m → ℝ)
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2 (rectMatMulVec Bplus r) ≤
      (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hden_pos : 0 < 1 - eta :=
    wedinLemma20_11_denominator_pos hsmall
  have hBplus_radius_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg (le_of_lt hAplus_pos) (le_of_lt hden_pos)
  have hbound :=
    wedinTheorem20_1_vecNorm2_Bplus_residual_le
      A B Aplus Bplus r hleftA hleftB hSymA hSymB hDelta
      hBplus_radius_nonneg hBplus hrangeA_residual
  have hcoeff :
      delta * (Aplus_norm / (1 - eta)) *
          (Aplus_norm / (1 - eta)) =
        eta * Aplus_norm / (1 - eta) ^ 2 := by
    rw [heta]
    field_simp [ne_of_gt hden_pos]
  simpa [hcoeff] using hbound

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    direct forcing-term estimate for `Bplus*(-DeltaA*x + Deltab)`.

This is the elementary norm part of the Wedin transfer: a pseudoinverse
operator-radius for `Bplus`, an operator-radius for `DeltaA`, and a vector
radius for `Deltab` bound the forcing contribution before it is combined with
the residual-transfer term. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_forcing_le
    {m k : ℕ} (Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab : Fin m → ℝ)
    (x : Fin (k + 1) → ℝ)
    {Bplus_norm DeltaA_norm Deltab_norm : ℝ}
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm) :
    vecNorm2
        (rectMatMulVec Bplus
          (fun i => -rectMatMulVec DeltaA x i + Deltab i)) ≤
      Bplus_norm * (DeltaA_norm * vecNorm2 x + Deltab_norm) := by
  let forcing : Fin m → ℝ :=
    fun i => -rectMatMulVec DeltaA x i + Deltab i
  have hforcing :
      vecNorm2 forcing ≤ DeltaA_norm * vecNorm2 x + Deltab_norm := by
    calc
      vecNorm2 forcing
          ≤ vecNorm2 (fun i : Fin m => -rectMatMulVec DeltaA x i) +
              vecNorm2 Deltab := by
              simpa [forcing] using
                vecNorm2_add_le (fun i : Fin m => -rectMatMulVec DeltaA x i)
                  Deltab
      _ = vecNorm2 (rectMatMulVec DeltaA x) + vecNorm2 Deltab := by
              rw [vecNorm2_neg]
      _ ≤ DeltaA_norm * vecNorm2 x + Deltab_norm :=
              add_le_add (hDeltaA x) hDeltab
  calc
    vecNorm2 (rectMatMulVec Bplus forcing)
        ≤ Bplus_norm * vecNorm2 forcing := hBplus forcing
    _ ≤ Bplus_norm * (DeltaA_norm * vecNorm2 x + Deltab_norm) :=
        mul_le_mul_of_nonneg_left hforcing hBplus_norm_nonneg

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    assembled bound for the forcing contribution plus the residual-transfer
    contribution, before the final source scalar normalization. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_forcing_add_residual_le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r : Fin m → ℝ)
    (x : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2
        (fun j =>
          rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i) j +
            rectMatMulVec Bplus r j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hden_pos : 0 < 1 - eta :=
    wedinLemma20_11_denominator_pos hsmall
  have hBplus_radius_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg (le_of_lt hAplus_pos) (le_of_lt hden_pos)
  have hforcing :
      vecNorm2
          (rectMatMulVec Bplus
            (fun i => -rectMatMulVec DeltaA x i + Deltab i)) ≤
        (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) :=
    wedinTheorem20_1_vecNorm2_Bplus_forcing_le
      Bplus DeltaA Deltab x hBplus_radius_nonneg hBplus hDeltaA hDeltab
  have hresidual :
      vecNorm2 (rectMatMulVec Bplus r) ≤
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r :=
    wedinTheorem20_1_vecNorm2_Bplus_residual_le_eta
      A B Aplus Bplus r hAplus_pos heta hsmall hleftA hleftB
      hSymA hSymB hDelta hBplus hrangeA_residual
  calc
    vecNorm2
        (fun j =>
          rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i) j +
            rectMatMulVec Bplus r j)
        ≤ vecNorm2
            (rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i)) +
          vecNorm2 (rectMatMulVec Bplus r) := by
            exact vecNorm2_add_le
              (rectMatMulVec Bplus
                (fun i => -rectMatMulVec DeltaA x i + Deltab i))
              (rectMatMulVec Bplus r)
    _ ≤ (Aplus_norm / (1 - eta)) *
            (DeltaA_norm * vecNorm2 x + Deltab_norm) +
          (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r :=
            add_le_add hforcing hresidual

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    assembled bound with the combined source vector
    `-DeltaA*x + Deltab + r` inside the single `Bplus` action. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_combined_forcing_residual_le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r : Fin m → ℝ)
    (x : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2
        (rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i)) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hsum :=
    wedinTheorem20_1_vecNorm2_Bplus_forcing_add_residual_le
      A B Aplus Bplus DeltaA Deltab r x hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual
  have hsplit :
      rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) =
        fun j =>
          rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i) j +
            rectMatMulVec Bplus r j := by
    simpa using
      rectMatMulVec_add Bplus
        (fun i : Fin m => -rectMatMulVec DeltaA x i + Deltab i) r
  simpa [hsplit] using hsum

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    if the perturbation algebra has produced the source equation for
    `B*(y-x)`, then the left inverse `Bplus*B = I` identifies the solution
    difference with the combined `Bplus` vector. -/
theorem wedinTheorem20_1_solution_difference_eq_Bplus_combined_of_B_mul
    {m k : ℕ} (B : Fin m → Fin (k + 1) → ℝ)
    (Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) :
    (fun j => y j - x j) =
      rectMatMulVec Bplus
        (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) := by
  calc
    (fun j => y j - x j)
        = rectMatMulVec (idMatrix (k + 1)) (fun j => y j - x j) := by
            symm
            exact rectMatMulVec_idMatrix (fun j => y j - x j)
    _ = rectMatMulVec (rectMatMul Bplus B) (fun j => y j - x j) := by
            rw [hleftB]
    _ = rectMatMulVec Bplus
          (rectMatMulVec B (fun j => y j - x j)) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) := by
            rw [hBdiff]

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    solution-difference norm bound after the source equation for `B*(y-x)`
    has been exposed.  This is still prior to the printed relative scalar
    normalization in (20.1). -/
theorem wedinTheorem20_1_vecNorm2_solution_difference_le_of_B_mul
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) :
    vecNorm2 (fun j => y j - x j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hdiff_eq :
      (fun j => y j - x j) =
        rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) :=
    wedinTheorem20_1_solution_difference_eq_Bplus_combined_of_B_mul
      B Bplus DeltaA Deltab r x y hleftB hBdiff
  rw [hdiff_eq]
  exact
    wedinTheorem20_1_vecNorm2_Bplus_combined_forcing_residual_le
      A B Aplus Bplus DeltaA Deltab r x hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    a perturbed residual annihilated by the `B` range projector is killed by
    `Bplus`. -/
theorem wedinTheorem20_1_Bplus_perturbed_residual_eq_zero
    {m k : ℕ} (B : Fin m → Fin (k + 1) → ℝ)
    (Bplus : Fin (k + 1) → Fin m → ℝ) (s : Fin m → ℝ)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    rectMatMulVec Bplus s = 0 := by
  have hBplusPB : rectMatMul Bplus (rectMatMul B Bplus) = Bplus := by
    calc
      rectMatMul Bplus (rectMatMul B Bplus)
          = rectMatMul (rectMatMul Bplus B) Bplus := by
              rw [rectMatMul_assoc]
      _ = rectMatMul (idMatrix (k + 1)) Bplus := by
              rw [hleftB]
      _ = Bplus := rectMatMul_id_left Bplus
  calc
    rectMatMulVec Bplus s
        = rectMatMulVec (rectMatMul Bplus (rectMatMul B Bplus)) s := by
            rw [hBplusPB]
    _ = rectMatMulVec Bplus (rectMatMulVec (rectMatMul B Bplus) s) := by
            rw [rectMatMulVec_rectMatMul]
    _ = 0 := by
            rw [hproj_s]
            ext j
            unfold rectMatMulVec
            simp

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    source-faithful solution-difference identity with the perturbed residual
    `s` present in the `B*(y-x)` equation and removed only through the
    `B` range-projector condition. -/
theorem wedinTheorem20_1_solution_difference_eq_Bplus_combined_of_B_mul_sub_residual
    {m k : ℕ} (B : Fin m → Fin (k + 1) → ℝ)
    (Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => ((-rectMatMulVec DeltaA x i + Deltab i) + r i) - s i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    (fun j => y j - x j) =
      rectMatMulVec Bplus
        (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) := by
  let combined : Fin m → ℝ :=
    fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i
  have hBplus_s : rectMatMulVec Bplus s = 0 :=
    wedinTheorem20_1_Bplus_perturbed_residual_eq_zero
      B Bplus s hleftB hproj_s
  have hsub :
      rectMatMulVec Bplus (fun i => combined i - s i) =
        rectMatMulVec Bplus combined := by
    calc
      rectMatMulVec Bplus (fun i => combined i - s i)
          = fun j => rectMatMulVec Bplus combined j - rectMatMulVec Bplus s j := by
              rw [rectMatMulVec_sub]
      _ = rectMatMulVec Bplus combined := by
              rw [hBplus_s]
              ext j
              simp
  calc
    (fun j => y j - x j)
        = rectMatMulVec (idMatrix (k + 1)) (fun j => y j - x j) := by
            symm
            exact rectMatMulVec_idMatrix (fun j => y j - x j)
    _ = rectMatMulVec (rectMatMul Bplus B) (fun j => y j - x j) := by
            rw [hleftB]
    _ = rectMatMulVec Bplus
          (rectMatMulVec B (fun j => y j - x j)) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec Bplus (fun i => combined i - s i) := by
            rw [hBdiff]
    _ = rectMatMulVec Bplus combined := hsub

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    source-faithful solution-difference norm bound with a perturbed residual
    `s` that is annihilated by the `B` range projector. -/
theorem wedinTheorem20_1_vecNorm2_solution_difference_le_of_B_mul_sub_residual
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => ((-rectMatMulVec DeltaA x i + Deltab i) + r i) - s i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    vecNorm2 (fun j => y j - x j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hdiff_eq :
      (fun j => y j - x j) =
        rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) :=
    wedinTheorem20_1_solution_difference_eq_Bplus_combined_of_B_mul_sub_residual
      B Bplus DeltaA Deltab r s x y hleftB hBdiff hproj_s
  rw [hdiff_eq]
  exact
    wedinTheorem20_1_vecNorm2_Bplus_combined_forcing_residual_le
      A B Aplus Bplus DeltaA Deltab r x hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual

/-- Higham, 2nd ed., Chapter 20, Wedin proof algebra:
    the residual definitions `r = b - A*x`, `s = b + Δb - B*y`, and
    `B = A + ΔA` imply the source equation
    `B*(y-x) = -ΔA*x + Δb + r - s`. -/
theorem wedinTheorem20_1_B_mul_solution_difference_eq_forcing_residual_sub_of_residuals
    {m k : ℕ} (A B DeltaA : Fin m → Fin (k + 1) → ℝ)
    (b Deltab r s : Fin m → ℝ) (x y : Fin (k + 1) → ℝ)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i) :
    rectMatMulVec B (fun j => y j - x j) =
      fun i => ((-rectMatMulVec DeltaA x i + Deltab i) + r i) - s i := by
  ext i
  have hdiff := congrFun (rectMatMulVec_sub B y x) i
  have hBx :
      rectMatMulVec B x i =
        rectMatMulVec A x i + rectMatMulVec DeltaA x i := by
    rw [hB]
    exact congrFun (rectMatMulVec_mat_add A DeltaA x) i
  have hri : r i = b i - rectMatMulVec A x i := by
    simpa using congrFun hr i
  have hsi : s i = (b i + Deltab i) - rectMatMulVec B y i := by
    simpa using congrFun hs i
  rw [hdiff, hBx, hri, hsi]
  ring

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    solution-difference norm bound after deriving the source
    `B*(y-x) = -ΔA*x + Δb + r - s` equation from the residual definitions.

The remaining visible `P_B s = 0` hypothesis is the perturbed least-squares
orthogonality condition and is not hidden inside the residual algebra. -/
theorem wedinTheorem20_1_vecNorm2_solution_difference_le_of_residual_definitions
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    vecNorm2 (fun j => y j - x j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => ((-rectMatMulVec DeltaA x i + Deltab i) + r i) - s i :=
    wedinTheorem20_1_B_mul_solution_difference_eq_forcing_residual_sub_of_residuals
      A B DeltaA b Deltab r s x y hB hr hs
  exact
    wedinTheorem20_1_vecNorm2_solution_difference_le_of_B_mul_sub_residual
      A B Aplus Bplus DeltaA Deltab r s x y hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual hBdiff hproj_s

/-- Higham, 2nd ed., Chapter 20, Wedin proof algebra:
    if the perturbed residual is orthogonal to every column of `B`, then the
    symmetric range projector `P_B = B*Bplus` annihilates it.

This is the normal-equation/least-squares optimality bridge for the explicit
projector condition used by the source-faithful `s`-residual Wedin route. -/
theorem wedinTheorem20_1_rangeProjection_perturbed_residual_eq_zero_of_column_orthogonal
    {m k : ℕ} (B : Fin m → Fin (k + 1) → ℝ)
    (Bplus : Fin (k + 1) → Fin m → ℝ) (s : Fin m → ℝ)
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    rectMatMulVec (rectMatMul B Bplus) s = 0 := by
  ext i
  unfold rectMatMulVec rectMatMul
  calc
    (∑ l : Fin m, (∑ j : Fin (k + 1), B i j * Bplus j l) * s l)
        = ∑ l : Fin m, (∑ j : Fin (k + 1), B l j * Bplus j i) * s l := by
            apply Finset.sum_congr rfl
            intro l _
            have hentry :
                (∑ j : Fin (k + 1), B i j * Bplus j l) =
                  ∑ j : Fin (k + 1), B l j * Bplus j i := by
              simpa [rectMatMul] using hSymB i l
            rw [hentry]
    _ = ∑ l : Fin m, ∑ j : Fin (k + 1),
          (B l j * Bplus j i) * s l := by
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_mul]
    _ = ∑ j : Fin (k + 1), ∑ l : Fin m,
          (B l j * Bplus j i) * s l := by
            rw [Finset.sum_comm]
    _ = ∑ j : Fin (k + 1), Bplus j i * (∑ l : Fin m, B l j * s l) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            ring
    _ = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            rw [horth_s j]
            ring

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    solution-difference norm bound using the residual definitions and the
    normal-equation column-orthogonality form of perturbed least-squares
    optimality.

This removes the raw `P_B s = 0` hypothesis from the caller-facing vector
route; the remaining scalar work is the printed relative normalization. -/
theorem wedinTheorem20_1_vecNorm2_solution_difference_le_of_residual_definitions_column_orthogonal
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun j => y j - x j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0 :=
    wedinTheorem20_1_rangeProjection_perturbed_residual_eq_zero_of_column_orthogonal
      B Bplus s hSymB horth_s
  exact
    wedinTheorem20_1_vecNorm2_solution_difference_le_of_residual_definitions
      A B Aplus Bplus DeltaA b Deltab r s x y hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual hB hr hs hproj_s

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1), conservative
    relative solution perturbation bound assembled from the currently proved
    Wedin vector route.

The result uses residual definitions, normal-equation column orthogonality for
the perturbed residual, relative perturbation budgets, and `kappa =
Aplus_norm*A_norm`.  The conclusion is the conservative scalar RHS rather than
the printed (20.1) RHS because the residual-transfer path still carries the
extra one-sided Lemma 20.12 denominator. -/
theorem wedinTheorem20_1_solutionRelativeRHSConservative_le_of_residual_definitions_column_orthogonal
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (hx_norm_pos : 0 < vecNorm2 x)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget :
      Deltab_norm ≤ eps * (A_norm * vecNorm2 x + vecNorm2 r))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
      wedinTheorem20_1SolutionRelativeRHSConservative
        kappa eps A_norm (vecNorm2 x) (vecNorm2 r) := by
  have hvec :
      vecNorm2 (fun j => y j - x j) ≤
        (Aplus_norm / (1 - eta)) *
            (DeltaA_norm * vecNorm2 x + Deltab_norm) +
          (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r :=
    wedinTheorem20_1_vecNorm2_solution_difference_le_of_residual_definitions_column_orthogonal
      A B Aplus Bplus DeltaA b Deltab r s x y hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual hB hr hs horth_s
  have heta_scalar : eta = kappa * eps := by
    rw [heta, hdelta, hkappa]
    ring
  have hsmall_scalar : kappa * eps < 1 := by
    rw [← heta_scalar]
    exact hsmall
  exact
    wedinTheorem20_1_solutionRelativeRHSConservative_of_vector_bound
      (hAplus_nonneg := le_of_lt hAplus_pos)
      (hA_norm_pos := hA_norm_pos)
      (hx_norm_pos := hx_norm_pos)
      (hkappa := hkappa)
      (heta := heta_scalar)
      (hsmall := hsmall_scalar)
      (hDeltaA_norm := hDeltaA_norm_budget)
      (hDeltab_norm := hDeltab_norm_budget)
      (hvec := hvec)

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1, residual side:
    residual algebra after substituting the Wedin solution-difference identity.

This is the formal version of
`s - r = (I - B Bplus) (Delta b - Delta A*x) - B Bplus*r`. -/
theorem wedinTheorem20_1_residual_difference_eq_projection_decomp
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    (fun i => s i - r i) =
      fun i =>
        rectMatMulVec
            (fun i j => idMatrix m i j - rectMatMul B Bplus i j)
            (fun i => Deltab i - rectMatMulVec DeltaA x i) i -
          rectMatMulVec (rectMatMul B Bplus) r i := by
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPB : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - PB i j
  let q : Fin m → ℝ := fun i => Deltab i - rectMatMulVec DeltaA x i
  let combined : Fin m → ℝ :=
    fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i
  have hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => ((-rectMatMulVec DeltaA x i + Deltab i) + r i) - s i :=
    wedinTheorem20_1_B_mul_solution_difference_eq_forcing_residual_sub_of_residuals
      A B DeltaA b Deltab r s x y hB hr hs
  have hdiff :
      (fun j => y j - x j) =
        rectMatMulVec Bplus combined :=
    wedinTheorem20_1_solution_difference_eq_Bplus_combined_of_B_mul_sub_residual
      B Bplus DeltaA Deltab r s x y hleftB hBdiff hproj_s
  have hB_yx :
      rectMatMulVec B (fun j => y j - x j) =
        rectMatMulVec PB combined := by
    calc
      rectMatMulVec B (fun j => y j - x j)
          = rectMatMulVec B (rectMatMulVec Bplus combined) := by
              rw [hdiff]
      _ = rectMatMulVec PB combined := by
              rw [rectMatMulVec_rectMatMul]
  have hcombined :
      combined = fun i => q i + r i := by
    ext i
    simp [combined, q]
    ring
  have hPB_combined :
      rectMatMulVec PB combined =
        fun i => rectMatMulVec PB q i + rectMatMulVec PB r i := by
    rw [hcombined]
    exact rectMatMulVec_add PB q r
  have hIPB_q :
      rectMatMulVec IPB q =
        fun i => q i - rectMatMulVec PB q i := by
    simpa [IPB, PB, q] using
      wedinLemma20_12_rectMatMulVec_projectionComplement PB q
  ext i
  have hsubB := congrFun (rectMatMulVec_sub B y x) i
  have hBx :
      rectMatMulVec B x i =
        rectMatMulVec A x i + rectMatMulVec DeltaA x i := by
    rw [hB]
    exact congrFun (rectMatMulVec_mat_add A DeltaA x) i
  have hri : r i = b i - rectMatMulVec A x i := by
    simpa using congrFun hr i
  have hsi : s i = (b i + Deltab i) - rectMatMulVec B y i := by
    simpa using congrFun hs i
  have hres :
      s i - r i =
        Deltab i - rectMatMulVec B (fun j => y j - x j) i -
          rectMatMulVec DeltaA x i := by
    have hBy :
        rectMatMulVec B y i =
          rectMatMulVec B (fun j => y j - x j) i + rectMatMulVec B x i := by
      linarith [hsubB]
    rw [hsi, hri, hBy, hBx]
    ring
  have hPB_combined_i :
      rectMatMulVec PB combined i =
        rectMatMulVec PB q i + rectMatMulVec PB r i := by
    exact congrFun hPB_combined i
  have hIPB_q_i :
      rectMatMulVec IPB q i = q i - rectMatMulVec PB q i := by
    exact congrFun hIPB_q i
  rw [hres, congrFun hB_yx i, hPB_combined_i, hIPB_q_i]
  simp [PB, q]
  ring

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1, residual side:
    vector residual-difference estimate once the source-strength projector
    estimate `||P_B(I-P_A)||₂ <= ||Delta A||₂ ||Aplus||₂` is supplied.

The supplied projector estimate is exactly the still-open full Lemma 20.12
equality/min dependency; this theorem closes the remaining residual algebra
without hiding that dependency. -/
theorem wedinTheorem20_1_vecNorm2_residual_difference_le_of_residual_definitions_projector_bound
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm : ℝ}
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    vecNorm2 (fun i => r i - s i) ≤
      Deltab_norm + DeltaA_norm * vecNorm2 x +
        (delta * Aplus_norm) * vecNorm2 r := by
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPB : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - PB i j
  let IPA : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - rectMatMul A Aplus i j
  let q : Fin m → ℝ := fun i => Deltab i - rectMatMulVec DeltaA x i
  have hdecomp :
      (fun i => s i - r i) =
        fun i => rectMatMulVec IPB q i - rectMatMulVec PB r i := by
    simpa [PB, IPB, q] using
      wedinTheorem20_1_residual_difference_eq_projection_decomp
        A B Bplus DeltaA b Deltab r s x y hleftB hB hr hs hproj_s
  have hneg :
      (fun i => r i - s i) = fun i => -(s i - r i) := by
    ext i
    ring
  have hq_norm :
      vecNorm2 q ≤ Deltab_norm + DeltaA_norm * vecNorm2 x := by
    calc
      vecNorm2 q
          ≤ vecNorm2 Deltab +
              vecNorm2 (fun i : Fin m => -rectMatMulVec DeltaA x i) := by
              simpa [q, sub_eq_add_neg] using
                vecNorm2_add_le Deltab
                  (fun i : Fin m => -rectMatMulVec DeltaA x i)
      _ = vecNorm2 Deltab + vecNorm2 (rectMatMulVec DeltaA x) := by
              rw [vecNorm2_neg]
      _ ≤ Deltab_norm + DeltaA_norm * vecNorm2 x :=
              add_le_add hDeltab (hDeltaA x)
  have hIPB :
      rectOpNorm2Le IPB 1 := by
    simpa [IPB, PB] using
      wedinLemma20_12_rectOpNorm2Le_projectionComplement_of_symmetric_left_inverse
        B Bplus hleftB hSymB
  have hIPB_q :
      vecNorm2 (rectMatMulVec IPB q) ≤
        Deltab_norm + DeltaA_norm * vecNorm2 x := by
    have h := hIPB q
    have h' : vecNorm2 (rectMatMulVec IPB q) ≤ vecNorm2 q := by
      simpa using h
    exact h'.trans hq_norm
  have hIPA_r : rectMatMulVec IPA r = r := by
    rw [show IPA = (fun i j => idMatrix m i j - rectMatMul A Aplus i j) by
      ext i j
      rfl]
    rw [wedinLemma20_12_rectMatMulVec_projectionComplement]
    rw [hrangeA_residual]
    ext i
    simp
  have hPB_r :
      vecNorm2 (rectMatMulVec PB r) ≤
        (delta * Aplus_norm) * vecNorm2 r := by
    have h := hPBIPA r
    have hPBIPA_r :
        rectMatMulVec
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j)) r =
          rectMatMulVec PB r := by
      calc
        rectMatMulVec
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j)) r
            = rectMatMulVec PB (rectMatMulVec IPA r) := by
                rw [rectMatMulVec_rectMatMul]
        _ = rectMatMulVec PB r := by
                rw [hIPA_r]
    simpa [hPBIPA_r] using h
  calc
    vecNorm2 (fun i => r i - s i)
        = vecNorm2 (fun i => s i - r i) := by
            rw [hneg]
            rw [vecNorm2_neg]
    _ = vecNorm2 (fun i => rectMatMulVec IPB q i - rectMatMulVec PB r i) := by
            rw [hdecomp]
    _ ≤ vecNorm2 (rectMatMulVec IPB q) +
          vecNorm2 (fun i : Fin m => -rectMatMulVec PB r i) := by
            simpa [sub_eq_add_neg] using
              vecNorm2_add_le (rectMatMulVec IPB q)
                (fun i : Fin m => -rectMatMulVec PB r i)
    _ = vecNorm2 (rectMatMulVec IPB q) +
          vecNorm2 (rectMatMulVec PB r) := by
            rw [vecNorm2_neg]
    _ ≤ (Deltab_norm + DeltaA_norm * vecNorm2 x) +
          (delta * Aplus_norm) * vecNorm2 r :=
            add_le_add hIPB_q hPB_r
    _ = Deltab_norm + DeltaA_norm * vecNorm2 x +
          (delta * Aplus_norm) * vecNorm2 r := by ring

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    scalar normalization of the residual perturbation bound from the vector
    residual estimate.

The assumptions `A_norm * ||x|| <= kappa * b_norm` and `||r|| <= b_norm`
are the LS-geometry bounds used in the source proof; the projector estimate is
kept in the vector theorem that supplies `hvec`. -/
theorem wedinTheorem20_1_residualRelativeRHS_of_vector_bound
    {res_norm DeltaA_norm Deltab_norm delta Aplus_norm kappa eps A_norm
      b_norm x_norm r_norm : ℝ}
    (hb_norm_pos : 0 < b_norm)
    (hx_norm_nonneg : 0 ≤ x_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa_nonneg : 0 ≤ kappa)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * b_norm)
    (hx_budget : A_norm * x_norm ≤ kappa * b_norm)
    (hr_budget : r_norm ≤ b_norm)
    (hvec :
      res_norm ≤ Deltab_norm + DeltaA_norm * x_norm +
        (delta * Aplus_norm) * r_norm) :
    res_norm / b_norm ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  have hDeltaA_x :
      DeltaA_norm * x_norm ≤ eps * kappa * b_norm := by
    have h1 : DeltaA_norm * x_norm ≤ (eps * A_norm) * x_norm :=
      mul_le_mul_of_nonneg_right hDeltaA_norm_budget hx_norm_nonneg
    have h2 : (eps * A_norm) * x_norm ≤ eps * (kappa * b_norm) := by
      calc
        (eps * A_norm) * x_norm = eps * (A_norm * x_norm) := by ring
        _ ≤ eps * (kappa * b_norm) :=
            mul_le_mul_of_nonneg_left hx_budget heps_nonneg
    exact h1.trans (by simpa [mul_assoc] using h2)
  have hproj_coeff : delta * Aplus_norm = eps * kappa := by
    rw [hdelta, hkappa]
    ring
  have hproj :
      (delta * Aplus_norm) * r_norm ≤ eps * kappa * b_norm := by
    rw [hproj_coeff]
    have hcoeff_nonneg : 0 ≤ eps * kappa :=
      mul_nonneg heps_nonneg hkappa_nonneg
    exact mul_le_mul_of_nonneg_left hr_budget hcoeff_nonneg
  have hscalar :
      res_norm ≤
        eps * b_norm + eps * kappa * b_norm + eps * kappa * b_norm := by
    calc
      res_norm
          ≤ Deltab_norm + DeltaA_norm * x_norm +
              (delta * Aplus_norm) * r_norm := hvec
      _ ≤ eps * b_norm + eps * kappa * b_norm +
              eps * kappa * b_norm := by
            exact add_le_add (add_le_add hDeltab_norm_budget hDeltaA_x) hproj
  calc
    res_norm / b_norm
        ≤ (eps * b_norm + eps * kappa * b_norm + eps * kappa * b_norm) /
            b_norm := div_le_div_of_nonneg_right hscalar (le_of_lt hb_norm_pos)
    _ = wedinTheorem20_1ResidualRelativeRHS kappa eps := by
          unfold wedinTheorem20_1ResidualRelativeRHS
          field_simp [ne_of_gt hb_norm_pos]
          ring

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    residual perturbation bound assembled from residual definitions and the
    source-strength projector estimate used in the proof of Wedin's theorem.

This closes the residual side modulo the same full Lemma 20.12
`P_B(I-P_A)` estimate needed by the printed solution bound. -/
theorem wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (heps_nonneg : 0 ≤ eps)
    (hkappa_nonneg : 0 ≤ kappa)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hx_budget : A_norm * vecNorm2 x ≤ kappa * vecNorm2 b)
    (hr_budget : vecNorm2 r ≤ vecNorm2 b)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  have hvec :
      vecNorm2 (fun i => r i - s i) ≤
        Deltab_norm + DeltaA_norm * vecNorm2 x +
          (delta * Aplus_norm) * vecNorm2 r :=
    wedinTheorem20_1_vecNorm2_residual_difference_le_of_residual_definitions_projector_bound
      A B Aplus Bplus DeltaA b Deltab r s x y hleftB hSymB
      hDeltaA hDeltab hrangeA_residual hPBIPA hB hr hs hproj_s
  exact
    wedinTheorem20_1_residualRelativeRHS_of_vector_bound
      (hb_norm_pos := hb_norm_pos)
      (hx_norm_nonneg := vecNorm2_nonneg x)
      (heps_nonneg := heps_nonneg)
      (hkappa_nonneg := hkappa_nonneg)
      (hkappa := hkappa)
      (hdelta := hdelta)
      (hDeltaA_norm_budget := hDeltaA_norm_budget)
      (hDeltab_norm_budget := hDeltab_norm_budget)
      (hx_budget := hx_budget)
      (hr_budget := hr_budget)
      (hvec := hvec)

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1:
    the exact least-squares residual orthogonality and residual definition
    identify the solution as `Aplus*b`. -/
theorem wedinTheorem20_1_solution_eq_Aplus_b_of_residual_definition
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    (Aplus : Fin (k + 1) → Fin m → ℝ)
    (b r : Fin m → ℝ) (x : Fin (k + 1) → ℝ)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hr : r = fun i => b i - rectMatMulVec A x i) :
    x = rectMatMulVec Aplus b := by
  have hAplusPA : rectMatMul Aplus (rectMatMul A Aplus) = Aplus := by
    calc
      rectMatMul Aplus (rectMatMul A Aplus)
          = rectMatMul (rectMatMul Aplus A) Aplus := by
              rw [rectMatMul_assoc]
      _ = rectMatMul (idMatrix (k + 1)) Aplus := by
              rw [hleftA]
      _ = Aplus := rectMatMul_id_left Aplus
  have hAplus_r : rectMatMulVec Aplus r = 0 := by
    calc
      rectMatMulVec Aplus r
          = rectMatMulVec (rectMatMul Aplus (rectMatMul A Aplus)) r := by
              rw [hAplusPA]
      _ = rectMatMulVec Aplus (rectMatMulVec (rectMatMul A Aplus) r) := by
              rw [rectMatMulVec_rectMatMul]
      _ = 0 := by
              rw [hrangeA_residual]
              ext j
              simp [rectMatMulVec]
  have hb_decomp : b = fun i => rectMatMulVec A x i + r i := by
    ext i
    have hri : r i = b i - rectMatMulVec A x i := by
      simpa using congrFun hr i
    linarith
  symm
  calc
    rectMatMulVec Aplus b
        = rectMatMulVec Aplus
            (fun i => rectMatMulVec A x i + r i) := by
            rw [hb_decomp]
    _ = fun j =>
          rectMatMulVec Aplus (rectMatMulVec A x) j +
            rectMatMulVec Aplus r j := by
            rw [rectMatMulVec_add]
    _ = rectMatMulVec Aplus (rectMatMulVec A x) := by
            rw [hAplus_r]
            ext j
            simp
    _ = rectMatMulVec (rectMatMul Aplus A) x := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec (idMatrix (k + 1)) x := by
            rw [hleftA]
    _ = x := rectMatMulVec_idMatrix x

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1:
    exact least-squares residuals are no larger than the right-hand side in
    Euclidean norm. -/
theorem wedinTheorem20_1_vecNorm2_residual_le_b_of_residual_definition
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    (Aplus : Fin (k + 1) → Fin m → ℝ)
    (b r : Fin m → ℝ) (x : Fin (k + 1) → ℝ)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hr : r = fun i => b i - rectMatMulVec A x i) :
    vecNorm2 r ≤ vecNorm2 b := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  have hb_decomp : b = fun i => rectMatMulVec A x i + r i := by
    ext i
    have hri : r i = b i - rectMatMulVec A x i := by
      simpa using congrFun hr i
    linarith
  have hPA_Ax :
      rectMatMulVec PA (rectMatMulVec A x) = rectMatMulVec A x := by
    simpa [PA] using
      rectMatMulVec_rangeProjection_apply_range_of_left_inverse A Aplus
        hleftA x
  have hPA_b : rectMatMulVec PA b = rectMatMulVec A x := by
    calc
      rectMatMulVec PA b
          = rectMatMulVec PA
              (fun i => rectMatMulVec A x i + r i) := by
              rw [hb_decomp]
      _ = fun i =>
            rectMatMulVec PA (rectMatMulVec A x) i +
              rectMatMulVec PA r i := by
              rw [rectMatMulVec_add]
      _ = rectMatMulVec A x := by
              rw [hPA_Ax, show rectMatMulVec PA r = 0 by
                simpa [PA] using hrangeA_residual]
              ext i
              simp
  have hresid_eq :
      (fun i => b i - rectMatMulVec PA b i) = r := by
    ext i
    have hri : r i = b i - rectMatMulVec A x i := by
      simpa using congrFun hr i
    have hPAi : rectMatMulVec PA b i = rectMatMulVec A x i := by
      exact congrFun hPA_b i
    rw [hPAi]
    exact hri.symm
  have hzero :
      (fun i : Fin m => b i - rectMatMulVec A (fun _ : Fin (k + 1) => 0) i) =
        b := by
    ext i
    simp [rectMatMulVec]
  have hbest :=
    rectMatMulVec_rangeProjection_residual_norm_le_range_residual_of_symmetric_left_inverse
      A Aplus hleftA hSymA b (fun _ : Fin (k + 1) => 0)
  simpa [PA, hresid_eq, hzero] using hbest

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1:
    the source `||A|| ||x|| <= kappa ||b||` geometry bound follows from
    `x = Aplus*b` and `kappa = ||Aplus|| ||A||`. -/
theorem wedinTheorem20_1_A_norm_mul_solution_norm_le_kappa_b_of_residual_definition
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    (Aplus : Fin (k + 1) → Fin m → ℝ)
    (b r : Fin m → ℝ) (x : Fin (k + 1) → ℝ)
    {Aplus_norm A_norm kappa : ℝ}
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hr : r = fun i => b i - rectMatMulVec A x i) :
    A_norm * vecNorm2 x ≤ kappa * vecNorm2 b := by
  have hx_eq :
      x = rectMatMulVec Aplus b :=
    wedinTheorem20_1_solution_eq_Aplus_b_of_residual_definition
      A Aplus b r x hleftA hrangeA_residual hr
  have hx_norm :
      vecNorm2 x ≤ Aplus_norm * vecNorm2 b := by
    rw [hx_eq]
    exact hAplus b
  calc
    A_norm * vecNorm2 x
        ≤ A_norm * (Aplus_norm * vecNorm2 b) :=
            mul_le_mul_of_nonneg_left hx_norm hA_norm_nonneg
    _ = kappa * vecNorm2 b := by
            rw [hkappa]
            ring

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    residual perturbation bound with the standard LS geometry bounds derived
    from the residual definition and exact-residual projection orthogonality.

The remaining explicit blocker is the source-strength projector estimate
`||P_B(I-P_A)|| <= ||Delta A|| ||Aplus||`, i.e. the full Lemma 20.12
equality/min surface. -/
theorem wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound_geometry
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  have hAplus_norm_nonneg : 0 ≤ Aplus_norm :=
    by
      have hright_nonneg :
          0 ≤ Aplus_norm * vecNorm2 b :=
        le_trans (vecNorm2_nonneg (rectMatMulVec Aplus b)) (hAplus b)
      nlinarith [hb_norm_pos]
  have hkappa_nonneg : 0 ≤ kappa := by
    rw [hkappa]
    exact mul_nonneg hAplus_norm_nonneg hA_norm_nonneg
  have hx_budget :
      A_norm * vecNorm2 x ≤ kappa * vecNorm2 b :=
    wedinTheorem20_1_A_norm_mul_solution_norm_le_kappa_b_of_residual_definition
      A Aplus b r x hA_norm_nonneg hkappa hAplus hleftA
      hrangeA_residual hr
  have hr_budget : vecNorm2 r ≤ vecNorm2 b :=
    wedinTheorem20_1_vecNorm2_residual_le_b_of_residual_definition
      A Aplus b r x hleftA hSymA hrangeA_residual hr
  exact
    wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound
      A B Aplus Bplus DeltaA b Deltab r s x y hb_norm_pos heps_nonneg
      hkappa_nonneg hkappa hdelta hDeltaA hDeltab hDeltaA_norm_budget
      hDeltab_norm_budget hx_budget hr_budget hleftB hSymB
      hrangeA_residual hPBIPA hB hr hs hproj_s

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    residual perturbation bound with the perturbed residual optimality
    hypothesis stated as column orthogonality.

This is the source-facing version of the residual-side Wedin wrapper above:
`B^T s = 0` is converted to `P_B s = 0` by the symmetric range-projector
lemma, so callers no longer have to expose the raw projector annihilation
condition.  The remaining explicit blocker is still the full Lemma 20.12
source-strength estimate `||P_B(I-P_A)|| <= ||Delta A|| ||Aplus||`. -/
theorem wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound_geometry_column_orthogonal
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  have hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0 :=
    wedinTheorem20_1_rangeProjection_perturbed_residual_eq_zero_of_column_orthogonal
      B Bplus s hSymB horth_s
  exact
    wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound_geometry
      A B Aplus Bplus DeltaA b Deltab r s x y hb_norm_pos hA_norm_nonneg
      heps_nonneg hkappa hdelta hAplus hDeltaA hDeltab hDeltaA_norm_budget
      hDeltab_norm_budget hleftA hleftB hSymA hSymB hrangeA_residual
      hPBIPA hB hr hs hproj_s

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
