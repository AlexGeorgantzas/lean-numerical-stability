-- Algorithms/HighamChapter8.lean
--
-- Source-facing entry points for Higham Chapter 8, "Triangular Systems".
-- The detailed proofs remain in the focused triangular-system modules; this
-- file provides stable chapter labels and light wrappers around those results.

import LeanFpAnalysis.FP.Algorithms.TriangularSolve
import LeanFpAnalysis.FP.Algorithms.ForwardSub
import LeanFpAnalysis.FP.Algorithms.TriangularSolveCombined
import LeanFpAnalysis.FP.Algorithms.TriangularForwardBound
import LeanFpAnalysis.FP.Algorithms.InverseBounds
import LeanFpAnalysis.FP.Algorithms.TriangularForwardComparison
import LeanFpAnalysis.FP.Algorithms.MMatrix
import LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor
import LeanFpAnalysis.FP.Analysis.HighamChapter7
import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-! ## §8.1 Backward Error Analysis -/

/-- **Algorithm 8.1**: the repository's floating-point back-substitution routine. -/
noncomputable def higham8_1_backSub (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fl_backSub fp n U b

/-- **Lemma 8.2 / Lemma 8.4, row-spec form** for Algorithm 8.1. -/
theorem higham8_2_backSub_row_spec (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hn : gammaValid fp n) :
    BackSubRowSpec fp n U b (fl_backSub fp n U b) :=
  fl_backSub_satisfies_spec fp n U b hU hn

/-- **Lemma 8.2**, row-tight form used to prove Theorem 8.3. -/
theorem higham8_2_backSub_row_tight (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hn : gammaValid fp n)
    (i : Fin n) :
    ∃ (φ : Fin n → ℝ),
      |φ i| ≤ gamma fp (n - i.val) ∧
      (∀ j, i.val < j.val → |φ j| ≤ gamma fp (j.val - i.val)) ∧
      b i = Finset.sum (Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)
              (fun j => U i j * (1 + φ j) * fl_backSub fp n U b j) :=
  backSub_row_tight fp n U b hU hn i

/-- **Theorem 8.3**: Algorithm 8.1 with Higham's row-specific constants. -/
theorem higham8_3_backSub_backward_error (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i, |ΔU i i| ≤ gamma fp (n - i.val) * |U i i|) ∧
      (∀ i j, i.val < j.val →
        |ΔU i j| ≤ gamma fp (j.val - i.val) * |U i j|) ∧
      (∀ i j, j.val < i.val → ΔU i j = 0) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * fl_backSub fp n U b j = b i :=
  backSub_backward_error_algorithm_8_1 fp n U b hU hUT hn

/-- **Theorem 8.5**, upper-triangular back-substitution specialization. -/
theorem higham8_5_backSub_backward_error (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i j, |ΔU i j| ≤ gamma fp n * |U i j|) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * fl_backSub fp n U b j = b i :=
  backSub_backward_error fp n U b hU hUT hn

/-- **Theorem 8.5**, lower-triangular forward-substitution specialization. -/
theorem higham8_5_forwardSub_backward_error (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i j, |ΔL i j| ≤ gamma fp n * |L i j|) ∧
      ∀ i, ∑ j : Fin n, (L i j + ΔL i j) * fl_forwardSub fp n L b j = b i :=
  forwardSub_backward_error fp n L b hL hLT hn

/-! ## §8.2 Forward Error Analysis -/

/-- Internal `(8.2)` transfer: a componentwise backward-error certificate with
no right-hand-side perturbation yields the Chapter 7 relative `∞`-norm forward
bound with `cond(T, x)` and `cond(T)`. -/
private theorem higham8_relative_infNorm_bound_of_componentwise_backward_error
    (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x x_hat b : Fin n → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hback : ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i))
    (hLeft : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hεcond : ε * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      ε / (1 - ε * condSkeel n hn A A_inv) *
        ch7SkeelCondAtSolutionInf n hn A A_inv x := by
  rcases hback with ⟨ΔA, hΔA, hPerturbed⟩
  have hM :
      ∀ i, ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|) ≤
        condSkeel n hn A A_inv := by
    intro i
    unfold condSkeel
    exact
      Finset.le_sup'
        (fun i' => ∑ j : Fin n, |A_inv i' j| * ∑ k : Fin n, |A j k|)
        (Finset.mem_univ i)
  have hmain :=
    componentwise_forward_error_exact_relative_infNorm n hn A A_inv x x_hat b
      ΔA (fun _ => 0) (fun i j => |A i j|) (fun _ => 0) ε hε hΔA
      (by intro i; simp)
      (by intro i j; exact abs_nonneg _)
      (by intro i; simp)
      hLeft hAx (by simpa using hPerturbed)
      (condSkeel n hn A A_inv) hM hεcond hx
  simpa [ch7SkeelCondAtSolutionInf] using hmain

/-- **Equation (8.2)** for the repository back-substitution routine:
relative `∞`-norm forward error bounded by
`cond(T,x) γ_n / (1 - cond(T) γ_n)`. -/
theorem higham8_2_backSub_relative_infNorm_bound (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hU_diag : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hInv : IsInverse n U U_inv)
    (hUx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hγ : gammaValid fp n)
    (hγcond : gamma fp n * condSkeel n hn U U_inv < 1)
    (hx : 0 < infNormVec x) :
    let x_hat := fl_backSub fp n U b
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      gamma fp n / (1 - gamma fp n * condSkeel n hn U U_inv) *
        ch7SkeelCondAtSolutionInf n hn U U_inv x := by
  dsimp
  apply higham8_relative_infNorm_bound_of_componentwise_backward_error
    n hn U U_inv x (fl_backSub fp n U b) b
  · exact gamma_nonneg fp hγ
  · rcases higham8_5_backSub_backward_error fp n U b hU_diag hUT hγ with
      ⟨ΔU, hΔU, hPerturbed⟩
    refine ⟨ΔU, ?_, ?_⟩
    · intro i j
      simpa using hΔU i j
    · simpa using hPerturbed
  · exact hInv.1
  · exact hUx
  · exact hγcond
  · exact hx

/-- **Equation (8.2)** for the repository forward-substitution routine:
relative `∞`-norm forward error bounded by
`cond(T,x) γ_n / (1 - cond(T) γ_n)`. -/
theorem higham8_2_forwardSub_relative_infNorm_bound (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (L L_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hL_diag : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsInverse n L L_inv)
    (hLx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hγ : gammaValid fp n)
    (hγcond : gamma fp n * condSkeel n hn L L_inv < 1)
    (hx : 0 < infNormVec x) :
    let x_hat := fl_forwardSub fp n L b
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      gamma fp n / (1 - gamma fp n * condSkeel n hn L L_inv) *
        ch7SkeelCondAtSolutionInf n hn L L_inv x := by
  dsimp
  apply higham8_relative_infNorm_bound_of_componentwise_backward_error
    n hn L L_inv x (fl_forwardSub fp n L b) b
  · exact gamma_nonneg fp hγ
  · rcases higham8_5_forwardSub_backward_error fp n L b hL_diag hLT hγ with
      ⟨ΔL, hΔL, hPerturbed⟩
    refine ⟨ΔL, ?_, ?_⟩
    · intro i j
      simpa using hΔL i j
    · simpa using hPerturbed
  · exact hInv.1
  · exact hLx
  · exact hγcond
  · exact hx

/-- **Equation (8.3)**: the upper-triangular stress matrix `U(α)`. -/
noncomputable def higham8_3_stressUpper (n : ℕ) (α : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then 1
    else if i.val < j.val then -α
    else 0

/-- **Equation (8.4)**: the displayed inverse-entry formula for `U(α)`. -/
noncomputable def higham8_4_stressUpperInvFormula (n : ℕ) (α : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then 1
    else if i.val < j.val then α * (1 + α) ^ (j.val - i.val - 1)
    else 0

/-- Geometric helper for the closed-form tails in the stress-matrix inverse. -/
lemma higham8_geom_one_add_mul_sum (α : ℝ) :
    ∀ m : ℕ, 1 + α * ∑ r ∈ Finset.range m, (1 + α) ^ r = (1 + α) ^ m := by
  intro m
  induction m with
  | zero =>
      simp
  | succ m ihm =>
      rw [Finset.sum_range_succ]
      calc
        1 + α * (∑ r ∈ Finset.range m, (1 + α) ^ r + (1 + α) ^ m)
            = (1 + α * ∑ r ∈ Finset.range m, (1 + α) ^ r) + α * (1 + α) ^ m := by
                ring
        _ = (1 + α) ^ m + α * (1 + α) ^ m := by
                rw [ihm]
        _ = (1 + α) ^ (m + 1) := by
                rw [pow_succ']
                ring

/-- **Equation (8.4)** support: the explicit inverse formula has column sums
`(1 + α)^j`. -/
theorem higham8_4_stressUpperInvFormula_col_sum (n : ℕ) (α : ℝ) (j : Fin n) :
    ∑ i : Fin n, higham8_4_stressUpperInvFormula n α i j = (1 + α) ^ j.val := by
  induction n with
  | zero =>
      exact Fin.elim0 j
  | succ n ih =>
      cases j using Fin.cases with
      | zero =>
          rw [Fin.sum_univ_succ]
          simp [higham8_4_stressUpperInvFormula]
      | succ j =>
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ i : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α i.succ (Fin.succ j)) =
                ∑ i : Fin n, higham8_4_stressUpperInvFormula n α i j := by
            apply Finset.sum_congr rfl
            intro i _hi
            simp [higham8_4_stressUpperInvFormula]
          have hhead :
              higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) =
                α * (1 + α) ^ j.val := by
            have hzero : (0 : Fin (n + 1)) ≠ Fin.succ j := by
              intro h
              exact Fin.succ_ne_zero j h.symm
            simp [higham8_4_stressUpperInvFormula, hzero]
          calc
            higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) +
                ∑ i : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α i.succ (Fin.succ j)
                =
              α * (1 + α) ^ j.val +
                ∑ i : Fin n, higham8_4_stressUpperInvFormula n α i j := by
                  rw [hhead, htail]
            _ = α * (1 + α) ^ j.val + (1 + α) ^ j.val := by
                  rw [ih j]
            _ = (1 + α) ^ (Fin.succ j).val := by
                  rw [show (Fin.succ j).val = j.val + 1 by rfl, pow_succ']
                  ring

/-- **Equation (8.4)** support: the explicit inverse formula has row sums
`(1 + α)^(n - 1 - i)`. -/
theorem higham8_4_stressUpperInvFormula_row_sum (n : ℕ) (α : ℝ) (i : Fin n) :
    ∑ j : Fin n, higham8_4_stressUpperInvFormula n α i j =
      (1 + α) ^ (n - 1 - i.val) := by
  induction n with
  | zero =>
      exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ j : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α 0 j.succ) =
                α * ∑ j : Fin n, (1 + α) ^ j.val := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            have hzero : (0 : Fin (n + 1)) ≠ j.succ := by
              intro h
              exact Fin.succ_ne_zero j h.symm
            simp [higham8_4_stressUpperInvFormula, hzero]
          calc
            higham8_4_stressUpperInvFormula (n + 1) α 0 0 +
                ∑ j : Fin n, higham8_4_stressUpperInvFormula (n + 1) α 0 j.succ
                =
              1 + α * ∑ j : Fin n, (1 + α) ^ j.val := by
                  rw [htail]
                  simp [higham8_4_stressUpperInvFormula]
            _ = 1 + α * ∑ r ∈ Finset.range n, (1 + α) ^ r := by
                  rw [Fin.sum_univ_eq_sum_range]
            _ = (1 + α) ^ n := higham8_geom_one_add_mul_sum α n
            _ = (1 + α) ^ ((n + 1) - 1 - (0 : Fin (n + 1)).val) := by
                  simp
      | succ i =>
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ j : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α (Fin.succ i) j.succ) =
                ∑ j : Fin n, higham8_4_stressUpperInvFormula n α i j := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [higham8_4_stressUpperInvFormula]
          calc
            higham8_4_stressUpperInvFormula (n + 1) α (Fin.succ i) 0 +
                ∑ j : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α (Fin.succ i) j.succ
                =
              ∑ j : Fin n, higham8_4_stressUpperInvFormula n α i j := by
                  rw [htail]
                  simp [higham8_4_stressUpperInvFormula]
            _ = (1 + α) ^ (n - 1 - i.val) := ih i
            _ = (1 + α) ^ ((n + 1) - 1 - (Fin.succ i).val) := by
                  have hexp : n - 1 - i.val = n - (i.val + 1) := by
                    have hi : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
                    omega
                  simpa using congrArg (fun m : Nat => (1 + α) ^ m) hexp

/-- **Equation (8.4)**: the displayed inverse-entry formula is a genuine right
inverse of the stress matrix `U(α)`. -/
theorem higham8_4_stressUpperInvFormula_isRightInverse (n : ℕ) (α : ℝ) :
    IsRightInverse n (higham8_3_stressUpper n α) (higham8_4_stressUpperInvFormula n α) := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro i j
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α 0 k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ 0) = 0 := by
                apply Finset.sum_eq_zero
                intro k _hk
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
              rw [htail]
              simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
          | succ j =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α 0 k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)) =
                    -α * ∑ k : Fin n, higham8_4_stressUpperInvFormula n α k j := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _hk
                have hzero : (0 : Fin (n + 1)) ≠ k.succ := by
                  intro h
                  exact Fin.succ_ne_zero k h.symm
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula, hzero]
              have hzeroj : (0 : Fin (n + 1)) ≠ Fin.succ j := by
                intro h
                exact Fin.succ_ne_zero j h.symm
              calc
                higham8_3_stressUpper (n + 1) α 0 0 *
                    higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) +
                    ∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α 0 k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)
                    =
                  α * (1 + α) ^ j.val - α * ∑ k : Fin n,
                    higham8_4_stressUpperInvFormula n α k j := by
                      rw [htail]
                      simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula, hzeroj]
                      ring
                _ = α * (1 + α) ^ j.val - α * (1 + α) ^ j.val := by
                      rw [higham8_4_stressUpperInvFormula_col_sum n α j]
                _ = 0 := by ring
                _ = (if (0 : Fin (n + 1)) = Fin.succ j then 1 else 0) := by
                      simp [hzeroj]
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α (Fin.succ i) k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ 0) = 0 := by
                apply Finset.sum_eq_zero
                intro k _hk
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
              rw [htail]
              simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
          | succ j =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α (Fin.succ i) k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)) =
                    ∑ k : Fin n,
                      higham8_3_stressUpper n α i k *
                        higham8_4_stressUpperInvFormula n α k j := by
                apply Finset.sum_congr rfl
                intro k _hk
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
              calc
                higham8_3_stressUpper (n + 1) α (Fin.succ i) 0 *
                    higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) +
                    ∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α (Fin.succ i) k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)
                    =
                  ∑ k : Fin n,
                    higham8_3_stressUpper n α i k *
                      higham8_4_stressUpperInvFormula n α k j := by
                      rw [htail]
                      simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
                _ = (if i = j then 1 else 0) := ih i j
                _ = (if (Fin.succ i : Fin (n + 1)) = Fin.succ j then 1 else 0) := by
                      simp

/-- **Equation (8.4)**: the displayed inverse-entry formula is a genuine
two-sided inverse of the stress matrix `U(α)`. -/
theorem higham8_4_stressUpperInvFormula_isInverse (n : ℕ) (α : ℝ) :
    IsInverse n (higham8_3_stressUpper n α) (higham8_4_stressUpperInvFormula n α) := by
  have hRight := higham8_4_stressUpperInvFormula_isRightInverse n α
  exact ⟨ch7_isLeftInverse_of_isRightInverse hRight, hRight⟩

/-- **Problem 8.2**, Appendix A witness `T(λ)`. -/
noncomputable def higham8_2_ratioWitness (lam : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 / lam
    else if i.val = 0 ∧ j.val = 1 then 1
    else if i.val = 0 ∧ j.val = 2 then 1
    else if i.val = 1 ∧ j.val = 1 then 1 / lam
    else if i.val = 1 ∧ j.val = 2 then 1 / lam
    else if i.val = 2 ∧ j.val = 2 then 1 / lam ^ 2
    else 0

/-- **Problem 8.2**, explicit inverse for the Appendix A witness `T(λ)`. -/
noncomputable def higham8_2_ratioWitnessInv (lam : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then lam
    else if i.val = 0 ∧ j.val = 1 then -(lam ^ 2)
    else if i.val = 1 ∧ j.val = 1 then lam
    else if i.val = 1 ∧ j.val = 2 then -(lam ^ 2)
    else if i.val = 2 ∧ j.val = 2 then lam ^ 2
    else 0

/-- **Problem 8.2**, the explicit comparison matrix `M(T(λ))`. -/
noncomputable def higham8_2_ratioWitnessComparison (lam : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 / lam
    else if i.val = 0 ∧ j.val = 1 then -1
    else if i.val = 0 ∧ j.val = 2 then -1
    else if i.val = 1 ∧ j.val = 1 then 1 / lam
    else if i.val = 1 ∧ j.val = 2 then -(1 / lam)
    else if i.val = 2 ∧ j.val = 2 then 1 / lam ^ 2
    else 0

/-- **Problem 8.2**, explicit inverse of `M(T(λ))`. -/
noncomputable def higham8_2_ratioWitnessComparisonInv (lam : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then lam
    else if i.val = 0 ∧ j.val = 1 then lam ^ 2
    else if i.val = 0 ∧ j.val = 2 then 2 * lam ^ 3
    else if i.val = 1 ∧ j.val = 1 then lam
    else if i.val = 1 ∧ j.val = 2 then lam ^ 2
    else if i.val = 2 ∧ j.val = 2 then lam ^ 2
    else 0

/-- The Appendix A witness is upper triangular. -/
lemma higham8_2_ratioWitness_upper (lam : ℝ) :
    ∀ i j : Fin 3, j.val < i.val → higham8_2_ratioWitness lam i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [higham8_2_ratioWitness] at hij ⊢

/-- The Appendix A inverse formula is a genuine two-sided inverse of `T(λ)`. -/
theorem higham8_2_ratioWitness_isInverse (lam : ℝ) (hlam : lam ≠ 0) :
    IsInverse 3 (higham8_2_ratioWitness lam) (higham8_2_ratioWitnessInv lam) := by
  refine ⟨?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, higham8_2_ratioWitness, higham8_2_ratioWitnessInv, hlam] <;>
    field_simp [hlam] <;> ring

/-- The comparison matrix of the Appendix A witness is the expected signed
upper-triangular matrix. -/
theorem higham8_2_ratioWitness_comparison_eq (lam : ℝ) (hlam : 0 ≤ lam) :
    comparisonMatrix 3 (higham8_2_ratioWitness lam) =
      higham8_2_ratioWitnessComparison lam := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [comparisonMatrix, higham8_2_ratioWitness, higham8_2_ratioWitnessComparison,
      abs_of_nonneg hlam]

/-- The explicit Appendix A formula is a genuine inverse of `M(T(λ))`. -/
theorem higham8_2_ratioWitnessComparisonInv_isInverse (lam : ℝ) (hlam : lam ≠ 0) :
    IsInverse 3 (higham8_2_ratioWitnessComparison lam)
      (higham8_2_ratioWitnessComparisonInv lam) := by
  refine ⟨?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, higham8_2_ratioWitnessComparison,
      higham8_2_ratioWitnessComparisonInv, hlam] <;>
    field_simp [hlam] <;> ring

private theorem higham8_2_ratioWitnessInv_row0_abs_sum (lam : ℝ) (hlam : 0 ≤ lam) :
    ∑ j : Fin 3, |higham8_2_ratioWitnessInv lam 0 j| = lam + lam ^ 2 := by
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg hlam,
    abs_of_nonneg (sq_nonneg lam)]

private theorem higham8_2_ratioWitnessComparisonInv_row0_abs_sum (lam : ℝ)
    (hlam : 0 ≤ lam) :
    ∑ j : Fin 3, |higham8_2_ratioWitnessComparisonInv lam 0 j| =
      lam + lam ^ 2 + 2 * lam ^ 3 := by
  have hcube : 0 ≤ lam ^ 3 := by
    calc
      0 ≤ lam * lam ^ 2 := mul_nonneg hlam (sq_nonneg lam)
      _ = lam ^ 3 := by ring
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessComparisonInv,
    abs_of_nonneg hlam, abs_of_nonneg (sq_nonneg lam), abs_of_nonneg hcube]

private theorem higham8_2_ratioWitnessComparisonInv_col2_abs_sum (lam : ℝ)
    (hlam : 0 ≤ lam) :
    ∑ i : Fin 3, |higham8_2_ratioWitnessComparisonInv lam i 2| =
      2 * lam ^ 3 + 2 * lam ^ 2 := by
  have hcube : 0 ≤ lam ^ 3 := by
    calc
      0 ≤ lam * lam ^ 2 := mul_nonneg hlam (sq_nonneg lam)
      _ = lam ^ 3 := by ring
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessComparisonInv,
    abs_of_nonneg (sq_nonneg lam), abs_of_nonneg hcube]
  ring

private theorem higham8_2_ratioWitnessInv_infNorm_le (lam : ℝ) (hlam : 1 ≤ lam) :
    infNorm (higham8_2_ratioWitnessInv lam) ≤ 2 * lam ^ 2 := by
  have hlam0 : 0 ≤ lam := by linarith
  apply infNorm_le_of_row_sum_le
  · intro i
    fin_cases i
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg hlam0,
        abs_of_nonneg (sq_nonneg lam)]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg hlam0, abs_of_nonneg (sq_nonneg lam)]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg (sq_nonneg lam)]
      nlinarith
  · nlinarith

private theorem higham8_2_ratioWitnessInv_oneNorm_le (lam : ℝ) (hlam : 1 ≤ lam) :
    oneNorm (higham8_2_ratioWitnessInv lam) ≤ 2 * lam ^ 2 := by
  have hlam0 : 0 ≤ lam := by linarith
  apply oneNorm_le_of_col_sum_le
  · intro j
    fin_cases j
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg hlam0]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg hlam0, abs_of_nonneg (sq_nonneg lam)]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg (sq_nonneg lam)]
      nlinarith
  · nlinarith

/-- **Problem 8.2**, appendix witness in the infinity norm:
for `λ ≥ 1`, the ratio `‖M(T(λ))⁻¹‖∞ / ‖T(λ)⁻¹‖∞` is at least `λ`. -/
theorem higham8_2_comparisonInverseInfNormRatio_ge_lambda (lam : ℝ) (hlam : 1 ≤ lam) :
    lam ≤
      infNorm (higham8_2_ratioWitnessComparisonInv lam) /
        infNorm (higham8_2_ratioWitnessInv lam) := by
  have hlam0 : 0 ≤ lam := by linarith
  have hlamne : lam ≠ 0 := by linarith
  have hnum_row :=
    row_sum_le_infNorm (higham8_2_ratioWitnessComparisonInv lam) (0 : Fin 3)
  rw [higham8_2_ratioWitnessComparisonInv_row0_abs_sum lam hlam0] at hnum_row
  have hnum : 2 * lam ^ 3 ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) := by
    nlinarith
  have hden := higham8_2_ratioWitnessInv_infNorm_le lam hlam
  have hden_row := row_sum_le_infNorm (higham8_2_ratioWitnessInv lam) (0 : Fin 3)
  rw [higham8_2_ratioWitnessInv_row0_abs_sum lam hlam0] at hden_row
  have hden_pos : 0 < infNorm (higham8_2_ratioWitnessInv lam) := by
    nlinarith
  have hscale_pos : 0 < 2 * lam ^ 2 := by nlinarith
  have hmid :
      infNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) ≤
        infNorm (higham8_2_ratioWitnessComparisonInv lam) /
          infNorm (higham8_2_ratioWitnessInv lam) := by
    field_simp [hscale_pos.ne', hden_pos.ne']
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hden
        (infNorm_nonneg (higham8_2_ratioWitnessComparisonInv lam)))
  calc
    lam = (2 * lam ^ 3) / (2 * lam ^ 2) := by
          field_simp [hlamne]
    _ ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) :=
          div_le_div_of_nonneg_right hnum hscale_pos.le
    _ ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) /
          infNorm (higham8_2_ratioWitnessInv lam) := hmid

/-- **Problem 8.2**, appendix witness in the one norm:
for `λ ≥ 1`, the ratio `‖M(T(λ))⁻¹‖₁ / ‖T(λ)⁻¹‖₁` is at least `λ`. -/
theorem higham8_2_comparisonInverseOneNormRatio_ge_lambda (lam : ℝ) (hlam : 1 ≤ lam) :
    lam ≤
      oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
        oneNorm (higham8_2_ratioWitnessInv lam) := by
  have hlam0 : 0 ≤ lam := by linarith
  have hlamne : lam ≠ 0 := by linarith
  have hnum_col :=
    col_sum_le_oneNorm (higham8_2_ratioWitnessComparisonInv lam) (2 : Fin 3)
  rw [higham8_2_ratioWitnessComparisonInv_col2_abs_sum lam hlam0] at hnum_col
  have hnum : 2 * lam ^ 3 ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) := by
    nlinarith
  have hden := higham8_2_ratioWitnessInv_oneNorm_le lam hlam
  have hden_col :=
    col_sum_le_oneNorm (higham8_2_ratioWitnessInv lam) (2 : Fin 3)
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg (sq_nonneg lam)]
    at hden_col
  have hden_pos : 0 < oneNorm (higham8_2_ratioWitnessInv lam) := by
    nlinarith
  have hscale_pos : 0 < 2 * lam ^ 2 := by nlinarith
  have hmid :
      oneNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) ≤
        oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
          oneNorm (higham8_2_ratioWitnessInv lam) := by
    field_simp [hscale_pos.ne', hden_pos.ne']
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hden
        (oneNorm_nonneg (higham8_2_ratioWitnessComparisonInv lam)))
  calc
    lam = (2 * lam ^ 3) / (2 * lam ^ 2) := by
          field_simp [hlamne]
    _ ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) :=
          div_le_div_of_nonneg_right hnum hscale_pos.le
    _ ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
          oneNorm (higham8_2_ratioWitnessInv lam) := hmid

/-- **Problem 8.2**: the Appendix A witness makes both the `1`- and `∞`-norm
comparison-inverse ratios arbitrarily large. -/
theorem higham8_2_comparisonInverseRatios_arbitrarily_large (R : ℝ) :
    ∃ lam : ℝ, 1 ≤ lam ∧
      R ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) /
            infNorm (higham8_2_ratioWitnessInv lam) ∧
      R ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
            oneNorm (higham8_2_ratioWitnessInv lam) := by
  refine ⟨max 1 R, le_max_left _ _, ?_, ?_⟩
  · exact le_trans (le_max_right _ _) <|
      higham8_2_comparisonInverseInfNormRatio_ge_lambda (max 1 R) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) <|
      higham8_2_comparisonInverseOneNormRatio_ge_lambda (max 1 R) (le_max_left _ _)

/-- **Lemma 8.6**: diagonal-dominance bound for `|U⁻¹||U|`. -/
theorem higham8_6_inv_abs_mul_bound_diagDom (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    ∀ i j : Fin n, i.val ≤ j.val →
      ∑ k : Fin n, |U_inv i k| * |U k j| ≤ 2 ^ (j.val - i.val) :=
  inv_abs_mul_bound_diagDom n U U_inv hDD hInv

/-- **Theorem 8.7**: componentwise forward error under condition (8.5). -/
theorem higham8_7_backSub_forward_error_diagDom (fp : FPModel) (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv)
    (hTx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hn : gammaValid fp n) :
    let x_hat := fl_backSub fp n U b
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      2 ^ (n - i.val) * gamma fp n *
          Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val ≤ j.val))
            ⟨i, by simp [Finset.mem_filter]⟩ (fun j => |x_hat j|) :=
  backSub_forward_error_diagDom fp n U U_inv x b hDD hInv hTx hn

/-- **Equation (8.6)**: lower-triangular analogue of condition (8.5). -/
def higham8_6_diagDominantLower (n : ℕ) (L : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, i.val < j.val → L i j = 0) ∧
  (∀ i : Fin n, L i i ≠ 0) ∧
  (∀ i j : Fin n, j.val < i.val → |L i j| ≤ |L i i|)

/-- Source condition preceding **Lemma 8.8**, as printed in the PDF:
`|u_ii| ≤ sum_{j=i+1}^n |u_ij|` for rows `i = 1:n-1`, together with upper
triangular shape.  The inequality direction is intentionally the source text's
direction. -/
def higham8_rowDominantUpperSource (n : ℕ) (U : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
  ∀ i : Fin n, i.val + 1 < n →
    |U i i| ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |U i j|

/-- Corrected source-facing condition for **Lemma 8.8**: `U` is upper
triangular with nonzero diagonal and the strict-upper absolute row sum is
bounded by the diagonal magnitude in each row. -/
def higham8_8_rowDiagDominantUpper (n : ℕ) (U : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
  (∀ i : Fin n, U i i ≠ 0) ∧
  (∀ i : Fin n,
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |U i j| ≤ |U i i|)

/-- **Lemma 8.8**, corrected theorem surface after the source audit.

If an upper-triangular matrix has nonzero diagonal and each strict-upper row
sum is bounded by the diagonal magnitude, then its Skeel condition number is
at most `2n - 1`. -/
theorem higham8_8_rowDiagDominantUpper_condSkeel_bound (n : ℕ) (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (hRD : higham8_8_rowDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    condSkeel n hn U U_inv ≤ 2 * (n : ℝ) - 1 := by
  rcases hRD with ⟨hUT, hDiag, hRow⟩
  rcases hInv with ⟨hLInv, hRInv⟩
  have hInv_ut := inv_upper_tri n U U_inv hUT hDiag hLInv
  let V : Fin n → Fin n → ℝ := fun a b => U a b / U a a
  let V_inv : Fin n → Fin n → ℝ := fun a b => U_inv a b * U b b
  have hVT : ∀ a b : Fin n, b.val < a.val → V a b = 0 := by
    intro a b hab
    simp [V, hUT a b hab]
  have hV_unit : ∀ a : Fin n, V a a = 1 := by
    intro a
    simp [V, hDiag a]
  have hV_row : ∀ a : Fin n,
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |V a j| ≤ 1 := by
    intro a
    calc
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |V a j|
          = (1 / |U a a|) *
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |U a j| := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              simp [V, div_eq_mul_inv, mul_comm]
      _ ≤ (1 / |U a a|) * |U a a| := by
            exact mul_le_mul_of_nonneg_left (hRow a) (one_div_nonneg.mpr (abs_nonneg _))
      _ = 1 := by
            rw [one_div, inv_mul_cancel₀]
            exact abs_ne_zero.mpr (hDiag a)
  have hVinv_ut : ∀ a b : Fin n, b.val < a.val → V_inv a b = 0 := by
    intro a b hab
    simp [V_inv, hInv_ut a b hab]
  have hVinv_diag : ∀ a : Fin n, V_inv a a = 1 := by
    intro a
    simp [V_inv, inv_diag_entry n U U_inv hUT hDiag hLInv hInv_ut a, hDiag a]
  have hVRInv : IsRightInverse n V V_inv := by
    intro a b
    unfold V V_inv
    have hsimp :
        ∑ k : Fin n, (U a k / U a a) * (U_inv k b * U b b) =
          (U b b / U a a) * ∑ k : Fin n, U a k * U_inv k b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      field_simp [hDiag a]
    rw [hsimp, hRInv a b]
    by_cases hab : a = b
    · subst hab
      simp [hDiag a]
    · simp [hab]
  have hVinv_le_one :=
    unitUpperTri_inv_entry_le_one_of_row_sum_le_one
      n V V_inv hVT hV_unit hV_row hVRInv hVinv_ut hVinv_diag
  let rowMass : Fin n → ℝ := fun j => ∑ k : Fin n, |U j k|
  have hrow_le_two_diag : ∀ j : Fin n, rowMass j ≤ 2 * |U j j| := by
    intro j
    unfold rowMass
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hrest_eq :
        ∑ k ∈ Finset.univ.erase j, |U j k| =
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val < k.val), |U j k| := by
      symm
      apply Finset.sum_subset
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
      · intro k hk hknot
        rw [Finset.mem_erase] at hk
        have hknot' : ¬ j.val < k.val := by
          intro hlt
          exact hknot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
        have hlt : k.val < j.val := by
          by_contra hge
          push_neg at hge
          exact hk.1 (Fin.ext (by omega))
        rw [hUT j k hlt, abs_zero]
    rw [hrest_eq]
    linarith [hRow j]
  let last : Fin n := ⟨n - 1, by omega⟩
  have hrow_last : rowMass last = |U last last| := by
    unfold rowMass
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ last)]
    suffices hrest : ∑ k ∈ Finset.univ.erase last, |U last k| = 0 by
      linarith
    apply Finset.sum_eq_zero
    intro k hk
    have hk_ne : k ≠ last := Finset.ne_of_mem_erase hk
    have hlt : k.val < last.val := by
      have hk_last : k.val ≠ n - 1 := by
        intro hk_eq
        apply hk_ne
        exact Fin.ext (by simpa [last] using hk_eq)
      show k.val < n - 1
      omega
    rw [hUT last k hlt, abs_zero]
  have hsum_upper :
      ∀ i : Fin n,
      ∑ j : Fin n, |U_inv i j| * rowMass j =
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val),
          |U_inv i j| * rowMass j := by
    intro i
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
    rw [hInv_ut i j hj, abs_zero, zero_mul]
  unfold condSkeel
  apply Finset.sup'_le
  intro i _
  change ∑ j : Fin n, |U_inv i j| * rowMass j ≤ 2 * (n : ℝ) - 1
  let S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => i.val ≤ j.val)
  have hlast_mem : last ∈ S := by
    simp [S, last]
    show i.val ≤ n - 1
    omega
  have hlast_term : |U_inv i last| * rowMass last ≤ 1 := by
    rw [hrow_last]
    calc
      |U_inv i last| * |U last last| = |V_inv i last| := by
        simp [V_inv, abs_mul, mul_comm]
      _ ≤ 1 := hVinv_le_one i last (by
        show i.val ≤ n - 1
        omega)
  have hrest_le :
      ∑ j ∈ S.erase last, |U_inv i j| * rowMass j ≤
        ∑ j ∈ S.erase last, (2 : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjS : j ∈ S := (Finset.mem_erase.mp hj).2
    have hij : i.val ≤ j.val := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
      exact hjS
    calc
      |U_inv i j| * rowMass j ≤ |U_inv i j| * (2 * |U j j|) := by
        exact mul_le_mul_of_nonneg_left (hrow_le_two_diag j) (abs_nonneg _)
      _ = 2 * |V_inv i j| := by
        ring_nf
        simp [V_inv, abs_mul, mul_comm]
      _ ≤ 2 := by
        have hle : |V_inv i j| ≤ 1 := hVinv_le_one i j hij
        nlinarith
  have hrest_subset :
      ∑ j ∈ S.erase last, (2 : ℝ) ≤ ∑ j ∈ Finset.univ.erase last, (2 : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro j hj
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩)
      (by
        intro j _ _
        positivity)
  calc
    ∑ j : Fin n, |U_inv i j| * rowMass j
        = ∑ j ∈ S, |U_inv i j| * rowMass j := by
            simpa [S] using hsum_upper i
    _ = |U_inv i last| * rowMass last +
          ∑ j ∈ S.erase last, |U_inv i j| * rowMass j := by
            rw [← Finset.add_sum_erase _ _ hlast_mem]
    _ ≤ 1 + ∑ j ∈ S.erase last, (2 : ℝ) := by
          exact add_le_add hlast_term hrest_le
    _ ≤ 1 + ∑ j ∈ Finset.univ.erase last, (2 : ℝ) := by
          simpa [add_comm] using add_le_add_left hrest_subset 1
    _ = 2 * (n : ℝ) - 1 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ last),
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
          ring

/-- The absolute value of the comparison matrix agrees entrywise with `|T|`. -/
private lemma comparisonMatrix_abs_apply (n : ℕ) (T : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    |comparisonMatrix n T i j| = |T i j| := by
  by_cases hij : i = j
  · subst hij
    simp [comparisonMatrix]
  · simp [comparisonMatrix, hij]

/-- Entrywise decomposition of `|M(T)|` as `2 diag(|t_ii|) - M(T)`. -/
private lemma comparisonMatrix_abs_eq_two_diag_sub (n : ℕ) (T : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    |comparisonMatrix n T i j| =
      2 * diagMatrix (fun k : Fin n => |T k k|) i j - comparisonMatrix n T i j := by
  by_cases hij : i = j
  · subst hij
    simp [comparisonMatrix, diagMatrix]
    ring
  · simp [comparisonMatrix, diagMatrix, hij]

/-- **Lemma 8.9**, explicit image vector
`(2 M(T)⁻¹ diag(|t_ii|) - I)|x|`. -/
noncomputable def higham8_9_comparisonImage (n : ℕ)
    (T M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 2 * ∑ j : Fin n, M_inv i j * |T j j| * |x j| - |x i|

/-- **Lemma 8.9**, equality part for the comparison matrix:
`cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_comparisonMatrix_condAtSolution_eq (n : ℕ) (hn : 0 < n)
    (T M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hM_nonneg : ∀ i j : Fin n, 0 ≤ M_inv i j)
    (hM_left : IsLeftInverse n (comparisonMatrix n T) M_inv) :
    ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x =
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have hdiagMul :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k =
          M_inv i k * |T k k| := by
    intro i k
    simpa [matMul] using
      matMul_diagMatrix_right M_inv (fun l : Fin n => |T l l|) i k
  have hleftEntry :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * comparisonMatrix n T j k = idMatrix n i k := by
    intro i k
    simpa [idMatrix] using hM_left i k
  have hcomparisonEntry :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k| =
          2 * (M_inv i k * |T k k|) - idMatrix n i k := by
    intro i k
    calc
      ∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k|
          = ∑ j : Fin n,
              (2 * (M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k) -
                M_inv i j * comparisonMatrix n T j k) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [comparisonMatrix_abs_eq_two_diag_sub n T j k]
              ring
      _ = 2 * ∑ j : Fin n, M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k -
            ∑ j : Fin n, M_inv i j * comparisonMatrix n T j k := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * (M_inv i k * |T k k|) - idMatrix n i k := by
            rw [hdiagMul i k, hleftEntry i k]
  have happly :
      ∀ i : Fin n,
        ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
            (fun _ => 0) x i =
          higham8_9_comparisonImage n T M_inv x i := by
    intro i
    unfold ch7AmplifiedRhsEF higham8_9_comparisonImage
    calc
      ∑ j : Fin n, |M_inv i j| *
          (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0)
          = ∑ j : Fin n, M_inv i j *
              ∑ k : Fin n, |comparisonMatrix n T j k| * |x k| := by
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_of_nonneg (hM_nonneg i j)]
              simp
      _ = ∑ k : Fin n,
            (∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k|) * |x k| := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ k : Fin n,
            (2 * (M_inv i k * |T k k|) - idMatrix n i k) * |x k| := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hcomparisonEntry i k]
      _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| -
            ∑ k : Fin n, idMatrix n i k * |x k| := by
            calc
              ∑ k : Fin n, (2 * (M_inv i k * |T k k|) - idMatrix n i k) * |x k|
                  = ∑ k : Fin n,
                      (2 * (M_inv i k * |T k k| * |x k|) -
                        idMatrix n i k * |x k|) := by
                        apply Finset.sum_congr rfl
                        intro k _
                        ring
              _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| -
                    ∑ k : Fin n, idMatrix n i k * |x k| := by
                      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| - |x i| := by
            simp [idMatrix]
  have hnonneg :
      ∀ i : Fin n, 0 ≤ higham8_9_comparisonImage n T M_inv x i := by
    intro i
    rw [← happly i]
    exact
      ch7AmplifiedRhsEF_nonneg n M_inv
        (fun a b => |comparisonMatrix n T a b|) (fun _ => 0) x
        (by
          intro a b
          exact abs_nonneg _)
        (by
          intro a
          simp)
        i
  have hforward :
      ch7ForwardBoundEF n hn M_inv (fun a b => |comparisonMatrix n T a b|)
          (fun _ => 0) x =
        infNormVec (higham8_9_comparisonImage n T M_inv x) := by
    unfold ch7ForwardBoundEF
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      rw [happly i, ← abs_of_nonneg (hnonneg i)]
      exact abs_le_infNormVec (higham8_9_comparisonImage n T M_inv x) i
    · apply infNormVec_le_of_abs_le
      · intro i
        rw [abs_of_nonneg (hnonneg i), ← happly i]
        exact
          Finset.le_sup'
            (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
              (fun _ => 0) x)
            (Finset.mem_univ i)
      · exact
          ch7ForwardBoundEF_nonneg n hn M_inv
            (fun a b => |comparisonMatrix n T a b|) (fun _ => 0) x
            (by
              intro a b
              exact abs_nonneg _)
            (by
              intro a
              simp)
  unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf
  rw [hforward]

/-- **Lemma 8.9**, inequality part:
`cond(T,x) ≤ cond(M(T),x)` once `|T⁻¹| ≤ M(T)⁻¹` and `M(T)⁻¹ ≥ 0` are known. -/
theorem higham8_9_condAtSolution_le_comparisonMatrix (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (habsInv : ∀ i j : Fin n, |T_inv i j| ≤ M_inv i j)
    (hM_nonneg : ∀ i j : Fin n, 0 ≤ M_inv i j) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := by
  have hnum :
      ch7ForwardBoundEF n hn T_inv (fun a b => |T a b|) (fun _ => 0) x ≤
        ch7ForwardBoundEF n hn M_inv (fun a b => |comparisonMatrix n T a b|)
          (fun _ => 0) x := by
    unfold ch7ForwardBoundEF
    apply Finset.sup'_le
    intro i _
    unfold ch7AmplifiedRhsEF
    calc
      ∑ j : Fin n, |T_inv i j| * (∑ k : Fin n, |T j k| * |x k| + 0)
          ≤ ∑ j : Fin n, M_inv i j * (∑ k : Fin n, |T j k| * |x k| + 0) := by
              apply Finset.sum_le_sum
              intro j _
              have hinner_nonneg : 0 ≤ ∑ k : Fin n, |T j k| * |x k| + 0 := by
                positivity
              exact mul_le_mul_of_nonneg_right (habsInv i j) hinner_nonneg
      _ = ∑ j : Fin n, M_inv i j *
            (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0) := by
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            have hsumEq :
                ∑ k : Fin n, |T j k| * |x k| =
                  ∑ k : Fin n, |comparisonMatrix n T j k| * |x k| := by
              apply Finset.sum_congr rfl
              intro k _
              rw [comparisonMatrix_abs_apply]
            rw [hsumEq]
      _ = ∑ j : Fin n, |M_inv i j| *
            (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hM_nonneg i j)]
      _ = ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
            (fun _ => 0) x i := by
            rfl
      _ ≤ Finset.sup' Finset.univ
            (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
            (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
              (fun _ => 0) x) := by
            exact
              Finset.le_sup'
                (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
                  (fun _ => 0) x)
                (Finset.mem_univ i)
  unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf
  exact div_le_div_of_nonneg_right hnum (infNormVec_nonneg x)

/-- **Lemma 8.9**, upper-triangular source wrapper:
`cond(T,x) ≤ cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_upperTriangular_condAtSolution_le_comparison_eq (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag : ∀ i : Fin n, T i i ≠ 0)
    (hInv : IsInverse n T T_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n T) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have habsInv :=
    abs_inv_le_compMatrix_inv n T T_inv M_inv
      hUT hT_diag hInv hM_RInv hM_inv_ut
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n T i i := by
    intro i
    simp [comparisonMatrix]
    exact hT_diag i
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n T i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n T i j = 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n T) M_inv
      hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  have hle :=
    higham8_9_condAtSolution_le_comparisonMatrix n hn T T_inv M_inv x habsInv hM_nonneg
  have heq :=
    higham8_9_comparisonMatrix_condAtSolution_eq n hn T M_inv x
      hM_nonneg (ch7_isLeftInverse_of_isRightInverse hM_RInv)
  calc
    ch7SkeelCondAtSolutionInf n hn T T_inv x
        ≤ ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := hle
    _ = infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := heq

/-- **Lemma 8.9**, lower-triangular source wrapper:
`cond(T,x) ≤ cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_lowerTriangular_condAtSolution_le_comparison_eq (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → T i j = 0)
    (hT_diag : ∀ i : Fin n, T i i ≠ 0)
    (hInv : IsInverse n T T_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n T) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have habsInv :=
    abs_inv_le_compMatrix_inv_lowerTri n T T_inv M_inv
      hLT hT_diag hInv hM_RInv hM_inv_lt
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n T i i := by
    intro i
    simp [comparisonMatrix]
    exact hT_diag i
  have hM_offdiag : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n T i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_lt : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n T i j = 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega), hLT i j hij]
  have hM_nonneg :=
    lower_tri_mmatrix_inv_nonneg n (comparisonMatrix n T) M_inv
      hM_lt hM_diag_pos hM_offdiag hM_RInv hM_inv_lt
  have hle :=
    higham8_9_condAtSolution_le_comparisonMatrix n hn T T_inv M_inv x habsInv hM_nonneg
  have heq :=
    higham8_9_comparisonMatrix_condAtSolution_eq n hn T M_inv x
      hM_nonneg (ch7_isLeftInverse_of_isRightInverse hM_RInv)
  calc
    ch7SkeelCondAtSolutionInf n hn T T_inv x
        ≤ ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := hle
    _ = infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := heq

/-- **Theorem 8.10**, formalized with Higham's exact `μ` recurrence rather
than an informal `O(u^2)` abbreviation. -/
theorem higham8_10_forwardSub_forward_error_mu_bound (fp : FPModel) (n : ℕ)
    (L L_inv M_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsInverse n L L_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n L) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1)) :
    let x_hat := fl_forwardSub fp n L b
    let y := fun i => ∑ j : Fin n, M_inv i j * |b j|
    ∀ i : Fin n, |x i - x_hat i| ≤ mu fp n i.val * y i :=
  forwardSub_forward_error_mu_bound fp n L L_inv M_inv x b hL_diag hLT hInv
    hM_RInv hM_inv_lt hTx hn hn1

/-- **Corollary 8.11**, μ-form for lower triangular M-matrices and `b ≥ 0`. -/
theorem higham8_11_mmatrix_forwardSub_relative_error (fp : FPModel) (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag_pos : ∀ i : Fin n, 0 < L i i)
    (hL_offdiag : ∀ i j : Fin n, j.val < i.val → L i j ≤ 0)
    (hInv : IsInverse n L L_inv)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (h2n : gammaValid fp (2 * n)) :
    let x_hat := fl_forwardSub fp n L b
    (∀ i, 0 ≤ x i) ∧
    (∀ i, 0 ≤ x_hat i) ∧
    (∀ i, |x i - x_hat i| ≤ mu fp n i.val * |x i|) :=
  mmatrix_forwardSub_relative_error fp n L L_inv x b hLT hL_diag_pos
    hL_offdiag hInv hTx hb hn hn1 h2n

/-- An upper-triangular row sum over `univ.erase i` only sees the strict-upper
entries. -/
private lemma higham8_upperTriangular_erase_sum_eq_strictUpper (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (i : Fin n) (v : Fin n → ℝ) :
    ∑ j ∈ Finset.univ.erase i, T i j * v j =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * v j := by
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
  · intro j hj hnot
    rw [Finset.mem_erase] at hj
    have hnot' : ¬ i.val < j.val := by
      intro hij
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
    have hji : j.val < i.val := by
      by_contra hge
      push_neg at hge
      exact hj.1 (Fin.ext (by omega))
    rw [hUT i j hji, zero_mul]

/-- For an upper triangular M-matrix, the comparison matrix equals the matrix
itself. -/
private theorem higham8_comparisonMatrix_eq_self_upper (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0) :
    comparisonMatrix n T = T := by
  funext i j
  unfold comparisonMatrix
  by_cases hij : i = j
  · subst hij
    simp [abs_of_pos (hT_diag_pos i)]
  · by_cases hij' : i.val < j.val
    · rw [abs_of_nonpos (hT_offdiag i j hij')]
      simp [hij]
    · have hji : j.val < i.val := by omega
      simp [hij, hUT i j hji]

/-- Exact solutions of upper-triangular M-matrix systems with nonnegative
right-hand side are nonnegative. -/
private theorem higham8_upperTriangularMMatrix_solution_nonneg (n : ℕ)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i) :
    ∀ i, 0 ≤ x i := by
  have hT_diag : ∀ i : Fin n, T i i ≠ 0 := fun i => ne_of_gt (hT_diag_pos i)
  have hInv_ut := inv_upper_tri n T T_inv hUT hT_diag hInv.1
  have hTinv_nonneg :=
    upper_tri_mmatrix_inv_nonneg n T T_inv
      hUT hT_diag_pos hT_offdiag hInv.2 hInv_ut
  have hx_eq : ∀ i : Fin n, x i = ∑ j : Fin n, T_inv i j * b j := by
    intro i
    have hLI := hInv.1 i
    have hsum :
        ∑ j : Fin n, T_inv i j * b j =
          ∑ j : Fin n, T_inv i j * (∑ k : Fin n, T j k * x k) := by
      congr 1
      funext j
      rw [hTx j]
    rw [hsum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    have hsimp : ∀ k : Fin n,
        (∑ j : Fin n, T_inv i j * T j k) * x k = (if i = k then 1 else 0) * x k := by
      intro k
      congr 1
      exact hLI k
    simp_rw [hsimp]
    simp [Finset.mem_univ]
  intro i
  rw [hx_eq i]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hTinv_nonneg i j) (hb j))

/-- Problem 8.4 row identity for the comparison-image vector under the
upper-triangular M-matrix assumptions. -/
private theorem higham8_problem8_4_comparisonImage_row_eq (n : ℕ)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (_hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    let y := higham8_9_comparisonImage n T T_inv x
    ∀ i : Fin n,
      T i i * y i =
        T i i * x i +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j := by
  intro y i
  have hy_simp : ∀ j : Fin n,
      y j = 2 * ∑ k : Fin n, T_inv j k * T k k * x k - x j := by
    intro j
    unfold y higham8_9_comparisonImage
    rw [abs_of_nonneg (hx_nonneg j)]
    apply congrArg (fun z => 2 * z - x j)
    apply Finset.sum_congr rfl
    intro k _
    rw [abs_of_pos (hT_diag_pos k), abs_of_nonneg (hx_nonneg k)]
  have hTy : ∀ i : Fin n, ∑ j : Fin n, T i j * y j = 2 * T i i * x i - b i := by
    intro i
    calc
      ∑ j : Fin n, T i j * y j
          = ∑ j : Fin n, T i j * (2 * ∑ k : Fin n, T_inv j k * T k k * x k - x j) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hy_simp j]
      _ = ∑ j : Fin n,
            (2 * (T i j * ∑ k : Fin n, T_inv j k * T k k * x k) - T i j * x j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = 2 * ∑ j : Fin n, T i j * ∑ k : Fin n, T_inv j k * T k k * x k -
            ∑ j : Fin n, T i j * x j := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k -
            ∑ j : Fin n, T i j * x j := by
              have hswap :
                  ∑ j : Fin n, T i j * ∑ k : Fin n, T_inv j k * T k k * x k
                    = ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k := by
                calc
                  ∑ j : Fin n, T i j * ∑ k : Fin n, T_inv j k * T k k * x k
                      = ∑ k : Fin n, ∑ j : Fin n, T i j * (T_inv j k * T k k * x k) := by
                          simp_rw [Finset.mul_sum]
                          rw [Finset.sum_comm]
                  _ = ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k := by
                        apply Finset.sum_congr rfl
                        intro k _
                        calc
                          ∑ j : Fin n, T i j * (T_inv j k * T k k * x k)
                              = ∑ j : Fin n, (T i j * T_inv j k) * (T k k * x k) := by
                                  apply Finset.sum_congr rfl
                                  intro j _
                                  ring
                          _ = (∑ j : Fin n, T i j * T_inv j k) * (T k k * x k) := by
                                  rw [Finset.sum_mul]
                          _ = (∑ j : Fin n, T i j * T_inv j k) * T k k * x k := by
                                  ring
              rw [hswap]
      _ = 2 * ∑ k : Fin n, idMatrix n i k * T k k * x k -
            ∑ j : Fin n, T i j * x j := by
              have hid :
                  ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k
                    = ∑ k : Fin n, idMatrix n i k * T k k * x k := by
                apply Finset.sum_congr rfl
                intro k _
                have hright := congrArg (fun z => z * (T k k * x k)) (hInv.2 i k)
                simpa [idMatrix, mul_assoc] using hright
              rw [hid]
      _ = 2 * (T i i * x i) - b i := by
              rw [hTx i]
              simp [idMatrix]
      _ = 2 * T i i * x i - b i := by
              ring
  have hTx_split :
      T i i * x i +
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * x j = b i := by
    have h := hTx i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    rw [higham8_upperTriangular_erase_sum_eq_strictUpper n T hUT i x] at h
    simpa using h
  have hTy_split :
      T i i * y i +
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * y j =
          2 * T i i * x i - b i := by
    have h := hTy i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    rw [higham8_upperTriangular_erase_sum_eq_strictUpper n T hUT i y] at h
    simpa using h
  have hTx_pos :
      T i i * x i =
        b i +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j := by
    have hsum :
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * x j =
          -∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum] at hTx_split
    linarith
  have hTy_pos :
      T i i * y i =
        2 * T i i * x i - b i +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j := by
    have hsum :
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * y j =
          -∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum] at hTy_split
    linarith
  linarith

/-- Problem 8.4 componentwise bound for the comparison-image vector:
`(2T⁻¹ diag(t_ii) - I)x ≤ (2(n-i)-1) x`. -/
private theorem higham8_problem8_4_comparisonImage_nonneg_bound (n : ℕ)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    let y := higham8_9_comparisonImage n T T_inv x
    ∀ i : Fin n,
      0 ≤ y i ∧
      y i ≤ (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) * x i := by
  intro y
  have hrow :=
    higham8_problem8_4_comparisonImage_row_eq n T T_inv x b
      hUT hT_diag_pos hT_offdiag hInv hTx hx_nonneg
  suffices h :
      ∀ d : ℕ, ∀ i : Fin n, n - 1 - i.val ≤ d →
        0 ≤ y i ∧ y i ≤ (((2 * d + 1 : ℕ) : ℝ)) * x i by
    intro i
    simpa using h (n - 1 - i.val) i (le_refl _)
  intro d
  induction d with
  | zero =>
      intro i hi
      have hi_last : i.val = n - 1 := by omega
      have hsumx_zero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        omega
      have hsumy_zero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        omega
      have hy_eq : y i = x i := by
        have hscaled : T i i * y i = T i i * x i := by
          have hrowi := hrow i
          rw [hsumx_zero, hsumy_zero, add_zero, add_zero] at hrowi
          simpa [y] using hrowi
        exact mul_left_cancel₀ (ne_of_gt (hT_diag_pos i)) hscaled
      refine ⟨?_, ?_⟩
      · simpa [hy_eq] using hx_nonneg i
      · rw [hy_eq]
        simp
  | succ d ih =>
      intro i hi
      by_cases htail : n - 1 - i.val ≤ d
      · rcases ih i htail with ⟨hy_nonneg, hy_le⟩
        refine ⟨hy_nonneg, ?_⟩
        calc
          y i ≤ (((2 * d + 1 : ℕ) : ℝ)) * x i := hy_le
          _ ≤ (((2 * (d + 1) + 1 : ℕ) : ℝ)) * x i := by
                have hcoef :
                    (((2 * d + 1 : ℕ) : ℝ)) ≤ (((2 * (d + 1) + 1 : ℕ) : ℝ)) := by
                  norm_num
                exact mul_le_mul_of_nonneg_right hcoef (hx_nonneg i)
      · let S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => i.val < j.val)
        let sx : ℝ := ∑ j ∈ S, (-T i j) * x j
        let sy : ℝ := ∑ j ∈ S, (-T i j) * y j
        have hrowi : T i i * y i = T i i * x i + sx + sy := by
          simpa [S, sx, sy, add_assoc, add_left_comm, add_comm] using hrow i
        have hsx_nonneg : 0 ≤ sx := by
          unfold sx S
          apply Finset.sum_nonneg
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact mul_nonneg (by linarith [hT_offdiag i j hj]) (hx_nonneg j)
        have hsy_nonneg : 0 ≤ sy := by
          unfold sy S
          apply Finset.sum_nonneg
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have hj_tail : n - 1 - j.val ≤ d := by omega
          exact mul_nonneg (by linarith [hT_offdiag i j hj]) (ih j hj_tail).1
        have hsx_le : sx ≤ T i i * x i := by
          have hTx_pos :
              T i i * x i = b i + sx := by
            have hTxi := hTx i
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hTxi
            rw [higham8_upperTriangular_erase_sum_eq_strictUpper n T hUT i x] at hTxi
            unfold sx S
            have hsum :
                ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * x j =
                  -∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    (-T i j) * x j := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
            rw [hsum] at hTxi
            linarith
          linarith [hb i, hTx_pos]
        have hsy_le : sy ≤ (((2 * d + 1 : ℕ) : ℝ)) * sx := by
          unfold sy sx S
          calc
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j
                ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    (((2 * d + 1 : ℕ) : ℝ)) * ((-T i j) * x j) := by
                    apply Finset.sum_le_sum
                    intro j hj
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                    have hj_tail : n - 1 - j.val ≤ d := by omega
                    have hy_le : y j ≤ (((2 * d + 1 : ℕ) : ℝ)) * x j := (ih j hj_tail).2
                    have hcoef_nonneg : 0 ≤ -T i j := by linarith [hT_offdiag i j hj]
                    calc
                      (-T i j) * y j ≤ (-T i j) * ((((2 * d + 1 : ℕ) : ℝ)) * x j) :=
                        mul_le_mul_of_nonneg_left hy_le hcoef_nonneg
                      _ = (((2 * d + 1 : ℕ) : ℝ)) * ((-T i j) * x j) := by ring
            _ = (((2 * d + 1 : ℕ) : ℝ)) *
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j := by
                    rw [← Finset.mul_sum]
        have hy_nonneg : 0 ≤ y i := by
          have hprod_nonneg : 0 ≤ T i i * y i := by
            linarith [hrowi, hsx_nonneg, hsy_nonneg, hx_nonneg i, hT_diag_pos i]
          by_contra hyneg
          push_neg at hyneg
          linarith [mul_neg_of_pos_of_neg (hT_diag_pos i) hyneg]
        have hc_nonneg : 0 ≤ (((2 * d + 1 : ℕ) : ℝ)) := by
          positivity
        have hsy_le' : sy ≤ (((2 * d + 1 : ℕ) : ℝ)) * (T i i * x i) := by
          exact le_trans hsy_le (mul_le_mul_of_nonneg_left hsx_le hc_nonneg)
        have hcoef_eq :
            (2 : ℝ) + (((2 * d + 1 : ℕ) : ℝ)) = (((2 * (d + 1) + 1 : ℕ) : ℝ)) := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_mul]
          norm_num
          ring
        have hscaled :
            T i i * y i ≤
              T i i * ((((2 * (d + 1) + 1 : ℕ) : ℝ)) * x i) := by
          calc
            T i i * y i = T i i * x i + sx + sy := hrowi
            _ ≤ T i i * x i + T i i * x i + (((2 * d + 1 : ℕ) : ℝ)) * (T i i * x i) := by
                  linarith
            _ = (T i i * x i) * ((2 : ℝ) + (((2 * d + 1 : ℕ) : ℝ))) := by
                  ring
            _ = (T i i * x i) * (((2 * (d + 1) + 1 : ℕ) : ℝ)) := by
                  rw [hcoef_eq]
            _ = T i i * (x i * (((2 * (d + 1) + 1 : ℕ) : ℝ))) := by
                  rw [mul_assoc]
            _ = T i i * ((((2 * (d + 1) + 1 : ℕ) : ℝ)) * x i) := by
                  congr 1
                  rw [mul_comm]
        refine ⟨hy_nonneg, ?_⟩
        exact le_of_mul_le_mul_left hscaled (hT_diag_pos i)

/-- **Problem 8.4**: if `T` is an upper triangular M-matrix and `b = Tx ≥ 0`,
then `cond(T,x) ≤ 2n-1`. -/
theorem higham8_4_upperTriangularMMatrix_condAtSolution_le (n : ℕ) (hn : 0 < n)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i)
    (hx : 0 < infNormVec x) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤ 2 * (n : ℝ) - 1 := by
  have hx_nonneg :=
    higham8_upperTriangularMMatrix_solution_nonneg n T T_inv x b
      hUT hT_diag_pos hT_offdiag hInv hTx hb
  have hComp :
      comparisonMatrix n T = T :=
    higham8_comparisonMatrix_eq_self_upper n T hUT hT_diag_pos hT_offdiag
  have hInv_ut :=
    inv_upper_tri n T T_inv hUT (fun i => ne_of_gt (hT_diag_pos i)) hInv.1
  have hy_bound :=
    higham8_problem8_4_comparisonImage_nonneg_bound n T T_inv x b
      hUT hT_diag_pos hT_offdiag hInv hTx hb hx_nonneg
  have hcoef_nonneg : 0 ≤ 2 * (n : ℝ) - 1 := by
    have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_iff.mpr hn
    linarith
  have hy_norm :
      infNormVec (higham8_9_comparisonImage n T T_inv x) ≤
        (2 * (n : ℝ) - 1) * infNormVec x := by
    apply infNormVec_le_of_abs_le
    · intro i
      rcases hy_bound i with ⟨hy_nonneg, hy_le⟩
      rw [abs_of_nonneg hy_nonneg]
      have hcoef_nat : 2 * (n - 1 - i.val) + 1 ≤ 2 * n - 1 := by omega
      have hcoef :
          (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) - 1 := by
        have hcoef' :
            (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) ≤ (((2 * n - 1 : ℕ) : ℝ)) := by
          exact_mod_cast hcoef_nat
        have htarget : (((2 * n - 1 : ℕ) : ℝ)) = 2 * (n : ℝ) - 1 := by
          have htwo : 1 ≤ 2 * n := by
            have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
            omega
          rw [Nat.cast_sub htwo, Nat.cast_mul, Nat.cast_one]
          ring
        rw [htarget] at hcoef'
        exact hcoef'
      have hxi_le : x i ≤ infNormVec x := by
        simpa [abs_of_nonneg (hx_nonneg i)] using abs_le_infNormVec x i
      calc
        higham8_9_comparisonImage n T T_inv x i
            ≤ (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) * x i := hy_le
        _ ≤ (2 * (n : ℝ) - 1) * x i :=
              mul_le_mul_of_nonneg_right hcoef (hx_nonneg i)
        _ ≤ (2 * (n : ℝ) - 1) * infNormVec x :=
              mul_le_mul_of_nonneg_left hxi_le hcoef_nonneg
    ·
      exact mul_nonneg hcoef_nonneg (infNormVec_nonneg x)
  have hcond_le :=
    higham8_9_upperTriangular_condAtSolution_le_comparison_eq n hn T T_inv T_inv x
      hUT (fun i => ne_of_gt (hT_diag_pos i)) hInv
      (by simpa [hComp] using hInv.2) hInv_ut
  calc
    ch7SkeelCondAtSolutionInf n hn T T_inv x
        ≤ infNormVec (higham8_9_comparisonImage n T T_inv x) / infNormVec x := hcond_le
    _ ≤ ((2 * (n : ℝ) - 1) * infNormVec x) / infNormVec x :=
          div_le_div_of_nonneg_right hy_norm (infNormVec_nonneg x)
    _ = 2 * (n : ℝ) - 1 := by
          field_simp [ne_of_gt hx]

/-! ## §8.3 Bounds for the Inverse -/

/-- **Equation (8.7)**: Higham's comparison matrix. -/
noncomputable def higham8_7_comparisonMatrix (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  comparisonMatrix n A

/-- **Theorem 8.12**, first comparison-matrix inverse inequality. -/
theorem higham8_12_abs_inv_le_comparison_inv (n : ℕ)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    ∀ i j : Fin n, |U_inv i j| ≤ M_inv i j :=
  abs_inv_le_compMatrix_inv n U U_inv M_inv hUT hU_diag hInv hM_RInv hM_inv_ut

/-- **Theorem 8.12**: the strict-upper row maximum used to define `W(U)`. -/
noncomputable def higham8_12_rowMaxStrictUpper (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  if h : i.val + 1 < n then
    Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val < j.val))
      (by
        refine ⟨⟨i.val + 1, h⟩, ?_⟩
        simp [Finset.mem_filter]
        exact Fin.lt_def.mpr (by simp))
      (fun j => |U i j|)
  else
    0

/-- The strict-upper row maximum is nonnegative. -/
lemma higham8_12_rowMaxStrictUpper_nonneg (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i : Fin n) :
    0 ≤ higham8_12_rowMaxStrictUpper n U i := by
  by_cases h : i.val + 1 < n
  · have hmem :
        (⟨i.val + 1, h⟩ : Fin n) ∈
          Finset.univ.filter (fun j : Fin n => i.val < j.val) := by
      simp [Finset.mem_filter]
      exact Fin.lt_def.mpr (by simp)
    have hs :
        |U i ⟨i.val + 1, h⟩| ≤
          Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val < j.val))
            ⟨⟨i.val + 1, h⟩, hmem⟩ (fun j => |U i j|) :=
      Finset.le_sup' (fun j => |U i j|) hmem
    simpa [higham8_12_rowMaxStrictUpper, h] using
      (le_trans (abs_nonneg _) hs)
  · simp [higham8_12_rowMaxStrictUpper, h]

/-- Any strict-upper entry is bounded by the corresponding row maximum. -/
lemma higham8_12_abs_le_rowMaxStrictUpper (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i j : Fin n) (hij : i.val < j.val) :
    |U i j| ≤ higham8_12_rowMaxStrictUpper n U i := by
  have hsucc : i.val + 1 < n := by omega
  have hs :
      |U i j| ≤
        Finset.sup' (Finset.univ.filter (fun k : Fin n => i.val < k.val))
          (by
            refine ⟨⟨i.val + 1, hsucc⟩, ?_⟩
            simp [Finset.mem_filter]
            exact Fin.lt_def.mpr (by simp))
          (fun k => |U i k|) :=
    Finset.le_sup' (fun k => |U i k|) (by
      show j ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val)
      exact Finset.mem_filter.mpr ⟨by simp, hij⟩)
  simpa [higham8_12_rowMaxStrictUpper, hsucc] using hs

/-- **Theorem 8.12**: Higham's row-max minorant `W(U)`. -/
noncomputable def higham8_12_WMatrix (n : ℕ)
    (U : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then |U i i|
    else if i.val < j.val then -(higham8_12_rowMaxStrictUpper n U i)
    else 0

/-- `W(U)` is upper triangular by construction. -/
lemma higham8_12_WMatrix_upper (n : ℕ) (U : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, j.val < i.val → higham8_12_WMatrix n U i j = 0 := by
  intro i j hij
  have hnotlt : ¬ i.val < j.val := by omega
  simp [higham8_12_WMatrix, hnotlt,
    show ¬ i = j from Fin.ne_of_val_ne (by omega)]

/-- The diagonal of `W(U)` is the absolute diagonal of `U`. -/
lemma higham8_12_WMatrix_diag (n : ℕ) (U : Fin n → Fin n → ℝ) (i : Fin n) :
    higham8_12_WMatrix n U i i = |U i i| := by
  simp [higham8_12_WMatrix]

/-- Strict-upper entries of `W(U)` are the negated row maxima. -/
lemma higham8_12_WMatrix_strictUpper (n : ℕ) (U : Fin n → Fin n → ℝ)
    {i j : Fin n} (hij : i.val < j.val) :
    higham8_12_WMatrix n U i j = -(higham8_12_rowMaxStrictUpper n U i) := by
  simp [higham8_12_WMatrix, hij, show ¬ i = j from Fin.ne_of_val_ne (by omega)]

/-- The comparison matrix dominates `W(U)` entrywise for upper-triangular `U`. -/
lemma higham8_12_WMatrix_le_comparisonMatrix (n : ℕ)
    (U : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    ∀ i j : Fin n, higham8_12_WMatrix n U i j ≤ comparisonMatrix n U i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [higham8_12_WMatrix, comparisonMatrix]
  · by_cases hlt : i.val < j.val
    · rw [higham8_12_WMatrix_strictUpper n U hlt]
      simpa [comparisonMatrix, hij] using
        (neg_le_neg (higham8_12_abs_le_rowMaxStrictUpper n U i j hlt))
    · have hji : j.val < i.val := by omega
      rw [higham8_12_WMatrix_upper n U i j hji]
      simp [comparisonMatrix, hij, hUT i j hji]

/-- The row maxima satisfy the source `β` bound when every strict-upper entry
is bounded by `β |u_ii|`. -/
lemma higham8_12_rowMaxStrictUpper_le_beta_mul_diag (n : ℕ)
    (U : Fin n → Fin n → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    ∀ i : Fin n, higham8_12_rowMaxStrictUpper n U i ≤ β * |U i i| := by
  intro i
  by_cases h : i.val + 1 < n
  · have hs :
        Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val < j.val))
          (by
            refine ⟨⟨i.val + 1, h⟩, ?_⟩
            simp [Finset.mem_filter]
            exact Fin.lt_def.mpr (by simp))
          (fun j => |U i j|) ≤ β * |U i i| := by
      apply Finset.sup'_le
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hβ_bound i j hj
    simpa [higham8_12_rowMaxStrictUpper, h] using hs
  · simpa [higham8_12_rowMaxStrictUpper, h] using
      (mul_nonneg hβ (abs_nonneg _))

/-- Under `β ≤ 1`, Higham's `W(U)` satisfies the repository's diagonal-dominant
upper-triangular condition (8.5). -/
theorem higham8_12_WMatrix_isDiagDominantUpper (n : ℕ)
    (U : Fin n → Fin n → ℝ) {β : ℝ}
    (hU_diag : ∀ i : Fin n, U i i ≠ 0) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    IsDiagDominantUpper n (higham8_12_WMatrix n U) := by
  refine ⟨higham8_12_WMatrix_upper n U, ?_, ?_⟩
  · intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_ne_zero.mpr (hU_diag i)
  · intro i j hij
    rw [higham8_12_WMatrix_diag, higham8_12_WMatrix_strictUpper n U hij]
    rw [abs_abs, abs_neg, abs_of_nonneg (higham8_12_rowMaxStrictUpper_nonneg n U i)]
    calc
      higham8_12_rowMaxStrictUpper n U i ≤ β * |U i i| :=
        higham8_12_rowMaxStrictUpper_le_beta_mul_diag n U hβ hβ_bound i
      _ ≤ |U i i| := by
        have hdiag_nonneg : 0 ≤ |U i i| := abs_nonneg _
        nlinarith

/-- **Theorem 8.14 support**: once `W(U)` is known to satisfy the source
`β ≤ 1` hypothesis, the existing diagonal-dominant inverse API gives the
rightmost `∞`-norm upper bound for `W(U)⁻¹`. -/
theorem higham8_14_WInv_infNorm_upperBound (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ) (i0 : Fin n) {β : ℝ}
    (hU_diag : ∀ i : Fin n, U i i ≠ 0) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|)
    (hInv : IsInverse n (higham8_12_WMatrix n U) W_inv) :
    infNorm W_inv ≤
      2 ^ (n - 1) *
        (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
          (fun k => |U k k|)) := by
  have hDD :=
    higham8_12_WMatrix_isDiagDominantUpper n U hU_diag hβ hβ1 hβ_bound
  simpa [higham8_12_WMatrix] using
    triInv_infNorm_upperBound n (higham8_12_WMatrix n U) W_inv i0 hDD hInv

/-- **Theorem 8.12**: the source `Z` minorant with diagonal `α` and strict
upper entries `-αβ`. -/
noncomputable def higham8_12_ZMatrix (n : ℕ) (α β : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => α * higham8_3_stressUpper n β i j

/-- Explicit inverse formula for the source `Z` matrix. -/
noncomputable def higham8_12_ZInvFormula (n : ℕ) (α β : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => (1 / α) * higham8_4_stressUpperInvFormula n β i j

/-- The explicit `Z` inverse formula has the same scaled column sums as the
stress-family inverse. -/
theorem higham8_12_ZInvFormula_col_sum (n : ℕ) (α β : ℝ) (j : Fin n) :
    ∑ i : Fin n, higham8_12_ZInvFormula n α β i j =
      (1 / α) * (1 + β) ^ j.val := by
  unfold higham8_12_ZInvFormula
  rw [← Finset.mul_sum, higham8_4_stressUpperInvFormula_col_sum]

/-- The explicit `Z` inverse formula has the same scaled row sums as the
stress-family inverse. -/
theorem higham8_12_ZInvFormula_row_sum (n : ℕ) (α β : ℝ) (i : Fin n) :
    ∑ j : Fin n, higham8_12_ZInvFormula n α β i j =
      (1 / α) * (1 + β) ^ (n - 1 - i.val) := by
  unfold higham8_12_ZInvFormula
  rw [← Finset.mul_sum, higham8_4_stressUpperInvFormula_row_sum]

/-- The explicit inverse formula is a genuine right inverse of the source `Z`
matrix. -/
theorem higham8_12_ZInvFormula_isRightInverse (n : ℕ) (α β : ℝ) (hα : α ≠ 0) :
    IsRightInverse n (higham8_12_ZMatrix n α β) (higham8_12_ZInvFormula n α β) := by
  intro i j
  calc
    ∑ k : Fin n, higham8_12_ZMatrix n α β i k * higham8_12_ZInvFormula n α β k j
        =
      ∑ k : Fin n,
        higham8_3_stressUpper n β i k * higham8_4_stressUpperInvFormula n β k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          unfold higham8_12_ZMatrix higham8_12_ZInvFormula
          field_simp [hα]
    _ = (if i = j then 1 else 0) :=
      higham8_4_stressUpperInvFormula_isRightInverse n β i j

/-- The explicit inverse formula is a genuine two-sided inverse of the source
`Z` matrix. -/
theorem higham8_12_ZInvFormula_isInverse (n : ℕ) (α β : ℝ) (hα : α ≠ 0) :
    IsInverse n (higham8_12_ZMatrix n α β) (higham8_12_ZInvFormula n α β) := by
  have hRight := higham8_12_ZInvFormula_isRightInverse n α β hα
  exact ⟨ch7_isLeftInverse_of_isRightInverse hRight, hRight⟩

/-- The explicit `Z` inverse formula is entrywise nonnegative for `α > 0` and
`β ≥ 0`. -/
lemma higham8_12_ZInvFormula_nonneg (n : ℕ) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ i j : Fin n, 0 ≤ higham8_12_ZInvFormula n α β i j := by
  intro i j
  unfold higham8_12_ZInvFormula
  have hscale : 0 ≤ 1 / α := one_div_nonneg.mpr hα.le
  by_cases hij : i = j
  · simpa [higham8_4_stressUpperInvFormula, hij] using hscale
  · by_cases hlt : i.val < j.val
    · have hpow : 0 ≤ (1 + β) ^ (j.val - i.val - 1) := by
        apply pow_nonneg
        linarith
      rw [higham8_4_stressUpperInvFormula, if_neg hij, if_pos hlt]
      exact mul_nonneg hscale (mul_nonneg hβ hpow)
    · simp [higham8_4_stressUpperInvFormula, hij, hlt]

private lemma higham8_12_WMatrix_offdiag_nonpos (n : ℕ)
    (U : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, i.val < j.val → higham8_12_WMatrix n U i j ≤ 0 := by
  intro i j hij
  rw [higham8_12_WMatrix_strictUpper n U hij]
  exact neg_nonpos.mpr (higham8_12_rowMaxStrictUpper_nonneg n U i)

private lemma higham8_12_ZMatrix_upper (n : ℕ) (α β : ℝ) :
    ∀ i j : Fin n, j.val < i.val → higham8_12_ZMatrix n α β i j = 0 := by
  intro i j hij
  have hneq : i ≠ j := Fin.ne_of_val_ne (by omega)
  have hnotlt : ¬ i.val < j.val := by omega
  simp [higham8_12_ZMatrix, higham8_3_stressUpper, hneq, hnotlt]

private lemma higham8_12_ZInvFormula_upper (n : ℕ) (α β : ℝ) :
    ∀ i j : Fin n, j.val < i.val → higham8_12_ZInvFormula n α β i j = 0 := by
  intro i j hij
  have hneq : i ≠ j := Fin.ne_of_val_ne (by omega)
  have hnotlt : ¬ i.val < j.val := by omega
  simp [higham8_12_ZInvFormula, higham8_4_stressUpperInvFormula, hneq, hnotlt]

private lemma higham8_12_ZInvFormula_diag (n : ℕ) (α β : ℝ) (i : Fin n) :
    higham8_12_ZInvFormula n α β i i = 1 / α := by
  simp [higham8_12_ZInvFormula, higham8_4_stressUpperInvFormula]

/-- **Theorem 8.12**, middle inverse-chain step `M(U)⁻¹ ≤ W(U)⁻¹`. -/
theorem higham8_12_comparisonInv_le_WInv (n : ℕ)
    (U M_inv W_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    ∀ i j : Fin n, M_inv i j ≤ W_inv i j := by
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    unfold comparisonMatrix
    simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n U i i := by
    intro i
    simp [comparisonMatrix, hU_diag i]
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n U i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_LInv := ch7_isLeftInverse_of_isRightInverse hM_RInv
  have hM_inv_ut :=
    inv_upper_tri n (comparisonMatrix n U) M_inv hM_ut
      (fun i => ne_of_gt (hM_diag_pos i)) hM_LInv
  have hM_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
      hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  have hW_diag_pos : ∀ i : Fin n, 0 < higham8_12_WMatrix n U i i := by
    intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_pos.mpr (hU_diag i)
  have hW_LInv := ch7_isLeftInverse_of_isRightInverse hW_RInv
  have hW_inv_ut :=
    inv_upper_tri n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U)
      (fun i => ne_of_gt (hW_diag_pos i)) hW_LInv
  have hW_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U) hW_diag_pos
      (higham8_12_WMatrix_offdiag_nonpos n U) hW_RInv hW_inv_ut
  suffices h :
      ∀ (d : ℕ), ∀ i j : Fin n, j.val - i.val ≤ d → i.val ≤ j.val →
        M_inv i j ≤ W_inv i j from
    fun i j => by
      by_cases hij : i.val ≤ j.val
      · exact h (j.val - i.val) i j (le_refl _) hij
      · push_neg at hij
        rw [hM_inv_ut i j (by omega), hW_inv_ut i j (by omega)]
  intro d
  induction d with
  | zero =>
      intro i j hdiff hij
      have heq : i = j := Fin.ext (by omega)
      subst heq
      have hM_diag :
          M_inv i i = 1 / |U i i| := by
        simpa [comparisonMatrix] using
          inv_diag_entry n (comparisonMatrix n U) M_inv
            hM_ut (fun k => ne_of_gt (hM_diag_pos k)) hM_LInv hM_inv_ut i
      have hW_diag :
          W_inv i i = 1 / |U i i| := by
        simpa [higham8_12_WMatrix] using
          inv_diag_entry n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_LInv hW_inv_ut i
      rw [hM_diag, hW_diag]
  | succ d ih =>
      intro i j hdiff hij
      by_cases heq : i.val = j.val
      · exact ih i j (by omega) (by omega)
      · have hij' : i.val < j.val := by omega
        have hUii_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
        have hrec_M :=
          inv_recurrence n (comparisonMatrix n U) M_inv hM_ut
            (fun k => ne_of_gt (hM_diag_pos k)) hM_RInv hM_inv_ut i j hij'
        have hrec_W :=
          inv_recurrence n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_RInv hW_inv_ut i j hij'
        have hM_prod :
            |U i i| * M_inv i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                |U i k| * M_inv k j := by
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  comparisonMatrix n U i k * M_inv k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    |U i k| * M_inv k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            simp [comparisonMatrix, show i ≠ k from Fin.ne_of_val_ne (by omega)]
          have hM_ii : comparisonMatrix n U i i = |U i i| := by
            simp [comparisonMatrix]
          rw [hM_ii] at hrec_M
          rw [hsum_rw] at hrec_M
          linarith
        have hW_prod :
            |U i i| * W_inv i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j := by
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_WMatrix n U i k * W_inv k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    higham8_12_rowMaxStrictUpper n U i * W_inv k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            rw [higham8_12_WMatrix_strictUpper n U hk.1]
            ring
          rw [higham8_12_WMatrix_diag] at hrec_W
          rw [hsum_rw] at hrec_W
          linarith
        have hsum_le :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                |U i k| * M_inv k j ≤
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          have hrow_le :
              |U i k| * M_inv k j ≤
                higham8_12_rowMaxStrictUpper n U i * M_inv k j :=
            mul_le_mul_of_nonneg_right
              (higham8_12_abs_le_rowMaxStrictUpper n U i k hk.1)
              (hM_nonneg k j)
          have hih :
              higham8_12_rowMaxStrictUpper n U i * M_inv k j ≤
                higham8_12_rowMaxStrictUpper n U i * W_inv k j :=
            mul_le_mul_of_nonneg_left
              (ih k j (by omega) (by omega))
              (higham8_12_rowMaxStrictUpper_nonneg n U i)
          exact hrow_le.trans hih
        calc
          M_inv i j =
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  |U i k| * M_inv k j) / |U i i| := by
              rw [← hM_prod]
              field_simp [ne_of_gt hUii_pos]
          _ ≤
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_rowMaxStrictUpper n U i * W_inv k j) / |U i i| :=
                div_le_div_of_nonneg_right hsum_le (le_of_lt hUii_pos)
          _ = W_inv i j := by
              rw [← hW_prod]
              field_simp [ne_of_gt hUii_pos]

/-- **Theorem 8.12**, last middle inverse-chain step `W(U)⁻¹ ≤ Z(U)⁻¹`. -/
theorem higham8_12_WInv_le_ZInvFormula (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    ∀ i j : Fin n, W_inv i j ≤ higham8_12_ZInvFormula n α β i j := by
  have hW_diag_pos : ∀ i : Fin n, 0 < higham8_12_WMatrix n U i i := by
    intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_pos.mpr (hU_diag i)
  have hW_LInv := ch7_isLeftInverse_of_isRightInverse hW_RInv
  have hW_inv_ut :=
    inv_upper_tri n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U)
      (fun i => ne_of_gt (hW_diag_pos i)) hW_LInv
  have hW_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U) hW_diag_pos
      (higham8_12_WMatrix_offdiag_nonpos n U) hW_RInv hW_inv_ut
  have hZ_RInv := higham8_12_ZInvFormula_isRightInverse n α β (ne_of_gt hα)
  suffices h :
      ∀ (d : ℕ), ∀ i j : Fin n, j.val - i.val ≤ d → i.val ≤ j.val →
        W_inv i j ≤ higham8_12_ZInvFormula n α β i j from
    fun i j => by
      by_cases hij : i.val ≤ j.val
      · exact h (j.val - i.val) i j (le_refl _) hij
      · push_neg at hij
        rw [hW_inv_ut i j (by omega), higham8_12_ZInvFormula_upper n α β i j (by omega)]
  intro d
  induction d with
  | zero =>
      intro i j hdiff hij
      have heq : i = j := Fin.ext (by omega)
      subst heq
      have hW_diag :
          W_inv i i = 1 / |U i i| := by
        simpa [higham8_12_WMatrix] using
          inv_diag_entry n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_LInv hW_inv_ut i
      have hdiag_le : 1 / |U i i| ≤ 1 / α := by
        exact one_div_le_one_div_of_le hα (hα_le_diag i)
      rw [hW_diag, higham8_12_ZInvFormula_diag]
      exact hdiag_le
  | succ d ih =>
      intro i j hdiff hij
      by_cases heq : i.val = j.val
      · exact ih i j (by omega) (by omega)
      · have hij' : i.val < j.val := by omega
        have hUii_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
        have hrec_W :=
          inv_recurrence n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_RInv hW_inv_ut i j hij'
        have hZ_prod :
            α * higham8_12_ZInvFormula n α β i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                (α * β) * higham8_12_ZInvFormula n α β k j := by
          have hZ_diag_pos : ∀ i : Fin n, 0 < higham8_12_ZMatrix n α β i i := by
            intro k
            simpa [higham8_12_ZMatrix, higham8_3_stressUpper] using hα
          have hrec_Z :=
            inv_recurrence n (higham8_12_ZMatrix n α β) (higham8_12_ZInvFormula n α β)
              (higham8_12_ZMatrix_upper n α β)
              (fun k => ne_of_gt (hZ_diag_pos k)) hZ_RInv
              (higham8_12_ZInvFormula_upper n α β) i j hij'
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_ZMatrix n α β i k * higham8_12_ZInvFormula n α β k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    (α * β) * higham8_12_ZInvFormula n α β k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            have hneq : i ≠ k := Fin.ne_of_val_ne (by omega)
            simp [higham8_12_ZMatrix, higham8_3_stressUpper, hneq, hk.1]
          have hZ_ii : higham8_12_ZMatrix n α β i i = α := by
            simp [higham8_12_ZMatrix, higham8_3_stressUpper]
          rw [hZ_ii] at hrec_Z
          rw [hsum_rw] at hrec_Z
          linarith
        have hW_prod :
            |U i i| * W_inv i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j := by
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_WMatrix n U i k * W_inv k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    higham8_12_rowMaxStrictUpper n U i * W_inv k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            rw [higham8_12_WMatrix_strictUpper n U hk.1]
            ring
          rw [higham8_12_WMatrix_diag] at hrec_W
          rw [hsum_rw] at hrec_W
          linarith
        have hsum_le :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j ≤
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                (β * |U i i|) * higham8_12_ZInvFormula n α β k j := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          have hrow_le :
              higham8_12_rowMaxStrictUpper n U i * W_inv k j ≤
                (β * |U i i|) * W_inv k j :=
            mul_le_mul_of_nonneg_right
              (higham8_12_rowMaxStrictUpper_le_beta_mul_diag n U hβ hβ_bound i)
              (hW_nonneg k j)
          have hih :
              (β * |U i i|) * W_inv k j ≤
                (β * |U i i|) * higham8_12_ZInvFormula n α β k j :=
            mul_le_mul_of_nonneg_left
              (ih k j (by omega) (by omega))
              (mul_nonneg hβ (abs_nonneg _))
          exact hrow_le.trans hih
        have hZ_beta_sum :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                β * higham8_12_ZInvFormula n α β k j =
              higham8_12_ZInvFormula n α β i j := by
          have hsum_factor :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  (α * β) * higham8_12_ZInvFormula n α β k j =
                α *
                  (∑ k ∈ Finset.univ.filter
                      (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                      β * higham8_12_ZInvFormula n α β k j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
          calc
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                β * higham8_12_ZInvFormula n α β k j
                =
              (α *
                (∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    β * higham8_12_ZInvFormula n α β k j)) / α := by
                  field_simp [ne_of_gt hα]
            _ =
              (α * higham8_12_ZInvFormula n α β i j) / α := by
                rw [← hsum_factor, hZ_prod]
            _ = higham8_12_ZInvFormula n α β i j := by
                field_simp [ne_of_gt hα]
        calc
          W_inv i j =
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_rowMaxStrictUpper n U i * W_inv k j) / |U i i| := by
              rw [← hW_prod]
              field_simp [ne_of_gt hUii_pos]
          _ ≤
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  (β * |U i i|) * higham8_12_ZInvFormula n α β k j) / |U i i| :=
                div_le_div_of_nonneg_right hsum_le (le_of_lt hUii_pos)
          _ =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                β * higham8_12_ZInvFormula n α β k j := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro k hk
              field_simp [ne_of_gt hUii_pos]
          _ = higham8_12_ZInvFormula n α β i j := hZ_beta_sum

private theorem higham8_12_comparisonInv_nonneg (n : ℕ)
    (U M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv) :
    ∀ i j : Fin n, 0 ≤ M_inv i j := by
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    unfold comparisonMatrix
    simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n U i i := by
    intro i
    simp [comparisonMatrix, hU_diag i]
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n U i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_LInv := ch7_isLeftInverse_of_isRightInverse hM_RInv
  have hM_inv_ut :=
    inv_upper_tri n (comparisonMatrix n U) M_inv hM_ut
      (fun i => ne_of_gt (hM_diag_pos i)) hM_LInv
  exact upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
    hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut

private theorem higham8_12_WInv_nonneg (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    ∀ i j : Fin n, 0 ≤ W_inv i j := by
  have hW_diag_pos : ∀ i : Fin n, 0 < higham8_12_WMatrix n U i i := by
    intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_pos.mpr (hU_diag i)
  have hW_LInv := ch7_isLeftInverse_of_isRightInverse hW_RInv
  have hW_inv_ut :=
    inv_upper_tri n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U)
      (fun i => ne_of_gt (hW_diag_pos i)) hW_LInv
  exact upper_tri_mmatrix_inv_nonneg n (higham8_12_WMatrix n U) W_inv
    (higham8_12_WMatrix_upper n U) hW_diag_pos
    (higham8_12_WMatrix_offdiag_nonpos n U) hW_RInv hW_inv_ut

private theorem higham8_infNorm_le_of_abs_le_nonneg {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, |A i j| ≤ B i j) :
    infNorm A ≤ infNorm B := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |A i j| ≤ ∑ j : Fin n, B i j := by
        apply Finset.sum_le_sum
        intro j _hj
        exact hAB i j
      _ = ∑ j : Fin n, |B i j| := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact (abs_of_nonneg (hB_nonneg i j)).symm
      _ ≤ infNorm B := row_sum_le_infNorm B i
  · exact infNorm_nonneg B

private theorem higham8_oneNorm_le_of_abs_le_nonneg {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, |A i j| ≤ B i j) :
    oneNorm A ≤ oneNorm B := by
  apply oneNorm_le_of_col_sum_le
  · intro j
    calc
      ∑ i : Fin n, |A i j| ≤ ∑ i : Fin n, B i j := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hAB i j
      _ = ∑ i : Fin n, |B i j| := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (abs_of_nonneg (hB_nonneg i j)).symm
      _ ≤ oneNorm B := col_sum_le_oneNorm B j
  · exact oneNorm_nonneg B

private theorem higham8_infNorm_le_of_nonneg_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) :
    infNorm A ≤ infNorm B := by
  apply higham8_infNorm_le_of_abs_le_nonneg A B hB_nonneg
  intro i j
  rw [abs_of_nonneg (hA_nonneg i j)]
  exact hAB i j

private theorem higham8_oneNorm_le_of_nonneg_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) :
    oneNorm A ≤ oneNorm B := by
  apply higham8_oneNorm_le_of_abs_le_nonneg A B hB_nonneg
  intro i j
  rw [abs_of_nonneg (hA_nonneg i j)]
  exact hAB i j

private theorem higham8_opNorm2_le_of_abs_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hAB : ∀ i j : Fin n, |A i j| ≤ B i j) :
    complexMatrixOp2 (realRectToCMatrix A) ≤
      complexMatrixOp2 (realRectToCMatrix B) := by
  have hB_rect :
      rectOpNorm2Le B (complexMatrixOp2 (realRectToCMatrix B)) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le B le_rfl
  have hA_rect :
      rectOpNorm2Le A (complexMatrixOp2 (realRectToCMatrix B)) :=
    rectOpNorm2Le_of_abs_entry_le hAB hB_rect
  exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le A
    (complexMatrixOp2_nonneg (realRectToCMatrix B)) hA_rect

private theorem higham8_opNorm2_le_of_nonneg_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) :
    complexMatrixOp2 (realRectToCMatrix A) ≤
      complexMatrixOp2 (realRectToCMatrix B) := by
  apply higham8_opNorm2_le_of_abs_le A B
  intro i j
  rw [abs_of_nonneg (hA_nonneg i j)]
  exact hAB i j

private theorem higham8_nonneg_real_matrix_absVec_mul_norm {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (z : CVec n) (i : Fin n) :
    ‖complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z) i‖ =
      ∑ j : Fin n, A i j * ‖z j‖ := by
  have hA_abs_eq : absMatrixRect A = A := by
    ext i j
    simp [absMatrixRect, hA_nonneg i j]
  have hA_abs :
      complexAbsMatrix (realRectToCMatrix A) = realRectToCMatrix A := by
    simpa [hA_abs_eq] using (realRectToCMatrix_absMatrixRect A).symm
  calc
    ‖complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z) i‖
        = ‖complexMatrixVecMul (complexAbsMatrix (realRectToCMatrix A))
            (complexAbsVec z) i‖ := by
              rw [hA_abs]
    _ = ∑ j : Fin n, ‖realRectToCMatrix A i j‖ * ‖z j‖ := by
          exact
            complexMatrixVecMul_absMatrix_absVec_norm_apply
              (realRectToCMatrix A) z i
    _ = ∑ j : Fin n, A i j * ‖z j‖ := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp [realRectToCMatrix, hA_nonneg i j]

private theorem higham8_absolute_norm_vec_le_of_nonneg_le {n : ℕ}
    {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    (habs : IsAbsoluteComplexVectorNorm ν)
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) (z : CVec n) :
    ν (complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z)) ≤
      ν (complexMatrixVecMul (realRectToCMatrix B) (complexAbsVec z)) := by
  have hmono : IsMonotoneComplexVectorNorm ν :=
    (absolute_norm_iff_monotone_norm hν).mp habs
  apply hmono
  intro i
  calc
    ‖complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z) i‖
        = ∑ j : Fin n, A i j * ‖z j‖ :=
          higham8_nonneg_real_matrix_absVec_mul_norm A hA_nonneg z i
    _ ≤ ∑ j : Fin n, B i j * ‖z j‖ := by
          apply Finset.sum_le_sum
          intro j _hj
          exact mul_le_mul_of_nonneg_right (hAB i j) (norm_nonneg (z j))
    _ = ‖complexMatrixVecMul (realRectToCMatrix B) (complexAbsVec z) i‖ := by
          symm
          exact higham8_nonneg_real_matrix_absVec_mul_norm B hB_nonneg z i

/-- **Theorem 8.12**, `∞`-norm chain induced by the entrywise inverse chain. -/
theorem higham8_12_infNorm_chain (n : ℕ)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    infNorm U_inv ≤ infNorm M_inv ∧
      infNorm M_inv ≤ infNorm W_inv ∧
      infNorm W_inv ≤ infNorm (higham8_12_ZInvFormula n α β) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hZ_nonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  have hUM :
      infNorm U_inv ≤ infNorm M_inv :=
    higham8_infNorm_le_of_abs_le_nonneg U_inv M_inv hM_nonneg
      (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
        hUT hU_diag hInv hM_RInv
        (inv_upper_tri n (comparisonMatrix n U) M_inv
          (by
            intro i j hij
            unfold comparisonMatrix
            simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
          (by
            intro i
            simp [comparisonMatrix, hU_diag i])
          (ch7_isLeftInverse_of_isRightInverse hM_RInv)))
  have hMW :
      infNorm M_inv ≤ infNorm W_inv :=
    higham8_infNorm_le_of_nonneg_le M_inv W_inv hM_nonneg hW_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv hUT hU_diag hM_RInv hW_RInv)
  have hWZ :
      infNorm W_inv ≤ infNorm (higham8_12_ZInvFormula n α β) :=
    higham8_infNorm_le_of_nonneg_le W_inv (higham8_12_ZInvFormula n α β)
      hW_nonneg hZ_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv)
  exact ⟨hUM, hMW, hWZ⟩

/-- **Theorem 8.12**, `1`-norm chain induced by the entrywise inverse chain. -/
theorem higham8_12_oneNorm_chain (n : ℕ)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    oneNorm U_inv ≤ oneNorm M_inv ∧
      oneNorm M_inv ≤ oneNorm W_inv ∧
      oneNorm W_inv ≤ oneNorm (higham8_12_ZInvFormula n α β) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hZ_nonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  have hUM :
      oneNorm U_inv ≤ oneNorm M_inv :=
    higham8_oneNorm_le_of_abs_le_nonneg U_inv M_inv hM_nonneg
      (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
        hUT hU_diag hInv hM_RInv
        (inv_upper_tri n (comparisonMatrix n U) M_inv
          (by
            intro i j hij
            unfold comparisonMatrix
            simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
          (by
            intro i
            simp [comparisonMatrix, hU_diag i])
          (ch7_isLeftInverse_of_isRightInverse hM_RInv)))
  have hMW :
      oneNorm M_inv ≤ oneNorm W_inv :=
    higham8_oneNorm_le_of_nonneg_le M_inv W_inv hM_nonneg hW_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv hUT hU_diag hM_RInv hW_RInv)
  have hWZ :
      oneNorm W_inv ≤ oneNorm (higham8_12_ZInvFormula n α β) :=
    higham8_oneNorm_le_of_nonneg_le W_inv (higham8_12_ZInvFormula n α β)
      hW_nonneg hZ_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv)
  exact ⟨hUM, hMW, hWZ⟩

/-- **Theorem 8.12**, `2`-norm chain induced by the entrywise inverse chain. -/
theorem higham8_12_opNorm2_chain (n : ℕ)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    complexMatrixOp2 (realRectToCMatrix U_inv) ≤
        complexMatrixOp2 (realRectToCMatrix M_inv) ∧
      complexMatrixOp2 (realRectToCMatrix M_inv) ≤
        complexMatrixOp2 (realRectToCMatrix W_inv) ∧
      complexMatrixOp2 (realRectToCMatrix W_inv) ≤
        complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hUM :
      complexMatrixOp2 (realRectToCMatrix U_inv) ≤
        complexMatrixOp2 (realRectToCMatrix M_inv) :=
    higham8_opNorm2_le_of_abs_le U_inv M_inv
      (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
        hUT hU_diag hInv hM_RInv
        (inv_upper_tri n (comparisonMatrix n U) M_inv
          (by
            intro i j hij
            unfold comparisonMatrix
            simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
          (by
            intro i
            simp [comparisonMatrix, hU_diag i])
          (ch7_isLeftInverse_of_isRightInverse hM_RInv)))
  have hMW :
      complexMatrixOp2 (realRectToCMatrix M_inv) ≤
        complexMatrixOp2 (realRectToCMatrix W_inv) :=
    higham8_opNorm2_le_of_nonneg_le M_inv W_inv hM_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv
        hUT hU_diag hM_RInv hW_RInv)
  have hWZ :
      complexMatrixOp2 (realRectToCMatrix W_inv) ≤
        complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) :=
    higham8_opNorm2_le_of_nonneg_le W_inv (higham8_12_ZInvFormula n α β)
      hW_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv)
  exact ⟨hUM, hMW, hWZ⟩

/-- **Theorem 8.12**, absolute-norm vector chain induced by the entrywise
inverse chain. -/
theorem higham8_12_absolute_norm_vector_chain (n : ℕ)
    {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    (habs : IsAbsoluteComplexVectorNorm ν)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|)
    (z : CVec n) :
    ν (complexMatrixVecMul (complexAbsMatrix (realRectToCMatrix U_inv))
          (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) ∧
      ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) ∧
      ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix (higham8_12_ZInvFormula n α β))
          (complexAbsVec z)) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hZ_nonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  have hUM :
      ν (complexMatrixVecMul (complexAbsMatrix (realRectToCMatrix U_inv))
            (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) := by
    have hA :
        ∀ i j : Fin n, absMatrixRect U_inv i j ≤ M_inv i j := by
      intro i j
      simpa [absMatrixRect] using
        (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
          hUT hU_diag hInv hM_RInv
          (inv_upper_tri n (comparisonMatrix n U) M_inv
            (by
              intro i j hij
              unfold comparisonMatrix
              simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
            (by
              intro i
              simp [comparisonMatrix, hU_diag i])
            (ch7_isLeftInverse_of_isRightInverse hM_RInv))) i j
    simpa [realRectToCMatrix_absMatrixRect] using
      (higham8_absolute_norm_vec_le_of_nonneg_le hν habs
        (absMatrixRect U_inv) M_inv
        (by intro i j; exact abs_nonneg _)
        hM_nonneg hA z)
  have hMW :
      ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) :=
    higham8_absolute_norm_vec_le_of_nonneg_le hν habs
      M_inv W_inv hM_nonneg hW_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv
        hUT hU_diag hM_RInv hW_RInv) z
  have hWZ :
      ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix (higham8_12_ZInvFormula n α β))
          (complexAbsVec z)) :=
    higham8_absolute_norm_vec_le_of_nonneg_le hν habs
      W_inv (higham8_12_ZInvFormula n α β) hW_nonneg hZ_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv) z
  exact ⟨hUM, hMW, hWZ⟩

/-- **Problem 8.5 / Theorem 8.14 support**: the scaled `Z` inverse has exact
∞-norm `(1 + β)^(n-1) / α` when `α > 0` and `β ≥ 0`. -/
theorem higham8_5_ZInvFormula_infNorm_eq (n : ℕ) (hn : 0 < n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    infNorm (higham8_12_ZInvFormula n α β) =
      (1 / α) * (1 + β) ^ (n - 1) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hnonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      have habs :
          ∑ j : Fin n, |higham8_12_ZInvFormula n α β i j| =
            ∑ j : Fin n, higham8_12_ZInvFormula n α β i j := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact abs_of_nonneg (hnonneg i j)
      rw [habs, higham8_12_ZInvFormula_row_sum]
      have hbase : 1 ≤ 1 + β := by linarith
      have hpow :
          (1 + β) ^ (n - 1 - i.val) ≤ (1 + β) ^ (n - 1) :=
        pow_le_pow_right₀ hbase (Nat.sub_le _ _)
      exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)
    · exact mul_nonneg (one_div_nonneg.mpr hα.le) (pow_nonneg (by linarith) _)
  · have hrow := row_sum_le_infNorm (higham8_12_ZInvFormula n α β) i0
    have habs :
        ∑ j : Fin n, |higham8_12_ZInvFormula n α β i0 j| =
          ∑ j : Fin n, higham8_12_ZInvFormula n α β i0 j := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact abs_of_nonneg (hnonneg i0 j)
    rw [habs, higham8_12_ZInvFormula_row_sum] at hrow
    simpa [i0] using hrow

/-- **Problem 8.5 / Theorem 8.14 support**: the scaled `Z` inverse has exact
1-norm `(1 + β)^(n-1) / α` when `α > 0` and `β ≥ 0`. -/
theorem higham8_5_ZInvFormula_oneNorm_eq (n : ℕ) (hn : 0 < n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    oneNorm (higham8_12_ZInvFormula n α β) =
      (1 / α) * (1 + β) ^ (n - 1) := by
  let jLast : Fin n := ⟨n - 1, by omega⟩
  have hnonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  apply le_antisymm
  · apply oneNorm_le_of_col_sum_le
    · intro j
      have habs :
          ∑ i : Fin n, |higham8_12_ZInvFormula n α β i j| =
            ∑ i : Fin n, higham8_12_ZInvFormula n α β i j := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact abs_of_nonneg (hnonneg i j)
      rw [habs, higham8_12_ZInvFormula_col_sum]
      have hbase : 1 ≤ 1 + β := by linarith
      have hpow : (1 + β) ^ j.val ≤ (1 + β) ^ (n - 1) := by
        have hj : j.val ≤ n - 1 := by omega
        exact pow_le_pow_right₀ hbase hj
      exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)
    · exact mul_nonneg (one_div_nonneg.mpr hα.le) (pow_nonneg (by linarith) _)
  · have hcol := col_sum_le_oneNorm (higham8_12_ZInvFormula n α β) jLast
    have habs :
        ∑ i : Fin n, |higham8_12_ZInvFormula n α β i jLast| =
          ∑ i : Fin n, higham8_12_ZInvFormula n α β i jLast := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact abs_of_nonneg (hnonneg i jLast)
    rw [habs, higham8_12_ZInvFormula_col_sum] at hcol
    simpa [jLast] using hcol

/-- **Problem 8.5 / Theorem 8.14 support**: the Euclidean operator norm of the
scaled `Z` inverse is bounded by the same explicit endpoint as the `1`- and
`∞`-norms. -/
theorem higham8_5_ZInvFormula_opNorm2_le (n : ℕ) (hn : 0 < n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
      (1 / α) * (1 + β) ^ (n - 1) := by
  let c : ℝ := (1 / α) * (1 + β) ^ (n - 1)
  have hbound :=
    problem7_10e_complexMatrixOp2_realRectToCMatrix_le_sqrt_one_mul_inf hn
      (higham8_12_ZInvFormula n α β)
  have hone := higham8_5_ZInvFormula_oneNorm_eq n hn hα hβ
  have hinf := higham8_5_ZInvFormula_infNorm_eq n hn hα hβ
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (one_div_nonneg.mpr hα.le) (pow_nonneg (by linarith) _)
  calc
    complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β))
        ≤ Real.sqrt
            (oneNorm (higham8_12_ZInvFormula n α β) *
              infNorm (higham8_12_ZInvFormula n α β)) := hbound
    _ = Real.sqrt (c * c) := by rw [hone, hinf]
    _ = c := by
      rw [show c * c = c ^ 2 by ring]
      simpa [abs_of_nonneg hc_nonneg] using (Real.sqrt_sq_eq_abs c)

/-- **Theorem 8.14 support**: under `β ≤ 1`, the exact `1`-norm of the scaled
`Z` inverse is bounded by `2^(n-1) / α`. -/
theorem higham8_14_ZInvFormula_oneNorm_upperBound (n : ℕ) (hn : 0 < n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    oneNorm (higham8_12_ZInvFormula n α β) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  rw [higham8_5_ZInvFormula_oneNorm_eq n hn hα hβ]
  have hpow : (1 + β) ^ (n - 1) ≤ (2 : ℝ) ^ (n - 1) := by
    have honeβ_nonneg : 0 ≤ 1 + β := by linarith
    have honeβ_le_two : 1 + β ≤ (2 : ℝ) := by linarith
    exact pow_le_pow_left₀ honeβ_nonneg honeβ_le_two (n - 1)
  exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)

/-- **Theorem 8.14 support**: under `β ≤ 1`, the exact `∞`-norm of the scaled
`Z` inverse is bounded by `2^(n-1) / α`. -/
theorem higham8_14_ZInvFormula_infNorm_upperBound (n : ℕ) (hn : 0 < n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    infNorm (higham8_12_ZInvFormula n α β) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  rw [higham8_5_ZInvFormula_infNorm_eq n hn hα hβ]
  have hpow : (1 + β) ^ (n - 1) ≤ (2 : ℝ) ^ (n - 1) := by
    have honeβ_nonneg : 0 ≤ 1 + β := by linarith
    have honeβ_le_two : 1 + β ≤ (2 : ℝ) := by linarith
    exact pow_le_pow_left₀ honeβ_nonneg honeβ_le_two (n - 1)
  exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)

/-- **Theorem 8.14 support**: under `β ≤ 1`, the Euclidean operator norm of
the scaled `Z` inverse is bounded by `2^(n-1) / α`. -/
theorem higham8_14_ZInvFormula_opNorm2_upperBound (n : ℕ) (hn : 0 < n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  have hendpoint := higham8_5_ZInvFormula_opNorm2_le n hn hα hβ
  have hpow : (1 + β) ^ (n - 1) ≤ (2 : ℝ) ^ (n - 1) := by
    have honeβ_nonneg : 0 ≤ 1 + β := by linarith
    have honeβ_le_two : 1 + β ≤ (2 : ℝ) := by linarith
    exact pow_le_pow_left₀ honeβ_nonneg honeβ_le_two (n - 1)
  have hscale :
      (1 / α) * (1 + β) ^ (n - 1) ≤ (1 / α) * (2 : ℝ) ^ (n - 1) :=
    mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)
  exact hendpoint.trans hscale

/-- **Theorem 8.14 support**: under `β ≤ 1`, the source `1`-norm of `U⁻¹`
is bounded by the same `Z(U)` endpoint. -/
theorem higham8_14_oneNorm_upperBound (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    oneNorm U_inv ≤ (1 / α) * (2 : ℝ) ^ (n - 1) := by
  have honeChain :=
    higham8_12_oneNorm_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  exact honeChain.1.trans
    (honeChain.2.1.trans
      (honeChain.2.2.trans
        (higham8_14_ZInvFormula_oneNorm_upperBound n hn hα hβ hβ1)))

/-- **Theorem 8.14 support**: under `β ≤ 1`, the source `2`-norm of `U⁻¹`
is bounded by the same `Z(U)` endpoint. -/
theorem higham8_14_opNorm2_upperBound (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    complexMatrixOp2 (realRectToCMatrix U_inv) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  have hchain :=
    higham8_12_opNorm2_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  exact hchain.1.trans
    (hchain.2.1.trans
      (hchain.2.2.trans
        (higham8_14_ZInvFormula_opNorm2_upperBound n hn hα hβ hβ1)))

/-- **Algorithm 8.13**, output quantity: the comparison-inverse ∞-norm bound. -/
noncomputable def higham8_13_mu {n : ℕ} (M_inv : Fin n → Fin n → ℝ) : ℝ :=
  infNorm M_inv

/-- **Algorithm 8.13**, exact vector computed by solving `M(U)y = e`. -/
noncomputable def higham8_13_y {n : ℕ} (M_inv : Fin n → Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j : Fin n, M_inv i j

/-- **Algorithm 8.13**, exact recurrence for `y = M(U)⁻¹e`. -/
theorem higham8_13_comparison_inverse_row_recurrence (n : ℕ)
    (U M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (i : Fin n) :
    |U i i| * higham8_13_y M_inv i = 1 +
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
        |U i j| * higham8_13_y M_inv j :=
  compMatrix_inv_upper_row_eq_ones n U M_inv hUT hU_diag hM_RInv i

/-- **Algorithm 8.13**, certified upper-bound property.  If `M_inv` is the
inverse of the comparison matrix and dominates `|U_inv|`, its displayed
∞-norm is an upper bound for `‖U⁻¹‖∞`. -/
theorem higham8_13_inverse_bound_from_comparison {n : ℕ}
    (U_inv M_inv : Fin n → Fin n → ℝ)
    (habs : ∀ i j : Fin n, |U_inv i j| ≤ M_inv i j) :
    infNorm U_inv ≤ higham8_13_mu M_inv := by
  unfold higham8_13_mu
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |U_inv i j|
        ≤ ∑ j : Fin n, M_inv i j := by
          apply Finset.sum_le_sum
          intro j _
          exact habs i j
      _ = ∑ j : Fin n, |M_inv i j| := by
          apply Finset.sum_congr rfl
          intro j _
          exact (abs_of_nonneg ((abs_nonneg (U_inv i j)).trans (habs i j))).symm
      _ ≤ infNorm M_inv := row_sum_le_infNorm M_inv i
  · exact infNorm_nonneg M_inv

/-- **Theorem 8.14**, ∞-norm lower-bound part of (8.9). -/
theorem higham8_14_infNorm_lowerBound (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
      (fun k => |U k k|)) ≤ infNorm U_inv := by
  classical
  let α : ℝ :=
    Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩ (fun k : Fin n => |U k k|)
  rcases Finset.exists_mem_eq_inf'
      (s := Finset.univ) ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|) with
    ⟨k, _hk_mem, hα_eq⟩
  have hrow :
      1 / |U k k| ≤ ∑ j : Fin n, |U_inv k j| :=
    triInv_row_sum_lowerBound n U U_inv hDD.1 hDD.2.1 hInv k
  calc
    1 / α = 1 / |U k k| := by
      simpa [α] using congrArg (fun x : ℝ => 1 / x) hα_eq
    _ ≤ ∑ j : Fin n, |U_inv k j| := hrow
    _ ≤ infNorm U_inv := row_sum_le_infNorm U_inv k

/-- **Theorem 8.14**, `1`-norm lower-bound part of (8.9) at a chosen
diagonal index. -/
theorem higham8_14_oneNorm_lowerBound (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv) :
    (1 / |U i0 i0|) ≤ oneNorm U_inv := by
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hInv.1
  have hdiag : U_inv i0 i0 = 1 / U i0 i0 :=
    inv_diag_entry n U U_inv hUT hU_diag hInv.1 hInv_ut i0
  have hterm : |U_inv i0 i0| ≤ ∑ i : Fin n, |U_inv i i0| := by
    simpa using
      (Finset.single_le_sum (fun i _hi => abs_nonneg (U_inv i i0))
        (Finset.mem_univ i0))
  have habs : |U_inv i0 i0| = 1 / |U i0 i0| := by
    rw [hdiag, abs_div, abs_one]
  calc
    1 / |U i0 i0| = |U_inv i0 i0| := by rw [habs]
    _ ≤ ∑ i : Fin n, |U_inv i i0| := hterm
    _ ≤ oneNorm U_inv := col_sum_le_oneNorm U_inv i0

/-- **Theorem 8.14**, `2`-norm lower-bound part of (8.9) at a chosen
diagonal index. -/
theorem higham8_14_opNorm2_lowerBound (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv) :
    (1 / |U i0 i0|) ≤ complexMatrixOp2 (realRectToCMatrix U_inv) := by
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hInv.1
  have hdiag : U_inv i0 i0 = 1 / U i0 i0 :=
    inv_diag_entry n U U_inv hUT hU_diag hInv.1 hInv_ut i0
  have hbound :=
    hasComplexMatrixLpBound_apply
      (complexMatrixOp2_hasComplexMatrixLpBound (realRectToCMatrix U_inv))
      (standardBasisCVec i0)
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hcol :
      complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
          (fun i : Fin n => realRectToCMatrix U_inv i i0) ≤
        complexMatrixOp2 (realRectToCMatrix U_inv) := by
    rw [complexMatrixVecMul_standardBasisCVec,
      complexVecLpNorm_standardBasisCVec (ENNReal.ofReal (2 : ℝ)) i0, mul_one] at hbound
    exact hbound
  have hcoord :
      ‖realRectToCMatrix U_inv i0 i0‖ ≤
        complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
          (fun i : Fin n => realRectToCMatrix U_inv i i0) := by
    letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
    simpa using
      (complexVecLpNorm_coord_le (ENNReal.ofReal (2 : ℝ))
        (fun i : Fin n => realRectToCMatrix U_inv i i0) i0)
  calc
    1 / |U i0 i0| = |U_inv i0 i0| := by
      rw [hdiag, abs_div, abs_one]
    _ = ‖realRectToCMatrix U_inv i0 i0‖ := by
      simp [realRectToCMatrix]
    _ ≤ complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
          (fun i : Fin n => realRectToCMatrix U_inv i i0) := hcoord
    _ ≤ complexMatrixOp2 (realRectToCMatrix U_inv) := hcol

/-- **Theorem 8.14**, ∞-norm part of the inverse-bound chain under (8.5). -/
theorem higham8_14_infNorm_upperBound (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    infNorm U_inv ≤
      2 ^ (n - 1) *
        (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
          (fun k => |U k k|)) :=
  triInv_infNorm_upperBound n U U_inv i0 hDD hInv

/-- **Theorem 8.14**, packaged `∞/1/2` norm chains in the source notation
using the minimum diagonal magnitude. -/
theorem higham8_14_full_norm_chain (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n) {β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    let α : ℝ :=
      Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
        (fun k : Fin n => |U k k|)
    (1 / α ≤ infNorm U_inv ∧
        infNorm U_inv ≤ infNorm M_inv ∧
        infNorm M_inv ≤ infNorm W_inv ∧
        infNorm W_inv ≤ infNorm (higham8_12_ZInvFormula n α β) ∧
        infNorm (higham8_12_ZInvFormula n α β) ≤
          (1 / α) * (2 : ℝ) ^ (n - 1)) ∧
      (1 / α ≤ oneNorm U_inv ∧
        oneNorm U_inv ≤ oneNorm M_inv ∧
        oneNorm M_inv ≤ oneNorm W_inv ∧
        oneNorm W_inv ≤ oneNorm (higham8_12_ZInvFormula n α β) ∧
        oneNorm (higham8_12_ZInvFormula n α β) ≤
          (1 / α) * (2 : ℝ) ^ (n - 1)) ∧
      (1 / α ≤ complexMatrixOp2 (realRectToCMatrix U_inv) ∧
        complexMatrixOp2 (realRectToCMatrix U_inv) ≤
          complexMatrixOp2 (realRectToCMatrix M_inv) ∧
        complexMatrixOp2 (realRectToCMatrix M_inv) ≤
          complexMatrixOp2 (realRectToCMatrix W_inv) ∧
        complexMatrixOp2 (realRectToCMatrix W_inv) ≤
          complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ∧
        complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
          (1 / α) * (2 : ℝ) ^ (n - 1)) := by
  classical
  let α : ℝ :=
    Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|)
  rcases Finset.exists_mem_eq_inf'
      (s := Finset.univ) ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|) with
    ⟨k, _hk_mem, hα_eq⟩
  have hα : 0 < α := by
    dsimp [α]
    rw [hα_eq]
    exact abs_pos.mpr (hU_diag k)
  have hα_le_diag : ∀ i : Fin n, α ≤ |U i i| := by
    intro i
    simpa [α] using
      (Finset.inf'_le (s := Finset.univ)
        (f := fun k : Fin n => |U k k|) (b := i) (Finset.mem_univ i))
  have hDD : IsDiagDominantUpper n U := by
    refine ⟨hUT, hU_diag, ?_⟩
    intro i j hij
    have hdiag_nonneg : 0 ≤ |U i i| := abs_nonneg (U i i)
    calc
      |U i j| ≤ β * |U i i| := hβ_bound i j hij
      _ ≤ |U i i| := by nlinarith
  have hInfChain :=
    higham8_12_infNorm_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  have hOneChain :=
    higham8_12_oneNorm_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  have hOp2Chain :=
    higham8_12_opNorm2_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  have hInfLower :
      1 / α ≤ infNorm U_inv :=
    higham8_14_infNorm_lowerBound n U U_inv i0 hDD hInv
  have hOneLower :
      1 / α ≤ oneNorm U_inv := by
    calc
      1 / α = 1 / |U k k| := by
        simpa [α] using congrArg (fun x : ℝ => 1 / x) hα_eq
      _ ≤ oneNorm U_inv :=
        higham8_14_oneNorm_lowerBound n U U_inv k hUT hU_diag hInv
  have hOp2Lower :
      1 / α ≤ complexMatrixOp2 (realRectToCMatrix U_inv) := by
    calc
      1 / α = 1 / |U k k| := by
        simpa [α] using congrArg (fun x : ℝ => 1 / x) hα_eq
      _ ≤ complexMatrixOp2 (realRectToCMatrix U_inv) :=
        higham8_14_opNorm2_lowerBound n U U_inv k hUT hU_diag hInv
  have hInfUpperZ :
      infNorm (higham8_12_ZInvFormula n α β) ≤
        (1 / α) * (2 : ℝ) ^ (n - 1) :=
    higham8_14_ZInvFormula_infNorm_upperBound n hn hα hβ hβ1
  have hOneUpperZ :
      oneNorm (higham8_12_ZInvFormula n α β) ≤
        (1 / α) * (2 : ℝ) ^ (n - 1) :=
    higham8_14_ZInvFormula_oneNorm_upperBound n hn hα hβ hβ1
  have hOp2UpperZ :
      complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
        (1 / α) * (2 : ℝ) ^ (n - 1) :=
    higham8_14_ZInvFormula_opNorm2_upperBound n hn hα hβ hβ1
  exact ⟨⟨hInfLower, hInfChain.1, hInfChain.2.1, hInfChain.2.2, hInfUpperZ⟩,
    ⟨⟨hOneLower, hOneChain.1, hOneChain.2.1, hOneChain.2.2, hOneUpperZ⟩,
      ⟨hOp2Lower, hOp2Chain.1, hOp2Chain.2.1, hOp2Chain.2.2, hOp2UpperZ⟩⟩⟩

/-- **Problem 8.7(a)**: the strict row-diagonal-dominance margin of row `i`. -/
noncomputable def higham8_7_rowDiagMargin {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  |A i i| - ∑ j ∈ Finset.univ.erase i, |A i j|

/-- **Problem 8.7(b)**: the positively scaled strict row-diagonal-dominance
margin of row `i`. -/
noncomputable def higham8_7_scaledRowDiagMargin {n : ℕ}
    (A : Fin n → Fin n → ℝ) (d : Fin n → ℝ) (i : Fin n) : ℝ :=
  |A i i| * d i - ∑ j ∈ Finset.univ.erase i, |A i j| * d j

private theorem higham8_7_nonneg_sup_eq_infNormVec {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx_nonneg : ∀ i : Fin n, 0 ≤ x i) :
    Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ x = infNormVec x := by
  let δ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ x
  have hδ_nonneg : 0 ≤ δ := by
    exact le_trans (hx_nonneg ⟨0, hn⟩) (Finset.le_sup' x (Finset.mem_univ _))
  apply le_antisymm
  · rcases Finset.exists_mem_eq_sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ x with
      ⟨i0, _, hδ⟩
    rw [hδ]
    simpa [abs_of_nonneg (hx_nonneg i0)] using abs_le_infNormVec x i0
  · apply infNormVec_le_of_abs_le
    · intro i
      have hle : x i ≤ δ := Finset.le_sup' x (Finset.mem_univ i)
      simpa [δ, abs_of_nonneg (hx_nonneg i)] using hle
    · exact hδ_nonneg

private theorem higham8_7_scaled_vector_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (d x : Fin n → ℝ)
    (hd_pos : ∀ i : Fin n, 0 < d i)
    (hβ_pos : ∀ i : Fin n, 0 < higham8_7_scaledRowDiagMargin A d i) :
    infNormVec x ≤
      ((Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d) /
        (Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
          (higham8_7_scaledRowDiagMargin A d))) *
        infNormVec (matMulVec n A x) := by
  let δ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d
  let β := Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (higham8_7_scaledRowDiagMargin A d)
  let ρ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (fun i : Fin n => |x i| / d i)
  have hδ_nonneg : 0 ≤ δ := by
    exact le_trans (le_of_lt (hd_pos ⟨0, hn⟩)) (Finset.le_sup' d (Finset.mem_univ _))
  have hρ_nonneg : 0 ≤ ρ := by
    have hterm : 0 ≤ |x ⟨0, hn⟩| / d ⟨0, hn⟩ := by
      exact div_nonneg (abs_nonneg _) (le_of_lt (hd_pos _))
    exact le_trans hterm (Finset.le_sup' (fun i : Fin n => |x i| / d i) (Finset.mem_univ _))
  have hβ_pos' : 0 < β := by
    rcases Finset.exists_mem_eq_inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_scaledRowDiagMargin A d) with
      ⟨i0, _, hβ⟩
    dsimp [β]
    rw [hβ]
    exact hβ_pos i0
  have hx_le : ∀ i : Fin n, |x i| ≤ d i * ρ := by
    intro i
    have hi : |x i| / d i ≤ ρ :=
      Finset.le_sup' (fun j : Fin n => |x j| / d j) (Finset.mem_univ i)
    have hmul := (div_le_iff₀ (hd_pos i)).mp hi
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hx_norm_le : infNormVec x ≤ δ * ρ := by
    apply infNormVec_le_of_abs_le
    · intro i
      have hiδ : d i ≤ δ := Finset.le_sup' d (Finset.mem_univ i)
      calc
        |x i| ≤ d i * ρ := hx_le i
        _ ≤ δ * ρ := mul_le_mul_of_nonneg_right hiδ hρ_nonneg
    · exact mul_nonneg hδ_nonneg hρ_nonneg
  rcases Finset.exists_mem_eq_sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      (fun i : Fin n => |x i| / d i) with
    ⟨i0, _, hρ⟩
  have hx_i0 : |x i0| = d i0 * ρ := by
    have hmul : ρ * d i0 = |x i0| :=
      (eq_div_iff (show d i0 ≠ 0 from (hd_pos i0).ne')).mp hρ
    simpa [mul_comm] using hmul.symm
  have hsplit :
      ∑ j : Fin n, A i0 j * x j =
        A i0 i0 * x i0 + ∑ j ∈ Finset.univ.erase i0, A i0 j * x j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
  have habs_diag :
      |A i0 i0| * |x i0| ≤
        |matMulVec n A x i0| +
          ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j| := by
    calc
      |A i0 i0| * |x i0| = |A i0 i0 * x i0| := by rw [abs_mul]
      _ = |matMulVec n A x i0 - ∑ j ∈ Finset.univ.erase i0, A i0 j * x j| := by
          unfold matMulVec
          rw [hsplit]
          ring
      _ ≤ |matMulVec n A x i0| + |∑ j ∈ Finset.univ.erase i0, A i0 j * x j| := by
          simpa using (abs_sub (matMulVec n A x i0)
            (∑ j ∈ Finset.univ.erase i0, A i0 j * x j))
      _ ≤ |matMulVec n A x i0| +
            ∑ j ∈ Finset.univ.erase i0, |A i0 j * x j| := by
          have hsumabs :
              |∑ j ∈ Finset.univ.erase i0, A i0 j * x j| ≤
                ∑ j ∈ Finset.univ.erase i0, |A i0 j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
          linarith
      _ = |matMulVec n A x i0| +
            ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j| := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul]
  have hoff :
      ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j| ≤
        (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
    calc
      ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j|
          ≤ ∑ j ∈ Finset.univ.erase i0, |A i0 j| * (d j * ρ) := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left (hx_le j) (abs_nonneg _)
      _ = ∑ j ∈ Finset.univ.erase i0, (|A i0 j| * d j) * ρ := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
            symm
            exact Finset.sum_mul (Finset.univ.erase i0) (fun j => |A i0 j| * d j) ρ
  have hmargin_i0 :
      higham8_7_scaledRowDiagMargin A d i0 * ρ ≤ |matMulVec n A x i0| := by
    have hlin :
        |A i0 i0| * |x i0| -
            (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ ≤
          |matMulVec n A x i0| := by
      have hbound :
          |A i0 i0| * |x i0| ≤
            |matMulVec n A x i0| +
              (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ :=
        by nlinarith [habs_diag, hoff]
      linarith
    unfold higham8_7_scaledRowDiagMargin
    calc
      (|A i0 i0| * d i0 - ∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ
          = |A i0 i0| * (d i0 * ρ) -
              (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
              ring
      _ = |A i0 i0| * |x i0| -
            (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
              rw [hx_i0]
      _ ≤ |matMulVec n A x i0| := hlin
  have hβρ :
      β * ρ ≤ infNormVec (matMulVec n A x) := by
    calc
      β * ρ
          ≤ higham8_7_scaledRowDiagMargin A d i0 * ρ := by
              exact mul_le_mul_of_nonneg_right
                (Finset.inf'_le (higham8_7_scaledRowDiagMargin A d) (Finset.mem_univ i0))
                hρ_nonneg
      _ ≤ |matMulVec n A x i0| := hmargin_i0
      _ ≤ infNormVec (matMulVec n A x) := abs_le_infNormVec _ i0
  have hρ_le : ρ ≤ infNormVec (matMulVec n A x) / β := by
    exact (le_div_iff₀ hβ_pos').2 (by simpa [mul_comm] using hβρ)
  calc
    infNormVec x ≤ δ * ρ := hx_norm_le
    _ ≤ δ * (infNormVec (matMulVec n A x) / β) := by
          exact mul_le_mul_of_nonneg_left hρ_le hδ_nonneg
    _ = (δ / β) * infNormVec (matMulVec n A x) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring

/-- **Problem 8.7(b)**: a positive diagonal row scaling `D = diag(d)` with
strictly diagonally dominant rows bounds `‖A⁻¹‖∞` by `‖D‖∞ / min_i β_i`. -/
theorem higham8_7_scaledStrictRowDiagDominant_invInfNorm_le (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (d : Fin n → ℝ)
    (hInv : IsInverse n A A_inv)
    (hd_pos : ∀ i : Fin n, 0 < d i)
    (hβ_pos : ∀ i : Fin n, 0 < higham8_7_scaledRowDiagMargin A d i) :
    infNorm A_inv ≤
      (Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d) /
        (Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
          (higham8_7_scaledRowDiagMargin A d)) := by
  let δ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d
  let β := Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (higham8_7_scaledRowDiagMargin A d)
  have hδ_nonneg : 0 ≤ δ := by
    exact le_trans (le_of_lt (hd_pos ⟨0, hn⟩)) (Finset.le_sup' d (Finset.mem_univ _))
  have hβ_pos' : 0 < β := by
    rcases Finset.exists_mem_eq_inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_scaledRowDiagMargin A d) with
      ⟨i0, _, hβ⟩
    dsimp [β]
    rw [hβ]
    exact hβ_pos i0
  have hprod_nonneg : 0 ≤ δ / β := div_nonneg hδ_nonneg (le_of_lt hβ_pos')
  apply infNorm_le_of_row_sum_le
  · intro i
    let s : Fin n → ℝ := fun j => SignType.sign (A_inv i j)
    have hs_norm : infNormVec s ≤ 1 := by
      apply infNormVec_le_of_abs_le
      · intro j
        cases hsgn : SignType.sign (A_inv i j) <;> simp [s, hsgn]
      · norm_num
    have hrow_eq : matMulVec n A_inv s i = ∑ j : Fin n, |A_inv i j| := by
      unfold matMulVec s
      apply Finset.sum_congr rfl
      intro j _
      simpa using (self_mul_sign (A_inv i j))
    have hprod : matMul n A A_inv = idMatrix n := by
      ext r c
      simpa [matMul, idMatrix] using hInv.2 r c
    have hAx : matMulVec n A (matMulVec n A_inv s) = s := by
      ext r
      calc
        matMulVec n A (matMulVec n A_inv s) r
            = matMulVec n (matMul n A A_inv) s r := by
                symm
                exact matMulVec_matMul n A A_inv s r
        _ = matMulVec n (idMatrix n) s r := by rw [hprod]
        _ = s r := by rw [matMulVec_id]
    have hvec :=
      higham8_7_scaled_vector_bound hn A d (matMulVec n A_inv s) hd_pos hβ_pos
    have hvec' : infNormVec (matMulVec n A_inv s) ≤ (δ / β) * infNormVec s := by
      simpa [δ, β, hAx] using hvec
    have hrow_abs : |matMulVec n A_inv s i| = ∑ j : Fin n, |A_inv i j| := by
      rw [hrow_eq]
      exact abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))
    calc
      ∑ j : Fin n, |A_inv i j| = |matMulVec n A_inv s i| := by
          symm
          exact hrow_abs
      _ ≤ infNormVec (matMulVec n A_inv s) := abs_le_infNormVec _ i
      _ ≤ (δ / β) * infNormVec s := hvec'
      _ ≤ (δ / β) * 1 := mul_le_mul_of_nonneg_left hs_norm hprod_nonneg
      _ = δ / β := by ring
  · exact hprod_nonneg

/-- **Problem 8.7(a)**: a strictly row diagonally dominant matrix satisfies
`‖A⁻¹‖∞ ≤ 1 / min_i α_i`. -/
theorem higham8_7_strictRowDiagDominant_invInfNorm_le (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A A_inv)
    (hα_pos : ∀ i : Fin n, 0 < higham8_7_rowDiagMargin A i) :
    infNorm A_inv ≤
      1 / (Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_rowDiagMargin A)) := by
  simpa [higham8_7_scaledRowDiagMargin, higham8_7_rowDiagMargin]
    using
      (higham8_7_scaledStrictRowDiagDominant_invInfNorm_le n hn A A_inv
        (fun _ => 1) hInv (fun _ => by norm_num)
        (by
          intro i
          simpa [higham8_7_scaledRowDiagMargin, higham8_7_rowDiagMargin]
            using hα_pos i))

/-- **Problem 8.7(c)**: taking `D = diag(M(U)⁻¹ e)` rederives the Algorithm
8.13 upper bound `‖M(U)⁻¹ e‖∞ ≥ ‖U⁻¹‖∞`. -/
theorem higham8_7_comparisonInverseOnes_infNorm_ge_inverseInfNorm (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    infNorm U_inv ≤ infNormVec (higham8_13_y M_inv) := by
  let y : Fin n → ℝ := higham8_13_y M_inv
  have habs :=
    abs_inv_le_compMatrix_inv n U U_inv M_inv hUT hU_diag hInv hM_RInv hM_inv_ut
  have hU_bound : infNorm U_inv ≤ infNorm M_inv := by
    simpa [higham8_13_mu] using higham8_13_inverse_bound_from_comparison U_inv M_inv habs
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n U i i := by
    intro i
    simp [comparisonMatrix]
    exact hU_diag i
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n U i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
      hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  have hM_LInv := ch7_isLeftInverse_of_isRightInverse hM_RInv
  have hM_inv_diag : ∀ i : Fin n, M_inv i i = 1 / |U i i| := by
    intro i
    have hM_inv_ut :=
      inv_upper_tri n (comparisonMatrix n U) M_inv hM_ut
        (fun k => by simpa [comparisonMatrix] using hU_diag k) hM_LInv
    simpa [comparisonMatrix] using
      inv_diag_entry n (comparisonMatrix n U) M_inv hM_ut
        (fun k => by simpa [comparisonMatrix] using hU_diag k) hM_LInv hM_inv_ut i
  have hy_pos : ∀ i : Fin n, 0 < y i := by
    intro i
    unfold y higham8_13_y
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hdiag_pos : 0 < M_inv i i := by
      rw [hM_inv_diag]
      exact one_div_pos.mpr (abs_pos.mpr (hU_diag i))
    have hrest_nonneg :
        0 ≤ ∑ j ∈ Finset.univ.erase i, M_inv i j := by
      exact Finset.sum_nonneg (fun j _ => hM_nonneg i j)
    linarith
  have hy_nonneg : ∀ i : Fin n, 0 ≤ y i := by
    intro i
    exact (hy_pos i).le
  have hβ_eq_one :
      ∀ i : Fin n, higham8_7_scaledRowDiagMargin (comparisonMatrix n U) y i = 1 := by
    intro i
    unfold higham8_7_scaledRowDiagMargin y higham8_13_y
    have herase_eq :
        ∑ j ∈ Finset.univ.erase i, |comparisonMatrix n U i j| * (∑ k : Fin n, M_inv j k) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
            |U i j| * (∑ k : Fin n, M_inv j k) := by
      calc
        ∑ j ∈ Finset.univ.erase i, |comparisonMatrix n U i j| * (∑ k : Fin n, M_inv j k)
            = ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                |comparisonMatrix n U i j| * (∑ k : Fin n, M_inv j k) := by
                  symm
                  apply Finset.sum_subset
                  · intro j hj
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                    exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
                  · intro k hk hknot
                    rw [Finset.mem_erase] at hk
                    have hknot' : ¬ i.val < k.val := by
                      intro hc
                      exact hknot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
                    have hlt : k.val < i.val := by omega
                    unfold comparisonMatrix
                    simp [show i ≠ k from Fin.ne_of_val_ne (by omega), hUT i k hlt, zero_mul]
        _ = ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
              |U i j| * (∑ k : Fin n, M_inv j k) := by
                apply Finset.sum_congr rfl
                intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                unfold comparisonMatrix
                simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hj]
    have hrow :=
      higham8_13_comparison_inverse_row_recurrence n U M_inv hUT hU_diag hM_RInv i
    unfold higham8_13_y at hrow
    rw [herase_eq]
    have hmain :
        |U i i| * (∑ j : Fin n, M_inv i j) -
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
              |U i j| * (∑ k : Fin n, M_inv j k) = 1 := by
      linarith [hrow]
    simpa [comparisonMatrix] using hmain
  have hM_bound :=
    higham8_7_scaledStrictRowDiagDominant_invInfNorm_le n hn
      (comparisonMatrix n U) M_inv y ⟨hM_LInv, hM_RInv⟩ hy_pos
      (by
        intro i
        rw [hβ_eq_one i]
        norm_num)
  have hy_sup :
      Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ y = infNormVec y :=
    higham8_7_nonneg_sup_eq_infNormVec hn y hy_nonneg
  have hβ_one :
      Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_scaledRowDiagMargin (comparisonMatrix n U) y) = 1 := by
    apply Finset.inf'_eq_of_forall
    intro i _
    exact hβ_eq_one i
  have hM_bound' : infNorm M_inv ≤ infNormVec y := by
    simpa [y, hy_sup, hβ_one] using hM_bound
  exact le_trans hU_bound hM_bound'

/-! ## Problems -/

private theorem higham8_8_matMulVec_scaledBasis {n : ℕ}
    (A_inv : Fin n → Fin n → ℝ) (i : Fin n) (alpha xj : ℝ) :
    matMulVec n A_inv (fun r => alpha * finiteBasisVec i r * xj) =
      fun r => alpha * A_inv r i * xj := by
  ext r
  unfold matMulVec
  rw [Finset.sum_eq_single i]
  · simp [finiteBasisVec]
    ring
  · intro c _ hc
    simp [finiteBasisVec, hc]
  · simp

private theorem higham8_8_maxEntryNorm_pos_of_inverse {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (hInv : IsInverse n A A_inv) :
    0 < maxEntryNorm hn A_inv := by
  rcases hInv with ⟨_, hRInv⟩
  by_contra hnonpos
  have hmax_zero : maxEntryNorm hn A_inv = 0 :=
    le_antisymm (le_of_not_gt hnonpos) (maxEntryNorm_nonneg hn A_inv)
  have hentry_zero : ∀ i j : Fin n, A_inv i j = 0 := by
    intro i j
    have hle : |A_inv i j| ≤ maxEntryNorm hn A_inv :=
      entry_le_maxEntryNorm hn A_inv i j
    rw [hmax_zero] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have h00 := hRInv ⟨0, hn⟩ ⟨0, hn⟩
  simp [hentry_zero] at h00

/-- **Problem 8.8(a)**, constructive singular rank-one perturbation.

    If `A_inv` is a right inverse of `A` and the `(j,i)` entry of `A_inv` is
    nonzero, then adding `α e_i e_jᵀ` with `α = -(A_inv j i)⁻¹` makes `A`
    singular.  This formalizes the source's possible case
    `α_ij = -(e_jᵀ A⁻¹ e_i)⁻¹`. -/
theorem higham8_8_rankOne_singular_update (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n)
    (hRInv : IsRightInverse n A A_inv)
    (hentry : A_inv j i ≠ 0) :
    Matrix.det
      (Matrix.of A +
        Matrix.single i j (-(A_inv j i)⁻¹)) = 0 := by
  classical
  let x : Fin n → ℝ := fun k => A_inv k i
  have hx_ne : x ≠ 0 := by
    intro hx
    exact hentry (congr_fun hx j)
  have hAx : ∀ r : Fin n, Matrix.mulVec (Matrix.of A) x r =
      if r = i then 1 else 0 := by
    intro r
    simpa [Matrix.mulVec, dotProduct, x] using hRInv r i
  have hmul :
      Matrix.mulVec
        (Matrix.of A + Matrix.single i j (-(A_inv j i)⁻¹)) x = 0 := by
    ext r
    by_cases hri : r = i
    · subst r
      simp [Matrix.add_mulVec, Matrix.single_mulVec, hAx, x]
      field_simp [hentry]
      norm_num
    · simp [Matrix.add_mulVec, Matrix.single_mulVec, hAx, x, hri]
  exact
    (Matrix.exists_mulVec_eq_zero_iff
      (M := (Matrix.of A +
        Matrix.single i j (-(A_inv j i)⁻¹)))).mp
      ⟨x, hx_ne, hmul⟩

/-- **Problem 8.8(a)**, converse singularity condition for a single-entry
rank-one perturbation.

    If `A + α e_i e_jᵀ` is singular, then necessarily
    `1 + α (A⁻¹)_{j i} = 0`. -/
theorem higham8_8_rankOne_singular_update_den_eq_zero (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (hInv : IsInverse n A A_inv)
    (hsing : Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0) :
    1 + alpha * A_inv j i = 0 := by
  classical
  rcases hInv with ⟨hLInv, _⟩
  rcases (Matrix.exists_mulVec_eq_zero_iff
      (M := (Matrix.of A + Matrix.single i j alpha))).mpr hsing with
    ⟨x, hx_ne, hmul⟩
  have hmul' := hmul
  rw [Matrix.add_mulVec, Matrix.single_mulVec] at hmul'
  have hAx : matMulVec n A x = fun r => -alpha * finiteBasisVec i r * x j := by
    ext r
    have hr := congrFun hmul' r
    by_cases hri : r = i
    · subst r
      have hr0 : matMulVec n A x i + alpha * x j = 0 := by
        simpa [Matrix.mulVec, matMulVec, finiteBasisVec] using hr
      have hrow : matMulVec n A x i = -alpha * x j := by
        linarith
      simpa [finiteBasisVec] using hrow
    · have hr0 : matMulVec n A x r = 0 := by
        simpa [Matrix.mulVec, matMulVec, finiteBasisVec, hri] using hr
      simpa [finiteBasisVec, hri] using hr0
  have hprod : matMul n A_inv A = idMatrix n := by
    ext r c
    simpa [matMul] using hLInv r c
  have hxrepr : x = matMulVec n A_inv (fun r => -alpha * finiteBasisVec i r * x j) := by
    ext r
    calc
      x r = matMulVec n (idMatrix n) x r := by rw [matMulVec_id]
      _ = matMulVec n (matMul n A_inv A) x r := by rw [hprod]
      _ = matMulVec n A_inv (matMulVec n A x) r := by
            exact matMulVec_matMul n A_inv A x r
      _ = matMulVec n A_inv (fun r => -alpha * finiteBasisVec i r * x j) r := by
            rw [hAx]
  have hxformula : ∀ r : Fin n, x r = -alpha * A_inv r i * x j := by
    intro r
    have hr := congrFun hxrepr r
    rw [higham8_8_matMulVec_scaledBasis A_inv i (-alpha) (x j)] at hr
    simpa [mul_assoc, mul_left_comm, mul_comm] using hr
  by_contra hden
  have hcoef : (1 + alpha * A_inv j i) * x j = 0 := by
    have hj := hxformula j
    nlinarith
  have hxj_zero : x j = 0 := by
    rcases mul_eq_zero.mp hcoef with hzero | hzero
    · exact False.elim (hden hzero)
    · exact hzero
  have hx_zero : x = 0 := by
    ext r
    rw [hxformula r, hxj_zero]
    simp
  exact hx_ne hx_zero

/-- **Problem 8.8(a)**, exact solvability criterion:
`A + α e_i e_jᵀ` is singular exactly when
`α = -(A⁻¹)_{j i}^{-1}` and `(A⁻¹)_{j i} ≠ 0`. -/
theorem higham8_8_rankOne_singular_update_iff (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (hInv : IsInverse n A A_inv) :
    Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0 ↔
      A_inv j i ≠ 0 ∧ alpha = -(A_inv j i)⁻¹ := by
  constructor
  · intro hsing
    have hden :=
      higham8_8_rankOne_singular_update_den_eq_zero n A A_inv i j alpha hInv hsing
    have hentry : A_inv j i ≠ 0 := by
      intro hzero
      simp [hzero] at hden
    refine ⟨hentry, ?_⟩
    rw [inv_eq_one_div]
    have hprod : alpha * A_inv j i = -1 := by
      linarith [hden]
    have halpha : alpha = -1 / A_inv j i := (eq_div_iff hentry).2 hprod
    simpa [div_eq_mul_inv] using halpha
  · intro h
    rcases hInv with ⟨_, hRInv⟩
    rcases h with ⟨hentry, halpha⟩
    simpa [halpha] using
      higham8_8_rankOne_singular_update n A A_inv i j hRInv hentry

/-- **Problem 8.8(a)**, source magnitude formula for a singular single-entry
perturbation. -/
theorem higham8_8_rankOne_singular_update_abs_eq_inv_abs_inverse_entry (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (hInv : IsInverse n A A_inv)
    (hsing : Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0) :
    |alpha| = |A_inv j i|⁻¹ := by
  rcases (higham8_8_rankOne_singular_update_iff n A A_inv i j alpha hInv).1 hsing with
    ⟨hentry, halpha⟩
  rw [halpha, abs_neg, abs_inv]

/-- **Problem 8.8(a)**, source "best place" criterion:
if `|(A⁻¹)_{r s}|` is maximal, then perturbing the `(s,r)` entry gives the
smallest-magnitude singular rank-one update. -/
theorem higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (r s : Fin n)
    (hInv : IsInverse n A A_inv)
    (hmax : |A_inv r s| = maxEntryNorm hn A_inv) :
    Matrix.det (Matrix.of A + Matrix.single s r (-(A_inv r s)⁻¹)) = 0 ∧
      ∀ i j : Fin n, ∀ alpha : ℝ,
        Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0 →
          |-(A_inv r s)⁻¹| ≤ |alpha| := by
  have hmax_pos : 0 < maxEntryNorm hn A_inv :=
    higham8_8_maxEntryNorm_pos_of_inverse hn A A_inv hInv
  have hrs_pos : 0 < |A_inv r s| := by
    rw [hmax]
    exact hmax_pos
  have hrs : A_inv r s ≠ 0 := abs_pos.mp hrs_pos
  refine ⟨?_, ?_⟩
  · rcases hInv with ⟨_, hRInv⟩
    simpa using
      higham8_8_rankOne_singular_update n A A_inv s r hRInv hrs
  · intro i j alpha hsing
    rcases (higham8_8_rankOne_singular_update_iff n A A_inv i j alpha hInv).1 hsing with
      ⟨hentry, halpha⟩
    have hentry_le : |A_inv j i| ≤ |A_inv r s| := by
      rw [hmax]
      exact entry_le_maxEntryNorm hn A_inv j i
    have hentry_pos : 0 < |A_inv j i| := abs_pos.mpr hentry
    calc
      |-(A_inv r s)⁻¹| = |A_inv r s|⁻¹ := by
        rw [abs_neg, abs_inv]
      _ ≤ |A_inv j i|⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hentry_pos hentry_le
      _ = |alpha| := by
        symm
        exact higham8_8_rankOne_singular_update_abs_eq_inv_abs_inverse_entry
          n A A_inv i j alpha hInv hsing

/-- **Problem 8.8(a)**, existence form of the Appendix A "best place" answer.

    For a nonsingular matrix, there is an inverse entry of maximal absolute
    value, and perturbing the transposed position yields a singular rank-one
    update of smallest possible magnitude. -/
theorem higham8_8_bestRankOneSingularUpdate_exists (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A A_inv) :
    ∃ r s : Fin n,
      |A_inv r s| = maxEntryNorm hn A_inv ∧
      Matrix.det (Matrix.of A + Matrix.single s r (-(A_inv r s)⁻¹)) = 0 ∧
      (∀ i j : Fin n, ∀ alpha : ℝ,
        Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0 →
          |-(A_inv r s)⁻¹| ≤ |alpha|) := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  let rowMax : Fin n → ℝ :=
    fun r => Finset.sup' Finset.univ hne (fun s => |A_inv r s|)
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup' hne rowMax
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup' hne (fun s => |A_inv r s|)
  have hmax : |A_inv r s| = maxEntryNorm hn A_inv := by
    calc
      |A_inv r s| = rowMax r := hs.symm
      _ = maxEntryNorm hn A_inv := by
            simpa [rowMax, maxEntryNorm] using hr.symm
  refine ⟨r, s, hmax, ?_, ?_⟩
  exact (higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry
    n hn A A_inv r s hInv hmax).1
  exact (higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry
    n hn A A_inv r s hInv hmax).2

/-- **Problem 8.8(b)**: the stress matrix `T_n = U(1)` is made singular by a
rank-one update in the `(n,1)` position with
`α = -2^(2-n) = -((2^(n-2))⁻¹)`. -/
theorem higham8_8b_stressUpper_lastFirst_singular_update (n : ℕ) (h2 : 1 < n) :
    Matrix.det
      (Matrix.of (higham8_3_stressUpper n 1) +
        Matrix.single ⟨n - 1, by omega⟩ ⟨0, by omega⟩
          (-((2 : ℝ) ^ (n - 2))⁻¹)) = 0 := by
  let last : Fin n := ⟨n - 1, by omega⟩
  let first : Fin n := ⟨0, by omega⟩
  have hInv := higham8_4_stressUpperInvFormula_isInverse n 1
  have hlt : first.val < last.val := by
    dsimp [first, last]
    omega
  have hne : first ≠ last := Fin.ne_of_val_ne (by
    dsimp [first, last]
    omega)
  have hsub : n - 1 - 1 = n - 2 := by
    omega
  have hpow_two : (1 + 1 : ℝ) ^ (n - 2) = (2 : ℝ) ^ (n - 2) := by
    norm_num
  have hentry_eq :
      higham8_4_stressUpperInvFormula n 1 first last = (2 : ℝ) ^ (n - 2) := by
    simp [higham8_4_stressUpperInvFormula, first, last, hlt, hne, hsub, hpow_two]
  have hentry : higham8_4_stressUpperInvFormula n 1 first last ≠ 0 := by
    rw [hentry_eq]
    positivity
  have hs :=
    higham8_8_rankOne_singular_update n
      (higham8_3_stressUpper n 1)
      (higham8_4_stressUpperInvFormula n 1)
      last first hInv.2 hentry
  simpa [first, last, higham8_4_stressUpperInvFormula, hlt, hne, hsub, hpow_two] using hs

end LeanFpAnalysis.FP
