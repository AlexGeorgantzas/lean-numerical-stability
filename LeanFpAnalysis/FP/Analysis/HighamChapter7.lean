-- Analysis/HighamChapter7.lean
--
-- Source-facing wrappers for Higham Chapter 7.
--
-- The heavy perturbation arguments live in `PerturbationTheory.lean`; this file
-- records Chapter 7 statements whose exact source shape is a relative
-- infinity-norm or practical-error corollary of those componentwise results.

import LeanFpAnalysis.FP.Analysis.PerturbationTheory

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- Chapter 7 forward-error kernels
-- ============================================================

/-- The vector `|A⁻¹|(E|x| + f)` appearing in Theorem 7.4 and (7.28). -/
noncomputable def ch7AmplifiedRhsEF (n : ℕ)
    (A_inv : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ)
    (f x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, |A_inv i j| *
    (∑ k : Fin n, E j k * |x k| + f j)

/-- The infinity-norm quantity `‖ |A⁻¹|(E|x| + f) ‖∞`. -/
noncomputable def ch7ForwardBoundEF (n : ℕ) (hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ)
    (f x : Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (ch7AmplifiedRhsEF n A_inv E f x)

/-- The vector `|A⁻¹||r|` used in practical residual bounds. -/
noncomputable def ch7ResidualImage (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (y b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, |A_inv i j| * |residualVec n A y b j|

/-- Nonnegativity of the Chapter 7 amplified right-hand side. -/
lemma ch7AmplifiedRhsEF_nonneg (n : ℕ)
    (A_inv : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ)
    (f x : Fin n → ℝ)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i) :
    ∀ i, 0 ≤ ch7AmplifiedRhsEF n A_inv E f x i := by
  intro i
  unfold ch7AmplifiedRhsEF
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (abs_nonneg _) (add_nonneg
      (Finset.sum_nonneg fun k _ => mul_nonneg (hE j k) (abs_nonneg _))
      (hf j))

/-- Nonnegativity of `‖ |A⁻¹|(E|x| + f) ‖∞`. -/
lemma ch7ForwardBoundEF_nonneg (n : ℕ) (hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ)
    (f x : Fin n → ℝ)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i) :
    0 ≤ ch7ForwardBoundEF n hn A_inv E f x := by
  unfold ch7ForwardBoundEF
  exact le_trans
    (ch7AmplifiedRhsEF_nonneg n A_inv E f x hE hf ⟨0, hn⟩)
    (Finset.le_sup' (ch7AmplifiedRhsEF n A_inv E f x)
      (Finset.mem_univ ⟨0, hn⟩))

-- ============================================================
-- Problem 7.1: local Neumann contraction infrastructure
-- ============================================================

/-- The nonnegative contraction matrix `ε |A⁻¹| E` from Problem 7.1. -/
noncomputable def ch7Problem71ContractionMatrix (n : ℕ) (ε : ℝ)
    (A_inv : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i k => ε * ∑ j : Fin n, |A_inv i j| * E j k

/-- Nonnegativity of the Problem 7.1 contraction matrix. -/
lemma ch7Problem71ContractionMatrix_nonneg (n : ℕ) {ε : ℝ}
    (A_inv : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ)
    (hε : 0 ≤ ε) (hE : ∀ i j, 0 ≤ E i j) :
    ∀ i k, 0 ≤ ch7Problem71ContractionMatrix n ε A_inv E i k := by
  intro i k
  unfold ch7Problem71ContractionMatrix
  exact mul_nonneg hε
    (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hE j k))

/-- A nonnegative left inverse for `I-M`, the matrix object denoted
`(I-M)⁻¹` in Problem 7.1. -/
def ch7NonnegativeResolvent (n : ℕ)
    (M R : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ R i j) ∧ IsLeftInverse n (matSub_id n M) R

/-- Exact entrywise resolvent bound.  If `R = (I-M)⁻¹` is available as a
nonnegative left-inverse certificate and `w ≤ v + M w`, then `w ≤ R v`. -/
theorem problem7_1_resolvent_componentwise_inequality_bound (n : ℕ)
    (M R : Fin n → Fin n → ℝ) (v w : Fin n → ℝ)
    (hR : ch7NonnegativeResolvent n M R)
    (hineq : ∀ i, w i ≤ v i + ∑ j : Fin n, M i j * w j) :
    ∀ i, w i ≤ ∑ j : Fin n, R i j * v j := by
  rcases hR with ⟨hR_nonneg, hR_left⟩
  have hsub_le : ∀ i, rectMatMulVec (matSub_id n M) w i ≤ v i := by
    intro i
    unfold rectMatMulVec matSub_id idMatrix
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    have hid : (∑ j : Fin n, (if i = j then (1 : ℝ) else 0) * w j) = w i := by
      simp
    rw [hid]
    linarith [hineq i]
  have hleft := rectMatMulVec_left_inverse_of_IsLeftInverse hR_left w
  intro i
  calc
    w i = rectMatMulVec R (rectMatMulVec (matSub_id n M) w) i := by
      rw [hleft]
    _ = ∑ j : Fin n, R i j * rectMatMulVec (matSub_id n M) w j := rfl
    _ ≤ ∑ j : Fin n, R i j * v j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hsub_le j) (hR_nonneg i j)

/-- A max-norm Neumann consequence for nonnegative componentwise
inequalities `w ≤ v + M w`.  This is the local infrastructure behind
Problem 7.1's `(I-M)⁻¹` bound when only a scalar row-sum contraction is
needed. -/
theorem problem7_1_neumann_componentwise_inequality_bound (n : ℕ) (hn : 0 < n)
    (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (c : ℝ) (_hc_nn : 0 ≤ c) (hc_lt : c < 1)
    (hbound : infNormBound n M c)
    (v w : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i)
    (hineq : ∀ i, w i ≤ v i + ∑ j : Fin n, M i j * w j) :
    ∀ i, w i ≤ (1 / (1 - c)) * ∑ j : Fin n, v j := by
  have hc1 : (0 : ℝ) < 1 - c := by linarith
  let hne : Finset.univ.Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  let W := Finset.sup' Finset.univ hne (fun i : Fin n => w i)
  let V := ∑ j : Fin n, v j
  have hW_ge : ∀ i : Fin n, w i ≤ W :=
    fun i => Finset.le_sup' (fun i : Fin n => w i) (Finset.mem_univ i)
  have hW_nn : (0 : ℝ) ≤ W := le_trans (hw ⟨0, hn⟩) (hW_ge ⟨0, hn⟩)
  have hW_bound : ∀ i : Fin n, w i ≤ v i + c * W := by
    intro i
    have h2 : ∑ j : Fin n, M i j * w j ≤ c * W := by
      have hMW : ∑ j : Fin n, M i j * w j ≤ ∑ j : Fin n, M i j * W :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hW_ge j) (hM i j)
      have hMW_eq : ∑ j : Fin n, M i j * W = W * ∑ j : Fin n, M i j := by
        simp_rw [mul_comm (M i _) W]
        exact (Finset.mul_sum Finset.univ (fun j => M i j) W).symm
      have hrow : ∑ j : Fin n, M i j ≤ c := by
        calc
          ∑ j : Fin n, M i j = ∑ j : Fin n, |M i j| := by
            congr 1
            ext j
            rw [abs_of_nonneg (hM i j)]
          _ ≤ c := row_sum_le_of_infNormBound hbound i
      calc
        ∑ j : Fin n, M i j * w j ≤ ∑ j : Fin n, M i j * W := hMW
        _ = W * ∑ j : Fin n, M i j := hMW_eq
        _ ≤ W * c := mul_le_mul_of_nonneg_left hrow hW_nn
        _ = c * W := mul_comm W c
    linarith [hineq i]
  have hV_max_le : ∀ i : Fin n, v i ≤ V :=
    fun i => Finset.single_le_sum (fun j _ => hv j) (Finset.mem_univ i)
  have hW_le_V : W ≤ V + c * W := by
    apply Finset.sup'_le
    intro i _
    calc
      w i ≤ v i + c * W := hW_bound i
      _ ≤ V + c * W := by linarith [hV_max_le i]
  have hW_final : W ≤ (1 / (1 - c)) * V := by
    have h1c_W : (1 - c) * W ≤ V := by nlinarith
    have hinv_nn : (0 : ℝ) ≤ 1 / (1 - c) := by positivity
    calc
      W = 1 / (1 - c) * ((1 - c) * W) := by
        field_simp [ne_of_gt hc1]
      _ ≤ (1 / (1 - c)) * V :=
        mul_le_mul_of_nonneg_left h1c_W hinv_nn
  intro i
  exact le_trans (hW_ge i) hW_final

/-- Problem 7.1 contraction inequality obtained from Theorem 7.4 by replacing
`|y|` with `|x| + |x-y|`. -/
theorem problem7_1_componentwise_contraction_ineq (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * E i j)
    (hΔb : ∀ i, |Δb i| ≤ ε * f i)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) :
    ∀ i, |x i - y i| ≤
      ε * ch7AmplifiedRhsEF n A_inv E f x i +
        ∑ k : Fin n, ch7Problem71ContractionMatrix n ε A_inv E i k *
          |x k - y k| := by
  have hCFE := componentwise_forward_error n A A_inv x y b ΔA Δb E f
    ε hε hΔA hΔb hE hf hInv hAx hPerturbed
  have hy_abs : ∀ k : Fin n, |y k| ≤ |x k| + |x k - y k| := by
    intro k
    calc
      |y k| = |x k + (y k - x k)| := by
        congr 1
        ring
      _ ≤ |x k| + |y k - x k| := abs_add_le _ _
      _ = |x k| + |x k - y k| := by rw [abs_sub_comm]
  intro i
  have hrow_bound :
      ∑ j : Fin n, |A_inv i j| *
          (∑ k : Fin n, E j k * |y k| + f j) ≤
        ∑ j : Fin n, |A_inv i j| *
          ((∑ k : Fin n, E j k * |x k| + f j) +
            ∑ k : Fin n, E j k * |x k - y k|) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hY :
        ∑ k : Fin n, E j k * |y k| ≤
          ∑ k : Fin n, E j k * (|x k| + |x k - y k|) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (hy_abs k) (hE j k)
    calc
      ∑ k : Fin n, E j k * |y k| + f j
          ≤ ∑ k : Fin n, E j k * (|x k| + |x k - y k|) + f j :=
            add_le_add hY (le_refl (f j))
      _ = (∑ k : Fin n, E j k * |x k| + f j) +
            ∑ k : Fin n, E j k * |x k - y k| := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          ring
  have hsplit :
      ε * (∑ j : Fin n, |A_inv i j| *
          ((∑ k : Fin n, E j k * |x k| + f j) +
            ∑ k : Fin n, E j k * |x k - y k|)) =
        ε * ch7AmplifiedRhsEF n A_inv E f x i +
          ∑ k : Fin n, ch7Problem71ContractionMatrix n ε A_inv E i k *
            |x k - y k| := by
    unfold ch7AmplifiedRhsEF ch7Problem71ContractionMatrix
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, mul_add]
    congr 1
    calc
      ε * (∑ j : Fin n, |A_inv i j| *
          ∑ k : Fin n, E j k * |x k - y k|)
          = ε * (∑ k : Fin n, ∑ j : Fin n,
              |A_inv i j| * (E j k * |x k - y k|)) := by
            congr 1
            calc
              ∑ j : Fin n, |A_inv i j| *
                  ∑ k : Fin n, E j k * |x k - y k|
                  = ∑ j : Fin n, ∑ k : Fin n,
                      |A_inv i j| * (E j k * |x k - y k|) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [Finset.mul_sum]
              _ = ∑ k : Fin n, ∑ j : Fin n,
                    |A_inv i j| * (E j k * |x k - y k|) := by
                    rw [Finset.sum_comm]
      _ = ∑ k : Fin n,
            ε * (∑ j : Fin n, |A_inv i j| * (E j k * |x k - y k|)) := by
            rw [Finset.mul_sum]
      _ = ∑ k : Fin n, (ε * ∑ j : Fin n, |A_inv i j| * E j k) *
            |x k - y k| := by
            apply Finset.sum_congr rfl
            intro k _
            calc
              ε * (∑ j : Fin n, |A_inv i j| * (E j k * |x k - y k|))
                  = ε * (∑ j : Fin n, (|A_inv i j| * E j k) *
                      |x k - y k|) := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
              _ = ε * ((∑ j : Fin n, |A_inv i j| * E j k) *
                    |x k - y k|) := by
                    rw [← Finset.sum_mul]
              _ = (ε * ∑ j : Fin n, |A_inv i j| * E j k) *
                    |x k - y k| := by
                    ring
  calc
    |x i - y i|
        ≤ ε * ∑ j : Fin n, |A_inv i j| *
          (∑ k : Fin n, E j k * |y k| + f j) := hCFE i
    _ ≤ ε * (∑ j : Fin n, |A_inv i j| *
          ((∑ k : Fin n, E j k * |x k| + f j) +
            ∑ k : Fin n, E j k * |x k - y k|)) :=
          mul_le_mul_of_nonneg_left hrow_bound hε
    _ = ε * ch7AmplifiedRhsEF n A_inv E f x i +
        ∑ k : Fin n, ch7Problem71ContractionMatrix n ε A_inv E i k *
          |x k - y k| := hsplit

/-- Problem 7.1 scalar Neumann consequence of the componentwise contraction:
if `ε |A⁻¹|E` is nonnegative and has infinity norm at most `c < 1`, then
the componentwise forward error is controlled by the amplified right-hand side
with the scalar Neumann factor `1/(1-c)`. -/
theorem problem7_1_componentwise_neumann_scalar_bound (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * E i j)
    (hΔb : ∀ i, |Δb i| ≤ ε * f i)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_lt : c < 1)
    (hbound : infNormBound n (ch7Problem71ContractionMatrix n ε A_inv E) c) :
    ∀ i, |x i - y i| ≤
      (1 / (1 - c)) *
        ∑ j : Fin n, ε * ch7AmplifiedRhsEF n A_inv E f x j := by
  let M := ch7Problem71ContractionMatrix n ε A_inv E
  let v : Fin n → ℝ := fun j => ε * ch7AmplifiedRhsEF n A_inv E f x j
  let w : Fin n → ℝ := fun j => |x j - y j|
  have hineq_raw :=
    problem7_1_componentwise_contraction_ineq n A A_inv x y b ΔA Δb E f
      ε hε hΔA hΔb hE hf hInv hAx hPerturbed
  have hineq : ∀ i, w i ≤ v i + ∑ j : Fin n, M i j * w j := by
    intro i
    simpa [M, v, w] using hineq_raw i
  have hM : ∀ i j, 0 ≤ M i j := by
    intro i j
    exact ch7Problem71ContractionMatrix_nonneg n A_inv E hε hE i j
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    exact mul_nonneg hε (ch7AmplifiedRhsEF_nonneg n A_inv E f x hE hf i)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    exact abs_nonneg _
  have hboundM : infNormBound n M c := by
    simpa [M] using hbound
  have h :=
    problem7_1_neumann_componentwise_inequality_bound n hn M hM c hc_nn hc_lt
      hboundM v w hv hw hineq
  intro i
  simpa [v, w] using h i

/-- If `M ≥ 0` and `‖M‖∞ ≤ c < 1`, then every solution of
`(I-M)w = v` with `v ≥ 0` is nonnegative. -/
theorem ch7_nonnegative_solution_of_nonnegative_contraction (n : ℕ) (hn : 0 < n)
    (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (c : ℝ) (hc_nn : 0 ≤ c) (hc_lt : c < 1)
    (hbound : infNormBound n M c)
    (v w : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hsolve : ∀ i, w i - ∑ j : Fin n, M i j * w j = v i) :
    ∀ i, 0 ≤ w i := by
  let p : Fin n → ℝ := fun i => max 0 (-w i)
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    exact le_max_left 0 (-w i)
  have hneg_le_p : ∀ i, -w i ≤ p i := by
    intro i
    exact le_max_right 0 (-w i)
  have hpineq : ∀ i, p i ≤ (0 : ℝ) + ∑ j : Fin n, M i j * p j := by
    intro i
    by_cases hwi : 0 ≤ w i
    · have hpi : p i = 0 := by
        dsimp [p]
        exact max_eq_left (neg_nonpos.mpr hwi)
      rw [hpi, zero_add]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hM i j) (hp_nonneg j)
    · have hwi_lt : w i < 0 := lt_of_not_ge hwi
      have hpi : p i = -w i := by
        dsimp [p]
        exact max_eq_right (le_of_lt (neg_pos.mpr hwi_lt))
      rw [hpi, zero_add]
      have hw_eq : w i = v i + ∑ j : Fin n, M i j * w j := by
        linarith [hsolve i]
      calc
        -w i = -v i - ∑ j : Fin n, M i j * w j := by
          rw [hw_eq]
          ring
        _ ≤ -(∑ j : Fin n, M i j * w j) := by
          linarith [hv i]
        _ = ∑ j : Fin n, M i j * (-w j) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ ≤ ∑ j : Fin n, M i j * p j := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hneg_le_p j) (hM i j)
  have hp_bound :=
    problem7_1_neumann_componentwise_inequality_bound n hn M hM c hc_nn hc_lt
      hbound (fun _ : Fin n => (0 : ℝ)) p
      (fun _ => le_rfl) hp_nonneg hpineq
  intro i
  have hp_zero : p i = 0 := by
    apply le_antisymm
    · simpa using hp_bound i
    · exact hp_nonneg i
  have hneg : -w i ≤ 0 := by
    exact le_trans (hneg_le_p i) (by rw [hp_zero])
  linarith

/-- If `M ≥ 0` and `‖M‖∞ ≤ c < 1`, then `I-M` is nonsingular. -/
theorem ch7_matSub_id_det_ne_zero_of_nonnegative_contraction (n : ℕ) (hn : 0 < n)
    (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (c : ℝ) (hc_nn : 0 ≤ c) (hc_lt : c < 1)
    (hbound : infNormBound n M c) :
    Matrix.det (matSub_id n M : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  intro hdet
  have hex :
      ∃ v : Fin n → ℝ, v ≠ 0 ∧
        Matrix.mulVec (matSub_id n M : Matrix (Fin n) (Fin n) ℝ) v = 0 :=
    (Matrix.exists_mulVec_eq_zero_iff
      (M := (matSub_id n M : Matrix (Fin n) (Fin n) ℝ))).2 hdet
  rcases hex with ⟨w, hw_ne, hmul_zero⟩
  have hsolve : ∀ i, w i - ∑ j : Fin n, M i j * w j = (0 : ℝ) := by
    intro i
    have hi := congrFun hmul_zero i
    change (∑ j : Fin n, matSub_id n M i j * w j) = 0 at hi
    unfold matSub_id idMatrix at hi
    simp_rw [sub_mul, Finset.sum_sub_distrib] at hi
    have hid : (∑ j : Fin n, (if i = j then (1 : ℝ) else 0) * w j) = w i := by
      simp
    rw [hid] at hi
    exact hi
  have hzero_bound :=
    neumann_exact_scalar_resolution n hn M hM c hc_nn hc_lt hbound
      (fun _ : Fin n => (0 : ℝ)) w hsolve
  have hw_zero : w = 0 := by
    ext i
    have habs_nonpos : |w i| ≤ 0 := by
      simpa using hzero_bound i
    exact abs_eq_zero.mp (le_antisymm habs_nonpos (abs_nonneg _))
  exact hw_ne hw_zero

/-- The actual nonsingular inverse of `I-M` is a nonnegative resolvent under
the local Neumann contraction hypotheses. -/
theorem ch7NonnegativeResolvent_nonsingInv_of_infNormBound (n : ℕ) (hn : 0 < n)
    (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (c : ℝ) (hc_nn : 0 ≤ c) (hc_lt : c < 1)
    (hbound : infNormBound n M c) :
    ch7NonnegativeResolvent n M (nonsingInv n (matSub_id n M)) := by
  have hdet :=
    ch7_matSub_id_det_ne_zero_of_nonnegative_contraction n hn M hM c
      hc_nn hc_lt hbound
  have hInv : IsInverse n (matSub_id n M) (nonsingInv n (matSub_id n M)) :=
    isInverse_nonsingInv_of_det_ne_zero n (matSub_id n M) hdet
  refine ⟨?_, hInv.1⟩
  intro i j
  let w : Fin n → ℝ := fun k => nonsingInv n (matSub_id n M) k j
  let e : Fin n → ℝ := fun k => if k = j then (1 : ℝ) else 0
  have he_nonneg : ∀ k, 0 ≤ e k := by
    intro k
    dsimp [e]
    split <;> norm_num
  have hsolve : ∀ k, w k - ∑ l : Fin n, M k l * w l = e k := by
    intro k
    have hk := hInv.2 k j
    dsimp [w, e]
    have hid :
        (∑ l : Fin n, (if k = l then (1 : ℝ) else 0) *
            nonsingInv n (matSub_id n M) l j) =
          nonsingInv n (matSub_id n M) k j := by
      simp
    calc
      nonsingInv n (matSub_id n M) k j -
          ∑ l : Fin n, M k l * nonsingInv n (matSub_id n M) l j
          =
        (∑ l : Fin n, (if k = l then (1 : ℝ) else 0) *
            nonsingInv n (matSub_id n M) l j) -
          ∑ l : Fin n, M k l * nonsingInv n (matSub_id n M) l j := by
            rw [hid]
      _ = ∑ l : Fin n, ((if k = l then (1 : ℝ) else 0) - M k l) *
            nonsingInv n (matSub_id n M) l j := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro l _
            ring
      _ = ∑ l : Fin n, matSub_id n M k l *
            nonsingInv n (matSub_id n M) l j := by
            apply Finset.sum_congr rfl
            intro l _
            unfold matSub_id idMatrix
            ring
      _ = if k = j then (1 : ℝ) else 0 := by
            simpa using hk
  have hw_nonneg :=
    ch7_nonnegative_solution_of_nonnegative_contraction n hn M hM c hc_nn hc_lt
      hbound e w he_nonneg hsolve
  exact hw_nonneg i

/-- Problem 7.1 exact matrix-valued resolvent form.  The inverse displayed in
the source is represented by the nonnegative left-inverse certificate `R` for
`I - ε |A⁻¹|E`. -/
theorem problem7_1_componentwise_resolvent_bound (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * E i j)
    (hΔb : ∀ i, |Δb i| ≤ ε * f i)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)
    (R : Fin n → Fin n → ℝ)
    (hR : ch7NonnegativeResolvent n
      (ch7Problem71ContractionMatrix n ε A_inv E) R) :
    ∀ i, |x i - y i| ≤
      ∑ j : Fin n, R i j * (ε * ch7AmplifiedRhsEF n A_inv E f x j) := by
  let M := ch7Problem71ContractionMatrix n ε A_inv E
  let v : Fin n → ℝ := fun j => ε * ch7AmplifiedRhsEF n A_inv E f x j
  let w : Fin n → ℝ := fun j => |x j - y j|
  have hineq_raw :=
    problem7_1_componentwise_contraction_ineq n A A_inv x y b ΔA Δb E f
      ε hε hΔA hΔb hE hf hInv hAx hPerturbed
  have hineq : ∀ i, w i ≤ v i + ∑ j : Fin n, M i j * w j := by
    intro i
    simpa [M, v, w] using hineq_raw i
  have h := problem7_1_resolvent_componentwise_inequality_bound n M R v w hR hineq
  intro i
  simpa [M, v, w] using h i

/-- Problem 7.1 exact matrix-valued inverse form using the repository's
`nonsingInv` for `(I - ε |A⁻¹|E)⁻¹`. -/
theorem problem7_1_componentwise_nonsingInv_resolvent_bound (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * E i j)
    (hΔb : ∀ i, |Δb i| ≤ ε * f i)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_lt : c < 1)
    (hbound : infNormBound n (ch7Problem71ContractionMatrix n ε A_inv E) c) :
    ∀ i, |x i - y i| ≤
      ∑ j : Fin n,
        nonsingInv n (matSub_id n (ch7Problem71ContractionMatrix n ε A_inv E)) i j *
          (ε * ch7AmplifiedRhsEF n A_inv E f x j) := by
  let M := ch7Problem71ContractionMatrix n ε A_inv E
  have hM : ∀ i j, 0 ≤ M i j := by
    intro i j
    exact ch7Problem71ContractionMatrix_nonneg n A_inv E hε hE i j
  have hR : ch7NonnegativeResolvent n M (nonsingInv n (matSub_id n M)) :=
    ch7NonnegativeResolvent_nonsingInv_of_infNormBound n hn M hM c hc_nn hc_lt
      (by simpa [M] using hbound)
  simpa [M] using
    problem7_1_componentwise_resolvent_bound n A A_inv x y b ΔA Δb E f ε hε
      hΔA hΔb hE hf hInv hAx hPerturbed
      (nonsingInv n (matSub_id n M)) hR

-- ============================================================
-- Equations (7.11), (7.13), and (7.14): condition numbers
-- ============================================================

/-- Equation (7.11), infinity-norm specialization:
    `cond_{E,f}(A,x) = ‖|A⁻¹|(E|x|+f)‖∞ / ‖x‖∞`. -/
noncomputable def ch7CondEFAtSolutionInf (n : ℕ) (hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ)
    (f x : Fin n → ℝ) : ℝ :=
  ch7ForwardBoundEF n hn A_inv E f x / infNormVec x

/-- Equation (7.13), infinity-norm Skeel condition number at a solution:
    `cond(A,x) = ‖|A⁻¹||A||x|‖∞ / ‖x‖∞`. -/
noncomputable def ch7SkeelCondAtSolutionInf (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ch7CondEFAtSolutionInf n hn A_inv (fun i j => |A i j|) (fun _ => 0) x

/-- The infinity norm of the all-ones vector is one for `n > 0`. -/
lemma infNormVec_const_one (n : ℕ) (hn : 0 < n) :
    infNormVec (fun _ : Fin n => (1 : ℝ)) = 1 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      simp
    · norm_num
  · have h := abs_le_infNormVec (fun _ : Fin n => (1 : ℝ)) ⟨0, hn⟩
    simpa using h

/-- Equation (7.14): the global Skeel condition is the solution-dependent
    Skeel condition evaluated at `e`. -/
theorem ch7SkeelCondAtOnes_eq_condSkeel (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) :
    ch7SkeelCondAtSolutionInf n hn A A_inv (fun _ : Fin n => (1 : ℝ)) =
      condSkeel n hn A A_inv := by
  unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf ch7ForwardBoundEF
    ch7AmplifiedRhsEF condSkeel
  rw [infNormVec_const_one n hn]
  simp

-- ============================================================
-- Theorem 7.4, relative infinity-norm form of (7.10)
-- ============================================================

/-- Relative infinity-norm form of Higham Theorem 7.4/(7.10).

    This is the `∞`-norm specialization of the source statement, obtained from
    the componentwise exact theorem in `PerturbationTheory.lean` by taking a
    vector infinity norm and dividing by `‖x‖∞`. -/
theorem componentwise_forward_error_exact_relative_infNorm (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * E i j)
    (hΔb : ∀ i, |Δb i| ≤ ε * f i)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)
    (M : ℝ) (hM : ∀ i, ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, E j k) ≤ M)
    (hεM : ε * M < 1) (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - y i) / infNormVec x ≤
      ε / (1 - ε * M) *
        (ch7ForwardBoundEF n hn A_inv E f x / infNormVec x) := by
  let C := ch7ForwardBoundEF n hn A_inv E f x
  have hcomp := componentwise_forward_error_exact n hn A A_inv x y b ΔA Δb E f
    ε hε hΔA hΔb hE hf hInv hAx hPerturbed M hM hεM
  have hC_nonneg : 0 ≤ C := ch7ForwardBoundEF_nonneg n hn A_inv E f x hE hf
  have hden_pos : 0 < 1 - ε * M := by linarith
  have hcoef_nonneg : 0 ≤ ε / (1 - ε * M) :=
    div_nonneg hε (le_of_lt hden_pos)
  have hB_nonneg : 0 ≤ ε / (1 - ε * M) * C :=
    mul_nonneg hcoef_nonneg hC_nonneg
  have hnorm :
      infNormVec (fun i => x i - y i) ≤ ε / (1 - ε * M) * C := by
    apply infNormVec_le_of_abs_le
    · intro i
      simpa [C, ch7ForwardBoundEF, ch7AmplifiedRhsEF] using hcomp i
    · exact hB_nonneg
  calc
    infNormVec (fun i => x i - y i) / infNormVec x
        ≤ (ε / (1 - ε * M) * C) / infNormVec x :=
          div_le_div_of_nonneg_right hnorm (le_of_lt hx)
    _ = ε / (1 - ε * M) * (C / infNormVec x) := by ring

/-- Standard `E = |A|`, `f = |b|` specialization of
    `componentwise_forward_error_exact_relative_infNorm`. -/
theorem normwise_forward_error_exact_relative_infNorm (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hΔb : ∀ i, |Δb i| ≤ ε * |b i|)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)
    (M : ℝ) (hM : ∀ i, ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|) ≤ M)
    (hεM : ε * M < 1) (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - y i) / infNormVec x ≤
      ε / (1 - ε * M) *
        (ch7ForwardBoundEF n hn A_inv (fun i j => |A i j|) (fun i => |b i|) x /
          infNormVec x) :=
  componentwise_forward_error_exact_relative_infNorm n hn A A_inv x y b ΔA Δb
    (fun i j => |A i j|) (fun i => |b i|) ε hε hΔA hΔb
    (fun _ _ => abs_nonneg _) (fun _ => abs_nonneg _) hInv hAx hPerturbed
    M hM hεM hx

-- ============================================================
-- Problem 7.2: residual/error sandwich in the infinity norm
-- ============================================================

/-- Problem 7.2, left inequality before scaling:
    `‖r‖∞ ≤ ‖A‖∞ ‖x-y‖∞` when `Ax=b` and `r=b-Ay`. -/
theorem problem7_2_infNorm_residual_lower (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i) :
    infNormVec (residualVec n A y b) ≤
      infNorm A * infNormVec (fun i => x i - y i) := by
  have hres :
      residualVec n A y b = matMulVec n A (fun i => x i - y i) := by
    ext i
    unfold residualVec matMulVec
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    linarith [hAx i]
  simpa [hres] using
    (infNormVec_matMulVec_le hn A (fun i => x i - y i))

/-- Problem 7.2, right inequality before scaling:
    `‖x-y‖∞ ≤ ‖A⁻¹‖∞ ‖r‖∞` when `A_inv A = I`. -/
theorem problem7_2_infNorm_residual_upper (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i) :
    infNormVec (fun i => x i - y i) ≤
      infNorm A_inv * infNormVec (residualVec n A y b) := by
  let r := residualVec n A y b
  have hFwd := forward_error_from_residual n A A_inv x y b hInv hAx
  have hcomponent :
      infNormVec (fun i => x i - y i) ≤
        infNormVec (matMulVec n (absMatrix n A_inv) (absVec n r)) := by
    apply infNormVec_le_of_abs_le
    · intro i
      have hentry_nonneg :
          0 ≤ matMulVec n (absMatrix n A_inv) (absVec n r) i := by
        unfold matMulVec absMatrix absVec
        exact Finset.sum_nonneg fun j _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _)
      calc
        |x i - y i| ≤ matMulVec n (absMatrix n A_inv) (absVec n r) i := by
          simpa [r, matMulVec, absMatrix, absVec] using hFwd i
        _ = |matMulVec n (absMatrix n A_inv) (absVec n r) i| :=
          (abs_of_nonneg hentry_nonneg).symm
        _ ≤ infNormVec (matMulVec n (absMatrix n A_inv) (absVec n r)) :=
          abs_le_infNormVec _ i
    · exact infNormVec_nonneg _
  calc
    infNormVec (fun i => x i - y i)
        ≤ infNormVec (matMulVec n (absMatrix n A_inv) (absVec n r)) := hcomponent
    _ ≤ infNorm (absMatrix n A_inv) * infNormVec (absVec n r) :=
        infNormVec_matMulVec_le hn (absMatrix n A_inv) (absVec n r)
    _ = infNorm A_inv * infNormVec (residualVec n A y b) := by
        rw [infNorm_absMatrix hn A_inv, infNormVec_absVec hn r]

/-- Problem 7.2, source-shaped lower bound in the infinity norm. -/
theorem problem7_2_infNorm_scaled_lower (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hA : 0 < infNorm A) (hx : 0 < infNormVec x) :
    infNormVec (residualVec n A y b) / (infNorm A * infNormVec x) ≤
      infNormVec (fun i => x i - y i) / infNormVec x := by
  have hraw := problem7_2_infNorm_residual_lower n hn A x y b hAx
  have hden_nonneg : 0 ≤ infNorm A * infNormVec x :=
    mul_nonneg (le_of_lt hA) (le_of_lt hx)
  have hA_ne : infNorm A ≠ 0 := ne_of_gt hA
  have hx_ne : infNormVec x ≠ 0 := ne_of_gt hx
  calc
    infNormVec (residualVec n A y b) / (infNorm A * infNormVec x)
        ≤ (infNorm A * infNormVec (fun i => x i - y i)) /
          (infNorm A * infNormVec x) :=
          div_le_div_of_nonneg_right hraw hden_nonneg
    _ = infNormVec (fun i => x i - y i) / infNormVec x := by
        field_simp [hA_ne, hx_ne]

/-- Problem 7.2, source-shaped upper bound in the infinity norm. -/
theorem problem7_2_infNorm_scaled_upper (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hA : 0 < infNorm A) (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - y i) / infNormVec x ≤
      kappaInf n hn A A_inv *
        (infNormVec (residualVec n A y b) / (infNorm A * infNormVec x)) := by
  have hraw := problem7_2_infNorm_residual_upper n hn A A_inv x y b hInv hAx
  have hA_ne : infNorm A ≠ 0 := ne_of_gt hA
  have hx_ne : infNormVec x ≠ 0 := ne_of_gt hx
  calc
    infNormVec (fun i => x i - y i) / infNormVec x
        ≤ (infNorm A_inv * infNormVec (residualVec n A y b)) /
          infNormVec x :=
          div_le_div_of_nonneg_right hraw (le_of_lt hx)
    _ = (infNorm A * infNorm A_inv) *
        (infNormVec (residualVec n A y b) / (infNorm A * infNormVec x)) := by
        field_simp [hA_ne, hx_ne]
    _ = kappaInf n hn A A_inv *
        (infNormVec (residualVec n A y b) / (infNorm A * infNormVec x)) := by
        rw [kappaInf_eq_infNorm_mul_infNorm n hn A A_inv]

-- ============================================================
-- Problem 7.7: dropping the right-hand-side perturbation budget
-- ============================================================

/-- Problem 7.7, componentwise core.

    If the residual is bounded with the standard componentwise denominator
    `|A||y| + |b|` and `ε < 1`, then it is bounded with no right-hand-side
    budget at the enlarged factor `2ε/(1-ε)`. This is the local algebraic
    step in Appendix A's proof of
    `ω_{|A|,0}(y) ≤ 2ω_{|A|,|b|}(y)/(1-ω_{|A|,|b|}(y))`. -/
theorem problem7_7_componentwise_abs_rhs_to_zero_rhs_residual_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hεlt : ε < 1)
    (hres : ∀ i, |residualVec n A y b i| ≤
      ε * (∑ j : Fin n, |A i j| * |y j| + |b i|)) :
    ∀ i, |residualVec n A y b i| ≤
      (2 * ε / (1 - ε)) *
        (∑ j : Fin n, |A i j| * |y j| + (0 : ℝ)) := by
  intro i
  let row : ℝ := ∑ j : Fin n, |A i j| * |y j|
  have hrow_nonneg : 0 ≤ row := by
    unfold row
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hden_pos : 0 < 1 - ε := by linarith
  have hres_i :
      |residualVec n A y b i| ≤ ε * (row + |b i|) := by
    simpa [row] using hres i
  have hAy : |∑ j : Fin n, A i j * y j| ≤ row := by
    unfold row
    calc
      |∑ j : Fin n, A i j * y j|
          ≤ ∑ j : Fin n, |A i j * y j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |A i j| * |y j| := by
          apply Finset.sum_congr rfl
          intro j _
          exact abs_mul (A i j) (y j)
  have hb_step : |b i| ≤ row + ε * (row + |b i|) := by
    have hb_repr :
        b i = residualVec n A y b i + ∑ j : Fin n, A i j * y j := by
      unfold residualVec
      ring
    calc
      |b i|
          = |residualVec n A y b i + ∑ j : Fin n, A i j * y j| := by
            rw [hb_repr]
      _ ≤ |residualVec n A y b i| + |∑ j : Fin n, A i j * y j| :=
          abs_add_le _ _
      _ ≤ ε * (row + |b i|) + row :=
          add_le_add hres_i hAy
      _ = row + ε * (row + |b i|) := by ring
  have hmove : (1 - ε) * |b i| ≤ (1 + ε) * row := by
    linarith
  have hb_le : |b i| ≤ ((1 + ε) / (1 - ε)) * row := by
    calc
      |b i| ≤ ((1 + ε) * row) / (1 - ε) :=
        (le_div_iff₀ hden_pos).mpr (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmove)
      _ = ((1 + ε) / (1 - ε)) * row := by ring
  have hres2 :
      |residualVec n A y b i| ≤
        ε * (row + ((1 + ε) / (1 - ε)) * row) := by
    calc
      |residualVec n A y b i| ≤ ε * (row + |b i|) := hres_i
      _ ≤ ε * (row + ((1 + ε) / (1 - ε)) * row) := by
          exact mul_le_mul_of_nonneg_left (add_le_add (le_refl row) hb_le) hε
  calc
    |residualVec n A y b i|
        ≤ ε * (row + ((1 + ε) / (1 - ε)) * row) := hres2
    _ = (2 * ε / (1 - ε)) *
        (∑ j : Fin n, |A i j| * |y j| + (0 : ℝ)) := by
        rw [show row = ∑ j : Fin n, |A i j| * |y j| by rfl]
        field_simp [ne_of_gt hden_pos]
        ring

/-- Problem 7.7, componentwise feasibility form.

    A feasible componentwise backward error with right-hand-side budget `|b|`
    implies a feasible componentwise backward error with right-hand-side budget
    zero at factor `2ε/(1-ε)`, for `0 ≤ ε < 1`. -/
theorem problem7_7_componentwise_zero_rhs_feasible_of_abs_rhs_feasible (n : ℕ)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hεlt : ε < 1)
    (hfeas : ∃ (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
      (∀ i j, |ΔA i j| ≤ ε * |A i j|) ∧
      (∀ i, |Δb i| ≤ ε * |b i|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)) :
    ∃ (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
      (∀ i j, |ΔA i j| ≤ (2 * ε / (1 - ε)) * |A i j|) ∧
      (∀ i, |Δb i| ≤ (2 * ε / (1 - ε)) * (0 : ℝ)) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) := by
  have hres :
      ∀ i, |residualVec n A y b i| ≤
        ε * (∑ j : Fin n, |A i j| * |y j| + |b i|) :=
    (oettli_prager n A y b (fun i j => |A i j|) (fun i => |b i|)
      ε hε (fun _ _ => abs_nonneg _) (fun _ => abs_nonneg _)).2 hfeas
  have hzero :=
    problem7_7_componentwise_abs_rhs_to_zero_rhs_residual_bound
      n A y b ε hε hεlt hres
  have hcoef : 0 ≤ 2 * ε / (1 - ε) := by
    exact div_nonneg (mul_nonneg (by norm_num) hε) (by linarith)
  exact
    (oettli_prager n A y b (fun i j => |A i j|) (fun _ => (0 : ℝ))
      (2 * ε / (1 - ε)) hcoef
      (fun _ _ => abs_nonneg _) (fun _ => le_rfl)).1 hzero

/-- Problem 7.7, normwise infinity-norm core.

    This is the Rigal-Gaches analogue of
    `problem7_7_componentwise_abs_rhs_to_zero_rhs_residual_bound`: a residual
    bound with denominator `‖A‖∞ ‖y‖∞ + ‖b‖∞` implies one with denominator
    `‖A‖∞ ‖y‖∞` at factor `2ε/(1-ε)`. -/
theorem problem7_7_normwise_inf_residual_bound (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hεlt : ε < 1)
    (hres : ∀ i, |residualVec n A y b i| ≤
      ε * (infNorm A *
        Finset.sup' Finset.univ
          (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |y j|) +
        infNormVec b)) :
    ∀ i, |residualVec n A y b i| ≤
      (2 * ε / (1 - ε)) *
        (infNorm A *
          Finset.sup' Finset.univ
            (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |y j|) +
          (0 : ℝ)) := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  let yNorm : ℝ := Finset.sup' Finset.univ hne (fun j : Fin n => |y j|)
  let C : ℝ := infNorm A * yNorm
  let β : ℝ := infNormVec b
  have hy_le : ∀ j : Fin n, |y j| ≤ yNorm := by
    intro j
    exact Finset.le_sup' (fun j : Fin n => |y j|) (Finset.mem_univ j)
  have hyNorm_nonneg : 0 ≤ yNorm :=
    le_trans (abs_nonneg (y ⟨0, hn⟩)) (hy_le ⟨0, hn⟩)
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg (infNorm_nonneg A) hyNorm_nonneg
  have hβ_nonneg : 0 ≤ β := by
    unfold β
    exact infNormVec_nonneg b
  have hden_pos : 0 < 1 - ε := by linarith
  have hres_i : ∀ i, |residualVec n A y b i| ≤ ε * (C + β) := by
    intro i
    simpa [C, β, yNorm, hne] using hres i
  have hAy : ∀ i, |∑ j : Fin n, A i j * y j| ≤ C := by
    intro i
    calc
      |∑ j : Fin n, A i j * y j|
          ≤ ∑ j : Fin n, |A i j * y j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |A i j| * |y j| := by
          apply Finset.sum_congr rfl
          intro j _
          exact abs_mul (A i j) (y j)
      _ ≤ ∑ j : Fin n, |A i j| * yNorm := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hy_le j) (abs_nonneg _)
      _ = (∑ j : Fin n, |A i j|) * yNorm := by rw [Finset.sum_mul]
      _ ≤ infNorm A * yNorm :=
          mul_le_mul_of_nonneg_right (row_sum_le_infNorm A i) hyNorm_nonneg
      _ = C := by rfl
  have hb_step : ∀ i, |b i| ≤ C + ε * (C + β) := by
    intro i
    have hb_repr :
        b i = residualVec n A y b i + ∑ j : Fin n, A i j * y j := by
      unfold residualVec
      ring
    calc
      |b i|
          = |residualVec n A y b i + ∑ j : Fin n, A i j * y j| := by
            rw [hb_repr]
      _ ≤ |residualVec n A y b i| + |∑ j : Fin n, A i j * y j| :=
          abs_add_le _ _
      _ ≤ ε * (C + β) + C :=
          add_le_add (hres_i i) (hAy i)
      _ = C + ε * (C + β) := by ring
  have hβ_step : β ≤ C + ε * (C + β) := by
    unfold β
    apply infNormVec_le_of_abs_le
    · intro i
      simpa [C, β] using hb_step i
    · exact add_nonneg hC_nonneg (mul_nonneg hε (add_nonneg hC_nonneg hβ_nonneg))
  have hmove : (1 - ε) * β ≤ (1 + ε) * C := by
    linarith
  have hβ_le : β ≤ ((1 + ε) / (1 - ε)) * C := by
    calc
      β ≤ ((1 + ε) * C) / (1 - ε) :=
        (le_div_iff₀ hden_pos).mpr (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmove)
      _ = ((1 + ε) / (1 - ε)) * C := by ring
  intro i
  have hres2 :
      |residualVec n A y b i| ≤
        ε * (C + ((1 + ε) / (1 - ε)) * C) := by
    calc
      |residualVec n A y b i| ≤ ε * (C + β) := hres_i i
      _ ≤ ε * (C + ((1 + ε) / (1 - ε)) * C) := by
          exact mul_le_mul_of_nonneg_left (add_le_add (le_refl C) hβ_le) hε
  calc
    |residualVec n A y b i|
        ≤ ε * (C + ((1 + ε) / (1 - ε)) * C) := hres2
    _ = (2 * ε / (1 - ε)) *
        (infNorm A *
          Finset.sup' Finset.univ
            (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |y j|) +
          (0 : ℝ)) := by
        simp only [C, yNorm]
        field_simp [ne_of_gt hden_pos]
        ring

/-- Problem 7.7, normwise infinity-norm feasibility form. -/
theorem problem7_7_normwise_zero_rhs_feasible_of_abs_rhs_feasible (n : ℕ)
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hεlt : ε < 1)
    (hfeas : ∃ (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, |ΔA i j| ≤ ε * infNorm A) ∧
      (∀ i, |Δb i| ≤ ε * infNormVec b) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)) :
    ∃ (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, |ΔA i j| ≤ (2 * ε / (1 - ε)) * infNorm A) ∧
      (∀ i, |Δb i| ≤ (2 * ε / (1 - ε)) * (0 : ℝ)) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) := by
  have hres :
      ∀ i, |residualVec n A y b i| ≤
        ε * (infNorm A *
          Finset.sup' Finset.univ
            (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |y j|) +
          infNormVec b) :=
    (rigal_gaches n hn A y b (infNorm A) (infNormVec b) ε
      (infNorm_nonneg A) (infNormVec_nonneg b) hε).2 hfeas
  have hzero :=
    problem7_7_normwise_inf_residual_bound n hn A y b ε hε hεlt hres
  have hcoef : 0 ≤ 2 * ε / (1 - ε) := by
    exact div_nonneg (mul_nonneg (by norm_num) hε) (by linarith)
  exact
    (rigal_gaches n hn A y b (infNorm A) 0 (2 * ε / (1 - ε))
      (infNorm_nonneg A) (by norm_num) hcoef).1 hzero

-- ============================================================
-- Problem 7.8: rectangular Frobenius backward error
-- ============================================================

/-- Residual for a rectangular system, `r = b - Ay`. -/
noncomputable def ch7RectResidual (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b : Fin m → ℝ) :
    Fin m → ℝ :=
  fun i => b i - ∑ j : Fin n, A i j * y j

/-- Feasibility relation for Problem 7.8:
    `(A + ΔA)y = b + Δb`. -/
def ch7Problem78Feasible {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b : Fin m → ℝ)
    (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ) : Prop :=
  ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i

/-- The augmented perturbation matrix `[ΔA, θ Δb]` with the weighted
right-hand-side perturbation in the first column. -/
noncomputable def ch7Problem78AugMatrix {m n : ℕ} (θ : ℝ)
    (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ) :
    Fin m → Fin (n + 1) → ℝ :=
  fun i => Fin.cases (θ * Δb i) (fun j => ΔA i j)

/-- The augmented vector `[-θ⁻¹; y]` used in Appendix A's proof of
Problem 7.8 for `θ > 0`. -/
noncomputable def ch7Problem78AugVector {n : ℕ} (θ : ℝ)
    (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases (-(θ⁻¹)) y

/-- Squared norm of the augmented vector `[-θ⁻¹; y]`. -/
lemma ch7Problem78AugVector_norm_sq {n : ℕ} (θ : ℝ)
    (y : Fin n → ℝ) :
    vecNorm2Sq (ch7Problem78AugVector θ y) =
      θ⁻¹ ^ 2 + vecNorm2Sq y := by
  unfold vecNorm2Sq ch7Problem78AugVector
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  ring

/-- For `θ > 0`, the augmented vector in Problem 7.8 has nonzero norm. -/
lemma ch7Problem78AugVector_norm_ne_zero_of_theta_pos {n : ℕ}
    {θ : ℝ} (hθ : 0 < θ) (y : Fin n → ℝ) :
    vecNorm2 (ch7Problem78AugVector θ y) ≠ 0 := by
  intro hzero
  have hzero_entries :=
    (vecNorm2_eq_zero_iff (ch7Problem78AugVector θ y)).mp hzero
  have hfirst := hzero_entries 0
  have hinv_ne : θ⁻¹ ≠ 0 := inv_ne_zero hθ.ne'
  exact hinv_ne (neg_eq_zero.mp (by simpa [ch7Problem78AugVector] using hfirst))

/-- Higham Problem 7.8 denominator identity:
`θ ‖[-θ⁻¹; y]‖₂ = sqrt(θ² ‖y‖₂² + 1)` for `θ > 0`. -/
theorem ch7Problem78_source_denominator_eq {n : ℕ}
    {θ : ℝ} (hθ : 0 < θ) (y : Fin n → ℝ) :
    θ * vecNorm2 (ch7Problem78AugVector θ y) =
      Real.sqrt (θ ^ 2 * vecNorm2Sq y + 1) := by
  let z := ch7Problem78AugVector θ y
  have hz_nonneg : 0 ≤ θ * vecNorm2 z :=
    mul_nonneg hθ.le (vecNorm2_nonneg z)
  have harg_nonneg : 0 ≤ θ ^ 2 * vecNorm2Sq y + 1 := by
    have hprod : 0 ≤ θ ^ 2 * vecNorm2Sq y :=
      mul_nonneg (sq_nonneg θ) (vecNorm2Sq_nonneg y)
    linarith
  symm
  rw [Real.sqrt_eq_iff_mul_self_eq harg_nonneg hz_nonneg]
  dsimp [z]
  rw [show (θ * vecNorm2 (ch7Problem78AugVector θ y)) *
        (θ * vecNorm2 (ch7Problem78AugVector θ y)) =
      θ ^ 2 * vecNorm2 (ch7Problem78AugVector θ y) ^ 2 by ring,
    vecNorm2_sq, ch7Problem78AugVector_norm_sq]
  field_simp [ne_of_gt hθ]
  ring

/-- Equivalence between the augmented-vector value and Higham's printed
Problem 7.8 value `θ‖r‖₂ / sqrt(θ²‖y‖₂² + 1)`. -/
theorem problem7_8_source_value_eq_augmented_value {m n : ℕ}
    {θ : ℝ} (hθ : 0 < θ) (y : Fin n → ℝ) (r : Fin m → ℝ) :
    θ * vecNorm2 r / Real.sqrt (θ ^ 2 * vecNorm2Sq y + 1) =
      vecNorm2 r / vecNorm2 (ch7Problem78AugVector θ y) := by
  have hz_ne := ch7Problem78AugVector_norm_ne_zero_of_theta_pos hθ y
  have hden := ch7Problem78_source_denominator_eq hθ y
  rw [← hden]
  field_simp [ne_of_gt hθ, hz_ne]

/-- The augmented feasibility equation in Appendix A:
    `[ΔA, θΔb] [-θ⁻¹; y] = b - Ay`. -/
theorem ch7Problem78_augMatrix_mul_augVector_of_feasible {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b : Fin m → ℝ)
    (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ)
    {θ : ℝ} (hθ : θ ≠ 0)
    (hfeas : ch7Problem78Feasible A y b ΔA Δb) :
    rectMatMulVec (ch7Problem78AugMatrix θ ΔA Δb)
        (ch7Problem78AugVector θ y) =
      ch7RectResidual m n A y b := by
  ext i
  unfold rectMatMulVec ch7Problem78AugMatrix ch7Problem78AugVector
    ch7RectResidual ch7Problem78Feasible at *
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  have htheta : θ * Δb i * -θ⁻¹ = -Δb i := by
    field_simp [hθ]
  rw [htheta]
  have hsplit :
      ∑ j : Fin n, (A i j + ΔA i j) * y j =
        ∑ j : Fin n, A i j * y j + ∑ j : Fin n, ΔA i j * y j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hf := hfeas i
  rw [hsplit] at hf
  linarith

/-- Converse form of the augmented feasibility equation. -/
theorem ch7Problem78_feasible_of_augMatrix_mul_augVector {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b : Fin m → ℝ)
    (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ)
    {θ : ℝ} (hθ : θ ≠ 0)
    (hmul :
      rectMatMulVec (ch7Problem78AugMatrix θ ΔA Δb)
          (ch7Problem78AugVector θ y) =
        ch7RectResidual m n A y b) :
    ch7Problem78Feasible A y b ΔA Δb := by
  intro i
  have hentry := congrFun hmul i
  unfold rectMatMulVec ch7Problem78AugMatrix ch7Problem78AugVector
    ch7RectResidual at hentry
  rw [Fin.sum_univ_succ] at hentry
  simp only [Fin.cases_zero, Fin.cases_succ] at hentry
  have htheta : θ * Δb i * -θ⁻¹ = -Δb i := by
    field_simp [hθ]
  rw [htheta] at hentry
  have hsplit :
      ∑ j : Fin n, (A i j + ΔA i j) * y j =
        ∑ j : Fin n, A i j * y j + ∑ j : Fin n, ΔA i j * y j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  linarith

/-- Problem 7.8 lower-bound core.  Any feasible perturbation has augmented
Frobenius norm large enough to map `[-θ⁻¹; y]` to the residual. -/
theorem problem7_8_frobenius_lower_bound_core {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b : Fin m → ℝ)
    (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ)
    {θ : ℝ} (hθ : θ ≠ 0)
    (hfeas : ch7Problem78Feasible A y b ΔA Δb) :
    vecNorm2 (ch7RectResidual m n A y b) ≤
      frobNormRect (ch7Problem78AugMatrix θ ΔA Δb) *
        vecNorm2 (ch7Problem78AugVector θ y) := by
  rw [← ch7Problem78_augMatrix_mul_augVector_of_feasible
    A y b ΔA Δb hθ hfeas]
  exact vecNorm2_rectMatMulVec_le_frobNormRect_mul
    (ch7Problem78AugMatrix θ ΔA Δb) (ch7Problem78AugVector θ y)

/-- Problem 7.8 lower bound as a quotient by the augmented-vector norm. -/
theorem problem7_8_frobenius_lower_bound_pos {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b : Fin m → ℝ)
    (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ)
    {θ : ℝ} (hθ : 0 < θ)
    (hfeas : ch7Problem78Feasible A y b ΔA Δb) :
    vecNorm2 (ch7RectResidual m n A y b) /
        vecNorm2 (ch7Problem78AugVector θ y) ≤
      frobNormRect (ch7Problem78AugMatrix θ ΔA Δb) := by
  have hz_ne := ch7Problem78AugVector_norm_ne_zero_of_theta_pos hθ y
  have hz_pos : 0 < vecNorm2 (ch7Problem78AugVector θ y) :=
    lt_of_le_of_ne (vecNorm2_nonneg _) (Ne.symm hz_ne)
  have hcore :=
    problem7_8_frobenius_lower_bound_core A y b ΔA Δb
      (ne_of_gt hθ) hfeas
  exact (div_le_iff₀ hz_pos).mpr hcore

/-- Rectangular rank-one matrix `r zᵀ / ‖z‖₂²`. -/
noncomputable def ch7RectRankOneDivVecNorm2Sq {m n : ℕ}
    (r : Fin m → ℝ) (z : Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => (1 / vecNorm2Sq z) * (r i * z j)

/-- The rank-one rectangular perturbation maps `z` to `r`. -/
theorem ch7RectRankOneDivVecNorm2Sq_mul_vec {m n : ℕ}
    (r : Fin m → ℝ) (z : Fin n → ℝ) (hz : vecNorm2 z ≠ 0) :
    rectMatMulVec (ch7RectRankOneDivVecNorm2Sq r z) z = r := by
  have hsq : vecNorm2Sq z ≠ 0 := by
    intro hzero
    have hnormsq : vecNorm2 z ^ 2 = 0 := by
      rw [vecNorm2_sq, hzero]
    exact hz (sq_eq_zero_iff.mp hnormsq)
  have hsq' : (∑ j : Fin n, z j ^ 2) ≠ 0 := by
    simpa [vecNorm2Sq] using hsq
  ext i
  unfold ch7RectRankOneDivVecNorm2Sq rectMatMulVec vecNorm2Sq
  calc
    (∑ j : Fin n, (1 / ∑ k : Fin n, z k ^ 2) * (r i * z j) * z j)
        = ∑ j : Fin n, ((1 / ∑ k : Fin n, z k ^ 2) * r i) * z j ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ((1 / ∑ j : Fin n, z j ^ 2) * r i) *
        (∑ j : Fin n, z j ^ 2) := by
          rw [Finset.mul_sum]
    _ = r i := by
          field_simp [hsq']

/-- Frobenius norm of the rectangular rank-one perturbation
`r zᵀ / ‖z‖₂²`. -/
theorem frobNormRect_ch7RectRankOneDivVecNorm2Sq {m n : ℕ}
    (r : Fin m → ℝ) (z : Fin n → ℝ) (hz : vecNorm2 z ≠ 0) :
    frobNormRect (ch7RectRankOneDivVecNorm2Sq r z) =
      vecNorm2 r / vecNorm2 z := by
  unfold ch7RectRankOneDivVecNorm2Sq
  rw [frobNormRect_eq_frobNormFn, frobNorm_rankOne_smul]
  have hden_nonneg : 0 ≤ vecNorm2Sq z := vecNorm2Sq_nonneg z
  have hden_eq : vecNorm2Sq z = vecNorm2 z ^ 2 := (vecNorm2_sq z).symm
  rw [abs_of_nonneg (one_div_nonneg.mpr hden_nonneg), hden_eq]
  field_simp [hz]

/-- The rank-one augmented matrix used to attain the Problem 7.8 lower
bound for `θ > 0`. -/
noncomputable def ch7Problem78RankOneAugMatrix {m n : ℕ}
    (θ : ℝ) (y : Fin n → ℝ) (r : Fin m → ℝ) :
    Fin m → Fin (n + 1) → ℝ :=
  ch7RectRankOneDivVecNorm2Sq r (ch7Problem78AugVector θ y)

/-- The `ΔA` block extracted from the rank-one augmented perturbation. -/
noncomputable def ch7Problem78RankOneDeltaA {m n : ℕ}
    (θ : ℝ) (y : Fin n → ℝ) (r : Fin m → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => ch7Problem78RankOneAugMatrix θ y r i j.succ

/-- The `Δb` vector extracted from the weighted first column of the rank-one
augmented perturbation. -/
noncomputable def ch7Problem78RankOneDeltaB {m n : ℕ}
    (θ : ℝ) (y : Fin n → ℝ) (r : Fin m → ℝ) : Fin m → ℝ :=
  fun i => θ⁻¹ * ch7Problem78RankOneAugMatrix θ y r i 0

/-- The extracted `ΔA, Δb` reassemble to the rank-one augmented matrix. -/
theorem ch7Problem78_augMatrix_rankOneDelta_eq {m n : ℕ}
    {θ : ℝ} (hθ : θ ≠ 0) (y : Fin n → ℝ) (r : Fin m → ℝ) :
    ch7Problem78AugMatrix θ
        (ch7Problem78RankOneDeltaA θ y r)
        (ch7Problem78RankOneDeltaB θ y r) =
      ch7Problem78RankOneAugMatrix θ y r := by
  ext i k
  refine Fin.cases ?_ ?_ k
  · unfold ch7Problem78AugMatrix ch7Problem78RankOneDeltaB
    simp only [Fin.cases_zero]
    field_simp [hθ]
  · intro j
    unfold ch7Problem78AugMatrix ch7Problem78RankOneDeltaA
    simp only [Fin.cases_succ]

/-- The rank-one augmented matrix maps `[-θ⁻¹; y]` exactly to `r`. -/
theorem ch7Problem78_rankOne_augMatrix_mul_augVector {m n : ℕ}
    {θ : ℝ} (hθ : 0 < θ) (y : Fin n → ℝ) (r : Fin m → ℝ) :
    rectMatMulVec (ch7Problem78RankOneAugMatrix θ y r)
        (ch7Problem78AugVector θ y) =
      r := by
  exact ch7RectRankOneDivVecNorm2Sq_mul_vec r
    (ch7Problem78AugVector θ y)
    (ch7Problem78AugVector_norm_ne_zero_of_theta_pos hθ y)

/-- The Frobenius norm of the rank-one augmented matrix is the Problem 7.8
lower-bound value. -/
theorem frobNormRect_ch7Problem78RankOneAugMatrix {m n : ℕ}
    {θ : ℝ} (hθ : 0 < θ) (y : Fin n → ℝ) (r : Fin m → ℝ) :
    frobNormRect (ch7Problem78RankOneAugMatrix θ y r) =
      vecNorm2 r / vecNorm2 (ch7Problem78AugVector θ y) := by
  exact frobNormRect_ch7RectRankOneDivVecNorm2Sq r
    (ch7Problem78AugVector θ y)
    (ch7Problem78AugVector_norm_ne_zero_of_theta_pos hθ y)

/-- Problem 7.8 attainment for `θ > 0`: the rank-one perturbation is feasible
and meets the lower bound. -/
theorem problem7_8_rankOne_attains_pos {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b : Fin m → ℝ)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      ch7Problem78Feasible A y b ΔA Δb ∧
      frobNormRect (ch7Problem78AugMatrix θ ΔA Δb) =
        vecNorm2 (ch7RectResidual m n A y b) /
          vecNorm2 (ch7Problem78AugVector θ y) := by
  let r := ch7RectResidual m n A y b
  let ΔA := ch7Problem78RankOneDeltaA θ y r
  let Δb := ch7Problem78RankOneDeltaB θ y r
  refine ⟨ΔA, Δb, ?_, ?_⟩
  · have hmul_rank :
        rectMatMulVec (ch7Problem78RankOneAugMatrix θ y r)
            (ch7Problem78AugVector θ y) =
          r :=
      ch7Problem78_rankOne_augMatrix_mul_augVector hθ y r
    have haug_eq :
        ch7Problem78AugMatrix θ ΔA Δb =
          ch7Problem78RankOneAugMatrix θ y r := by
      simpa [ΔA, Δb, r] using
        ch7Problem78_augMatrix_rankOneDelta_eq (ne_of_gt hθ) y r
    apply ch7Problem78_feasible_of_augMatrix_mul_augVector A y b ΔA Δb (ne_of_gt hθ)
    rw [haug_eq]
    simpa [r] using hmul_rank
  · have haug_eq :
        ch7Problem78AugMatrix θ ΔA Δb =
          ch7Problem78RankOneAugMatrix θ y r := by
      simpa [ΔA, Δb, r] using
        ch7Problem78_augMatrix_rankOneDelta_eq (ne_of_gt hθ) y r
    rw [haug_eq]
    simpa [r] using frobNormRect_ch7Problem78RankOneAugMatrix hθ y r

/-- Problem 7.8 for `θ > 0`, encoded as a lower bound for every feasible
perturbation plus an attaining feasible perturbation. -/
theorem problem7_8_frobenius_characterization_pos {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b : Fin m → ℝ)
    {θ : ℝ} (hθ : 0 < θ) :
    (∀ (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      ch7Problem78Feasible A y b ΔA Δb →
        vecNorm2 (ch7RectResidual m n A y b) /
            vecNorm2 (ch7Problem78AugVector θ y) ≤
          frobNormRect (ch7Problem78AugMatrix θ ΔA Δb)) ∧
    ∃ (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      ch7Problem78Feasible A y b ΔA Δb ∧
      frobNormRect (ch7Problem78AugMatrix θ ΔA Δb) =
        vecNorm2 (ch7RectResidual m n A y b) /
          vecNorm2 (ch7Problem78AugVector θ y) := by
  exact
    ⟨fun ΔA Δb hfeas =>
      problem7_8_frobenius_lower_bound_pos A y b ΔA Δb hθ hfeas,
      problem7_8_rankOne_attains_pos A y b hθ⟩

/-- Problem 7.8 at `θ = 0`: the weighted cost ignores `Δb`, so choosing
`ΔA = 0` and `Δb = Ay - b` makes the augmented Frobenius cost zero. -/
theorem problem7_8_zero_parameter_attains {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b : Fin m → ℝ) :
    ∃ (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      ch7Problem78Feasible A y b ΔA Δb ∧
      frobNormRect (ch7Problem78AugMatrix 0 ΔA Δb) = 0 := by
  refine
    ⟨fun _ _ => 0,
      fun i => ∑ j : Fin n, A i j * y j - b i,
      ?_, ?_⟩
  · intro i
    simp
  · unfold frobNormRect
    have hsq :
        frobNormSqRect
            (ch7Problem78AugMatrix 0
              (fun (_ : Fin m) (_ : Fin n) => (0 : ℝ))
              (fun i => ∑ j : Fin n, A i j * y j - b i)) = 0 := by
      apply (frobNormSqRect_eq_zero_iff _).mpr
      intro i k
      refine Fin.cases ?_ ?_ k
      · simp [ch7Problem78AugMatrix]
      · intro j
        simp [ch7Problem78AugMatrix]
    rw [hsq]
    simp

-- ============================================================
-- Lemma 7.9: practical error bounds
-- ============================================================

/-- Lemma 7.9, componentwise core: if `ω(E|x̂|+f)` bounds the residual
    componentwise, then `ω |A⁻¹|(E|x̂|+f)` bounds `|A⁻¹||r|`. -/
theorem lemma7_9_componentwise_bound (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ) (ω : ℝ)
    (hωres : ∀ j, |residualVec n A y b j| ≤
      ω * (∑ k : Fin n, E j k * |y k| + f j)) :
    ∀ i, ch7ResidualImage n A A_inv y b i ≤
      ω * ch7AmplifiedRhsEF n A_inv E f y i := by
  intro i
  unfold ch7ResidualImage ch7AmplifiedRhsEF
  calc
    ∑ j : Fin n, |A_inv i j| * |residualVec n A y b j|
        ≤ ∑ j : Fin n, |A_inv i j| *
          (ω * (∑ k : Fin n, E j k * |y k| + f j)) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hωres j) (abs_nonneg _)
    _ = ω * ∑ j : Fin n, |A_inv i j| *
          (∑ k : Fin n, E j k * |y k| + f j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- Lemma 7.9, relative infinity-norm practical bound (7.29). -/
theorem lemma7_9_relative_infNorm_bound (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ) (ω : ℝ)
    (hω : 0 ≤ ω) (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i)
    (hωres : ∀ j, |residualVec n A y b j| ≤
      ω * (∑ k : Fin n, E j k * |y k| + f j))
    (hy : 0 < infNormVec y) :
    infNormVec (ch7ResidualImage n A A_inv y b) / infNormVec y ≤
      ω * (ch7ForwardBoundEF n hn A_inv E f y / infNormVec y) := by
  let C := ch7ForwardBoundEF n hn A_inv E f y
  have hC_nonneg : 0 ≤ C := ch7ForwardBoundEF_nonneg n hn A_inv E f y hE hf
  have hcomp := lemma7_9_componentwise_bound n A A_inv y b E f ω hωres
  have hnorm :
      infNormVec (ch7ResidualImage n A A_inv y b) ≤ ω * C := by
    apply infNormVec_le_of_abs_le
    · intro i
      have hri_nonneg : 0 ≤ ch7ResidualImage n A A_inv y b i := by
        unfold ch7ResidualImage
        exact Finset.sum_nonneg fun j _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _)
      rw [abs_of_nonneg hri_nonneg]
      calc
        ch7ResidualImage n A A_inv y b i
            ≤ ω * ch7AmplifiedRhsEF n A_inv E f y i := hcomp i
        _ ≤ ω * C := by
            exact mul_le_mul_of_nonneg_left
              (Finset.le_sup' (ch7AmplifiedRhsEF n A_inv E f y)
                (Finset.mem_univ i)) hω
    · exact mul_nonneg hω hC_nonneg
  calc
    infNormVec (ch7ResidualImage n A A_inv y b) / infNormVec y
        ≤ (ω * C) / infNormVec y :=
          div_le_div_of_nonneg_right hnorm (le_of_lt hy)
    _ = ω * (C / infNormVec y) := by ring

/-- Equality case recorded in Lemma 7.9: if `E|x̂|+f` is a scalar multiple of
    `|r|` with reciprocal factor `ω`, then the practical bound is exact before
    taking the infinity norm. -/
theorem lemma7_9_exact_for_residual_multiple (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ) (ω c : ℝ)
    (hscale : ∀ j, ∑ k : Fin n, E j k * |y k| + f j =
      c * |residualVec n A y b j|)
    (hωc : ω * c = 1) :
    ∀ i, ω * ch7AmplifiedRhsEF n A_inv E f y i =
      ch7ResidualImage n A A_inv y b i := by
  intro i
  unfold ch7AmplifiedRhsEF ch7ResidualImage
  calc
    ω * (∑ j : Fin n, |A_inv i j| *
        (∑ k : Fin n, E j k * |y k| + f j))
        = ω * (∑ j : Fin n, |A_inv i j| *
            (c * |residualVec n A y b j|)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [hscale j]
    _ = (ω * c) *
        (∑ j : Fin n, |A_inv i j| * |residualVec n A y b j|) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ j : Fin n, |A_inv i j| * |residualVec n A y b j| := by
          rw [hωc]
          ring

-- ============================================================
-- Equation (7.33): stochastic matrices
-- ============================================================

/-- A finite row-stochastic matrix: nonnegative entries and each row sums to 1. -/
def IsStochasticMatrix (n : ℕ) (P : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j : Fin n, P i j = 1)

/-- Equation (7.33): a stochastic matrix satisfies `P e = e`. -/
theorem stochasticMatrix_mul_ones (n : ℕ) (P : Fin n → Fin n → ℝ)
    (hP : IsStochasticMatrix n P) :
    matMulVec n P (fun _ : Fin n => (1 : ℝ)) = fun _ : Fin n => (1 : ℝ) := by
  ext i
  unfold matMulVec
  simpa using hP.2 i

end LeanFpAnalysis.FP
