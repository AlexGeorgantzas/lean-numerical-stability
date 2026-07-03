-- Algorithms/Cholesky/CholeskyPerturbation.lean
--
-- Theorem 10.8 (Sun): Perturbation sensitivity of the Cholesky factorization.
--
-- If A is SPD with Cholesky factorization A = R^T R and ΔA is symmetric
-- with ‖A⁻¹ΔA‖₂ < 1, then A + ΔA = (R + ΔR)^T (R + ΔR) and:
--   ‖ΔR‖_F / ‖R‖_F ≤ κ₂(A) / (2‖A‖₂) · ‖ΔA‖_F   (normwise)
--   |ΔR| ≤ triu(|R⁻ᵀ||ΔA||R⁻¹|) · (1 + O(‖ΔA‖))   (componentwise)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination
import LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §10.2  Upper triangular part
-- ============================================================

/-- **Upper triangular part** of a matrix: triu(A)_{ij} = A_{ij} if i ≤ j, else 0. -/
noncomputable def triuPart {n : ℕ} (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if i.val ≤ j.val then A i j else 0

lemma triuPart_upper {n : ℕ} (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, j.val < i.val → triuPart A i j = 0 := by
  intro i j hij
  unfold triuPart
  simp [show ¬(i.val ≤ j.val) from by omega]

lemma triuPart_diag_and_above {n : ℕ} (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, i.val ≤ j.val → triuPart A i j = A i j := by
  intro i j hij
  unfold triuPart
  simp [hij]

-- ============================================================
-- §10.2  The `up` operator (Theorem 10.8 proof machinery)
-- ============================================================

/-- **The `up` operator** (proof route for Theorem 10.8; Sun, BIT 31
    (1991), advisory route logged in the chapter report): the upper
    triangular part with halved diagonal,
    `up(Y)_{ij} = Y_{ij}` for `i < j`, `Y_{ii}/2` on the diagonal, `0`
    below. -/
noncomputable def upHalf {n : ℕ} (Y : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i.val < j.val then Y i j
    else if i = j then Y i j / 2
    else 0

lemma upHalf_strict_lower {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (i j : Fin n) (hij : j.val < i.val) : upHalf Y i j = 0 := by
  unfold upHalf
  rw [if_neg (by omega : ¬ i.val < j.val),
    if_neg (fun he : i = j => by subst he; omega)]

lemma upHalf_strict_upper {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (i j : Fin n) (hij : i.val < j.val) : upHalf Y i j = Y i j := by
  unfold upHalf
  rw [if_pos hij]

lemma upHalf_diag {n : ℕ} (Y : Fin n → Fin n → ℝ) (i : Fin n) :
    upHalf Y i i = Y i i / 2 := by
  unfold upHalf
  rw [if_neg (lt_irrefl _), if_pos rfl]

/-- **Triangular recovery** (Theorem 10.8 proof, step 1): an upper
    triangular `X` is recovered from its symmetrization,
    `up(X + Xᵀ) = X`. -/
theorem upHalf_add_transpose {n : ℕ} (X : Fin n → Fin n → ℝ)
    (hX : ∀ i j : Fin n, j.val < i.val → X i j = 0) :
    ∀ i j : Fin n, upHalf (fun p q => X p q + X q p) i j = X i j := by
  intro i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [upHalf_strict_upper _ i j h]
    rw [hX j i h, add_zero]
  · have hij : i = j := Fin.ext h
    subst hij
    rw [upHalf_diag]
    ring
  · rw [upHalf_strict_lower _ i j h, hX i j h]

/-- **Frobenius halving** (Theorem 10.8 proof, step 2): for a symmetric
    matrix `Y`, `‖up(Y)‖_F² ≤ ‖Y‖_F²/2` — the strict upper part carries
    at most half of the off-diagonal mass and the halved diagonal at
    most a quarter of the diagonal mass. -/
theorem frobNormSq_upHalf_le_half {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (hY : ∀ i j : Fin n, Y i j = Y j i) :
    frobNormSq (upHalf Y) ≤ frobNormSq Y / 2 := by
  have hpoint : ∀ i j : Fin n,
      2 * upHalf Y i j ^ 2 + 2 * upHalf Y j i ^ 2 ≤
      Y i j ^ 2 + Y j i ^ 2 := by
    intro i j
    rcases lt_trichotomy i.val j.val with h | h | h
    · rw [upHalf_strict_upper Y i j h, upHalf_strict_lower Y j i h,
        hY j i]
      nlinarith [sq_nonneg (Y i j)]
    · have hij : i = j := Fin.ext h
      subst hij
      rw [upHalf_diag]
      nlinarith [sq_nonneg (Y i i)]
    · rw [upHalf_strict_lower Y i j h, upHalf_strict_upper Y j i h,
        hY j i]
      nlinarith [sq_nonneg (Y i j)]
  have hsum : ∑ i : Fin n, ∑ j : Fin n,
      (2 * upHalf Y i j ^ 2 + 2 * upHalf Y j i ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n, (Y i j ^ 2 + Y j i ^ 2) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
  have hsplit : ∀ (M : Fin n → Fin n → ℝ) (c : ℝ),
      ∑ i : Fin n, ∑ j : Fin n, (c * M i j ^ 2 + c * M j i ^ 2) =
      c * (∑ i : Fin n, ∑ j : Fin n, M i j ^ 2) +
      c * (∑ i : Fin n, ∑ j : Fin n, M j i ^ 2) := by
    intro M c
    have inner : ∀ i : Fin n, ∑ j : Fin n,
        (c * M i j ^ 2 + c * M j i ^ 2) =
        c * (∑ j : Fin n, M i j ^ 2) +
        c * (∑ j : Fin n, M j i ^ 2) := by
      intro i
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => inner i,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hswapU : ∑ i : Fin n, ∑ j : Fin n, upHalf Y j i ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, upHalf Y i j ^ 2 :=
    Finset.sum_comm
  have hswapY : ∑ i : Fin n, ∑ j : Fin n, Y j i ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, Y i j ^ 2 :=
    Finset.sum_comm
  have hL := hsplit (upHalf Y) 2
  have hR := hsplit Y 1
  rw [hswapU] at hL
  rw [hswapY] at hR
  simp only [one_mul] at hR
  unfold frobNormSq
  have hsum' := hsum
  rw [hL] at hsum'
  have hRfix : ∑ i : Fin n, ∑ j : Fin n, (Y i j ^ 2 + Y j i ^ 2) =
      (∑ i : Fin n, ∑ j : Fin n, Y i j ^ 2) +
      ∑ i : Fin n, ∑ j : Fin n, Y i j ^ 2 := by
    have := hsplit Y 1
    simp only [one_mul] at this
    rw [this, hswapY]
  rw [hRfix] at hsum'
  linarith

/-- **Perturbed Gram identity** (Theorem 10.8 proof, step 3): if
    `RᵀR = A` and `(R+ΔR)ᵀ(R+ΔR) = A + ΔA` entrywise, the perturbation
    satisfies `RᵀΔR + ΔRᵀR + ΔRᵀΔR = ΔA` entrywise — the exact identity
    the `up`-operator route symmetrizes. -/
theorem cholesky_perturbation_gram_identity {n : ℕ}
    (A ΔA R ΔR : Fin n → Fin n → ℝ)
    (hA : ∀ i j : Fin n, ∑ k : Fin n, R k i * R k j = A i j)
    (hAΔ : ∀ i j : Fin n, ∑ k : Fin n,
      (R k i + ΔR k i) * (R k j + ΔR k j) = A i j + ΔA i j) :
    ∀ i j : Fin n,
      (∑ k : Fin n, R k i * ΔR k j) + (∑ k : Fin n, ΔR k i * R k j) +
      (∑ k : Fin n, ΔR k i * ΔR k j) = ΔA i j := by
  intro i j
  have h := hAΔ i j
  have hsplit : ∑ k : Fin n,
      (R k i + ΔR k i) * (R k j + ΔR k j) =
      (∑ k : Fin n, R k i * R k j) +
      ((∑ k : Fin n, R k i * ΔR k j) + (∑ k : Fin n, ΔR k i * R k j) +
       (∑ k : Fin n, ΔR k i * ΔR k j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, hA i j] at h
  linarith

/-- **Scalar absorption endgame** (Theorem 10.8 proof, step 4): from
    the quadratic self-bound `t ≤ a(δ + t²)` and the small-root
    certificate `a·t < 1`, `t ≤ aδ/(1 − a·t)`. -/
theorem cholesky_perturbation_scalar_endgame (a δ t : ℝ)
    (hquad : t ≤ a * (δ + t ^ 2)) (hat : a * t < 1) :
    t ≤ a * δ / (1 - a * t) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **Scalar endgame, display form** (Theorem 10.8, printed display
    shape): if moreover `a·t ≤ c < 1` with `a, δ ≥ 0`, the bound takes
    the source's monotone form `t ≤ aδ/(1 − c)`. -/
theorem cholesky_perturbation_scalar_endgame_display (a δ t c : ℝ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hquad : t ≤ a * (δ + t ^ 2))
    (hac : a * t ≤ c) (hc1 : c < 1) :
    t ≤ a * δ / (1 - c) := by
  have hat : a * t < 1 := lt_of_le_of_lt hac hc1
  have h1 := cholesky_perturbation_scalar_endgame a δ t hquad hat
  have h2 : a * δ / (1 - a * t) ≤ a * δ / (1 - c) :=
    div_le_div₀ (mul_nonneg ha hδ) le_rfl (by linarith) (by linarith)
  exact h1.trans h2

-- ============================================================
-- §10.2  Theorem 10.8: Sun perturbation bound (normwise)
-- ============================================================

/-- **Abstract Cholesky perturbation normwise-bound interface**
    (Higham §10.2, Theorem 10.8, first part).

    If A is SPD with A = R^T R and ΔA is symmetric with ‖A⁻¹ΔA‖₂ < 1,
    then A + ΔA = (R + ΔR)^T(R + ΔR) where:
      frobNormSq(ΔR) ≤ (κ₂(A) / (2 · norm₂(A)))² · frobNormSq(ΔA) + O(‖ΔA‖²)

    We state the first-order bound in squared form to avoid sqrt.
    The condition number κ₂(A) = ‖A‖₂ · ‖A⁻¹‖₂ is taken as a hypothesis.
    The perturbation existence/bound itself is supplied as `hpert`. -/
theorem cholesky_perturbation_normwise (n : ℕ)
    (A R : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (_hChol : CholeskyFactSpec n A R)
    (_hSym_A : ∀ i j : Fin n, A i j = A j i)
    (_hSym_ΔA : ∀ i j : Fin n, ΔA i j = ΔA j i)
    -- Norms and condition number as hypotheses
    (norm2_A : ℝ) (_hnorm2_pos : 0 < norm2_A)
    (κ2_A : ℝ) (_hκ2_pos : 0 < κ2_A)
    -- Perturbation is small enough
    (_hSmall : frobNormSq ΔA < norm2_A ^ 2)
    -- The bound: existence of ΔR with the Frobenius norm bound
    -- This first-order perturbation result follows from implicit function
    -- theorem applied to the map R ↦ R^T R.
    (hpert : ∃ ΔR : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → ΔR i j = 0) ∧
      (∀ i j, ∑ k : Fin n, (R k i + ΔR k i) * (R k j + ΔR k j) = A i j + ΔA i j) ∧
      frobNormSq ΔR ≤ κ2_A ^ 2 / (4 * norm2_A ^ 2) * frobNormSq ΔA) :
    ∃ ΔR : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → ΔR i j = 0) ∧
      (∀ i j, ∑ k : Fin n, (R k i + ΔR k i) * (R k j + ΔR k j) = A i j + ΔA i j) ∧
      frobNormSq ΔR ≤ κ2_A ^ 2 / (4 * norm2_A ^ 2) * frobNormSq ΔA :=
  hpert

-- ============================================================
-- §10.2  Theorem 10.8: Sun perturbation bound (componentwise)
-- ============================================================

/-- **Cholesky perturbation componentwise bound** (Higham §10.2, Theorem 10.8, second part).

    Under the conditions of the normwise bound, if ε = ‖(R+ΔR)⁻ᵀ ΔA (R+ΔR)⁻¹‖₂ < 1:
      |ΔR| ≤ triu(|R⁻ᵀ| · |ΔA| · |R⁻¹|) · (1 + O(ε))

    We take the componentwise bound as a hypothesis and express it
    using the upper triangular part and matrix inverses. -/
theorem cholesky_perturbation_componentwise (n : ℕ)
    (R ΔR R_invT R_inv : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (_hChol_R : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (_hΔR_upper : ∀ i j : Fin n, j.val < i.val → ΔR i j = 0)
    -- R⁻ᵀ and R⁻¹ are the transposes/inverses
    (_hR_invT : IsLeftInverse n (fun i j => R j i) R_invT)
    (_hR_inv : IsRightInverse n R R_inv)
    -- First-order bound
    (α : ℝ) (_hα : 0 ≤ α)
    (hbound : ∀ i j : Fin n, i.val ≤ j.val →
      |ΔR i j| ≤ (1 + α) *
        ∑ k₁ : Fin n, |R_invT i k₁| *
          ∑ k₂ : Fin n, |ΔA k₁ k₂| * |R_inv k₂ j|) :
    ∀ i j : Fin n, |ΔR i j| ≤ (1 + α) *
      (if i.val ≤ j.val then
        ∑ k₁ : Fin n, |R_invT i k₁| *
          ∑ k₂ : Fin n, |ΔA k₁ k₂| * |R_inv k₂ j|
       else 0) := by
  intro i j
  by_cases hij : i.val ≤ j.val
  · simp [hij]
    exact hbound i j hij
  · simp [show ¬(i.val ≤ j.val) from by omega]
    have hij' : j.val < i.val := by omega
    have hΔR_zero := _hΔR_upper i j hij'
    simp [hΔR_zero]

-- ============================================================
-- §10.2  Sensitivity of leading submatrices
-- ============================================================

/-- **Leading submatrix sensitivity** (Higham §10.2, Remark after Theorem 10.8).

    The Cholesky factor of A_k = A(1:k, 1:k) is R_k = R(1:k, 1:k).
    Since κ₂(A_{k+1}) ≥ κ₂(A_k) by eigenvalue interlacing:
    - If A is ill-conditioned but A_k is well-conditioned,
      then R_k is insensitive to perturbations but later columns
      of R are much more sensitive.

    We state this as a monotonicity property of the condition number
    along the leading submatrix chain. -/
theorem cholesky_cond_monotone
    (κ : ℕ → ℝ)
    (_hκ_mono : ∀ k : ℕ, κ k ≤ κ (k + 1))
    (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    κ k₁ ≤ κ k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ d ih =>
    calc κ k₁ ≤ κ (k₁ + d) := ih (by omega)
      _ ≤ κ (k₁ + d + 1) := _hκ_mono _
      _ = κ (k₁ + (d + 1)) := by ring_nf

end LeanFpAnalysis.FP
