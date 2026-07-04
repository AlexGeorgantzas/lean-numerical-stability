-- Algorithms/Cholesky/CholeskyIndefinite.lean
--
-- Chapter 11: Symmetric indefinite and skew-symmetric systems.
--
-- Block LDL^T factorization: PAPT = LDLT where L is unit lower triangular
-- and D is block diagonal with 1×1 or 2×2 blocks.
--
-- Pivoting strategies:
-- - Complete pivoting (Bunch-Parlett): α = (1+√17)/8, growth ≤ (2.57)^{n-1}
-- - Partial pivoting (Bunch-Kaufman): same α, O(n²) comparisons

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- Chapter 11  Source predicates and block diagonal structure
-- ============================================================

/-- A symmetric tridiagonal matrix predicate, used by Aasen's method and by the
    symmetric-tridiagonal specialization of block LDL^T. -/
def IsSymTridiagonal (n : ℕ) (T : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, T i j = T j i) ∧
  (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → T i j = 0)

/-- A real skew-symmetric matrix predicate, `A^T = -A`. -/
def IsSkewSymmetric (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, A i j = -A j i

/-- A skew-symmetric matrix has zero diagonal. -/
theorem skewSymmetric_diag_zero (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hA : IsSkewSymmetric n A) :
    ∀ i : Fin n, A i i = 0 := by
  intro i
  have h := hA i i
  linarith

/-- **Block diagonal predicate** for the D factor in block LDL^T.

    D is block diagonal with blocks of size 1 or 2.
    Entries D_{ij} = 0 whenever i and j are not in the same block.

    We model this by requiring: for |i - j| > 1, D_{ij} = 0;
    and D is symmetric. The block structure means each 2×2 block
    [d_{k,k}  d_{k,k+1}; d_{k+1,k}  d_{k+1,k+1}] is nonsingular. -/
def IsBlockDiag (n : ℕ) (D : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, D i j = D j i) ∧
  (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → D i j = 0)

/-- Skew block diagonal structure for Chapter 11, equation (11.16): diagonal
    blocks are zero `1x1` blocks or skew `2x2` blocks. -/
def IsSkewBlockDiag (n : ℕ) (D : Fin n → Fin n → ℝ) : Prop :=
  IsSkewSymmetric n D ∧
  (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → D i j = 0)

-- ============================================================
-- Chapter 11  Block LDL^T and Aasen specifications
-- ============================================================

/-- **Block LDL^T factorization** (Higham Chapter 11).

    For a symmetric matrix A, the diagonal pivoting method computes:
      P A P^T = L D L^T

    where P is a permutation, L is unit lower triangular, and D is
    block diagonal with 1×1 or 2×2 diagonal blocks.

    The 2×2 blocks arise when a 1×1 pivot would be too small
    (potentially causing instability). Each 2×2 block is nonsingular. -/
structure BlockLDLTSpec (n : ℕ) (A L D : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L is unit lower triangular: diagonal entries are 1. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular: entries above diagonal are 0. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- D is block diagonal with 1×1 or 2×2 blocks. -/
  D_block_diag : IsBlockDiag n D
  /-- P A P^T = L D L^T: the product recovers the permuted matrix. -/
  product_eq : ∀ i j : Fin n,
    ∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * D k₁ k₂ * L j k₂ = A (σ i) (σ j)

/-- **Aasen factorization** source specification:
`P A P^T = L T L^T`, with `L` unit lower triangular, first column `e_1`,
and `T` symmetric tridiagonal. -/
structure AasenSpec (n : ℕ) (A L T : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- The first column of L is the first coordinate vector. -/
  L_first_col : ∀ i j : Fin n, j.val = 0 → i.val ≠ 0 → L i j = 0
  /-- T is symmetric tridiagonal. -/
  T_tridiag : IsSymTridiagonal n T
  /-- P A P^T = L T L^T. -/
  product_eq : ∀ i j : Fin n,
    ∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * T k₁ k₂ * L j k₂ = A (σ i) (σ j)

/-- Skew-symmetric block LDL^T factorization source specification for
Chapter 11, equation (11.16). -/
structure SkewBlockLDLTSpec (n : ℕ) (A L D : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) : Prop where
  /-- The input is skew-symmetric. -/
  skew_A : IsSkewSymmetric n A
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- D is skew block diagonal. -/
  D_skew_block_diag : IsSkewBlockDiag n D
  /-- P A P^T = L D L^T. -/
  product_eq : ∀ i j : Fin n,
    ∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * D k₁ k₂ * L j k₂ = A (σ i) (σ j)

/-- **Block LDL^T backward error** (Higham Chapter 11).

    The computed factors satisfy:
      |L̂ D̂ L̂^T − PAP^T| ≤ ε · |L̂| · |D̂| · |L̂^T|  componentwise -/
structure BlockLDLTBackwardError (n : ℕ) (A L_hat D_hat : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (ε : ℝ) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L̂ is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L_hat i i = 1
  /-- L̂ is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0
  /-- D̂ is block diagonal. -/
  D_block_diag : IsBlockDiag n D_hat
  /-- Componentwise backward error. -/
  backward_bound : ∀ i j : Fin n,
    |∑ k₁ : Fin n, ∑ k₂ : Fin n, L_hat i k₁ * D_hat k₁ k₂ * L_hat j k₂ -
      A (σ i) (σ j)| ≤
    ε * ∑ k₁ : Fin n, ∑ k₂ : Fin n, |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂|

/-- Pivot block size used by Chapter 11 algorithms. -/
inductive PivotSize where
  | one
  | two
  deriving DecidableEq, Repr

/-- Algorithm 11.1 source decision predicate for the first Bunch-Parlett
complete-pivoting step, expressed in terms of the printed scalar quantities
`mu0` and `mu1`. -/
def BunchParlettCompletePivotChoice (α μ0 μ1 : ℝ) (s : PivotSize) : Prop :=
  match s with
  | PivotSize.one => μ1 ≥ α * μ0
  | PivotSize.two => μ1 < α * μ0

/-- Branch labels for Algorithm 11.2. -/
inductive BunchKaufmanCase where
  | noAction
  | case1
  | case2
  | case3
  | case4
  deriving DecidableEq, Repr

/-- Algorithm 11.2 source decision predicate for the Bunch-Kaufman partial
pivoting tests at the first stage. -/
def BunchKaufmanPartialPivotCase
    (α a11 arr ω1 ωr : ℝ) (branch : BunchKaufmanCase) : Prop :=
  match branch with
  | BunchKaufmanCase.noAction => ω1 = 0
  | BunchKaufmanCase.case1 => ω1 ≠ 0 ∧ |a11| ≥ α * ω1
  | BunchKaufmanCase.case2 =>
      ω1 ≠ 0 ∧ |a11| < α * ω1 ∧ |a11| * ωr ≥ α * ω1 ^ 2
  | BunchKaufmanCase.case3 =>
      ω1 ≠ 0 ∧ |a11| < α * ω1 ∧ |a11| * ωr < α * ω1 ^ 2 ∧
        |arr| ≥ α * ωr
  | BunchKaufmanCase.case4 =>
      ω1 ≠ 0 ∧ |a11| < α * ω1 ∧ |a11| * ωr < α * ω1 ^ 2 ∧
        |arr| < α * ωr

/-- Algorithm 11.5 source predicate for a successful symmetric rook-pivot
first-stage decision.  The loop and search path are not modeled here; this
records the printed local tests that certify the returned pivot size. -/
def SymmetricRookFirstPivotChoice
    (α a11 arr ω1 ωr : ℝ) (s : PivotSize) : Prop :=
  (|a11| ≥ α * ω1 ∧ s = PivotSize.one) ∨
  (|arr| ≥ α * ωr ∧ s = PivotSize.one) ∨
  (ω1 = ωr ∧ s = PivotSize.two)

-- ============================================================
-- Chapter 11.1.1  Complete pivoting (Bunch-Parlett)
-- ============================================================

/-- **Bunch-Parlett pivoting parameter** α = (1 + √17)/8.

    This minimizes the worst-case element growth by equating
    the growth bounds for 1×1 and 2×2 pivot steps.

    α is the positive root of 4α² − α − 1 = 0. -/
noncomputable def bunchParlettAlpha : ℝ := (1 + Real.sqrt 17) / 8

/-- **Bunch-Parlett α is a root of 4α² − α − 1 = 0**.

    This algebraic identity characterizes α = (1 + √17)/8 as the solution that
    minimizes the worst-case element growth. -/
theorem bunch_parlett_alpha_root :
    4 * bunchParlettAlpha ^ 2 - bunchParlettAlpha - 1 = 0 := by
  unfold bunchParlettAlpha
  have h17 : Real.sqrt 17 * Real.sqrt 17 = 17 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  field_simp
  nlinarith [h17]

/-- **Abstract Bunch-Parlett growth-factor interface** (Higham §11.1.1).

    The diagonal pivoting method with complete pivoting has
    growth factor bounded by (1 + α⁻¹)^{n−1} where α = (1+√17)/8.

    Since 1 + α⁻¹ ≈ 2.57, this gives growth ≤ (2.57)^{n−1}.

    A more detailed analysis by Bunch shows that the growth factor
    is no more than 3.07(n−1)^{0.446} times the LU complete pivoting bound.
    The hypothesis `hρ` supplies the pivot-growth analysis. -/
theorem bunch_parlett_growth_bound (n : ℕ) (_hn : 0 < n)
    (ρ_n : ℝ)
    -- Growth factor hypothesis: ρ_n ≤ (1 + α⁻¹)^{n-1}
    (hρ : ρ_n ≤ (1 + bunchParlettAlpha⁻¹) ^ (n - 1)) :
    ρ_n ≤ (1 + bunchParlettAlpha⁻¹) ^ (n - 1) :=
  hρ

/-- **Abstract Bunch-Parlett L-factor bound interface** (Higham §11.1.1).

    For the complete pivoting strategy, no element of CE⁻¹ (the
    multiplier block) exceeds max{1/α, 1/(1-α)} in absolute value.
    This bounds ‖L‖ independently of A.  The entrywise multiplier bound is
    supplied as `hL`. -/
theorem bunch_parlett_L_bound (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (c_bound : ℝ)
    (_hc : c_bound = max (1 / bunchParlettAlpha) (1 / (1 - bunchParlettAlpha)))
    (hL : ∀ i j : Fin n, |L i j| ≤ c_bound) :
    ∀ i j : Fin n, |L i j| ≤ c_bound :=
  hL

/-- **Multiplier bound for a 1×1 pivot** (Higham §11.1.1–§11.1.2).

    A 1×1 pivot `e` accepted by the Bunch–Parlett / Bunch–Kaufman test
    `α·ω ≤ |e|`, where `ω` bounds the magnitude of the off-pivot column entries
    `c`, produces subdiagonal multipliers `c / e` with `|c / e| ≤ 1/α`.

    This is the elementwise fact behind "no element of `CE⁻¹` exceeds
    `max{1/α, 1/(1-α)}`", hence `‖L‖` is bounded independently of `A`.  It is a
    genuine derivation from the pivot-acceptance test, not an assumed bound. -/
theorem oneByOne_multiplier_bound (c e ω α : ℝ)
    (hα : 0 < α) (hω : 0 < ω) (hc : |c| ≤ ω) (he : α * ω ≤ |e|) :
    |c / e| ≤ 1 / α := by
  have hαω : 0 < α * ω := mul_pos hα hω
  have hepos : 0 < |e| := lt_of_lt_of_le hαω he
  have hinv : (0 : ℝ) < 1 / α := by positivity
  have hstep : ω ≤ 1 / α * |e| := by
    have h1 := mul_le_mul_of_nonneg_left he (le_of_lt hinv)
    rwa [← mul_assoc, one_div_mul_cancel (ne_of_gt hα), one_mul] at h1
  rw [abs_div, div_le_iff₀ hepos]
  linarith [hc, hstep]

/-- **Element growth for a 1×1 Schur step** (Higham §11.1.1, and §11.1.2 cases
    (1)–(3)).  With `μ₀` bounding the magnitude of every active entry
    (`|b|, |c₁|, |c₂| ≤ μ₀`) and a 1×1 pivot `e` accepted under `α·μ₀ ≤ |e|`,
    the Schur-complement entry `b − c₁·c₂/e` satisfies
    `|b − c₁·c₂/e| ≤ (1 + 1/α)·μ₀`.  Iterating this per-step bound is the
    mechanism behind the growth-factor bound `ρₙ ≤ (1 + α⁻¹)^{n−1}`. -/
theorem oneByOne_schur_growth (b c1 c2 e μ0 α : ℝ)
    (hα : 0 < α) (hμ : 0 < μ0)
    (hb : |b| ≤ μ0) (hc1 : |c1| ≤ μ0) (hc2 : |c2| ≤ μ0)
    (he : α * μ0 ≤ |e|) :
    |b - c1 * c2 / e| ≤ (1 + 1 / α) * μ0 := by
  have hmult : |c2 / e| ≤ 1 / α :=
    oneByOne_multiplier_bound c2 e μ0 α hα hμ hc2 he
  have hcorr : |c1 * c2 / e| ≤ 1 / α * μ0 := by
    rw [mul_div_assoc, abs_mul]
    calc |c1| * |c2 / e|
        ≤ μ0 * (1 / α) := mul_le_mul hc1 hmult (abs_nonneg _) (le_of_lt hμ)
      _ = 1 / α * μ0 := by ring
  have htri : |b - c1 * c2 / e| ≤ |b| + |c1 * c2 / e| := by
    have h := abs_add_le b (-(c1 * c2 / e))
    simpa [sub_eq_add_neg, abs_neg] using h
  calc |b - c1 * c2 / e|
      ≤ |b| + |c1 * c2 / e| := htri
    _ ≤ μ0 + 1 / α * μ0 := add_le_add hb hcorr
    _ = (1 + 1 / α) * μ0 := by ring

/-- **2×2 complete-pivot determinant bound** (Higham §11.1.1).

    When complete pivoting selects a 2×2 pivot block
    `E = [[e₁₁, e₂₁], [e₂₁, e₂₂]]`, the off-diagonal entry has the maximal
    magnitude `μ₀` (`e₂₁² = μ₀²`), the diagonal entries are bounded by the best
    1×1 pivot `μ₁ ≤ α·μ₀`, and the determinant satisfies
    `det E = e₁₁e₂₂ − e₂₁² ≤ (α² − 1)·μ₀²`.  This is the printed estimate
    `det(E) ≤ μ₁² − μ₀² ≤ (α² − 1)μ₀²`. -/
theorem twoByTwo_completePivot_det_bound (e11 e22 e21 μ0 μ1 α : ℝ)
    (hμ1 : 0 ≤ μ1)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0) :
    e11 * e22 - e21 ^ 2 ≤ (α ^ 2 - 1) * μ0 ^ 2 := by
  have h1 : e11 * e22 ≤ μ1 * μ1 := by
    calc e11 * e22 ≤ |e11 * e22| := le_abs_self _
      _ = |e11| * |e22| := abs_mul _ _
      _ ≤ μ1 * μ1 := mul_le_mul he11 he22 (abs_nonneg _) hμ1
  have hαμ0 : 0 ≤ α * μ0 := le_trans hμ1 hμ1α
  have h2 : μ1 * μ1 ≤ (α * μ0) * (α * μ0) :=
    mul_le_mul hμ1α hμ1α hμ1 hαμ0
  nlinarith [h1, h2, he21]

/-- **2×2 complete-pivot determinant magnitude lower bound** (Higham §11.1.1).

    For `α ∈ [0, 1)`, the 2×2 pivot chosen by complete pivoting is nonsingular
    with `|det E| ≥ (1 − α²)·μ₀²`, the printed bound used to control `E⁻¹`. -/
theorem twoByTwo_completePivot_absdet_lower (e11 e22 e21 μ0 μ1 α : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0) :
    (1 - α ^ 2) * μ0 ^ 2 ≤ |e11 * e22 - e21 ^ 2| := by
  have hdet := twoByTwo_completePivot_det_bound e11 e22 e21 μ0 μ1 α
    hμ1 he11 he22 he21 hμ1α
  have hμ0sq : 0 ≤ μ0 ^ 2 := sq_nonneg μ0
  have hα2 : (0 : ℝ) ≤ 1 - α ^ 2 := by nlinarith [hα0, hα1]
  have hneg : e11 * e22 - e21 ^ 2 ≤ 0 := by
    nlinarith [hdet, mul_nonneg hα2 hμ0sq]
  rw [abs_of_nonpos hneg]
  nlinarith [hdet]

/-- Elementary bound `|x·y·z| ≤ p·q·r` from `|x| ≤ p`, `|y| ≤ q`, `|z| ≤ r`
    with `p, q ≥ 0`.  Used to bound the length-two inner products in the 2×2
    Schur-complement growth estimate. -/
theorem abs_triple_mul_le (x y z p q r : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hx : |x| ≤ p) (hy : |y| ≤ q) (hz : |z| ≤ r) :
    |x * y * z| ≤ p * q * r := by
  rw [abs_mul, abs_mul]
  have h1 : |x| * |y| ≤ p * q := mul_le_mul hx hy (abs_nonneg _) hp
  exact mul_le_mul h1 hz (abs_nonneg _) (mul_nonneg hp hq)

/-- **2×2 complete-pivoting element growth** (Higham §11.1.1, eq. (11.4)).

    The Schur-complement entry
    `ã = b − (c_i1(f₁₁c_j1 + f₁₂c_j2) + c_i2(f₂₁c_j1 + f₂₂c_j2))`,
    built from the inverse-block entries `f` bounded entrywise by
    `|f₁₁|, |f₂₂| ≤ αK` and `|f₁₂|, |f₂₁| ≤ K` with `K = 1/((1−α²)μ₀)`
    (`hK : (1−α²)·μ₀·K = 1`), and with every active entry bounded by `μ₀`,
    satisfies the printed bound `|ã| ≤ (1 + 2/(1−α))·μ₀`.

    Together with `oneByOne_schur_growth` (the `(1 + 1/α)μ₀` bound for a 1×1
    step) this gives both single-step growth bounds of §11.1.1, whose equality
    `(1 + 1/α)² = 1 + 2/(1−α)` fixes `α = (1+√17)/8`. -/
theorem twoByTwo_schur_growth
    (b ci1 ci2 cj1 cj2 f11 f12 f21 f22 μ0 α K : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1)
    (hb : |b| ≤ μ0)
    (hci1 : |ci1| ≤ μ0) (hci2 : |ci2| ≤ μ0)
    (hcj1 : |cj1| ≤ μ0) (hcj2 : |cj2| ≤ μ0)
    (hf11 : |f11| ≤ α * K) (hf12 : |f12| ≤ K)
    (hf21 : |f21| ≤ K) (hf22 : |f22| ≤ α * K) :
    |b - (ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2))|
      ≤ (1 + 2 / (1 - α)) * μ0 := by
  have hμ0 : 0 ≤ μ0 := le_of_lt hμ
  have hα2 : α ^ 2 < 1 := by nlinarith [hα0, hα1]
  have hden : 0 < (1 - α ^ 2) * μ0 := mul_pos (by linarith [hα2]) hμ
  have hK0 : 0 ≤ K := by nlinarith [hK, hden]
  have hαK : 0 ≤ α * K := mul_nonneg hα0 hK0
  have t1 : |ci1 * f11 * cj1| ≤ μ0 * (α * K) * μ0 :=
    abs_triple_mul_le ci1 f11 cj1 μ0 (α * K) μ0 hμ0 hαK hci1 hf11 hcj1
  have t2 : |ci1 * f12 * cj2| ≤ μ0 * K * μ0 :=
    abs_triple_mul_le ci1 f12 cj2 μ0 K μ0 hμ0 hK0 hci1 hf12 hcj2
  have t3 : |ci2 * f21 * cj1| ≤ μ0 * K * μ0 :=
    abs_triple_mul_le ci2 f21 cj1 μ0 K μ0 hμ0 hK0 hci2 hf21 hcj1
  have t4 : |ci2 * f22 * cj2| ≤ μ0 * (α * K) * μ0 :=
    abs_triple_mul_le ci2 f22 cj2 μ0 (α * K) μ0 hμ0 hαK hci2 hf22 hcj2
  have hexpand :
      ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2)
        = (ci1 * f11 * cj1) + (ci1 * f12 * cj2)
          + (ci2 * f21 * cj1) + (ci2 * f22 * cj2) := by ring
  have hcorr :
      |ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2)|
        ≤ 2 * μ0 ^ 2 * K * (1 + α) := by
    rw [hexpand]
    have htri :
        |(ci1 * f11 * cj1) + (ci1 * f12 * cj2)
            + (ci2 * f21 * cj1) + (ci2 * f22 * cj2)|
          ≤ |ci1 * f11 * cj1| + |ci1 * f12 * cj2|
            + |ci2 * f21 * cj1| + |ci2 * f22 * cj2| := by
      refine le_trans (abs_add_le _ _) ?_
      refine add_le_add (le_trans (abs_add_le _ _) ?_) (le_refl _)
      exact add_le_add (abs_add_le _ _) (le_refl _)
    have hsum : |ci1 * f11 * cj1| + |ci1 * f12 * cj2|
        + |ci2 * f21 * cj1| + |ci2 * f22 * cj2|
          ≤ 2 * μ0 ^ 2 * K * (1 + α) := by nlinarith [t1, t2, t3, t4]
    exact le_trans htri hsum
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hid : 2 * μ0 ^ 2 * K * (1 + α) = 2 * μ0 / (1 - α) := by
    rw [eq_div_iff (ne_of_gt h1α)]
    nlinarith [hK]
  have hfinal :
      |b - (ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2))|
        ≤ μ0 + 2 * μ0 / (1 - α) := by
    have htri2 :
        |b - (ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2))|
          ≤ |b|
            + |ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2)| := by
      have h := abs_add_le b
        (-(ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2)))
      rwa [← sub_eq_add_neg, abs_neg] at h
    calc |b - (ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2))|
        ≤ |b|
          + |ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2)| := htri2
      _ ≤ μ0 + 2 * μ0 ^ 2 * K * (1 + α) := add_le_add hb hcorr
      _ = μ0 + 2 * μ0 / (1 - α) := by rw [hid]
  have hrhs : (1 + 2 / (1 - α)) * μ0 = μ0 + 2 * μ0 / (1 - α) := by
    field_simp
  rw [hrhs]
  exact hfinal

-- ============================================================
-- Chapter 11.1.2  Partial pivoting (Bunch-Kaufman)
-- ============================================================

/-- **Abstract Bunch-Kaufman stability interface** (Higham §11.1.2).

    Same α = (1+√17)/8 as complete pivoting, but requires only
    O(n²) comparisons (searches at most two columns per stage).

    The growth factor is still bounded by (2.57)^{n−1},
    though no example is known where this bound is attained.

    The stability result for partial pivoting:
      ‖|L̂||D̂||L̂^T|‖_M ≤ 36n · ρ_n · ‖A‖_M

    The hypothesis `hstab` supplies the pivoting/stability analysis. -/
theorem bunch_kaufman_stability (n : ℕ)
    (A L_hat D_hat : Fin n → Fin n → ℝ)
    (ρ_n : ℝ)
    (maxNorm_A : ℝ) (_hmA : 0 ≤ maxNorm_A)
    -- Maximum entry norm bounds
    (_hA_norm : ∀ i j : Fin n, |A i j| ≤ maxNorm_A)
    -- The stability bound as hypothesis
    (hstab : ∀ i j : Fin n,
      ∑ k₁ : Fin n, ∑ k₂ : Fin n,
        |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂| ≤
      36 * ↑n * ρ_n * maxNorm_A) :
    ∀ i j : Fin n,
      ∑ k₁ : Fin n, ∑ k₂ : Fin n,
        |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂| ≤
      36 * ↑n * ρ_n * maxNorm_A :=
  hstab

/-- **Abstract Bunch-Kaufman solve backward-error interface**
    (Higham §11.1.2, Higham [559, 1995]).

    The computed solution to Ax = b via diagonal pivoting with
    partial pivoting satisfies:
      (A + ΔA) x̂ = b  with  |ΔA| ≤ p₂(n) · u · |L̂| · |D̂| · |L̂^T|

    where p₂ is a linear polynomial in n.  The hypothesis `hsolve` supplies
    the detailed solve analysis. -/
theorem bunch_kaufman_solve_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat D_hat : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (b x_hat : Fin n → ℝ)
    (_hBLDLT : BlockLDLTBackwardError n A L_hat D_hat σ (gamma fp n))
    (ρ_n maxNorm_A : ℝ)
    -- Growth + stability bound
    (_hstab : ∀ i j : Fin n,
      ∑ k₁ : Fin n, ∑ k₂ : Fin n,
        |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂| ≤
      36 * ↑n * ρ_n * maxNorm_A)
    -- The solve backward error bound
    (hsolve : ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        gamma fp n * 36 * ↑n * ρ_n * maxNorm_A) ∧
      (∀ i, ∑ j : Fin n, (A (σ i) (σ j) + ΔA i j) *
        x_hat j = b (σ i))) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        gamma fp n * 36 * ↑n * ρ_n * maxNorm_A) ∧
      (∀ i, ∑ j : Fin n, (A (σ i) (σ j) + ΔA i j) *
        x_hat j = b (σ i)) :=
  hsolve

-- ============================================================
-- Chapter 11.1.4  Tridiagonal symmetric matrices
-- ============================================================

/-- Bunch's symmetric-tridiagonal pivoting parameter from Algorithm 11.6,
`alpha = (sqrt 5 - 1)/2`. -/
noncomputable def bunchTridiagonalAlpha : ℝ := (Real.sqrt 5 - 1) / 2

/-- The tridiagonal pivoting parameter satisfies `alpha^2 + alpha - 1 = 0`. -/
theorem bunch_tridiagonal_alpha_root :
    bunchTridiagonalAlpha ^ 2 + bunchTridiagonalAlpha - 1 = 0 := by
  unfold bunchTridiagonalAlpha
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  field_simp
  nlinarith [h5]

/-- Algorithm 11.6 source decision predicate for Bunch's tridiagonal pivot-size
strategy. -/
def BunchTridiagonalPivotChoice
    (σ a11 a21 : ℝ) (s : PivotSize) : Prop :=
  (σ * |a11| ≥ bunchTridiagonalAlpha * a21 ^ 2 ∧ s = PivotSize.one) ∨
  (σ * |a11| < bunchTridiagonalAlpha * a21 ^ 2 ∧ s = PivotSize.two)

-- ============================================================
-- Chapter 11.3  Skew-symmetric block LDL^T
-- ============================================================

/-- Algorithm 11.9 source decision predicate for Bunch's skew-symmetric pivoting
strategy at the first stage. -/
def SkewBunchPivotChoice (firstColumnTailZero : Prop)
    (pivotMagnitude : ℝ) (s : PivotSize) : Prop :=
  (firstColumnTailZero ∧ s = PivotSize.one) ∨
  (¬ firstColumnTailZero ∧ 0 < pivotMagnitude ∧ s = PivotSize.two)

end LeanFpAnalysis.FP
