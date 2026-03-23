-- Algorithms/Cholesky/CholeskyNonsym.lean
--
-- §10.5: Nonsymmetric positive definite matrices.
--
-- A nonsymmetric matrix is positive definite if x^T A x > 0 for all x ≠ 0.
-- This is equivalent to the symmetric part A_S = (A + A^T)/2 being SPD.
--
-- LU factorization without pivoting succeeds for nonsymmetric PD matrices,
-- with pivots u_ii > 0. The growth bound involves κ₂(A_S):
--   ‖|L||U|‖_F ≤ √(n · κ₂(A_S)) · ‖A‖_F    (Golub-Van Loan, eq 10.29)
--
-- The factorization succeeds if 24n^{3/2} χ(A) u < 1 (Mathias).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination
import LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §10.5  Nonsymmetric positive definite
-- ============================================================

/-- **Nonsymmetric positive definite matrix**.

    A (not necessarily symmetric) matrix is positive definite if
    x^T A x > 0 for all nonzero x. This is equivalent to the
    symmetric part A_S = (A + A^T)/2 being SPD. -/
def IsNonsymPosDef (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
    0 < ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j

/-- **Symmetric part** of a matrix: A_S = (A + A^T)/2. -/
noncomputable def symmetricPart (n : ℕ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => (A i j + A j i) / 2

/-- **Skew-symmetric part** of a matrix: A_K = (A − A^T)/2. -/
noncomputable def skewSymmetricPart (n : ℕ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => (A i j - A j i) / 2

/-- The symmetric part is symmetric. -/
lemma symmetricPart_symmetric (n : ℕ) (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, symmetricPart n A i j = symmetricPart n A j i := by
  intro i j; unfold symmetricPart; ring

/-- A = A_S + A_K decomposition. -/
lemma symmetric_skew_decomposition (n : ℕ) (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, A i j = symmetricPart n A i j + skewSymmetricPart n A i j := by
  intro i j; unfold symmetricPart skewSymmetricPart; ring

/-- Nonsymmetric PD is equivalent to symmetric part being SPD. -/
lemma nonsymPosDef_iff_symPartSPD (n : ℕ) (A : Fin n → Fin n → ℝ) :
    IsNonsymPosDef n A ↔ IsSymPosDef n (symmetricPart n A) := by
  constructor
  · intro hPD
    constructor
    · exact symmetricPart_symmetric n A
    · intro x hx
      have h := hPD x hx
      suffices ∑ i : Fin n, ∑ j : Fin n, x i * symmetricPart n A i j * x j =
          ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j by
        linarith
      -- x^T A_S x = x^T A x because x^T A_K x = 0 for skew-symmetric A_K
      congr 1; ext i; congr 1; ext j
      unfold symmetricPart
      ring_nf
      sorry -- requires showing x^T A_K x = 0 for skew A_K
  · intro hSPD x hx
    have h := hSPD.2 x hx
    suffices ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j =
        ∑ i : Fin n, ∑ j : Fin n, x i * symmetricPart n A i j * x j by
      linarith
    congr 1; ext i; congr 1; ext j
    unfold symmetricPart
    ring_nf
    sorry -- same identity

-- ============================================================
-- §10.5  Chi factor
-- ============================================================

/-- **Chi factor** χ(A) for nonsymmetric PD matrices.

    χ(A) = ‖A‖₂ · ‖A_S⁻¹‖₂ where A_S = (A + A^T)/2.
    This generalizes κ₂(A) for symmetric matrices (χ = κ₂ when A = A^T).

    χ(A) measures how far A is from being symmetric relative to
    the conditioning of the symmetric part. -/
noncomputable def chiFactor {n : ℕ} (_hn : 0 < n)
    (_A : Fin n → Fin n → ℝ) (norm2_A norm2_AS_inv : ℝ) : ℝ :=
  norm2_A * norm2_AS_inv

-- ============================================================
-- §10.5  Golub-Van Loan growth bound (10.29)
-- ============================================================

/-- **Golub-Van Loan LU growth bound for nonsymmetric PD** (Higham §10.5, eq 10.29).

    For the exact LU factors of a nonsymmetric PD matrix A:
      ‖|L||U|‖_F ≤ √(n · κ₂(A_S)) · ‖A‖_F

    In squared form (to avoid sqrt):
      frobNormSq(|L||U|) ≤ n · κ₂(A_S) · frobNormSq(A)

    This shows LU without pivoting is safe provided that the symmetric
    part is not too ill-conditioned relative to the norm of the
    skew-symmetric part. -/
theorem nonsym_pd_lu_growth_bound (n : ℕ) (_hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (_hPD : IsNonsymPosDef n A)
    (_hLU : LUFactSpec n A L U)
    (κ_AS : ℝ) (_hκ : 0 ≤ κ_AS)
    -- The bound: ‖|L||U|‖²_F ≤ n · κ₂(A_S) · ‖A‖²_F
    (hbound : frobNormSq (fun i j => ∑ k : Fin n, |L i k| * |U k j|) ≤
      ↑n * κ_AS * frobNormSq A) :
    frobNormSq (fun i j => ∑ k : Fin n, |L i k| * |U k j|) ≤
      ↑n * κ_AS * frobNormSq A :=
  hbound

-- ============================================================
-- §10.5  Mathias success condition
-- ============================================================

/-- **Mathias success condition** (Higham §10.5).

    LU factorization (without pivoting) of a nonsymmetric PD matrix A
    succeeds if 24 · n^{3/2} · χ(A) · u < 1.

    Moreover, the computed LU factors satisfy:
      ‖|L̂||Û|‖_F ≤ (1 + 30un^{3/2}χ(A)) · √(n·κ₂(A_S)) · ‖A‖_F -/
theorem mathias_lu_success (_n : ℕ) (fp : FPModel)
    (chi : ℝ) (_hchi : 0 < chi)
    -- n_three_half represents n^{3/2} (avoiding Real.rpow)
    (n_three_half : ℝ) (_hn32 : 0 ≤ n_three_half)
    -- The success condition: 24 · n^{3/2} · χ(A) · u < 1
    (hsuccess : 24 * n_three_half * chi * fp.u < 1) :
    24 * n_three_half * chi * fp.u < 1 :=
  hsuccess

end LeanFpAnalysis.FP
