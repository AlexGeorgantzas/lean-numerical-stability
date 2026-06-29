-- Algorithms/Underdetermined/UnderdeterminedSpec.lean
--
-- Solution methods and perturbation theory for underdetermined systems
-- (Higham §21.1-§21.2).
--
-- An underdetermined system Ax = b with A ∈ ℝ^{m×n}, m < n, has
-- infinitely many solutions. The minimum 2-norm solution is
-- x_LS = Aᵀ(AAᵀ)⁻¹b = A⁺b.
--
-- Two solution methods use the QR factorization Aᵀ = Q[R; 0]:
-- - Q method: solve Rᵀy₁ = b, form x = Q[y₁; 0]ᵀ
-- - SNE method: solve RᵀRy = b, form x = Aᵀy
--
-- Theorem 21.1 (Demmel-Higham): Componentwise perturbation bound
-- for the minimum-norm solution.
-- Lemma 21.2 (Kielbasiński-Schwetlick): Asymmetric normal equation
-- perturbations can be symmetrized without increasing the bound.

import Mathlib.Data.Real.Basic
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §21.1  Minimum-norm solution specification
-- ============================================================

/-- **Minimum 2-norm solution of an underdetermined system** (Higham §21.1).

    For Ax = b with A ∈ ℝ^{m×n} (m < n), the minimum-norm solution is
    x_LS = Aᵀ(AAᵀ)⁻¹b. In the QR factorization framework with
    Aᵀ = Q[R; 0], this becomes x_LS = Q[R⁻ᵀb; 0].

    Since A is rectangular, we work with the m×m Gram matrix AAᵀ.
    The structure captures: (AAᵀ)⁻¹ exists (A has full row rank),
    and x solves the normal equations AAᵀy = b with x = Aᵀy. -/
structure MinNormSolution (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ) : Prop where
  /-- AAᵀ is invertible. -/
  gram_inv : IsInverse m AAT AAT_inv
  /-- y solves the normal equations AAᵀy = b. -/
  normal_eq : ∀ i, matMulVec m AAT y i = b i

/-- Euclidean norm of row `i` of a rectangular matrix. -/
noncomputable def rectRowNorm2 {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : ℝ :=
  vecNorm2 (fun j : Fin n => A i j)

/-- A rectangular row 2-norm is nonnegative. -/
theorem rectRowNorm2_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : 0 ≤ rectRowNorm2 A i :=
  vecNorm2_nonneg _

/-- Higham, 2nd ed., Chapter 21, Section 21.1:
    exact minimum 2-norm solution predicate for a rectangular
    underdetermined system `A x = b`. -/
structure RectMinNormSolution (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop where
  /-- The candidate solves the rectangular system. -/
  system_eq : rectMatMulVec A x = b
  /-- The candidate has no larger Euclidean norm than any other solution. -/
  min_norm : ∀ z : Fin n → ℝ, rectMatMulVec A z = b → vecNorm2 x ≤ vecNorm2 z

/-- Rectangular Gram matrix `A Aᵀ` for an underdetermined system. -/
noncomputable def rectGram {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    Fin m → Fin m → ℝ :=
  fun i j => ∑ k : Fin n, A i k * A j k

/-- Transpose-times-vector action `Aᵀ y` for a rectangular matrix. -/
noncomputable def rectTransposeMulVec {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin m, A i j * y i

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    every vector of the form `Aᵀ y` is orthogonal to the nullspace of `A`.
    This is the algebraic orthogonality fact behind the minimum-norm
    characterization of `Aᵀ(AAᵀ)⁻¹b`. -/
theorem higham21_eq21_4_rect_transpose_nullspace_orthogonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ)
    (hz : rectMatMulVec A z = (0 : Fin m → ℝ)) :
    ∑ j : Fin n, rectTransposeMulVec A y j * z j = 0 := by
  unfold rectTransposeMulVec
  calc
    ∑ j : Fin n, (∑ i : Fin m, A i j * y i) * z j
        = ∑ j : Fin n, ∑ i : Fin m, (A i j * y i) * z j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ j : Fin n, (A i j * y i) * z j := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin m, y i * rectMatMulVec A z i := by
            apply Finset.sum_congr rfl
            intro i _
            unfold rectMatMulVec
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = 0 := by
            rw [hz]
            simp

/-- A rectangular-system solution that is orthogonal to the nullspace of `A`
    is a minimum Euclidean-norm solution. -/
theorem rectMinNormSolution_of_system_eq_and_nullspace_orthogonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hx : rectMatMulVec A x = b)
    (horth : ∀ e : Fin n → ℝ,
      rectMatMulVec A e = (0 : Fin m → ℝ) →
        (∑ j : Fin n, x j * e j) = 0) :
    RectMinNormSolution m n A b x := by
  constructor
  · exact hx
  · intro z hz
    let e : Fin n → ℝ := fun j => z j - x j
    have he_kernel : rectMatMulVec A e = (0 : Fin m → ℝ) := by
      unfold e
      rw [rectMatMulVec_sub, hz, hx]
      ext i
      simp
    have hinner : (∑ j : Fin n, x j * e j) = 0 :=
      horth e he_kernel
    have hz_decomp : z = fun j : Fin n => x j + e j := by
      ext j
      unfold e
      ring
    have hpyth : vecNorm2Sq z = vecNorm2Sq x + vecNorm2Sq e := by
      rw [hz_decomp]
      simpa [finiteVecNorm2Sq_fin] using
        (finiteVecNorm2Sq_add_of_inner_eq_zero x e hinner)
    unfold vecNorm2
    exact Real.sqrt_le_sqrt
      (by
        rw [hpyth]
        exact le_add_of_nonneg_right (vecNorm2Sq_nonneg e))

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    if a vector of the form `Aᵀ y` solves `A x = b`, then it is the
    minimum 2-norm solution of the rectangular underdetermined system.
    This closes the minimum-norm direction of the normal-equation formula;
    the explicit inverse/pseudoinverse construction remains separate. -/
theorem higham21_eq21_4_rect_transpose_min_norm_of_solves {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin m → ℝ)
    (hsolve : rectMatMulVec A (rectTransposeMulVec A y) = b) :
    RectMinNormSolution m n A b (rectTransposeMulVec A y) :=
  rectMinNormSolution_of_system_eq_and_nullspace_orthogonal
    A b (rectTransposeMulVec A y) hsolve
    (fun e he =>
      higham21_eq21_4_rect_transpose_nullspace_orthogonal A y e he)

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    algebraic normal-equation identity `A (Aᵀ y) = (A Aᵀ) y`. -/
theorem rectMatMulVec_rectTransposeMulVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin m → ℝ) :
    rectMatMulVec A (rectTransposeMulVec A y) =
      matMulVec m (rectGram A) y := by
  ext i
  unfold rectMatMulVec rectTransposeMulVec matMulVec rectGram
  calc
    (∑ j : Fin n, A i j * ∑ r : Fin m, A r j * y r)
        = ∑ j : Fin n, ∑ r : Fin m, A i j * (A r j * y r) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
    _ = ∑ r : Fin m, ∑ j : Fin n, A i j * (A r j * y r) := by
            rw [Finset.sum_comm]
    _ = ∑ r : Fin m, (∑ j : Fin n, A i j * A r j) * y r := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    if `y` solves `(A Aᵀ)y = b`, then `Aᵀy` solves `A x = b`. -/
theorem rectTransposeMulVec_solves_of_gram_normal_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hAAT : ∀ i j : Fin m, AAT i j = rectGram A i j)
    (hy : ∀ i : Fin m, matMulVec m AAT y i = b i) :
    rectMatMulVec A (rectTransposeMulVec A y) = b := by
  ext i
  rw [rectMatMulVec_rectTransposeMulVec]
  calc
    matMulVec m (rectGram A) y i = matMulVec m AAT y i := by
      unfold matMulVec
      apply Finset.sum_congr rfl
      intro j _
      rw [(hAAT i j).symm]
    _ = b i := hy i

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    source-facing wrapper for the normal-equation direction of
    `x_LS = Aᵀ(AAᵀ)⁻¹b`.  The minimum-norm and pseudoinverse parts remain
    separate selected targets. -/
theorem higham21_eq21_4_rect_transpose_solves {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hAAT : ∀ i j : Fin m, AAT i j = rectGram A i j)
    (hy : ∀ i : Fin m, matMulVec m AAT y i = b i) :
    rectMatMulVec A (rectTransposeMulVec A y) = b :=
  rectTransposeMulVec_solves_of_gram_normal_eq A AAT b y hAAT hy

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    source-facing normal-equation minimum-norm wrapper.  If `y` solves
    `(A Aᵀ)y = b`, then the formed vector `Aᵀy` is an exact minimum
    2-norm solution of `A x = b`.  The explicit inverse/pseudoinverse
    construction remains a separate selected target. -/
theorem higham21_eq21_4_rect_transpose_min_norm_of_gram_normal_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hAAT : ∀ i j : Fin m, AAT i j = rectGram A i j)
    (hy : ∀ i : Fin m, matMulVec m AAT y i = b i) :
    RectMinNormSolution m n A b (rectTransposeMulVec A y) :=
  higham21_eq21_4_rect_transpose_min_norm_of_solves A b y
    (rectTransposeMulVec_solves_of_gram_normal_eq A AAT b y hAAT hy)

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.5):
    source-facing wrapper for the SNE formation step.  Once the seminormal
    equation matrix is identified with `A Aᵀ`, solving that Gram system and
    forming `x = Aᵀ y` gives a solution of the rectangular system `A x = b`.
    This does not assert the full minimum-norm or QR-derived stability result. -/
theorem higham21_eq21_5_sne_rect_transpose_solution {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (SNE : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (x : Fin n → ℝ)
    (hSNE : ∀ i j : Fin m, SNE i j = rectGram A i j)
    (hy : ∀ i : Fin m, matMulVec m SNE y i = b i)
    (hx : x = rectTransposeMulVec A y) :
    rectMatMulVec A x = b := by
  rw [hx]
  exact rectTransposeMulVec_solves_of_gram_normal_eq A SNE b y hSNE hy

-- ============================================================
-- §21.2  Theorem 21.1: Demmel-Higham perturbation bound
-- ============================================================

/-- **Theorem 21.1** (Demmel and Higham): Componentwise perturbation
    of the minimum 2-norm solution to an underdetermined system.

    Let A ∈ ℝ^{m×n} (m ≤ n) be of full rank, and let x, y be the
    minimum 2-norm solutions to Ax = b and (A+ΔA)y = b+Δb. Then:

    ‖x−y‖/‖x‖ ≤ (‖|I−A⁺A|·Eᵀ·|A⁺ᵀx|‖ + ‖|A⁺|·(f+E|x|)‖)·ε/‖x‖ + O(ε²)

    where |ΔA| ≤ εE, |Δb| ≤ εf.

    Special cases (eqs. 21.8-21.9):
    - E = |A|H, f = |b|: bound involves cond₂(A) = ‖|A⁺||A|‖₂
    - Normwise: ‖x−y‖₂/‖x‖₂ ≤ min{3,n−m+2}(mn)^{1/2}κ₂(A)ε + O(ε²)

    Recorded as an abstract predicate until the rectangular pseudoinverse
    perturbation expansion is fully formalized. -/
structure DemmelHighamPerturbation (m : ℕ)
    (x y : Fin m → ℝ) (kappa eps : ℝ)
    (sol_bound : ℝ) : Prop where
  /-- κ₂(A) > 0. -/
  kappa_pos : 0 < kappa
  /-- ε is nonnegative. -/
  eps_nonneg : 0 ≤ eps
  /-- The perturbation is small enough. -/
  small_pert : kappa * eps < 1
  /-- Forward error bound (normwise form, eq. 21.9):
      ‖x−y‖₂ ≤ sol_bound. -/
  bound : ∀ i, |y i - x i| ≤ sol_bound

-- ============================================================
-- §21.2  Lemma 21.2: Kielbasiński-Schwetlick symmetrization
-- ============================================================

/-- **Lemma 21.2** (Kielbasiński and Schwetlick): Perturbation symmetrization
    for underdetermined normal equations.

    If x̄ satisfies (A+ΔA₁)x̄ = b and x̄ = (A+ΔA₂)ᵀȳ, then there
    exists a single ΔA with ΔA = ΔA₁G₁ + ΔA₂G₂ (G₁+G₂=I) such that
    x̄ is the minimum 2-norm solution to (A+ΔA)x = b.

    The normwise bound satisfies: ‖ΔA‖_p ≤ (‖ΔA₁‖²_p + ‖ΔA₂‖²_p)^{1/2}.

    This is the underdetermined analogue of Lemma 20.6.
    Recorded as an abstract predicate until the rectangular projector
    construction is fully formalized. -/
structure KielbasinskiSchwetlickUndet (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin m → ℝ)
    (eps1 eps2 : ℝ) : Prop where
  /-- Perturbation bounds are nonneg. -/
  eps_nonneg : 0 ≤ eps1 ∧ 0 ≤ eps2
  /-- There exists a symmetrized perturbation ΔG to the Gram system
      with ‖ΔG‖ ≤ (eps1² + eps2²)^{1/2} such that x̂ is the
      minimum-norm solution to a nearby system. -/
  symmetrized : ∃ (ΔG : Fin m → Fin m → ℝ),
    frobNorm ΔG ≤
      Real.sqrt (eps1 ^ 2 + eps2 ^ 2) ∧
    (∀ i, matMulVec m (fun a b => AAT a b + ΔG a b) x_hat i = b i)

end LeanFpAnalysis.FP
