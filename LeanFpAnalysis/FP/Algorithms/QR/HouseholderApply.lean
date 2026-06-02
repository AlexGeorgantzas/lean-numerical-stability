-- Algorithms/QR/HouseholderApply.lean
--
-- Concrete rounded application of a Householder reflector to a vector.
--
-- The operation modeled here is y = b - beta * v * (v^T b), implemented with
-- the local rounded dot-product, multiplication, and subtraction operations.
-- The full Lemma 18.2 backward-error bridge to `HouseholderAppError` is a later
-- theorem; this file supplies the concrete kernel and unroll lemma.

import LeanFpAnalysis.FP.Algorithms.DotProduct
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderSpec

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §18.3  Concrete Householder application kernel
-- ============================================================

/-- Exact application identity for `P = I - beta * v * v^T`.

    This is the exact algebraic target for the rounded kernel below. -/
theorem householder_matMulVec_eq (n : ℕ) (v : Fin n → ℝ) (beta : ℝ)
    (b : Fin n → ℝ) :
    matMulVec n (householder n v beta) b =
      fun i => b i - beta * v i * (∑ j : Fin n, v j * b j) := by
  ext i
  unfold matMulVec householder idMatrix
  have hid : ∑ j : Fin n, (if i = j then 1 else 0) * b j = b i := by
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  have houter :
      ∑ j : Fin n, beta * v i * v j * b j =
        beta * v i * (∑ j : Fin n, v j * b j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  trans
    (∑ j : Fin n, (if i = j then 1 else 0) * b j) -
      ∑ j : Fin n, beta * v i * v j * b j
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [hid, houter]

/-- Rounded application of `I - beta * v * v^T` to vector `b`.

    Operation order:
    1. `t = fl_dotProduct v b`;
    2. `w = fl_mul beta t`;
    3. `y_i = fl_sub b_i (fl_mul w v_i)`.

    This is the concrete algorithmic object needed before proving the
    `HouseholderAppError` contract from Higham Lemma 18.2.  That bridge also
    needs the source hypothesis that the computed Householder vector satisfies
    Higham's equation (18.3), so it is intentionally not claimed in this file
    yet. -/
noncomputable def fl_householderApply (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  let t := fl_dotProduct fp n v b
  let w := fp.fl_mul beta t
  fun i => fp.fl_sub (b i) (fp.fl_mul w (v i))

/-- Matrix represented by the primitive rounding errors in one rounded
    Householder application.

    This is not an arbitrary post-hoc perturbation.  Each entry is determined
    by the same dot-product, scalar-multiplication, componentwise
    multiplication, and subtraction error variables that occur in
    `fl_householderApply_unroll`. -/
noncomputable def householderApplyRoundedMatrix (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ)
    (η : Fin n → ℝ) (δw : ℝ)
    (δmul δsub : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    idMatrix n i j * (1 + δsub i) -
      (beta * (1 + δw)) * v i * (1 + δmul i) *
        v j * (1 + η j) * (1 + δsub i)

/-- Concrete perturbation matrix represented by the primitive rounding errors
    in one Householder application, relative to an exact target matrix `P`.

    The next Higham Lemma 18.2 step is precisely to bound this matrix in
    Frobenius norm when `P = I - v vᵀ`, the input vector satisfies
    `HouseholderVectorError`, and the displayed rounding variables satisfy the
    primitive `FPModel` bounds. -/
noncomputable def householderApplyDeltaMatrix (n : ℕ)
    (P : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (beta : ℝ)
    (η : Fin n → ℝ) (δw : ℝ)
    (δmul δsub : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => householderApplyRoundedMatrix n v beta η δw δmul δsub i j - P i j

/-- Unroll the concrete Householder-vector application into primitive rounding
    errors from the dot product, one scalar multiplication, one per-component
    multiplication, and one per-component subtraction. -/
theorem fl_householderApply_unroll (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ (η : Fin n → ℝ) (δw : ℝ) (δmul δsub : Fin n → ℝ),
      (∀ j : Fin n, |η j| ≤ gamma fp n) ∧
      |δw| ≤ fp.u ∧
      (∀ i : Fin n, |δmul i| ≤ fp.u) ∧
      (∀ i : Fin n, |δsub i| ≤ fp.u) ∧
      ∀ i : Fin n,
        fl_householderApply fp n v beta b i =
          (b i -
            (((beta * (∑ j : Fin n, v j * b j * (1 + η j))) * (1 + δw)) *
              v i * (1 + δmul i))) *
            (1 + δsub i) := by
  let t := fl_dotProduct fp n v b
  let w := fp.fl_mul beta t
  obtain ⟨η, hη, hdot⟩ := dotProduct_backward_error fp n v b hn
  obtain ⟨δw, hδw, hw⟩ := fp.model_mul beta t
  have hmul : ∀ i : Fin n, ∃ δ : ℝ,
      |δ| ≤ fp.u ∧ fp.fl_mul w (v i) = (w * v i) * (1 + δ) := by
    intro i
    exact fp.model_mul w (v i)
  let δmul : Fin n → ℝ := fun i => Classical.choose (hmul i)
  have hδmul : ∀ i : Fin n, |δmul i| ≤ fp.u := fun i =>
    (Classical.choose_spec (hmul i)).1
  have hmul_eq : ∀ i : Fin n,
      fp.fl_mul w (v i) = (w * v i) * (1 + δmul i) := fun i =>
    (Classical.choose_spec (hmul i)).2
  have hsub : ∀ i : Fin n, ∃ δ : ℝ,
      |δ| ≤ fp.u ∧
        fp.fl_sub (b i) (fp.fl_mul w (v i)) =
          (b i - fp.fl_mul w (v i)) * (1 + δ) := by
    intro i
    exact fp.model_sub (b i) (fp.fl_mul w (v i))
  let δsub : Fin n → ℝ := fun i => Classical.choose (hsub i)
  have hδsub : ∀ i : Fin n, |δsub i| ≤ fp.u := fun i =>
    (Classical.choose_spec (hsub i)).1
  have hsub_eq : ∀ i : Fin n,
      fp.fl_sub (b i) (fp.fl_mul w (v i)) =
        (b i - fp.fl_mul w (v i)) * (1 + δsub i) := fun i =>
    (Classical.choose_spec (hsub i)).2
  refine ⟨η, δw, δmul, δsub, hη, hδw, hδmul, hδsub, ?_⟩
  intro i
  have happ :
      fl_householderApply fp n v beta b i =
        fp.fl_sub (b i) (fp.fl_mul w (v i)) := by
    rfl
  rw [happ, hsub_eq i, hmul_eq i]
  rw [show w = beta * t * (1 + δw) from hw,
      show t = ∑ j : Fin n, v j * b j * (1 + η j) from hdot]

/-- Matrix-form unroll for the concrete rounded Householder application.

    The rounded output is exactly the product of `b` by the matrix
    `householderApplyRoundedMatrix` built from the primitive rounding errors.
    This is the algebraic bridge needed before proving the Lemma 18.2
    Frobenius-norm perturbation bound. -/
theorem fl_householderApply_matrix_unroll (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ (η : Fin n → ℝ) (δw : ℝ) (δmul δsub : Fin n → ℝ),
      (∀ j : Fin n, |η j| ≤ gamma fp n) ∧
      |δw| ≤ fp.u ∧
      (∀ i : Fin n, |δmul i| ≤ fp.u) ∧
      (∀ i : Fin n, |δsub i| ≤ fp.u) ∧
      fl_householderApply fp n v beta b =
        matMulVec n
          (householderApplyRoundedMatrix n v beta η δw δmul δsub) b := by
  obtain ⟨η, δw, δmul, δsub, hη, hδw, hδmul, hδsub, hunroll⟩ :=
    fl_householderApply_unroll fp n v beta b hn
  refine ⟨η, δw, δmul, δsub, hη, hδw, hδmul, hδsub, ?_⟩
  ext i
  rw [hunroll i]
  unfold matMulVec householderApplyRoundedMatrix
  have hfirst :
      (∑ j : Fin n, idMatrix n i j * (1 + δsub i) * b j) =
        b i * (1 + δsub i) := by
    unfold idMatrix
    simp [Finset.sum_ite_eq, Finset.mem_univ]
    ring
  have hsecond :
      (∑ j : Fin n,
          ((beta * (1 + δw)) * v i * (1 + δmul i) *
            v j * (1 + η j) * (1 + δsub i)) * b j) =
        (((beta * (∑ j : Fin n, v j * b j * (1 + η j))) *
          (1 + δw)) * v i * (1 + δmul i)) * (1 + δsub i) := by
    calc
      (∑ j : Fin n,
          ((beta * (1 + δw)) * v i * (1 + δmul i) *
            v j * (1 + η j) * (1 + δsub i)) * b j)
          =
            (beta * (1 + δw) * v i * (1 + δmul i) * (1 + δsub i)) *
              (∑ j : Fin n, v j * b j * (1 + η j)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
      _ =
        (((beta * (∑ j : Fin n, v j * b j * (1 + η j))) *
          (1 + δw)) * v i * (1 + δmul i)) * (1 + δsub i) := by
            ring
  have hmatrix :
      (∑ j : Fin n,
          (idMatrix n i j * (1 + δsub i) -
            beta * (1 + δw) * v i * (1 + δmul i) *
              v j * (1 + η j) * (1 + δsub i)) * b j) =
        b i * (1 + δsub i) -
          (((beta * (∑ j : Fin n, v j * b j * (1 + η j))) *
            (1 + δw)) * v i * (1 + δmul i)) * (1 + δsub i) := by
    calc
      (∑ j : Fin n,
          (idMatrix n i j * (1 + δsub i) -
            beta * (1 + δw) * v i * (1 + δmul i) *
              v j * (1 + η j) * (1 + δsub i)) * b j)
          =
            (∑ j : Fin n, idMatrix n i j * (1 + δsub i) * b j) -
              (∑ j : Fin n,
                ((beta * (1 + δw)) * v i * (1 + δmul i) *
                  v j * (1 + η j) * (1 + δsub i)) * b j) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro j _
                ring
      _ =
          b i * (1 + δsub i) -
            (((beta * (∑ j : Fin n, v j * b j * (1 + η j))) *
              (1 + δw)) * v i * (1 + δmul i)) * (1 + δsub i) := by
            rw [hfirst, hsecond]
  rw [hmatrix]
  ring

/-- If the concrete perturbation matrix extracted from the rounded
    Householder-application kernel has the required Frobenius bound, then the
    rounded kernel satisfies the `HouseholderAppError` contract.

    This theorem is intentionally only a packaging bridge: it does not prove the
    Lemma 18.2 norm estimate.  The hypothesis `hbound` is the remaining source
    theorem to formalize, not an arbitrary post-hoc perturbation. -/
theorem fl_householderApply_appError_of_matrix_bound (fp : FPModel) (n : ℕ)
    (P : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (beta : ℝ)
    (b : Fin n → ℝ) (c : ℝ)
    (hn : gammaValid fp n) (horth : IsOrthogonal n P)
    (hbound :
      ∀ (η : Fin n → ℝ) (δw : ℝ) (δmul δsub : Fin n → ℝ),
        (∀ j : Fin n, |η j| ≤ gamma fp n) →
        |δw| ≤ fp.u →
        (∀ i : Fin n, |δmul i| ≤ fp.u) →
        (∀ i : Fin n, |δsub i| ≤ fp.u) →
        frobNorm
          (householderApplyDeltaMatrix n P v beta η δw δmul δsub) ≤ c) :
    HouseholderAppError n P b (fl_householderApply fp n v beta b) c := by
  obtain ⟨η, δw, δmul, δsub, hη, hδw, hδmul, hδsub, hmatrix⟩ :=
    fl_householderApply_matrix_unroll fp n v beta b hn
  refine ⟨horth, ?_⟩
  refine ⟨householderApplyDeltaMatrix n P v beta η δw δmul δsub,
    hbound η δw δmul δsub hη hδw hδmul hδsub, ?_⟩
  intro i
  calc
    fl_householderApply fp n v beta b i =
        matMulVec n (householderApplyRoundedMatrix n v beta η δw δmul δsub) b i := by
          exact congr_fun hmatrix i
    _ = matMulVec n
          (fun a j =>
            P a j + householderApplyDeltaMatrix n P v beta η δw δmul δsub a j) b i := by
          unfold matMulVec householderApplyDeltaMatrix
          apply Finset.sum_congr rfl
          intro j _
          ring

end LeanFpAnalysis.FP
