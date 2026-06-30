-- Algorithms/LeastSquares/LSE.lean
--
-- Exact equality-constrained least-squares infrastructure (Higham §20.9).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Algorithms.QR.GramSchmidtPolar
import LeanFpAnalysis.FP.Algorithms.QR.Higham19
import LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §20.9  Equality-constrained least squares
-- ============================================================

/-- Higham, 2nd ed., Chapter 20, equation (20.23), feasibility part:
    `B x = d` for the equality-constrained least-squares problem. -/
def LSEFeasible {p n : ℕ} (B : Fin p → Fin n → ℝ)
    (d : Fin p → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin p, rectMatMulVec B x i = d i

/-- Higham, 2nd ed., Chapter 20, equation (20.23):
    `x` solves `min ||b - A x||_2` subject to `B x = d`.

    The shared objective uses the squared norm and residual sign `A x - b`;
    both are equivalent to the displayed source objective for minimizers. -/
def IsLSEMinimizer {m n p : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (B : Fin p → Fin n → ℝ)
    (d : Fin p → ℝ) (x : Fin n → ℝ) : Prop :=
  LSEFeasible B d x ∧
  ∀ y : Fin n → ℝ, LSEFeasible B d y → lsObjective A b x ≤ lsObjective A b y

/-- The linear constraint map `x ↦ B x` used in the equality-constrained
    least-squares problem (20.23). -/
noncomputable def lseConstraintLinearMap {p n : ℕ}
    (B : Fin p → Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin p → ℝ) where
  toFun := rectMatMulVec B
  map_add' := by
    intro x y
    exact rectMatMulVec_add B x y
  map_smul' := by
    intro a x
    exact rectMatMulVec_smul B a x

/-- Higham, 2nd ed., Chapter 20, equation (20.24), first condition:
    local finite-dimensional formulation of the full-row-rank assumption
    `rank(B)=p` as surjectivity of the constraint map `x ↦ B x`. -/
def LSEFullRowRank {p n : ℕ} (B : Fin p → Fin n → ℝ) : Prop :=
  Function.Surjective (lseConstraintLinearMap B)

/-- Higham, 2nd ed., Chapter 20, equation (20.24), consistency consequence:
    the local full-row-rank condition makes the equality constraint `B x = d`
    feasible for every right-hand side `d`. -/
theorem LSEFullRowRank.exists_feasible {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (d : Fin p → ℝ) :
    ∃ x : Fin n → ℝ, LSEFeasible B d x := by
  rcases hB d with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro i
  simpa [lseConstraintLinearMap] using congrFun hx i

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 rank bridge:
    full row rank of `B` makes the transpose map `Bᵀ` injective.  This is the
    finite-dimensional algebra used by the exact-MGS GQR route to connect the
    source rank assumption to MGS nonbreakdown hypotheses. -/
theorem LSEFullRowRank.transpose_rectMatMulVec_injective {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B) :
    Function.Injective
      (rectMatMulVec (fun j : Fin n => fun i : Fin p => B i j)) := by
  let Bt : Fin n → Fin p → ℝ := fun j => fun i => B i j
  have hker : ∀ w : Fin p → ℝ, rectMatMulVec Bt w = 0 → w = 0 := by
    intro w hw
    rcases hB w with ⟨x, hx⟩
    have hxB : rectMatMulVec B x = w := by
      simpa [lseConstraintLinearMap] using hx
    have hinner :
        (∑ i : Fin p, w i * rectMatMulVec B x i) = 0 := by
      calc
        (∑ i : Fin p, w i * rectMatMulVec B x i)
            = ∑ i : Fin p, ∑ j : Fin n, w i * (B i j * x j) := by
                unfold rectMatMulVec
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
        _ = ∑ j : Fin n, ∑ i : Fin p, w i * (B i j * x j) := by
                rw [Finset.sum_comm]
        _ = ∑ j : Fin n, (∑ i : Fin p, B i j * w i) * x j := by
                apply Finset.sum_congr rfl
                intro j _
                calc
                  (∑ i : Fin p, w i * (B i j * x j))
                      = ∑ i : Fin p, (B i j * w i) * x j := by
                          apply Finset.sum_congr rfl
                          intro i _
                          ring
                  _ = (∑ i : Fin p, B i j * w i) * x j := by
                          rw [Finset.sum_mul]
        _ = ∑ j : Fin n, rectMatMulVec Bt w j * x j := by
                unfold rectMatMulVec Bt
                rfl
        _ = 0 := by
                simp [hw]
    have hsq : vecNorm2Sq w = 0 := by
      calc
        vecNorm2Sq w
            = ∑ i : Fin p, w i * rectMatMulVec B x i := by
                rw [hxB]
                unfold vecNorm2Sq
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = 0 := hinner
    have hnorm : vecNorm2 w = 0 := by
      unfold vecNorm2
      rw [Real.sqrt_eq_zero (vecNorm2Sq_nonneg w)]
      exact hsq
    ext i
    exact (vecNorm2_eq_zero_iff w).mp hnorm i
  intro y z hyz
  have hdiff : rectMatMulVec Bt (fun i => y i - z i) = 0 := by
    ext j
    have hentry := congrFun hyz j
    change (∑ i : Fin p, B i j * y i) =
      (∑ i : Fin p, B i j * z i) at hentry
    unfold rectMatMulVec Bt
    change (∑ i : Fin p, B i j * (y i - z i)) = 0
    calc
      (∑ i : Fin p, B i j * (y i - z i))
          = ∑ i : Fin p, (B i j * y i - B i j * z i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : Fin p, B i j * y i) -
            (∑ i : Fin p, B i j * z i) := by
              rw [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hentry
  have hzero := hker (fun i => y i - z i) hdiff
  ext i
  have hi : y i - z i = 0 := by
    simpa using congrFun hzero i
  exact sub_eq_zero.mp hi

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 exact-MGS rank bridge:
    full row rank of `B` supplies the stage-0 nonbreakdown fact for MGS applied
    to `Bᵀ`.  This is the first pivot in the rank-to-all-MGS-stages route. -/
theorem LSEFullRowRank.transpose_mgs_stage0_norm_ne_zero {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B) (j : Fin p) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors
        (fun col : Fin n => fun row : Fin p => B row col) 0 j) ≠ 0 := by
  exact
    modifiedGramSchmidtVectors_zero_norm_ne_zero_of_rectMatMulVec_injective
      (fun col : Fin n => fun row : Fin p => B row col)
      hB.transpose_rectMatMulVec_injective j

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 exact-MGS rank bridge:
    full row rank of `B` supplies every nonzero-stage normalizer needed for
    exact MGS applied to `Bᵀ`. -/
theorem LSEFullRowRank.transpose_mgs_norm_ne_zero {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B) (j : Fin p) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors
        (fun col : Fin n => fun row : Fin p => B row col) j.val j) ≠ 0 := by
  exact
    modifiedGramSchmidtVectors_norm_ne_zero_of_rectMatMulVec_injective
      (fun col : Fin n => fun row : Fin p => B row col)
      hB.transpose_rectMatMulVec_injective j

/-- Column permutations preserve equality-constrained least-squares minimizers.

    This is the coordinate-change bridge used by Higham's Chapter 20
    elimination method in (20.29): after solving the permuted problem, pulling
    the coefficient vector back by `Πᵀ` gives a minimizer for the original
    variables. -/
theorem IsLSEMinimizer.of_permuteCols {m n p : ℕ} (π : Fin n ≃ Fin n)
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x : Fin n → ℝ}
    (h : IsLSEMinimizer (rectPermuteCols π A) b (rectPermuteCols π B) d x) :
    IsLSEMinimizer A b B d (vecPermute π.symm x) := by
  refine ⟨?feasible, ?minimal⟩
  · intro i
    have hmul := congrFun (rectMatMulVec_permuteCols π B x) i
    exact hmul.symm.trans (h.1 i)
  · intro y hy
    have hy_perm : LSEFeasible (rectPermuteCols π B) d (vecPermute π y) := by
      intro i
      have hmul := congrFun
        (rectMatMulVec_permuteCols π B (vecPermute π y)) i
      rw [hmul]
      rw [vecPermute_symm_vecPermute]
      exact hy i
    have hineq := h.2 (vecPermute π y) hy_perm
    rw [lsObjective_permuteCols π A b x] at hineq
    rw [lsObjective_permuteCols π A b (vecPermute π y)] at hineq
    rw [vecPermute_symm_vecPermute] at hineq
    exact hineq

/-- Higham, 2nd ed., Chapter 20, equation (20.24), second condition:
    `null(A) ∩ null(B) = {0}`.  The full-row-rank consistency side is
    represented separately by `LSEFullRowRank`. -/
def LSENullIntersectionTrivial {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) : Prop :=
  ∀ v : Fin n → ℝ,
    rectMatMulVec A v = 0 →
    rectMatMulVec B v = 0 →
    v = 0

/-- Higham, 2nd ed., Chapter 20, equation (20.24): vertical stack
    `[A; B]`, the local representation of `[A^T, B^T]^T`. -/
noncomputable def lseStackedMatrix {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) :
    Fin (m + p) → Fin n → ℝ :=
  Fin.append A B

/-- Multiplication by the vertical stack `[A; B]` splits into the two source
    actions `A x` and `B x`. -/
theorem lseStackedMatrix_mulVec {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (x : Fin n → ℝ) :
    rectMatMulVec (lseStackedMatrix A B) x =
      Fin.append (rectMatMulVec A x) (rectMatMulVec B x) := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (m + p) =>
      rectMatMulVec (lseStackedMatrix A B) x i =
        Fin.append (rectMatMulVec A x) (rectMatMulVec B x) i)
    ?left ?right i
  · intro i
    unfold rectMatMulVec lseStackedMatrix
    simp [Fin.append_left]
  · intro i
    unfold rectMatMulVec lseStackedMatrix
    simp [Fin.append_right]

/-- Kernel splitting for the stacked matrix `[A; B]` in (20.24). -/
theorem lseStackedMatrix_mulVec_eq_zero_iff {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (v : Fin n → ℝ) :
    rectMatMulVec (lseStackedMatrix A B) v = 0 ↔
      rectMatMulVec A v = 0 ∧ rectMatMulVec B v = 0 := by
  constructor
  · intro h
    constructor
    · ext i
      have hi := congrFun h (Fin.castAdd p i)
      rw [congrFun (lseStackedMatrix_mulVec A B v) (Fin.castAdd p i)] at hi
      simpa [Fin.append_left] using hi
    · ext i
      have hi := congrFun h (Fin.natAdd m i)
      rw [congrFun (lseStackedMatrix_mulVec A B v) (Fin.natAdd m i)] at hi
      simpa [Fin.append_right] using hi
  · rintro ⟨hA, hB⟩
    ext i
    rw [congrFun (lseStackedMatrix_mulVec A B v) i]
    refine Fin.addCases
      (motive := fun i : Fin (m + p) =>
        Fin.append (rectMatMulVec A v) (rectMatMulVec B v) i = 0)
      ?left ?right i
    · intro i
      simpa [Fin.append_left] using congrFun hA i
    · intro i
      simpa [Fin.append_right] using congrFun hB i

/-- Local finite-dimensional formulation of the source statement that
    `[A^T, B^T]^T` has full column rank. -/
def LSEStackedFullColumnRank {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) : Prop :=
  Function.Injective (rectMatMulVec (lseStackedMatrix A B))

/-- Higham, 2nd ed., Chapter 20, equation (20.24), prose after the display:
    the null-intersection condition
    `null(A) ∩ null(B) = {0}` is equivalent to full column rank of
    `[A^T, B^T]^T`, represented locally as injectivity of `[A; B]`. -/
theorem LSENullIntersectionTrivial.iff_lseStackedFullColumnRank {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) :
    LSENullIntersectionTrivial A B ↔ LSEStackedFullColumnRank A B := by
  constructor
  · intro hnull x y hxy
    have hdiff_zero :
        rectMatMulVec (lseStackedMatrix A B) (fun j => x j - y j) = 0 := by
      rw [rectMatMulVec_sub (lseStackedMatrix A B) x y]
      ext i
      exact sub_eq_zero.mpr (congrFun hxy i)
    have hparts := (lseStackedMatrix_mulVec_eq_zero_iff A B
      (fun j => x j - y j)).1 hdiff_zero
    have hzero := hnull (fun j => x j - y j) hparts.1 hparts.2
    ext j
    have hj := congrFun hzero j
    dsimp at hj
    linarith
  · intro hfull v hAv hBv
    have hstack_zero :
        rectMatMulVec (lseStackedMatrix A B) v = 0 :=
      (lseStackedMatrix_mulVec_eq_zero_iff A B v).2 ⟨hAv, hBv⟩
    have hzero_action :
        rectMatMulVec (lseStackedMatrix A B) v =
          rectMatMulVec (lseStackedMatrix A B) (0 : Fin n → ℝ) := by
      rw [hstack_zero]
      ext i
      simp [rectMatMulVec]
    exact hfull hzero_action

/-- A square finite matrix is lower triangular when all entries above the
    diagonal vanish.  This is the exact triangularity predicate used by
    Higham's generalized QR factorization in (20.27). -/
def IsLowerTriangular {n : ℕ} (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i.val < j.val → L i j = 0

/-- A relative entrywise perturbation of a lower-triangular matrix is still
    lower triangular.  Above the diagonal the reference entries are zero, so
    the absolute perturbation bound forces the perturbation entries to vanish
    there as well. -/
theorem IsLowerTriangular.add_of_entrywise_abs_le_mul_abs {n : ℕ}
    {T Delta : Fin n → Fin n → ℝ} {eta : ℝ}
    (hT : IsLowerTriangular T)
    (hDelta : ∀ i j : Fin n, |Delta i j| ≤ eta * |T i j|) :
    IsLowerTriangular (fun i j => T i j + Delta i j) := by
  intro i j hij
  have hTij : T i j = 0 := hT i j hij
  have hbound : |Delta i j| ≤ 0 := by
    simpa [hTij] using hDelta i j
  have hDeltaij : Delta i j = 0 := by
    exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg (Delta i j)))
  simp [hTij, hDeltaij]

/-- A relative entrywise perturbation with factor strictly below one preserves
    nonzero diagonal entries. -/
theorem diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one {n : ℕ}
    {T Delta : Fin n → Fin n → ℝ} {eta : ℝ}
    (hdiag : ∀ i : Fin n, T i i ≠ 0)
    (heta_lt : eta < 1)
    (hDelta : ∀ i j : Fin n, |Delta i j| ≤ eta * |T i j|) :
    ∀ i : Fin n, T i i + Delta i i ≠ 0 := by
  intro i hzero
  have hDelta_eq : Delta i i = -T i i := by
    linarith
  have habs_eq : |Delta i i| = |T i i| := by
    rw [hDelta_eq, abs_neg]
  have hle : |T i i| ≤ eta * |T i i| := by
    simpa [habs_eq] using hDelta i i
  have hpos : 0 < |T i i| := abs_pos.mpr (hdiag i)
  nlinarith

private theorem isInverse_rectMatMulVec_bijective {n : ℕ}
    (T Tinv : Fin n → Fin n → ℝ) (hInv : IsInverse n T Tinv) :
    Function.Bijective (rectMatMulVec T) := by
  constructor
  · intro x y hxy
    ext i
    calc
      x i = matMulVec n (idMatrix n) x i := by rw [matMulVec_id]
      _ = matMulVec n (matMul n Tinv T) x i := by
            have hmat : matMul n Tinv T = idMatrix n := by
              ext a b
              exact hInv.1 a b
            rw [hmat]
      _ = matMulVec n Tinv (matMulVec n T x) i := by
            exact matMulVec_matMul n Tinv T x i
      _ = matMulVec n Tinv (matMulVec n T y) i := by
            have hxy' : matMulVec n T x = matMulVec n T y := by
              simpa [rectMatMulVec, matMulVec] using hxy
            rw [hxy']
      _ = matMulVec n (matMul n Tinv T) y i := by
            exact (matMulVec_matMul n Tinv T y i).symm
      _ = matMulVec n (idMatrix n) y i := by
            have hmat : matMul n Tinv T = idMatrix n := by
              ext a b
              exact hInv.1 a b
            rw [hmat]
      _ = y i := by rw [matMulVec_id]
  · intro b
    refine ⟨matMulVec n Tinv b, ?_⟩
    ext i
    calc
      rectMatMulVec T (matMulVec n Tinv b) i
          = matMulVec n T (matMulVec n Tinv b) i := by
            rfl
      _ = matMulVec n (matMul n T Tinv) b i := by
            exact (matMulVec_matMul n T Tinv b i).symm
      _ = matMulVec n (idMatrix n) b i := by
            have hmat : matMul n T Tinv = idMatrix n := by
              ext a b
              exact hInv.2 a b
            rw [hmat]
      _ = b i := by rw [matMulVec_id]

/-- A finite lower-triangular real matrix with nonzero diagonal is a
    nonsingular square solve map.

    This is the determinant-to-solve-map bridge used for Higham's statement
    after Theorem 20.9 that the lower-triangular GQR blocks `S` and `L22` are
    nonsingular. -/
theorem rectMatMulVec_bijective_of_lowerTriangular_diag_ne_zero {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hlower : IsLowerTriangular T)
    (hdiag : ∀ i : Fin n, T i i ≠ 0) :
    Function.Bijective (rectMatMulVec T) := by
  have hdet : Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
    det_ne_zero_of_lower_triangular_diag_ne_zero n T hlower hdiag
  rcases exists_isInverse_of_det_ne_zero n T hdet with ⟨Tinv, hInv⟩
  exact isInverse_rectMatMulVec_bijective T Tinv hInv

/-- A square matrix whose rectangular matrix-vector action is injective has
    nonzero determinant. -/
theorem rectMatMulVec_det_ne_zero_of_injective {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hinj : Function.Injective (rectMatMulVec T)) :
    Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  let M : Matrix (Fin n) (Fin n) ℝ := T
  have hM_inj : Function.Injective M.mulVec := by
    intro x y hxy
    apply hinj
    ext i
    have hi := congrFun hxy i
    simpa [M, rectMatMulVec, Matrix.mulVec] using hi
  have hunitM : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hM_inj
  have hdetUnit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunitM
  have hdetNe : M.det ≠ 0 := isUnit_iff_ne_zero.mp hdetUnit
  simpa [M] using hdetNe

/-- A finite lower-triangular real matrix with nonzero determinant has nonzero
    diagonal entries.  This is the transpose form of
    `diag_ne_zero_of_upper_triangular_det_ne_zero`. -/
theorem diag_ne_zero_of_lower_triangular_det_ne_zero {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hlower : IsLowerTriangular T)
    (hdet : Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∀ i : Fin n, T i i ≠ 0 := by
  let M : Matrix (Fin n) (Fin n) ℝ := T
  have hupper : ∀ i j : Fin n, j.val < i.val → T j i = 0 := by
    intro i j hji
    exact hlower j i hji
  have hdetT :
      Matrix.det ((fun i j : Fin n => T j i) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    have hdetTranspose : Matrix.det M.transpose ≠ 0 := by
      rw [Matrix.det_transpose]
      simpa [M] using hdet
    have hmat :
        ((fun i j : Fin n => T j i) : Matrix (Fin n) (Fin n) ℝ) =
          M.transpose := by
      ext i j
      simp [M, Matrix.transpose_apply]
    rw [hmat]
    exact hdetTranspose
  have hdiagT := diag_ne_zero_of_upper_triangular_det_ne_zero n
    (fun i j : Fin n => T j i) hupper hdetT
  intro i
  exact hdiagT i

/-- A finite lower-triangular real matrix with injective square solve map has
    nonzero diagonal entries. -/
theorem rectMatMulVec_diag_ne_zero_of_lowerTriangular_injective {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hlower : IsLowerTriangular T)
    (hinj : Function.Injective (rectMatMulVec T)) :
    ∀ i : Fin n, T i i ≠ 0 :=
  diag_ne_zero_of_lower_triangular_det_ne_zero hlower
    (rectMatMulVec_det_ne_zero_of_injective hinj)

/-- A finite lower-triangular real matrix with bijective square solve map has
    nonzero diagonal entries. -/
theorem rectMatMulVec_diag_ne_zero_of_lowerTriangular_bijective {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hlower : IsLowerTriangular T)
    (hbij : Function.Bijective (rectMatMulVec T)) :
    ∀ i : Fin n, T i i ≠ 0 :=
  rectMatMulVec_diag_ne_zero_of_lowerTriangular_injective hlower hbij.1

/-- Higham, 2nd ed., Chapter 20, equation (20.27):
    the displayed block matrix for `U^T A Q`.

    The source dimensions are represented as columns `p + q`, with `q = n-p`,
    and rows `r + q`, with `r = m-n+p`. -/
noncomputable def gqrAQBlock {r p q : ℕ}
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ) :
    Fin (r + q) → Fin (p + q) → ℝ :=
  Fin.append
    (fun i : Fin r => Fin.append (L11 i) (fun _ : Fin q => 0))
    (fun i : Fin q => Fin.append (L21 i) (L22 i))

/-- Higham, 2nd ed., Chapter 20, equation (20.27):
    the displayed block matrix `[S 0]` for `B Q`. -/
noncomputable def gqrBQBlock {p q : ℕ}
    (S : Fin p → Fin p → ℝ) :
    Fin p → Fin (p + q) → ℝ :=
  fun i => Fin.append (S i) (fun _ : Fin q => 0)

/-- Matrix-vector multiplication by the `B Q = [S 0]` block in (20.27)
    reduces to the triangular factor `S` acting on the first block of `y`. -/
theorem gqrBQBlock_mulVec {p q : ℕ}
    (S : Fin p → Fin p → ℝ)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec (gqrBQBlock S) (Fin.append y1 y2) =
      rectMatMulVec S y1 := by
  ext i
  unfold rectMatMulVec gqrBQBlock
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- The transpose of a square upper-triangular QR block is lower triangular.

    This is the first triangularity bridge in Higham's Chapter 20 construction
    of the generalized QR factorization in Theorem 20.9: a QR factorization of
    `Bᵀ` supplies an upper-triangular `R`, whose transpose becomes the lower
    triangular `S` in `B Q = [S 0]`. -/
theorem isLowerTriangular_matTranspose_of_isUpperTriangular {n : ℕ}
    {R : Fin n → Fin n → ℝ}
    (hR : IsUpperTriangular n R) :
    IsLowerTriangular (matTranspose R) := by
  intro i j hij
  unfold matTranspose
  exact hR j i hij

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    reverse both indices of an upper-triangular QR block.  This is the square
    block produced when a standard `[R;0]` QR display is turned into the
    lower-triangular block in the tall associated form (20.28). -/
def gqrReverseSquare {n : ℕ} (R : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => R (Fin.rev i) (Fin.rev j)

/-- Reversing both indices turns an upper-triangular QR block into the
    lower-triangular block used in Higham's Chapter 20 GQR display (20.28). -/
theorem gqrReverseSquare_lowerTriangular_of_upper {n : ℕ}
    {R : Fin n → Fin n → ℝ}
    (hR : IsUpperTriangular n R) :
    IsLowerTriangular (gqrReverseSquare R) := by
  intro i j hij
  unfold gqrReverseSquare
  exact hR (Fin.rev i) (Fin.rev j) ((Fin.rev_lt_rev).2 hij)

/-- Diagonal nonzeroness is preserved by the index reversal used to convert an
    upper QR block into the lower GQR block. -/
theorem gqrReverseSquare_diag_ne_zero_iff {n : ℕ}
    (R : Fin n → Fin n → ℝ) :
    (∀ i : Fin n, gqrReverseSquare R i i ≠ 0) ↔
      ∀ i : Fin n, R i i ≠ 0 := by
  constructor
  · intro h i
    have hi := h (Fin.rev i)
    simpa [gqrReverseSquare] using hi
  · intro h i
    simpa [gqrReverseSquare] using h (Fin.rev i)

/-- Permutation matrix for a finite index equivalence.  This is the orthogonal
    left-factor used to make the row permutations in the Chapter 20 GQR block
    constructions explicit. -/
def finPermMatrix {n : ℕ} (σ : Fin n ≃ Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if σ i = j then 1 else 0

/-- Left multiplication by a permutation matrix permutes the rows of a
    rectangular matrix. -/
theorem matMulRectLeft_finPermMatrix {m n : ℕ}
    (σ : Fin m ≃ Fin m) (A : Fin m → Fin n → ℝ) :
    matMulRectLeft (finPermMatrix σ) A = rectPermuteRows σ A := by
  ext i j
  unfold matMulRectLeft finPermMatrix rectPermuteRows
  simp

/-- A finite permutation matrix is orthogonal. -/
theorem finPermMatrix_orthogonal {n : ℕ} (σ : Fin n ≃ Fin n) :
    IsOrthogonal n (finPermMatrix σ) := by
  constructor
  · intro i j
    unfold finPermMatrix matTranspose
    calc
      (∑ x : Fin n,
          (if σ x = i then (1 : ℝ) else 0) *
            if σ x = j then (1 : ℝ) else 0)
          = ∑ x : Fin n,
              if σ x = i then if σ x = j then (1 : ℝ) else 0 else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hxi : σ x = i <;> simp [hxi]
      _ = if i = j then 1 else 0 := by
          calc
            (∑ x : Fin n,
                if σ x = i then if σ x = j then (1 : ℝ) else 0 else 0)
                = ∑ y : Fin n,
                    if y = i then if y = j then (1 : ℝ) else 0 else 0 := by
                    exact Equiv.sum_comp σ
                      (fun y : Fin n =>
                        if y = i then if y = j then (1 : ℝ) else 0 else 0)
            _ = if i = j then 1 else 0 := by
                by_cases hij : i = j <;> simp [hij]
  · intro i j
    unfold finPermMatrix matTranspose
    calc
      (∑ x : Fin n,
          (if σ i = x then (1 : ℝ) else 0) *
            if σ j = x then (1 : ℝ) else 0)
          = ∑ x : Fin n,
              if σ i = x then if σ j = x then (1 : ℝ) else 0 else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hxi : σ i = x <;> simp [hxi]
      _ = if i = j then 1 else 0 := by
          calc
            (∑ x : Fin n,
                if σ i = x then if σ j = x then (1 : ℝ) else 0 else 0)
                = (if σ j = σ i then (1 : ℝ) else 0) := by
                    rw [Finset.sum_ite_eq]
                    simp
            _ = if i = j then 1 else 0 := by
                by_cases hij : i = j
                · subst j
                  simp
                · have hsig : σ j ≠ σ i := by
                    intro h
                    exact hij ((Equiv.apply_eq_iff_eq σ).1 h.symm)
                  simp [hij, hsig]

/-- Square GQR conversion step: if a standard QR transform triangularizes the
    column-reversed square matrix, then reversing the transformed rows produces
    `gqrReverseSquare R`, the lower-triangular block used in (20.28). -/
theorem gqrReverseRowsOfQRReversedCols {n : ℕ}
    (C V R : Fin n → Fin n → ℝ)
    (hqr : matMulRectLeft (matTranspose V) (rectPermuteCols Fin.revPerm C) = R) :
    matMulRectLeft (finPermMatrix Fin.revPerm)
      (matMulRectLeft (matTranspose V) C) = gqrReverseSquare R := by
  ext i j
  rw [matMulRectLeft_finPermMatrix]
  unfold rectPermuteRows gqrReverseSquare
  have hentry := congrFun (congrFun hqr (Fin.rev i)) (Fin.rev j)
  unfold matMulRectLeft matTranspose rectPermuteCols at hentry
  unfold matMulRectLeft matTranspose
  simpa using hentry

/-- The zero-tail transformed QR block `[R;0]` is just `R`. -/
theorem lsQRTallBlock_zero {n : ℕ} (R : Fin n → Fin n → ℝ) :
    lsQRTallBlock (k := 0) R = R := by
  ext i j
  unfold lsQRTallBlock
  refine Fin.addCases ?_ ?_ i
  · intro i
    change Fin.append R (fun _ : Fin 0 => fun _ : Fin n => 0)
        (Fin.castAdd 0 i) j = R i j
    rw [Fin.append_left]
  · intro i
    exact Fin.elim0 i

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    a QR transform of a column-reversed square block gives an orthogonal
    left-factor whose transpose sends the original block to a lower-triangular
    block. -/
theorem exists_orthogonal_gqrReverseSquare_of_qr_reversed_cols {n : ℕ}
    (C V R : Fin n → Fin n → ℝ)
    (hV : IsOrthogonal n V)
    (hR : IsUpperTriangular n R)
    (hqr : matMulRectLeft (matTranspose V) (rectPermuteCols Fin.revPerm C) = R) :
    ∃ U : Fin n → Fin n → ℝ,
      IsOrthogonal n U ∧
        matMulRectLeft (matTranspose U) C = gqrReverseSquare R ∧
          IsLowerTriangular (gqrReverseSquare R) := by
  let P : Fin n → Fin n → ℝ := finPermMatrix Fin.revPerm
  let U : Fin n → Fin n → ℝ := matMul n V (matTranspose P)
  refine ⟨U, ?_, ?_, gqrReverseSquare_lowerTriangular_of_upper hR⟩
  · exact hV.mul (finPermMatrix_orthogonal Fin.revPerm).transpose
  · have hUt : matTranspose U = matMul n P (matTranspose V) := by
      simp [U, P, matTranspose_matMul, matTranspose_involutive]
    calc
      matMulRectLeft (matTranspose U) C
          = matMulRectLeft (matMul n P (matTranspose V)) C := by rw [hUt]
      _ = matMulRectLeft P (matMulRectLeft (matTranspose V) C) := by
          rw [matMulRectLeft_assoc]
      _ = gqrReverseSquare R := by
          simpa [P] using gqrReverseRowsOfQRReversedCols C V R hqr

private theorem isRightInverse_of_isLeftInverse_square {n : ℕ}
    {T Tinv : Fin n → Fin n → ℝ}
    (hLeft : IsLeftInverse n T Tinv) :
    IsRightInverse n T Tinv := by
  have hmatLeft :
      (Matrix.of Tinv : Matrix (Fin n) (Fin n) ℝ) *
          (Matrix.of T : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.of_apply, idMatrix] using hLeft i j
  have hmatRight :
      (Matrix.of T : Matrix (Fin n) (Fin n) ℝ) *
          (Matrix.of Tinv : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    mul_eq_one_comm.mp hmatLeft
  intro i j
  have hentry := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hmatRight
  simpa [Matrix.mul_apply, Matrix.of_apply, idMatrix] using hentry

private theorem isOrthogonal_of_column_orthonormal {n : ℕ}
    {Q : Fin n → Fin n → ℝ}
    (hcols : ∀ a b : Fin n,
      (∑ i : Fin n, Q i a * Q i b) = if a = b then 1 else 0) :
    IsOrthogonal n Q := by
  have hleft : IsLeftInverse n Q (matTranspose Q) := by
    intro a b
    simpa [matTranspose] using hcols a b
  exact ⟨hleft, isRightInverse_of_isLeftInverse_square hleft⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    a rectangular exact factorization `Bᵀ = Q₁ R` with orthonormal columns can
    be completed to a square orthogonal `Q` satisfying
    `Qᵀ Bᵀ = [R; 0]`.

    This removes the supplied square-orthogonal factor from the `Bᵀ` QR part of
    the GQR construction.  It is exact finite-dimensional algebra; the
    rectangular factorization itself is still an input to this theorem. -/
theorem exists_orthogonal_completion_tall_qr_block {p q : ℕ}
    (Bt : Fin (p + q) → Fin p → ℝ)
    (Q1 : Fin (p + q) → Fin p → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ1 : GramSchmidtOrthonormalColumns Q1)
    (hfactor : Bt = matMulRect (p + q) p p Q1 R) :
    ∃ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q ∧
        (∀ i j, Q i (Fin.castAdd q j) = Q1 i j) ∧
        matMulRectLeft (matTranspose Q) Bt = lsQRTallBlock (k := q) R := by
  classical
  let s : Set (Fin (p + q)) :=
    {a | ∃ j : Fin p, a = Fin.castAdd q j}
  let X : Fin (p + q) → Fin (p + q) → ℝ :=
    fun i a =>
      if ha : ∃ j : Fin p, a = Fin.castAdd q j then
        Q1 i (Classical.choose ha)
      else
        0
  have hX : ∀ a b : s,
      (∑ i : Fin (p + q), X i a * X i b) =
        if a = b then 1 else 0 := by
    intro a b
    rcases a.2 with ⟨ja, hja⟩
    rcases b.2 with ⟨jb, hjb⟩
    have hXa : ∀ i : Fin (p + q), X i a = Q1 i ja := by
      intro i
      have ha : ∃ j : Fin p, (a : Fin (p + q)) = Fin.castAdd q j :=
        ⟨ja, hja⟩
      have hchoose : Classical.choose ha = ja := by
        apply Fin.castAdd_injective p q
        simp [hja]
      simp [X, ha, hchoose]
    have hXb : ∀ i : Fin (p + q), X i b = Q1 i jb := by
      intro i
      have hb : ∃ j : Fin p, (b : Fin (p + q)) = Fin.castAdd q j :=
        ⟨jb, hjb⟩
      have hchoose : Classical.choose hb = jb := by
        apply Fin.castAdd_injective p q
        simp [hjb]
      simp [X, hb, hchoose]
    have hsubeq : a = b ↔ ja = jb := by
      constructor
      · intro hab
        apply Fin.castAdd_injective p q
        calc
          Fin.castAdd q ja = (a : Fin (p + q)) := hja.symm
          _ = (b : Fin (p + q)) := congrArg Subtype.val hab
          _ = Fin.castAdd q jb := hjb
      · intro h
        apply Subtype.ext
        calc
          (a : Fin (p + q)) = Fin.castAdd q ja := hja
          _ = Fin.castAdd q jb := by rw [h]
          _ = (b : Fin (p + q)) := hjb.symm
    calc
      (∑ i : Fin (p + q), X i a * X i b)
          = ∑ i : Fin (p + q), Q1 i ja * Q1 i jb := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hXa i, hXb i]
      _ = idMatrix p ja jb := hQ1 ja jb
      _ = if a = b then 1 else 0 := by
          by_cases h : ja = jb
          · subst jb
            have hab : a = b := hsubeq.mpr rfl
            simp [idMatrix, hab]
          · have hab : a ≠ b := fun hab => h (hsubeq.mp hab)
            simp [idMatrix, h, hab]
  obtain ⟨Q, hQpreserve, hQcols⟩ :=
    partialColOrthonormal_exists_fullColOrthonormal X s hX
  refine ⟨Q, isOrthogonal_of_column_orthonormal hQcols, ?_, ?_⟩
  · intro i j
    have hmem : Fin.castAdd q j ∈ s := ⟨j, rfl⟩
    have hp := hQpreserve (Fin.castAdd q j) hmem i
    have hcast : ∃ k : Fin p, Fin.castAdd q j = Fin.castAdd q k :=
      ⟨j, rfl⟩
    have hchoose : Classical.choose hcast = j := by
      apply Fin.castAdd_injective p q
      exact (Classical.choose_spec hcast).symm
    simpa [X, hcast, hchoose] using hp
  · subst Bt
    ext row col
    refine Fin.addCases
      (motive := fun row : Fin (p + q) =>
        matMulRectLeft (matTranspose Q)
            (matMulRect (p + q) p p Q1 R) row col =
          lsQRTallBlock (k := q) R row col)
      ?top ?bottom row
    · intro row
      have hpreserve : ∀ i : Fin (p + q), Q i (Fin.castAdd q row) = Q1 i row :=
        fun i => by
          have hmem : Fin.castAdd q row ∈ s := ⟨row, rfl⟩
          have hp := hQpreserve (Fin.castAdd q row) hmem i
          have hcast : ∃ k : Fin p, Fin.castAdd q row = Fin.castAdd q k :=
            ⟨row, rfl⟩
          have hchoose : Classical.choose hcast = row := by
            apply Fin.castAdd_injective p q
            exact (Classical.choose_spec hcast).symm
          simpa [X, hcast, hchoose] using hp
      have hsum_rearrange :
          (∑ i : Fin (p + q),
              Q i (Fin.castAdd q row) *
                (∑ k : Fin p, Q1 i k * R k col)) =
            ∑ k : Fin p,
              (∑ i : Fin (p + q), Q i (Fin.castAdd q row) * Q1 i k) *
                R k col := by
        calc
          (∑ i : Fin (p + q),
              Q i (Fin.castAdd q row) *
                (∑ k : Fin p, Q1 i k * R k col))
              =
            ∑ i : Fin (p + q), ∑ k : Fin p,
              Q i (Fin.castAdd q row) * (Q1 i k * R k col) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
          _ =
            ∑ k : Fin p, ∑ i : Fin (p + q),
              Q i (Fin.castAdd q row) * (Q1 i k * R k col) := by
              rw [Finset.sum_comm]
          _ =
            ∑ k : Fin p,
              (∑ i : Fin (p + q), Q i (Fin.castAdd q row) * Q1 i k) *
                R k col := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              ring
      calc
        matMulRectLeft (matTranspose Q)
            (matMulRect (p + q) p p Q1 R) (Fin.castAdd q row) col
            =
          ∑ k : Fin p,
            (∑ i : Fin (p + q), Q i (Fin.castAdd q row) * Q1 i k) *
              R k col := by
              unfold matMulRectLeft matTranspose matMulRect
              exact hsum_rearrange
        _ =
          ∑ k : Fin p, idMatrix p row k * R k col := by
              apply Finset.sum_congr rfl
              intro k _
              have horth :
                  (∑ i : Fin (p + q), Q1 i row * Q1 i k) =
                    idMatrix p row k := by
                simpa [GramSchmidtOrthonormalColumns, rectangularGram] using
                  hQ1 row k
              rw [show (∑ i : Fin (p + q), Q i (Fin.castAdd q row) * Q1 i k) =
                  ∑ i : Fin (p + q), Q1 i row * Q1 i k from by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [hpreserve i]]
              rw [horth]
        _ = R row col := by
              simp [idMatrix]
        _ = lsQRTallBlock (k := q) R (Fin.castAdd q row) col := by
              simp [lsQRTallBlock]
    · intro row
      have hsum_rearrange :
          (∑ i : Fin (p + q),
              Q i (Fin.natAdd p row) *
                (∑ k : Fin p, Q1 i k * R k col)) =
            ∑ k : Fin p,
              (∑ i : Fin (p + q), Q i (Fin.natAdd p row) * Q1 i k) *
                R k col := by
        calc
          (∑ i : Fin (p + q),
              Q i (Fin.natAdd p row) *
                (∑ k : Fin p, Q1 i k * R k col))
              =
            ∑ i : Fin (p + q), ∑ k : Fin p,
              Q i (Fin.natAdd p row) * (Q1 i k * R k col) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
          _ =
            ∑ k : Fin p, ∑ i : Fin (p + q),
              Q i (Fin.natAdd p row) * (Q1 i k * R k col) := by
              rw [Finset.sum_comm]
          _ =
            ∑ k : Fin p,
              (∑ i : Fin (p + q), Q i (Fin.natAdd p row) * Q1 i k) *
                R k col := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              ring
      have htail_orth : ∀ k : Fin p,
          (∑ i : Fin (p + q), Q i (Fin.natAdd p row) * Q1 i k) = 0 := by
        intro k
        have hne : Fin.natAdd p row ≠ Fin.castAdd q k := by
          intro h
          have hval := congrArg Fin.val h
          have hp_le : p ≤ k.val := by
            calc
              p ≤ p + row.val := Nat.le_add_right p row.val
              _ = k.val := by simpa using hval
          exact (Nat.not_le_of_gt k.isLt) hp_le
        have horth := hQcols (Fin.natAdd p row) (Fin.castAdd q k)
        have hsumQ :
            (∑ i : Fin (p + q), Q i (Fin.natAdd p row) *
              Q i (Fin.castAdd q k)) = 0 := by
          simpa [hne] using horth
        have hpreserve : ∀ i : Fin (p + q), Q i (Fin.castAdd q k) = Q1 i k :=
          fun i => by
            have hmem : Fin.castAdd q k ∈ s := ⟨k, rfl⟩
            have hp := hQpreserve (Fin.castAdd q k) hmem i
            have hcast : ∃ j : Fin p, Fin.castAdd q k = Fin.castAdd q j :=
              ⟨k, rfl⟩
            have hchoose : Classical.choose hcast = k := by
              apply Fin.castAdd_injective p q
              exact (Classical.choose_spec hcast).symm
            simpa [X, hcast, hchoose] using hp
        calc
          (∑ i : Fin (p + q), Q i (Fin.natAdd p row) * Q1 i k)
              =
            ∑ i : Fin (p + q), Q i (Fin.natAdd p row) *
              Q i (Fin.castAdd q k) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hpreserve i]
          _ = 0 := hsumQ
      calc
        matMulRectLeft (matTranspose Q)
            (matMulRect (p + q) p p Q1 R) (Fin.natAdd p row) col
            =
          ∑ k : Fin p,
            (∑ i : Fin (p + q), Q i (Fin.natAdd p row) * Q1 i k) *
              R k col := by
              unfold matMulRectLeft matTranspose matMulRect
              exact hsum_rearrange
        _ = 0 := by
              simp [htail_orth]
        _ = lsQRTallBlock (k := q) R (Fin.natAdd p row) col := by
              simp [lsQRTallBlock]

/-- Exact-MGS version of
    `exists_orthogonal_gqrReverseSquare_of_qr_reversed_cols`: nonzero MGS stages
    for the column-reversed square block supply the orthogonal transform and
    lower-triangular GQR block. -/
theorem exists_orthogonal_gqrReverseSquare_of_mgs_reversed_cols {n : ℕ}
    (C : Fin n → Fin n → ℝ)
    (hdiag : ∀ k : Fin n,
      gsColumnNorm2
        (modifiedGramSchmidtVectors (rectPermuteCols Fin.revPerm C) k.val k) ≠ 0) :
    ∃ (U : Fin n → Fin n → ℝ) (R : Fin n → Fin n → ℝ),
      IsOrthogonal n U ∧ IsUpperTriangular n R ∧
        matMulRectLeft (matTranspose U) C = gqrReverseSquare R ∧
          IsLowerTriangular (gqrReverseSquare R) := by
  let Crev : Fin n → Fin n → ℝ := rectPermuteCols Fin.revPerm C
  let R : Fin n → Fin n → ℝ := modifiedGramSchmidtR Crev
  have hfactor :
      Crev = matMulRect n n n (modifiedGramSchmidtQ Crev) R := by
    exact modifiedGramSchmidt_exact_factorization Crev hdiag
  have horth : GramSchmidtOrthonormalColumns (modifiedGramSchmidtQ Crev) :=
    modifiedGramSchmidtQ_orthonormal_columns Crev hdiag
  obtain ⟨V, hV, _hpreserve, hqr⟩ :=
    exists_orthogonal_completion_tall_qr_block (p := n) (q := 0)
      Crev (modifiedGramSchmidtQ Crev) R horth hfactor
  have hRupper : IsUpperTriangular n R :=
    IsUpperTrapezoidal.to_upperTriangular
      (modifiedGramSchmidtR_upper_trapezoidal Crev)
  have hqrR : matMulRectLeft (matTranspose V) (rectPermuteCols Fin.revPerm C) = R := by
    simpa [Crev, lsQRTallBlock_zero] using hqr
  rcases exists_orthogonal_gqrReverseSquare_of_qr_reversed_cols
      C V R hV hRupper hqrR with
    ⟨U, hU, hUeq, hLower⟩
  exact ⟨U, R, hU, hRupper, hUeq, hLower⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    a supplied tall QR factorization of `Bᵀ` yields the constraint block
    identity `B Q = [Rᵀ 0]` in the GQR display (20.27).

    The hypothesis is the exact transformed QR block
    `Qᵀ Bᵀ = [R;0]`.  Taking transposes entrywise gives the source GQR
    constraint block with `S = Rᵀ`.  This is still supplied exact algebra: it
    does not construct the QR factorization itself. -/
theorem gqrBQBlock_eq_of_transpose_tall_qr {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hqr : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R) :
    matMulRect p (p + q) (p + q) B Q = gqrBQBlock (matTranspose R) := by
  ext i j
  refine Fin.addCases
    (motive := fun j : Fin (p + q) =>
      matMulRect p (p + q) (p + q) B Q i j =
        gqrBQBlock (matTranspose R) i j)
    ?left ?right j
  · intro j
    have hentry := congrFun (congrFun hqr (Fin.castAdd q j)) i
    unfold matMulRectLeft matTranspose lsQRTallBlock at hentry
    unfold matMulRect gqrBQBlock matTranspose
    rw [Fin.append_left] at hentry
    rw [Fin.append_left]
    calc
      (∑ k : Fin (p + q), B i k * Q k (Fin.castAdd q j))
          = ∑ k : Fin (p + q), Q k (Fin.castAdd q j) * B i k := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = R j i := hentry
  · intro j
    have hentry := congrFun (congrFun hqr (Fin.natAdd p j)) i
    unfold matMulRectLeft matTranspose lsQRTallBlock at hentry
    unfold matMulRect gqrBQBlock matTranspose
    rw [Fin.append_right] at hentry
    rw [Fin.append_right]
    calc
      (∑ k : Fin (p + q), B i k * Q k (Fin.natAdd p j))
          = ∑ k : Fin (p + q), Q k (Fin.natAdd p j) * B i k := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = 0 := hentry

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    exact MGS data for `Bᵀ`, once its computed columns are known
    orthonormal, supplies the completed tall QR block `Qᵀ Bᵀ = [R;0]`.

    This removes the arbitrary supplied rectangular factorization from the
    previous completion theorem.  The remaining exposed QR-side dependency is
    the local orthonormal-columns proof for the MGS `Q` factor. -/
theorem exists_transpose_tall_qr_of_mgs_orthonormal {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ)
    (hdiag : ∀ k : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun j : Fin (p + q) => fun i : Fin p => B i j) k.val k) ≠ 0)
    (horth : GramSchmidtOrthonormalColumns
      (modifiedGramSchmidtQ
        (fun j : Fin (p + q) => fun i : Fin p => B i j))) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (R : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsUpperTriangular p R ∧
        matMulRectLeft (matTranspose Q)
          (fun j : Fin (p + q) => fun i : Fin p => B i j) =
          lsQRTallBlock (k := q) R := by
  let Bt : Fin (p + q) → Fin p → ℝ :=
    fun j => fun i => B i j
  let R : Fin p → Fin p → ℝ := modifiedGramSchmidtR Bt
  have hfactor :
      Bt = matMulRect (p + q) p p (modifiedGramSchmidtQ Bt) R := by
    exact modifiedGramSchmidt_exact_factorization Bt hdiag
  have hRupper : IsUpperTriangular p R :=
    IsUpperTrapezoidal.to_upperTriangular
      (modifiedGramSchmidtR_upper_trapezoidal Bt)
  obtain ⟨Q, hQorth, _hpreserve, hblock⟩ :=
    exists_orthogonal_completion_tall_qr_block Bt
      (modifiedGramSchmidtQ Bt) R horth hfactor
  refine ⟨Q, R, hQorth, hRupper, ?_⟩
  simpa [Bt] using hblock

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    exact MGS data for `Bᵀ` with nonzero stage normalizers supplies the
    completed tall QR block `Qᵀ Bᵀ = [R;0]`.

    This discharges the previous explicit MGS orthonormality dependency using
    the exact MGS orthonormal-columns theorem. -/
theorem exists_transpose_tall_qr_of_mgs {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ)
    (hdiag : ∀ k : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun j : Fin (p + q) => fun i : Fin p => B i j) k.val k) ≠ 0) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (R : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsUpperTriangular p R ∧
        matMulRectLeft (matTranspose Q)
          (fun j : Fin (p + q) => fun i : Fin p => B i j) =
          lsQRTallBlock (k := q) R := by
  have horth : GramSchmidtOrthonormalColumns
      (modifiedGramSchmidtQ
        (fun j : Fin (p + q) => fun i : Fin p => B i j)) :=
    modifiedGramSchmidtQ_orthonormal_columns
      (fun j : Fin (p + q) => fun i : Fin p => B i j) hdiag
  exact exists_transpose_tall_qr_of_mgs_orthonormal B hdiag horth

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    exact MGS data for `Bᵀ`, plus the remaining MGS orthonormality
    dependency, constructs the GQR constraint block `B Q = [S 0]` with
    `S` lower triangular. -/
theorem exists_gqr_constraint_block_of_mgs_orthonormal {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ)
    (hdiag : ∀ k : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun j : Fin (p + q) => fun i : Fin p => B i j) k.val k) ≠ 0)
    (horth : GramSchmidtOrthonormalColumns
      (modifiedGramSchmidtQ
        (fun j : Fin (p + q) => fun i : Fin p => B i j))) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S := by
  obtain ⟨Q, R, hQorth, hRupper, hqr⟩ :=
    exists_transpose_tall_qr_of_mgs_orthonormal B hdiag horth
  refine ⟨Q, matTranspose R, hQorth,
    isLowerTriangular_matTranspose_of_isUpperTriangular hRupper, ?_⟩
  exact gqrBQBlock_eq_of_transpose_tall_qr B Q R hqr

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    exact MGS data for `Bᵀ` with nonzero stage normalizers constructs the GQR
    constraint block `B Q = [S 0]` with `S` lower triangular. -/
theorem exists_gqr_constraint_block_of_mgs {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ)
    (hdiag : ∀ k : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun j : Fin (p + q) => fun i : Fin p => B i j) k.val k) ≠ 0) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S := by
  have horth : GramSchmidtOrthonormalColumns
      (modifiedGramSchmidtQ
        (fun j : Fin (p + q) => fun i : Fin p => B i j)) :=
    modifiedGramSchmidtQ_orthonormal_columns
      (fun j : Fin (p + q) => fun i : Fin p => B i j) hdiag
  exact exists_gqr_constraint_block_of_mgs_orthonormal B hdiag horth

/-- Finite-index associativity equivalence used to pass between Lean's
    `k + (p + q)` row shape and Higham's associated `((k + p) + q)` display. -/
def finAddAssocEquiv (k p q : ℕ) :
    Fin ((k + p) + q) ≃ Fin (k + (p + q)) where
  toFun := Fin.cast (Nat.add_assoc k p q)
  invFun := Fin.cast (Nat.add_assoc k p q).symm
  left_inv := by
    intro i
    ext
    simp [Fin.cast]
  right_inv := by
    intro i
    ext
    simp [Fin.cast]

/-- Finite-index commutativity equivalence for row reindexing between
    `r + q` and `q + r` shapes.  It preserves the numeric index value. -/
def finAddCommEquiv (r q : ℕ) : Fin (r + q) ≃ Fin (q + r) where
  toFun := Fin.cast (Nat.add_comm r q)
  invFun := Fin.cast (Nat.add_comm q r)
  left_inv := by
    intro i
    ext
    simp [Fin.cast]
  right_inv := by
    intro i
    ext
    simp [Fin.cast]

/-- Orthonormal columns are preserved by a finite row-index equivalence. -/
theorem GramSchmidtOrthonormalColumns.reindexRowsEquiv {m m' n : ℕ}
    (e : Fin m ≃ Fin m') {Q : Fin m → Fin n → ℝ}
    (hQ : GramSchmidtOrthonormalColumns Q) :
    GramSchmidtOrthonormalColumns
      (fun i : Fin m' => fun j : Fin n => Q (e.symm i) j) := by
  intro a b
  unfold rectangularGram
  calc
    (∑ i : Fin m', Q (e.symm i) a * Q (e.symm i) b)
        = ∑ i : Fin m, Q i a * Q i b := by
            exact Equiv.sum_comp e.symm
              (fun i : Fin m => Q i a * Q i b)
    _ = idMatrix n a b := hQ a b

/-- Orthogonality is preserved by conjugating rows and columns through a finite
    index equivalence. -/
theorem IsOrthogonal.reindexRowsColsEquiv {m m' : ℕ}
    (e : Fin m ≃ Fin m') {U : Fin m' → Fin m' → ℝ}
    (hU : IsOrthogonal m' U) :
    IsOrthogonal m (fun i j : Fin m => U (e i) (e j)) := by
  constructor
  · intro i j
    unfold matTranspose
    calc
      (∑ k : Fin m, U (e k) (e i) * U (e k) (e j))
          = ∑ k' : Fin m', U k' (e i) * U k' (e j) := by
              exact Equiv.sum_comp e
                (fun k' : Fin m' => U k' (e i) * U k' (e j))
      _ = if e i = e j then 1 else 0 := hU.col_orthonormal (e i) (e j)
      _ = if i = j then 1 else 0 := by
          by_cases hij : i = j
          · subst j
            simp
          · have he : e i ≠ e j := fun heq =>
              hij ((Equiv.apply_eq_iff_eq e).1 heq)
            simp [hij, he]
  · intro i j
    unfold matTranspose
    calc
      (∑ k : Fin m, U (e i) (e k) * U (e j) (e k))
          = ∑ k' : Fin m', U (e i) k' * U (e j) k' := by
              exact Equiv.sum_comp e
                (fun k' : Fin m' => U (e i) k' * U (e j) k')
      _ = if e i = e j then 1 else 0 := by
          have hrow := hU.right_inv (e i) (e j)
          simpa [matTranspose] using hrow
      _ = if i = j then 1 else 0 := by
          by_cases hij : i = j
          · subst j
            simp
          · have he : e i ≠ e j := fun heq =>
              hij ((Equiv.apply_eq_iff_eq e).1 heq)
            simp [hij, he]

/-- Matrix-vector multiplication by the `U^T A Q` block in (20.27). -/
theorem gqrAQBlock_mulVec {r p q : ℕ}
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2) =
      Fin.append
        (rectMatMulVec L11 y1)
        (fun i : Fin q => rectMatMulVec L21 y1 i +
          rectMatMulVec L22 y2 i) := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (r + q) =>
      rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2) i =
        Fin.append (rectMatMulVec L11 y1)
          (fun i : Fin q => rectMatMulVec L21 y1 i +
            rectMatMulVec L22 y2 i) i)
    ?left ?right i
  · intro i
    unfold rectMatMulVec gqrAQBlock
    rw [Fin.append_left, Fin.append_left, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  · intro i
    unfold rectMatMulVec gqrAQBlock
    rw [Fin.append_right, Fin.append_right, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

/-- Candidate lower block `L` reconstructed from the (20.27) GQR block display
in the tall case `m >= n`, with `r = k + p`. Its first `p` rows are the bottom
`p` rows of `L11` followed by the zero block, and its last `q` rows are
`[L21 L22]`; lower-triangularity is an explicit hypothesis of the link theorem
below. -/
noncomputable def gqrAQTallLFromEq20_27 {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ) :
    Fin (p + q) → Fin (p + q) → ℝ :=
  Fin.append
    (fun i : Fin p => Fin.append (L11 (Fin.natAdd k i)) (fun _ : Fin q => 0))
    (fun i : Fin q => Fin.append (L21 i) (L22 i))

/-- Tall (20.28) reconstruction helper: the candidate square block `L`
    recovered from (20.27) is lower triangular once the trailing `p` rows of
    `L11` and the `L22` block have the corresponding lower-triangular patterns.

    This is still only block-shape algebra; it does not prove those patterns
    from a QR construction. -/
theorem gqrAQTallLFromEq20_27_lowerTriangular_of_blocks {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hL11 : ∀ i j : Fin p, i.val < j.val →
      L11 (Fin.natAdd k i) j = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22) := by
  intro i
  exact Fin.addCases
    (motive := fun i : Fin (p + q) =>
      ∀ j : Fin (p + q), i.val < j.val →
        gqrAQTallLFromEq20_27 L11 L21 L22 i j = 0)
    (fun i j hij =>
      Fin.addCases
        (motive := fun j : Fin (p + q) =>
          (Fin.castAdd q i).val < j.val →
            gqrAQTallLFromEq20_27 L11 L21 L22 (Fin.castAdd q i) j = 0)
        (fun j hij => by
          simpa [gqrAQTallLFromEq20_27] using hL11 i j (by simpa using hij))
        (fun j _hij => by
          simp [gqrAQTallLFromEq20_27])
        j hij)
    (fun i j hij =>
      Fin.addCases
        (motive := fun j : Fin (p + q) =>
          (Fin.natAdd p i).val < j.val →
            gqrAQTallLFromEq20_27 L11 L21 L22 (Fin.natAdd p i) j = 0)
        (fun j hij => by
          have hij' : p + i.val < j.val := by simpa using hij
          have hle : j.val ≤ p + i.val :=
            Nat.le_trans (Nat.le_of_lt j.isLt) (Nat.le_add_right p i.val)
          exact False.elim ((Nat.not_lt.mpr hle) hij'))
        (fun j hij => by
          simpa [gqrAQTallLFromEq20_27] using hL22 i j (by simpa using hij))
        j hij)
    i

/-- Source-facing tall-case link between the (20.27) block display and the
(20.28) display. If the leading `k` rows of `L11` vanish and the reconstructed
bottom block is lower triangular, then the row action of (20.27) is exactly
`[0; L]` in the tall case `m >= n`. -/
theorem gqrAQBlock_tall_eq20_28_row_action_of_top_zero {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, L11 (Fin.castAdd p i) j = 0)
    (hlower : IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22)) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin k),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q (Fin.castAdd p i)) = 0) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin p),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q (Fin.natAdd k i)) =
        rectMatMulVec (gqrAQTallLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q i)) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.natAdd (k + p) i) =
        rectMatMulVec (gqrAQTallLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
          (Fin.natAdd p i)) := by
  refine ⟨hlower, ?_, ?_, ?_⟩
  · intro y1 y2 i
    unfold rectMatMulVec gqrAQBlock
    rw [Fin.append_left, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right, hzero i]
  · intro y1 y2 i
    unfold rectMatMulVec gqrAQBlock gqrAQTallLFromEq20_27
    rw [Fin.append_left, Fin.append_left]
  · intro y1 y2 i
    unfold rectMatMulVec gqrAQBlock gqrAQTallLFromEq20_27
    rw [Fin.append_right, Fin.append_right]

/-- Tall (20.28) row-action reconstruction from source-shaped block conditions:
    the leading `k` rows vanish, the trailing `p` rows of `L11` are lower
    triangular, and `L22` is lower triangular.

    This avoids exposing the combined reconstructed-`L` triangularity as a
    separate hypothesis, but still does not prove those block conditions from QR.
    -/
theorem gqrAQBlock_tall_eq20_28_row_action_of_top_zero_blocks {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, L11 (Fin.castAdd p i) j = 0)
    (hL11 : ∀ i j : Fin p, i.val < j.val →
      L11 (Fin.natAdd k i) j = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin k),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q (Fin.castAdd p i)) = 0) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin p),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q (Fin.natAdd k i)) =
        rectMatMulVec (gqrAQTallLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q i)) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.natAdd (k + p) i) =
        rectMatMulVec (gqrAQTallLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
          (Fin.natAdd p i)) := by
  exact gqrAQBlock_tall_eq20_28_row_action_of_top_zero L11 L21 L22 hzero
    (gqrAQTallLFromEq20_27_lowerTriangular_of_blocks L11 L21 L22 hL11 hL22)

/-- Leading block `X` reconstructed from the (20.27) GQR block display in the
wide case `m < n`, with `p = k + r`. It consists of the first `k` columns of
`L11` and `L21`. -/
noncomputable def gqrAQWideXFromEq20_27 {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ) :
    Fin (r + q) → Fin k → ℝ :=
  Fin.append
    (fun i : Fin r => fun j : Fin k => L11 i (Fin.castAdd r j))
    (fun i : Fin q => fun j : Fin k => L21 i (Fin.castAdd r j))

/-- Candidate lower block `L` reconstructed from the (20.27) GQR block display
in the wide case `m < n`, with `p = k + r`. It consists of the trailing `r`
columns of `L11` and `L21`, together with the zero block and `L22`;
lower-triangularity is an explicit hypothesis of the link theorem below. -/
noncomputable def gqrAQWideLFromEq20_27 {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ) :
    Fin (r + q) → Fin (r + q) → ℝ :=
  Fin.append
    (fun i : Fin r => Fin.append (fun j : Fin r => L11 i (Fin.natAdd k j))
      (fun _ : Fin q => 0))
    (fun i : Fin q => Fin.append (fun j : Fin r => L21 i (Fin.natAdd k j)) (L22 i))

/-- Wide (20.28) reconstruction helper: the candidate trailing square block `L`
    recovered from (20.27) is lower triangular once the trailing `r` columns of
    `L11` and the `L22` block have the corresponding lower-triangular patterns.

    This is still only block-shape algebra; it does not prove those patterns
    from a QR construction. -/
theorem gqrAQWideLFromEq20_27_lowerTriangular_of_blocks {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hL11 : ∀ i j : Fin r, i.val < j.val →
      L11 i (Fin.natAdd k j) = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22) := by
  intro i
  exact Fin.addCases
    (motive := fun i : Fin (r + q) =>
      ∀ j : Fin (r + q), i.val < j.val →
        gqrAQWideLFromEq20_27 L11 L21 L22 i j = 0)
    (fun i j hij =>
      Fin.addCases
        (motive := fun j : Fin (r + q) =>
          (Fin.castAdd q i).val < j.val →
            gqrAQWideLFromEq20_27 L11 L21 L22 (Fin.castAdd q i) j = 0)
        (fun j hij => by
          simpa [gqrAQWideLFromEq20_27] using hL11 i j (by simpa using hij))
        (fun j _hij => by
          simp [gqrAQWideLFromEq20_27])
        j hij)
    (fun i j hij =>
      Fin.addCases
        (motive := fun j : Fin (r + q) =>
          (Fin.natAdd r i).val < j.val →
            gqrAQWideLFromEq20_27 L11 L21 L22 (Fin.natAdd r i) j = 0)
        (fun j hij => by
          have hij' : r + i.val < j.val := by simpa using hij
          have hle : j.val ≤ r + i.val :=
            Nat.le_trans (Nat.le_of_lt j.isLt) (Nat.le_add_right r i.val)
          exact False.elim ((Nat.not_lt.mpr hle) hij'))
        (fun j hij => by
          simpa [gqrAQWideLFromEq20_27] using hL22 i j (by simpa using hij))
        j hij)
    i

/-- Source-facing wide-case link between the (20.27) block display and the
(20.28) display. If the reconstructed trailing block is lower triangular, then
the row action of (20.27) is exactly `[X L]` in the wide case `m < n`. -/
theorem gqrAQBlock_wide_eq20_28_row_action {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hlower : IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22)) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin r),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append (Fin.append y0 y1) y2)
          (Fin.castAdd q i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 L11 L21) y0 (Fin.castAdd q i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
            (Fin.castAdd q i)) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append (Fin.append y0 y1) y2)
          (Fin.natAdd r i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 L11 L21) y0 (Fin.natAdd r i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
            (Fin.natAdd r i)) := by
  refine ⟨hlower, ?_, ?_⟩
  · intro y0 y1 y2 i
    unfold rectMatMulVec gqrAQBlock gqrAQWideXFromEq20_27 gqrAQWideLFromEq20_27
    simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right, add_comm]
  · intro y0 y1 y2 i
    unfold rectMatMulVec gqrAQBlock gqrAQWideXFromEq20_27 gqrAQWideLFromEq20_27
    simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right, add_assoc]

/-- Wide (20.28) row-action reconstruction from source-shaped block
    conditions: the trailing `r` columns of `L11` and the `L22` block have the
    corresponding lower-triangular patterns.

    This avoids exposing the combined reconstructed-`L` triangularity as a
    separate hypothesis, but still does not prove those block conditions from QR.
    -/
theorem gqrAQBlock_wide_eq20_28_row_action_of_blocks {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hL11 : ∀ i j : Fin r, i.val < j.val →
      L11 i (Fin.natAdd k j) = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin r),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append (Fin.append y0 y1) y2)
          (Fin.castAdd q i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 L11 L21) y0 (Fin.castAdd q i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
            (Fin.castAdd q i)) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append (Fin.append y0 y1) y2)
          (Fin.natAdd r i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 L11 L21) y0 (Fin.natAdd r i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
            (Fin.natAdd r i)) := by
  exact gqrAQBlock_wide_eq20_28_row_action L11 L21 L22
    (gqrAQWideLFromEq20_27_lowerTriangular_of_blocks L11 L21 L22 hL11 hL22)

/-- Associated-row version of the tall (20.28) block `[0; L]` with row type
`Fin ((k + p) + q)`, matching the row association of (20.27) when
`r = k + p`. -/
noncomputable def gqrAQTallBlockAssoc {k p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ) :
    Fin ((k + p) + q) → Fin (p + q) → ℝ :=
  Fin.append
    (Fin.append (fun _ : Fin k => fun _ : Fin (p + q) => 0)
      (fun i : Fin p => fun j => L (Fin.castAdd q i) j))
    (fun i : Fin q => fun j => L (Fin.natAdd p i) j)

/-- Vector-action form of the associated-row tall (20.28) block `[0; L]`,
    matching the row association used by (20.27). -/
theorem gqrAQTallBlockAssoc_mulVec {k p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ)
    (y : Fin (p + q) → ℝ) :
    rectMatMulVec (gqrAQTallBlockAssoc (k := k) L) y =
      Fin.append
        (Fin.append (0 : Fin k → ℝ)
          (fun i : Fin p => rectMatMulVec L y (Fin.castAdd q i)))
        (fun i : Fin q => rectMatMulVec L y (Fin.natAdd p i)) := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin ((k + p) + q) =>
      rectMatMulVec (gqrAQTallBlockAssoc (k := k) L) y i =
        Fin.append
          (Fin.append (0 : Fin k → ℝ)
            (fun i : Fin p => rectMatMulVec L y (Fin.castAdd q i)))
          (fun i : Fin q => rectMatMulVec L y (Fin.natAdd p i)) i)
    ?topRows ?bottomRows i
  · intro i
    refine Fin.addCases
      (motive := fun i : Fin (k + p) =>
        rectMatMulVec (gqrAQTallBlockAssoc (k := k) L) y (Fin.castAdd q i) =
          Fin.append
            (Fin.append (0 : Fin k → ℝ)
              (fun i : Fin p => rectMatMulVec L y (Fin.castAdd q i)))
            (fun i : Fin q => rectMatMulVec L y (Fin.natAdd p i))
            (Fin.castAdd q i))
      ?zeroRows ?middleRows i
    · intro i
      simp [rectMatMulVec, gqrAQTallBlockAssoc]
    · intro i
      simp [rectMatMulVec, gqrAQTallBlockAssoc]
  · intro i
    simp [rectMatMulVec, gqrAQTallBlockAssoc]

/-- Higham, 2nd ed., Chapter 20, equation (20.28), associated-row tall-case
    shape for `U^T A Q = [0; L]` in the row association used by (20.27).

    This records the exact displayed block shape once the transformed matrix is
    supplied. It does not construct the orthogonal factors. -/
structure GQRAQTallAssocCase (k p q : ℕ)
    (M : Fin ((k + p) + q) → Fin (p + q) → ℝ) where
  /-- Lower-triangular square block `L`. -/
  L : Fin (p + q) → Fin (p + q) → ℝ
  /-- Source triangularity condition on `L`. -/
  lowerL : IsLowerTriangular L
  /-- Source block identity `M = [0; L]` with associated rows. -/
  aq_eq : M = gqrAQTallBlockAssoc (k := k) L

/-- Vector-action form of a supplied associated-row tall (20.28) shape. -/
theorem GQRAQTallAssocCase.mulVec_eq {k p q : ℕ}
    {M : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    (h : GQRAQTallAssocCase k p q M) (y : Fin (p + q) → ℝ) :
    rectMatMulVec M y =
      Fin.append
        (Fin.append (0 : Fin k → ℝ)
          (fun i : Fin p => rectMatMulVec h.L y (Fin.castAdd q i)))
        (fun i : Fin q => rectMatMulVec h.L y (Fin.natAdd p i)) := by
  rcases h with ⟨L, _lowerL, hM⟩
  subst M
  simpa using gqrAQTallBlockAssoc_mulVec (k := k) L y

/-- Tall (20.28)-to-(20.27) extraction: the `L11` block induced by a supplied
    `[0; L]` shape. Its leading `k` rows vanish and its trailing `p` rows are
    the first `p` columns of `L`. -/
noncomputable def gqrAQTallL11FromEq20_28 {k p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ) :
    Fin (k + p) → Fin p → ℝ :=
  Fin.append
    (fun _ : Fin k => fun _ : Fin p => 0)
    (fun i : Fin p => fun j : Fin p => L (Fin.castAdd q i) (Fin.castAdd q j))

/-- Tall (20.28)-to-(20.27) extraction: the `L21` block induced by a supplied
    `[0; L]` shape. -/
noncomputable def gqrAQTallL21FromEq20_28 {p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ) :
    Fin q → Fin p → ℝ :=
  fun i : Fin q => fun j : Fin p => L (Fin.natAdd p i) (Fin.castAdd q j)

/-- Tall (20.28)-to-(20.27) extraction: the trailing `L22` block induced by a
    supplied `[0; L]` shape. -/
noncomputable def gqrAQTallL22FromEq20_28 {p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ) :
    Fin q → Fin q → ℝ :=
  fun i : Fin q => fun j : Fin q => L (Fin.natAdd p i) (Fin.natAdd p j)

/-- The trailing `L22` block extracted from a lower-triangular tall-case
    (20.28) block is lower triangular. -/
theorem gqrAQTallL22FromEq20_28_lowerTriangular {p q : ℕ}
    {L : Fin (p + q) → Fin (p + q) → ℝ}
    (hL : IsLowerTriangular L) :
    IsLowerTriangular (gqrAQTallL22FromEq20_28 L) := by
  intro i j hij
  unfold gqrAQTallL22FromEq20_28
  exact hL (Fin.natAdd p i) (Fin.natAdd p j) (by simpa using hij)

/-- Tall-case reverse block packaging: extracting `L11`, `L21`, and `L22`
    from a supplied (20.28) `[0; L]` shape gives the (20.27) `UᵀAQ` block.

    This is the algebraic direction needed by the construction route in
    Theorem 20.9 after an orthogonal `U` has been supplied with
    `Uᵀ(AQ) = [0; L]`. It does not construct `U`. -/
theorem gqrAQBlock_eq_tallBlockAssoc_of_eq20_28 {k p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ)
    (hL : IsLowerTriangular L) :
    gqrAQBlock
        (gqrAQTallL11FromEq20_28 (k := k) L)
        (gqrAQTallL21FromEq20_28 L)
        (gqrAQTallL22FromEq20_28 L) =
      gqrAQTallBlockAssoc (k := k) L := by
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin ((k + p) + q) =>
      gqrAQBlock
          (gqrAQTallL11FromEq20_28 (k := k) L)
          (gqrAQTallL21FromEq20_28 L)
          (gqrAQTallL22FromEq20_28 L) i j =
        gqrAQTallBlockAssoc (k := k) L i j)
    ?topRows ?bottomRows i
  · intro i
    refine Fin.addCases
      (motive := fun i : Fin (k + p) =>
        gqrAQBlock
            (gqrAQTallL11FromEq20_28 (k := k) L)
            (gqrAQTallL21FromEq20_28 L)
            (gqrAQTallL22FromEq20_28 L) (Fin.castAdd q i) j =
          gqrAQTallBlockAssoc (k := k) L (Fin.castAdd q i) j)
      ?zeroRows ?middleRows i
    · intro i
      refine Fin.addCases
        (motive := fun j : Fin (p + q) =>
          gqrAQBlock
              (gqrAQTallL11FromEq20_28 (k := k) L)
              (gqrAQTallL21FromEq20_28 L)
              (gqrAQTallL22FromEq20_28 L) (Fin.castAdd q (Fin.castAdd p i)) j =
            gqrAQTallBlockAssoc (k := k) L (Fin.castAdd q (Fin.castAdd p i)) j)
        (fun j => by
          simp [gqrAQBlock, gqrAQTallBlockAssoc, gqrAQTallL11FromEq20_28])
        (fun j => by
          simp [gqrAQBlock, gqrAQTallBlockAssoc, gqrAQTallL11FromEq20_28])
        j
    · intro i
      refine Fin.addCases
        (motive := fun j : Fin (p + q) =>
          gqrAQBlock
              (gqrAQTallL11FromEq20_28 (k := k) L)
              (gqrAQTallL21FromEq20_28 L)
              (gqrAQTallL22FromEq20_28 L) (Fin.castAdd q (Fin.natAdd k i)) j =
            gqrAQTallBlockAssoc (k := k) L (Fin.castAdd q (Fin.natAdd k i)) j)
        (fun j => by
          simp [gqrAQBlock, gqrAQTallBlockAssoc, gqrAQTallL11FromEq20_28])
        (fun j => by
          have hij : (Fin.castAdd q i).val < (Fin.natAdd p j).val :=
            Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right p j.val)
          have hzero := hL (Fin.castAdd q i) (Fin.natAdd p j) hij
          simp [gqrAQBlock, gqrAQTallBlockAssoc, gqrAQTallL11FromEq20_28,
            hzero])
        j
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin (p + q) =>
        gqrAQBlock
            (gqrAQTallL11FromEq20_28 (k := k) L)
            (gqrAQTallL21FromEq20_28 L)
            (gqrAQTallL22FromEq20_28 L) (Fin.natAdd (k + p) i) j =
          gqrAQTallBlockAssoc (k := k) L (Fin.natAdd (k + p) i) j)
      (fun j => by
        simp [gqrAQBlock, gqrAQTallBlockAssoc,
          gqrAQTallL21FromEq20_28])
      (fun j => by
        simp [gqrAQBlock, gqrAQTallBlockAssoc,
          gqrAQTallL22FromEq20_28])
      j

/-- Matrix form of the tall (20.27)-to-(20.28) reconstruction. If the leading
`k` rows of `L11` vanish and the reconstructed bottom block is lower
triangular, then the raw (20.27) matrix is the associated-row `[0; L]` block
from (20.28). -/
theorem gqrAQBlock_tall_eq20_28_matrix_of_top_zero {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, L11 (Fin.castAdd p i) j = 0)
    (hlower : IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22)) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22) ∧
      gqrAQBlock L11 L21 L22 =
        gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 L11 L21 L22) := by
  refine ⟨hlower, ?_⟩
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin ((k + p) + q) =>
      gqrAQBlock L11 L21 L22 i j =
        gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 L11 L21 L22) i j)
    ?topRows ?bottomRows i
  · intro i
    refine Fin.addCases
      (motive := fun i : Fin (k + p) =>
        gqrAQBlock L11 L21 L22 (Fin.castAdd q i) j =
          gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 L11 L21 L22)
            (Fin.castAdd q i) j)
      ?zeroRows ?middleRows i
    · intro i
      refine Fin.addCases
        (motive := fun j : Fin (p + q) =>
          gqrAQBlock L11 L21 L22 (Fin.castAdd q (Fin.castAdd p i)) j =
            gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 L11 L21 L22)
              (Fin.castAdd q (Fin.castAdd p i)) j)
        ?left ?right j
      · intro j
        unfold gqrAQBlock gqrAQTallBlockAssoc
        simp [Fin.append_left, hzero i j]
      · intro j
        unfold gqrAQBlock gqrAQTallBlockAssoc
        simp [Fin.append_left, Fin.append_right]
    · intro i
      unfold gqrAQBlock gqrAQTallBlockAssoc gqrAQTallLFromEq20_27
      simp [Fin.append_left, Fin.append_right]
  · intro i
    unfold gqrAQBlock gqrAQTallBlockAssoc gqrAQTallLFromEq20_27
    simp [Fin.append_left, Fin.append_right]

/-- Tall (20.28) matrix reconstruction from source-shaped block conditions:
    the leading `k` rows vanish, the trailing `p` rows of `L11` are lower
    triangular, and `L22` is lower triangular. -/
theorem gqrAQBlock_tall_eq20_28_matrix_of_top_zero_blocks {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, L11 (Fin.castAdd p i) j = 0)
    (hL11 : ∀ i j : Fin p, i.val < j.val →
      L11 (Fin.natAdd k i) j = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22) ∧
      gqrAQBlock L11 L21 L22 =
        gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 L11 L21 L22) := by
  exact gqrAQBlock_tall_eq20_28_matrix_of_top_zero L11 L21 L22 hzero
    (gqrAQTallLFromEq20_27_lowerTriangular_of_blocks L11 L21 L22 hL11 hL22)

/-- Associated-column version of the wide (20.28) block `[X L]` with column
type `Fin ((k + r) + q)`, matching the column association of (20.27) when
`p = k + r`. -/
noncomputable def gqrAQWideBlockAssoc {k r q : ℕ}
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin (r + q) → Fin ((k + r) + q) → ℝ :=
  fun i =>
    Fin.append
      (Fin.append (X i) (fun j : Fin r => L i (Fin.castAdd q j)))
      (fun j : Fin q => L i (Fin.natAdd r j))

/-- Leading `X` block extracted from an associated-column wide matrix in
    Higham's Chapter 20 display (20.28). -/
def gqrAQWideAssocX {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) :
    Fin (r + q) → Fin k → ℝ :=
  fun i j => M i (Fin.castAdd q (Fin.castAdd r j))

/-- Trailing square `L` block extracted from an associated-column wide matrix in
    Higham's Chapter 20 display (20.28). -/
def gqrAQWideAssocL {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) :
    Fin (r + q) → Fin (r + q) → ℝ :=
  fun i j =>
    Fin.addCases
      (motive := fun _ : Fin (r + q) => ℝ)
      (fun a : Fin r => M i (Fin.castAdd q (Fin.natAdd k a)))
      (fun b : Fin q => M i (Fin.natAdd (k + r) b)) j

/-- Any associated-column wide matrix is recovered from its leading block and
    trailing square block.  Thus, for the wide case of (20.28), only
    lower-triangularity of the trailing block is a real shape condition. -/
theorem gqrAQWideBlockAssoc_extract_eq {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) :
    M = gqrAQWideBlockAssoc (gqrAQWideAssocX M) (gqrAQWideAssocL M) := by
  ext i j
  unfold gqrAQWideBlockAssoc gqrAQWideAssocX gqrAQWideAssocL
  refine Fin.addCases ?_ ?_ j
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro j
      simp [Fin.append_left]
    · intro j
      simp [Fin.append_left, Fin.append_right]
  · intro j
    simp [Fin.append_right]

/-- Extracting the trailing associated-column wide block commutes with a square
    left multiplication. -/
theorem gqrAQWideAssocL_matMulRectLeft {k r q : ℕ}
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) :
    gqrAQWideAssocL (matMulRectLeft U M) =
      matMulRectLeft U (gqrAQWideAssocL M) := by
  ext i j
  unfold gqrAQWideAssocL matMulRectLeft
  refine Fin.addCases ?_ ?_ j
  · intro j
    simp
  · intro j
    simp

/-- Vector-action form of the associated-column wide (20.28) block `[X L]`,
    matching the column association used by (20.27). -/
theorem gqrAQWideBlockAssoc_mulVec {k r q : ℕ}
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ)
    (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec (gqrAQWideBlockAssoc X L) (Fin.append (Fin.append y0 y1) y2) =
      fun i : Fin (r + q) =>
        rectMatMulVec X y0 i + rectMatMulVec L (Fin.append y1 y2) i := by
  ext i
  simp [rectMatMulVec, gqrAQWideBlockAssoc, Fin.sum_univ_add, add_assoc]

/-- Higham, 2nd ed., Chapter 20, equation (20.28), associated-column wide-case
    shape for `U^T A Q = [X L]` in the column association used by (20.27).

    This records the exact displayed block shape once the transformed matrix is
    supplied. It does not construct the orthogonal factors. -/
structure GQRAQWideAssocCase (k r q : ℕ)
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) where
  /-- Leading block `X`. -/
  X : Fin (r + q) → Fin k → ℝ
  /-- Lower-triangular square block `L`. -/
  L : Fin (r + q) → Fin (r + q) → ℝ
  /-- Source triangularity condition on `L`. -/
  lowerL : IsLowerTriangular L
  /-- Source block identity `M = [X L]` with associated columns. -/
  aq_eq : M = gqrAQWideBlockAssoc X L

/-- Wide associated-shape constructor for Higham's Chapter 20 display (20.28):
    once the trailing extracted square block is lower triangular, the matrix has
    the required `[X L]` associated-column shape. -/
def GQRAQWideAssocCase.of_trailing_lower {k r q : ℕ}
    {M : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    (hL : IsLowerTriangular (gqrAQWideAssocL M)) :
    GQRAQWideAssocCase k r q M :=
  ⟨gqrAQWideAssocX M, gqrAQWideAssocL M, hL,
    gqrAQWideBlockAssoc_extract_eq M⟩

/-- Wide associated-shape construction from a QR transform of the column-reversed
    trailing square block.  This removes the opaque associated-shape assumption
    for the wide branch of Higham's Chapter 20 GQR construction whenever that
    square QR route is supplied. -/
theorem GQRAQWideAssocCase.exists_of_trailing_qr_reversed_cols {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ)
    (V R : Fin (r + q) → Fin (r + q) → ℝ)
    (hV : IsOrthogonal (r + q) V)
    (hR : IsUpperTriangular (r + q) R)
    (hqr : matMulRectLeft (matTranspose V)
        (rectPermuteCols Fin.revPerm (gqrAQWideAssocL M)) = R) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQWideAssocCase k r q
          (matMulRectLeft (matTranspose U) M)) := by
  rcases exists_orthogonal_gqrReverseSquare_of_qr_reversed_cols
      (gqrAQWideAssocL M) V R hV hR hqr with
    ⟨U, hU, htrail, hLower⟩
  refine ⟨U, hU, ?_⟩
  have hExtract :
      gqrAQWideAssocL (matMulRectLeft (matTranspose U) M) =
        gqrReverseSquare R := by
    rw [gqrAQWideAssocL_matMulRectLeft]
    exact htrail
  refine ⟨GQRAQWideAssocCase.of_trailing_lower ?_⟩
  rw [hExtract]
  exact hLower

/-- Exact-MGS version of
    `GQRAQWideAssocCase.exists_of_trailing_qr_reversed_cols`: nonzero MGS
    stages for the column-reversed trailing square block construct the
    orthogonal `U` and the wide associated `[X L]` shape. -/
theorem GQRAQWideAssocCase.exists_of_trailing_mgs_reversed_cols {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ)
    (hdiag : ∀ j : Fin (r + q),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (rectPermuteCols Fin.revPerm (gqrAQWideAssocL M)) j.val j) ≠ 0) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQWideAssocCase k r q
          (matMulRectLeft (matTranspose U) M)) := by
  rcases exists_orthogonal_gqrReverseSquare_of_mgs_reversed_cols
      (gqrAQWideAssocL M) hdiag with
    ⟨U, R, hU, _hRupper, htrail, hLower⟩
  refine ⟨U, hU, ?_⟩
  have hExtract :
      gqrAQWideAssocL (matMulRectLeft (matTranspose U) M) =
        gqrReverseSquare R := by
    rw [gqrAQWideAssocL_matMulRectLeft]
    exact htrail
  refine ⟨GQRAQWideAssocCase.of_trailing_lower ?_⟩
  rw [hExtract]
  exact hLower

/-- Wide associated-shape construction from exact Householder QR of the
    column-reversed trailing square block.

    This is the rank-tolerant analogue of
    `GQRAQWideAssocCase.exists_of_trailing_mgs_reversed_cols`: zero active
    columns are handled by the exact Householder recursion instead of exposed
    as nonbreakdown hypotheses. -/
theorem GQRAQWideAssocCase.exists_of_trailing_exact_householder_reversed_cols
    {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQWideAssocCase k r q
          (matMulRectLeft (matTranspose U) M)) := by
  let C : Fin (r + q) → Fin (r + q) → ℝ :=
    rectPermuteCols Fin.revPerm (gqrAQWideAssocL M)
  exact GQRAQWideAssocCase.exists_of_trailing_qr_reversed_cols
    M
    (exactHouseholderQR_Q (r + q) C)
    (exactHouseholderQR_R (r + q) C)
    (by
      simpa [C] using exactHouseholderQR_Q_orthogonal (r + q) C)
    (by
      simpa [C] using exactHouseholderQR_R_upper (r + q) C)
    (by
      simpa [C] using
        (exactHouseholderQR_R_eq_matMulRectLeft_transpose_Q (r + q) C).symm)

/-- Vector-action form of a supplied associated-column wide (20.28) shape. -/
theorem GQRAQWideAssocCase.mulVec_eq {k r q : ℕ}
    {M : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    (h : GQRAQWideAssocCase k r q M)
    (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec M (Fin.append (Fin.append y0 y1) y2) =
      fun i : Fin (r + q) =>
        rectMatMulVec h.X y0 i + rectMatMulVec h.L (Fin.append y1 y2) i := by
  rcases h with ⟨X, L, _lowerL, hM⟩
  subst M
  simpa using gqrAQWideBlockAssoc_mulVec X L y0 y1 y2

/-- Wide (20.28)-to-(20.27) extraction: the `L11` block induced by a supplied
    `[X L]` shape. Its first `k` columns come from `X`, and its trailing `r`
    columns come from the leading columns of `L`. -/
noncomputable def gqrAQWideL11FromEq20_28 {k r q : ℕ}
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin r → Fin (k + r) → ℝ :=
  fun i : Fin r =>
    Fin.append
      (X (Fin.castAdd q i))
      (fun j : Fin r => L (Fin.castAdd q i) (Fin.castAdd q j))

/-- Wide (20.28)-to-(20.27) extraction: the `L21` block induced by a supplied
    `[X L]` shape. -/
noncomputable def gqrAQWideL21FromEq20_28 {k r q : ℕ}
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin q → Fin (k + r) → ℝ :=
  fun i : Fin q =>
    Fin.append
      (X (Fin.natAdd r i))
      (fun j : Fin r => L (Fin.natAdd r i) (Fin.castAdd q j))

/-- Wide (20.28)-to-(20.27) extraction: the trailing `L22` block induced by a
    supplied `[X L]` shape. -/
noncomputable def gqrAQWideL22FromEq20_28 {r q : ℕ}
    (L : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin q → Fin q → ℝ :=
  fun i : Fin q => fun j : Fin q => L (Fin.natAdd r i) (Fin.natAdd r j)

/-- The trailing `L22` block extracted from a lower-triangular wide-case
    (20.28) block is lower triangular. -/
theorem gqrAQWideL22FromEq20_28_lowerTriangular {r q : ℕ}
    {L : Fin (r + q) → Fin (r + q) → ℝ}
    (hL : IsLowerTriangular L) :
    IsLowerTriangular (gqrAQWideL22FromEq20_28 L) := by
  intro i j hij
  unfold gqrAQWideL22FromEq20_28
  exact hL (Fin.natAdd r i) (Fin.natAdd r j) (by simpa using hij)

/-- Wide-case reverse block packaging: extracting `L11`, `L21`, and `L22`
    from a supplied (20.28) `[X L]` shape gives the (20.27) `UᵀAQ` block.

    Lower-triangularity of `L` supplies the top-right zero block in (20.27).
    This is the algebraic direction needed by the construction route in
    Theorem 20.9 after an orthogonal `U` has been supplied with
    `Uᵀ(AQ) = [X L]`. It does not construct `U`. -/
theorem gqrAQBlock_eq_wideBlockAssoc_of_eq20_28 {k r q : ℕ}
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ)
    (hL : IsLowerTriangular L) :
    gqrAQBlock
        (gqrAQWideL11FromEq20_28 X L)
        (gqrAQWideL21FromEq20_28 X L)
        (gqrAQWideL22FromEq20_28 L) =
      gqrAQWideBlockAssoc X L := by
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin (r + q) =>
      gqrAQBlock
          (gqrAQWideL11FromEq20_28 X L)
          (gqrAQWideL21FromEq20_28 X L)
          (gqrAQWideL22FromEq20_28 L) i j =
        gqrAQWideBlockAssoc X L i j)
    ?topRows ?bottomRows i
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin ((k + r) + q) =>
        gqrAQBlock
            (gqrAQWideL11FromEq20_28 X L)
            (gqrAQWideL21FromEq20_28 X L)
            (gqrAQWideL22FromEq20_28 L) (Fin.castAdd q i) j =
          gqrAQWideBlockAssoc X L (Fin.castAdd q i) j)
      ?topLeftCols ?topRightCols j
    · intro j
      refine Fin.addCases
        (motive := fun j : Fin (k + r) =>
          gqrAQBlock
              (gqrAQWideL11FromEq20_28 X L)
              (gqrAQWideL21FromEq20_28 X L)
              (gqrAQWideL22FromEq20_28 L) (Fin.castAdd q i) (Fin.castAdd q j) =
            gqrAQWideBlockAssoc X L (Fin.castAdd q i) (Fin.castAdd q j))
        (fun j => by
          simp [gqrAQBlock, gqrAQWideBlockAssoc, gqrAQWideL11FromEq20_28])
        (fun j => by
          simp [gqrAQBlock, gqrAQWideBlockAssoc, gqrAQWideL11FromEq20_28])
        j
    · intro j
      have hij : (Fin.castAdd q i).val < (Fin.natAdd r j).val :=
        Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right r j.val)
      have hzero := hL (Fin.castAdd q i) (Fin.natAdd r j) hij
      simp [gqrAQBlock, gqrAQWideBlockAssoc, hzero]
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin ((k + r) + q) =>
        gqrAQBlock
            (gqrAQWideL11FromEq20_28 X L)
            (gqrAQWideL21FromEq20_28 X L)
            (gqrAQWideL22FromEq20_28 L) (Fin.natAdd r i) j =
          gqrAQWideBlockAssoc X L (Fin.natAdd r i) j)
      ?bottomLeftCols ?bottomRightCols j
    · intro j
      refine Fin.addCases
        (motive := fun j : Fin (k + r) =>
          gqrAQBlock
              (gqrAQWideL11FromEq20_28 X L)
              (gqrAQWideL21FromEq20_28 X L)
              (gqrAQWideL22FromEq20_28 L) (Fin.natAdd r i) (Fin.castAdd q j) =
            gqrAQWideBlockAssoc X L (Fin.natAdd r i) (Fin.castAdd q j))
        (fun j => by
          simp [gqrAQBlock, gqrAQWideBlockAssoc, gqrAQWideL21FromEq20_28])
        (fun j => by
          simp [gqrAQBlock, gqrAQWideBlockAssoc, gqrAQWideL21FromEq20_28])
        j
    · intro j
      simp [gqrAQBlock, gqrAQWideBlockAssoc, gqrAQWideL22FromEq20_28]

/-- Matrix form of the wide (20.27)-to-(20.28) reconstruction. If the
reconstructed trailing block is lower triangular, then the raw (20.27) matrix is
the associated-column `[X L]` block from (20.28). -/
theorem gqrAQBlock_wide_eq20_28_matrix {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hlower : IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22)) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22) ∧
      gqrAQBlock L11 L21 L22 =
        gqrAQWideBlockAssoc
          (gqrAQWideXFromEq20_27 L11 L21)
          (gqrAQWideLFromEq20_27 L11 L21 L22) := by
  refine ⟨hlower, ?_⟩
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin (r + q) =>
      gqrAQBlock L11 L21 L22 i j =
        gqrAQWideBlockAssoc
          (gqrAQWideXFromEq20_27 L11 L21)
          (gqrAQWideLFromEq20_27 L11 L21 L22) i j)
    ?topRows ?bottomRows i
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin ((k + r) + q) =>
        gqrAQBlock L11 L21 L22 (Fin.castAdd q i) j =
          gqrAQWideBlockAssoc
            (gqrAQWideXFromEq20_27 L11 L21)
            (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.castAdd q i) j)
      ?topLeftCols ?topRightCols j
    · intro j
      refine Fin.addCases
        (motive := fun j : Fin (k + r) =>
          gqrAQBlock L11 L21 L22 (Fin.castAdd q i) (Fin.castAdd q j) =
            gqrAQWideBlockAssoc
              (gqrAQWideXFromEq20_27 L11 L21)
              (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.castAdd q i)
              (Fin.castAdd q j))
        ?topXCols ?topLCols j
      · intro j
        unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideXFromEq20_27
        simp [Fin.append_left]
      · intro j
        unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideLFromEq20_27
        simp [Fin.append_left, Fin.append_right]
    · intro j
      unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideLFromEq20_27
      simp [Fin.append_left, Fin.append_right]
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin ((k + r) + q) =>
        gqrAQBlock L11 L21 L22 (Fin.natAdd r i) j =
          gqrAQWideBlockAssoc
            (gqrAQWideXFromEq20_27 L11 L21)
            (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.natAdd r i) j)
      ?bottomLeftCols ?bottomRightCols j
    · intro j
      refine Fin.addCases
        (motive := fun j : Fin (k + r) =>
          gqrAQBlock L11 L21 L22 (Fin.natAdd r i) (Fin.castAdd q j) =
            gqrAQWideBlockAssoc
              (gqrAQWideXFromEq20_27 L11 L21)
              (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.natAdd r i)
              (Fin.castAdd q j))
        ?bottomXCols ?bottomLCols j
      · intro j
        unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideXFromEq20_27
        simp [Fin.append_left, Fin.append_right]
      · intro j
        unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideLFromEq20_27
        simp [Fin.append_left, Fin.append_right]
    · intro j
      unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideLFromEq20_27
      simp [Fin.append_left, Fin.append_right]

/-- Wide (20.28) matrix reconstruction from source-shaped block conditions:
    the trailing `r` columns of `L11` and `L22` have the displayed
    lower-triangular patterns. -/
theorem gqrAQBlock_wide_eq20_28_matrix_of_blocks {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hL11 : ∀ i j : Fin r, i.val < j.val →
      L11 i (Fin.natAdd k j) = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22) ∧
      gqrAQBlock L11 L21 L22 =
        gqrAQWideBlockAssoc
          (gqrAQWideXFromEq20_27 L11 L21)
          (gqrAQWideLFromEq20_27 L11 L21 L22) := by
  exact gqrAQBlock_wide_eq20_28_matrix L11 L21 L22
    (gqrAQWideLFromEq20_27_lowerTriangular_of_blocks L11 L21 L22 hL11 hL22)

/-- Higham, 2nd ed., Chapter 20, equation (20.28), tall case `m ≥ n`:
    the displayed block `[0; L]`, with `k = m - n` zero rows. -/
noncomputable def gqrAQTallBlock {k n : ℕ}
    (L : Fin n → Fin n → ℝ) : Fin (k + n) → Fin n → ℝ :=
  Fin.append (fun _ : Fin k => fun _ : Fin n => 0) L

/-- Matrix-vector multiplication by the tall (20.28) block `[0; L]`. -/
theorem gqrAQTallBlock_mulVec {k n : ℕ}
    (L : Fin n → Fin n → ℝ) (y : Fin n → ℝ) :
    rectMatMulVec (gqrAQTallBlock L) y =
      Fin.append (0 : Fin k → ℝ) (rectMatMulVec L y) := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (k + n) =>
      rectMatMulVec (gqrAQTallBlock L) y i =
        Fin.append (0 : Fin k → ℝ) (rectMatMulVec L y) i)
    ?left ?right i
  · intro i
    unfold rectMatMulVec gqrAQTallBlock
    rw [Fin.append_left, Fin.append_left]
    simp
  · intro i
    unfold rectMatMulVec gqrAQTallBlock
    rw [Fin.append_right, Fin.append_right]

/-- Higham, 2nd ed., Chapter 20, equation (20.28), wide case `m < n`:
    the displayed block `[X L]`, with `k = n - m` leading columns. -/
noncomputable def gqrAQWideBlock {k m : ℕ}
    (X : Fin m → Fin k → ℝ) (L : Fin m → Fin m → ℝ) :
    Fin m → Fin (k + m) → ℝ :=
  fun i => Fin.append (X i) (L i)

/-- Matrix-vector multiplication by the wide (20.28) block `[X L]`. -/
theorem gqrAQWideBlock_mulVec {k m : ℕ}
    (X : Fin m → Fin k → ℝ) (L : Fin m → Fin m → ℝ)
    (y1 : Fin k → ℝ) (y2 : Fin m → ℝ) :
    rectMatMulVec (gqrAQWideBlock X L) (Fin.append y1 y2) =
      fun i : Fin m => rectMatMulVec X y1 i + rectMatMulVec L y2 i := by
  ext i
  unfold rectMatMulVec gqrAQWideBlock
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- Higham, 2nd ed., Chapter 20, equation (20.28), supplied tall-case
    shape for `U^T A Q = [0; L]`.

    This records the exact displayed block shape once the matrix has already
    been supplied; it does not construct the orthogonal factors. -/
structure GQRAQTallCase (k n : ℕ)
    (M : Fin (k + n) → Fin n → ℝ) where
  /-- Lower-triangular square block `L`. -/
  L : Fin n → Fin n → ℝ
  /-- Source triangularity condition on `L`. -/
  lowerL : IsLowerTriangular L
  /-- Source block identity `M = [0; L]`. -/
  aq_eq : M = gqrAQTallBlock L

/-- Vector-action form of a supplied tall (20.28) shape. -/
theorem GQRAQTallCase.mulVec_eq {k n : ℕ}
    {M : Fin (k + n) → Fin n → ℝ}
    (h : GQRAQTallCase k n M) (y : Fin n → ℝ) :
    rectMatMulVec M y =
      Fin.append (0 : Fin k → ℝ) (rectMatMulVec h.L y) := by
  rcases h with ⟨L, _lowerL, hM⟩
  subst M
  simpa using gqrAQTallBlock_mulVec L y

/-- Completion helper for the tall associated (20.28) route: an orthonormal
    rectangular factor can be extended to a square orthogonal matrix whose
    bottom columns are the original columns in reverse order.

    The reversed placement is the row-side companion to applying QR/MGS to the
    column-reversed `A Q₂` block: after the later matrix-action step, the upper
    triangular QR factor becomes the lower-triangular `L₂₂` block. -/
theorem exists_orthogonal_completion_bottom_reversed_columns {r q : ℕ}
    (Q2 : Fin (r + q) → Fin q → ℝ)
    (hQ2 : GramSchmidtOrthonormalColumns Q2) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        ∀ i j, U i (Fin.natAdd r j) = Q2 i (Fin.rev j) := by
  classical
  let s : Set (Fin (r + q)) :=
    {a | ∃ j : Fin q, a = Fin.natAdd r j}
  let X : Fin (r + q) → Fin (r + q) → ℝ :=
    fun i a =>
      if ha : ∃ j : Fin q, a = Fin.natAdd r j then
        Q2 i (Fin.rev (Classical.choose ha))
      else
        0
  have hX : ∀ a b : s,
      (∑ i : Fin (r + q), X i a * X i b) =
        if a = b then 1 else 0 := by
    intro a b
    rcases a.2 with ⟨ja, hja⟩
    rcases b.2 with ⟨jb, hjb⟩
    have hXa : ∀ i : Fin (r + q), X i a = Q2 i (Fin.rev ja) := by
      intro i
      have ha : ∃ j : Fin q, (a : Fin (r + q)) = Fin.natAdd r j :=
        ⟨ja, hja⟩
      have hchoose : Classical.choose ha = ja := by
        apply (Fin.natAdd_inj r).mp
        calc
          Fin.natAdd r (Classical.choose ha) = (a : Fin (r + q)) :=
            (Classical.choose_spec ha).symm
          _ = Fin.natAdd r ja := hja
      simp [X, ha, hchoose]
    have hXb : ∀ i : Fin (r + q), X i b = Q2 i (Fin.rev jb) := by
      intro i
      have hb : ∃ j : Fin q, (b : Fin (r + q)) = Fin.natAdd r j :=
        ⟨jb, hjb⟩
      have hchoose : Classical.choose hb = jb := by
        apply (Fin.natAdd_inj r).mp
        calc
          Fin.natAdd r (Classical.choose hb) = (b : Fin (r + q)) :=
            (Classical.choose_spec hb).symm
          _ = Fin.natAdd r jb := hjb
      simp [X, hb, hchoose]
    have hsubeq : a = b ↔ ja = jb := by
      constructor
      · intro hab
        apply (Fin.natAdd_inj r).mp
        calc
          Fin.natAdd r ja = (a : Fin (r + q)) := hja.symm
          _ = (b : Fin (r + q)) := congrArg Subtype.val hab
          _ = Fin.natAdd r jb := hjb
      · intro h
        apply Subtype.ext
        calc
          (a : Fin (r + q)) = Fin.natAdd r ja := hja
          _ = Fin.natAdd r jb := by rw [h]
          _ = (b : Fin (r + q)) := hjb.symm
    calc
      (∑ i : Fin (r + q), X i a * X i b)
          =
        ∑ i : Fin (r + q), Q2 i (Fin.rev ja) * Q2 i (Fin.rev jb) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hXa i, hXb i]
      _ = idMatrix q (Fin.rev ja) (Fin.rev jb) :=
            hQ2 (Fin.rev ja) (Fin.rev jb)
      _ = if a = b then 1 else 0 := by
          by_cases h : ja = jb
          · subst jb
            have hab : a = b := hsubeq.mpr rfl
            simp [idMatrix, hab]
          · have hab : a ≠ b := fun hab => h (hsubeq.mp hab)
            have hrev : Fin.rev ja ≠ Fin.rev jb :=
              fun hrev => h (Fin.rev_injective hrev)
            simp [idMatrix, hrev, hab]
  obtain ⟨U, hUpreserve, hUcols⟩ :=
    partialColOrthonormal_exists_fullColOrthonormal X s hX
  refine ⟨U, isOrthogonal_of_column_orthonormal hUcols, ?_⟩
  intro i j
  have hmem : Fin.natAdd r j ∈ s := ⟨j, rfl⟩
  have hp := hUpreserve (Fin.natAdd r j) hmem i
  have hcast : ∃ k : Fin q, Fin.natAdd r j = Fin.natAdd r k :=
    ⟨j, rfl⟩
  have hchoose : Classical.choose hcast = j := by
    apply (Fin.natAdd_inj r).mp
    exact (Classical.choose_spec hcast).symm
  simpa [X, hcast, hchoose] using hp

/-- Tall associated-shape construction from a QR factorization of the
    column-reversed block.  If
    `rectPermuteCols Fin.revPerm C = Q2 R` with orthonormal `Q2` columns and
    upper-triangular `R`, then a completed square orthogonal `U` sends the
    original block `C` to `[0; gqrReverseSquare R]`.

    This is the small-block row/column orientation step needed for the
    oracle-recommended `A Q₂` route in Higham's Chapter 20 GQR construction. -/
theorem GQRAQTallCase.exists_of_qr_reversed_cols {r q : ℕ}
    (C : Fin (r + q) → Fin q → ℝ)
    (Q2 : Fin (r + q) → Fin q → ℝ)
    (R : Fin q → Fin q → ℝ)
    (hQ2 : GramSchmidtOrthonormalColumns Q2)
    (hR : IsUpperTriangular q R)
    (hfactor : rectPermuteCols Fin.revPerm C =
      matMulRect (r + q) q q Q2 R) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQTallCase r q (matMulRectLeft (matTranspose U) C)) := by
  rcases exists_orthogonal_completion_bottom_reversed_columns Q2 hQ2 with
    ⟨U, hU, hUbottom⟩
  let L : Fin q → Fin q → ℝ := gqrReverseSquare R
  refine ⟨U, hU, ⟨⟨L, gqrReverseSquare_lowerTriangular_of_upper hR, ?_⟩⟩⟩
  ext row col
  have hC : ∀ i : Fin (r + q),
      C i col = ∑ k : Fin q, Q2 i k * R k (Fin.rev col) := by
    intro i
    have hentry := congrFun (congrFun hfactor i) (Fin.rev col)
    simpa [rectPermuteCols, matMulRect] using hentry
  have hsum_rearrange : ∀ a : Fin (r + q),
      (∑ i : Fin (r + q),
          U i a * (∑ k : Fin q, Q2 i k * R k (Fin.rev col))) =
        ∑ k : Fin q,
          (∑ i : Fin (r + q), U i a * Q2 i k) * R k (Fin.rev col) := by
    intro a
    calc
      (∑ i : Fin (r + q),
          U i a * (∑ k : Fin q, Q2 i k * R k (Fin.rev col)))
          =
        ∑ i : Fin (r + q), ∑ k : Fin q,
          U i a * (Q2 i k * R k (Fin.rev col)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ =
        ∑ k : Fin q, ∑ i : Fin (r + q),
          U i a * (Q2 i k * R k (Fin.rev col)) := by
            rw [Finset.sum_comm]
      _ =
        ∑ k : Fin q,
          (∑ i : Fin (r + q), U i a * Q2 i k) * R k (Fin.rev col) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
  refine Fin.addCases
    (motive := fun row : Fin (r + q) =>
      matMulRectLeft (matTranspose U) C row col =
        gqrAQTallBlock (k := r) L row col)
    ?topRows ?bottomRows row
  · intro row
    have htail_orth : ∀ k : Fin q,
        (∑ i : Fin (r + q), U i (Fin.castAdd q row) * Q2 i k) = 0 := by
      intro k
      have hne :
          Fin.castAdd q row ≠ Fin.natAdd r (Fin.rev k) := by
        intro h
        have hval := congrArg Fin.val h
        have hrle : r ≤ row.val := by
          calc
            r ≤ r + (Fin.rev k).val := Nat.le_add_right r (Fin.rev k).val
            _ = row.val := hval.symm
        exact (Nat.not_le_of_gt row.isLt) hrle
      have hpreserve : ∀ i : Fin (r + q),
          U i (Fin.natAdd r (Fin.rev k)) = Q2 i k := by
        intro i
        simpa using hUbottom i (Fin.rev k)
      calc
        (∑ i : Fin (r + q), U i (Fin.castAdd q row) * Q2 i k)
            =
          ∑ i : Fin (r + q),
            U i (Fin.castAdd q row) * U i (Fin.natAdd r (Fin.rev k)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hpreserve i]
        _ = 0 := by
              simpa [hne] using
                hU.col_orthonormal (Fin.castAdd q row)
                  (Fin.natAdd r (Fin.rev k))
    calc
      matMulRectLeft (matTranspose U) C (Fin.castAdd q row) col
          =
        ∑ i : Fin (r + q), U i (Fin.castAdd q row) * C i col := by
            simp [matMulRectLeft, matTranspose]
      _ =
        ∑ i : Fin (r + q),
          U i (Fin.castAdd q row) *
            (∑ k : Fin q, Q2 i k * R k (Fin.rev col)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hC i]
      _ =
        ∑ k : Fin q,
          (∑ i : Fin (r + q), U i (Fin.castAdd q row) * Q2 i k) *
            R k (Fin.rev col) := hsum_rearrange (Fin.castAdd q row)
      _ = 0 := by
            simp [htail_orth]
      _ = gqrAQTallBlock (k := r) L (Fin.castAdd q row) col := by
            simp [gqrAQTallBlock]
  · intro row
    have hpreserve : ∀ i : Fin (r + q),
        U i (Fin.natAdd r row) = Q2 i (Fin.rev row) := by
      intro i
      exact hUbottom i row
    calc
      matMulRectLeft (matTranspose U) C (Fin.natAdd r row) col
          =
        ∑ i : Fin (r + q), U i (Fin.natAdd r row) * C i col := by
            simp [matMulRectLeft, matTranspose]
      _ =
        ∑ i : Fin (r + q),
          U i (Fin.natAdd r row) *
            (∑ k : Fin q, Q2 i k * R k (Fin.rev col)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hC i]
      _ =
        ∑ k : Fin q,
          (∑ i : Fin (r + q), U i (Fin.natAdd r row) * Q2 i k) *
            R k (Fin.rev col) := hsum_rearrange (Fin.natAdd r row)
      _ =
        ∑ k : Fin q,
          (∑ i : Fin (r + q), Q2 i (Fin.rev row) * Q2 i k) *
            R k (Fin.rev col) := by
            apply Finset.sum_congr rfl
            intro k _
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            rw [hpreserve i]
      _ =
        ∑ k : Fin q, idMatrix q (Fin.rev row) k * R k (Fin.rev col) := by
            apply Finset.sum_congr rfl
            intro k _
            have horth :
                (∑ i : Fin (r + q), Q2 i (Fin.rev row) * Q2 i k) =
                  idMatrix q (Fin.rev row) k := by
              simpa [GramSchmidtOrthonormalColumns, rectangularGram] using
                hQ2 (Fin.rev row) k
            rw [horth]
      _ = R (Fin.rev row) (Fin.rev col) := by
            simp [idMatrix]
      _ = gqrAQTallBlock (k := r) L (Fin.natAdd r row) col := by
            simp [gqrAQTallBlock, L, gqrReverseSquare]

/-- Tall associated-shape construction from exact Householder QR of the
    column-reversed block.

    Unlike the exact-MGS wrapper, this route is rank-tolerant for the
    transformed block: zero active columns are handled by the exact Householder
    panel recursion rather than exposed as nonbreakdown hypotheses. -/
theorem GQRAQTallCase.exists_of_exact_householder_reversed_cols {r q : ℕ}
    (C : Fin (r + q) → Fin q → ℝ) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQTallCase r q (matMulRectLeft (matTranspose U) C)) := by
  let e : Fin (r + q) ≃ Fin (q + r) := finAddCommEquiv r q
  let C' : Fin (q + r) → Fin q → ℝ := fun i j => C (e.symm i) j
  let Crev : Fin (q + r) → Fin q → ℝ := rectPermuteCols Fin.revPerm C'
  let Qfull : Fin (q + r) → Fin (q + r) → ℝ :=
    exactHouseholderQRPanel_Q (q + r) q Crev
  let Rhat : Fin (q + r) → Fin q → ℝ :=
    exactHouseholderQRPanel_R (q + r) q Crev
  let Q2' : Fin (q + r) → Fin q → ℝ :=
    fun i j => Qfull i (Fin.castAdd r j)
  let R : Fin q → Fin q → ℝ :=
    fun i j => Rhat (Fin.castAdd r i) j
  have hQfull : IsOrthogonal (q + r) Qfull := by
    simpa [Qfull] using exactHouseholderQRPanel_Q_orthogonal (q + r) q Crev
  have hRhatUpper : IsUpperTrapezoidal (q + r) q Rhat := by
    simpa [Rhat] using exactHouseholderQRPanel_R_upper_trapezoidal (q + r) q Crev
  have hQ2' : GramSchmidtOrthonormalColumns Q2' := by
    intro a b
    simpa [Q2', GramSchmidtOrthonormalColumns, rectangularGram, idMatrix,
      Fin.castAdd] using
      hQfull.col_orthonormal (Fin.castAdd r a) (Fin.castAdd r b)
  have hR : IsUpperTriangular q R := by
    intro i j hji
    simpa [R, Fin.castAdd] using
      hRhatUpper (Fin.castAdd r i) j hji
  have hRhatEq :
      Rhat = matMulRectLeft (matTranspose Qfull) Crev := by
    simpa [Qfull, Rhat, Crev] using
      exactHouseholderQRPanel_R_eq_matMulRectLeft_transpose_Q
        (q + r) q Crev
  have hCrevFull : Crev = matMulRectLeft Qfull Rhat := by
    have hright :
        matMul (q + r) Qfull (matTranspose Qfull) = idMatrix (q + r) := by
      ext i j
      exact hQfull.right_inv i j
    calc
      Crev = matMulRectLeft (idMatrix (q + r)) Crev := by
          exact (matMulRectLeft_id Crev).symm
      _ = matMulRectLeft (matMul (q + r) Qfull (matTranspose Qfull)) Crev := by
          rw [hright]
      _ = matMulRectLeft Qfull (matMulRectLeft (matTranspose Qfull) Crev) := by
          rw [matMulRectLeft_assoc]
      _ = matMulRectLeft Qfull Rhat := by
          rw [← hRhatEq]
  have hThin' : Crev = matMulRect (q + r) q q Q2' R := by
    rw [hCrevFull]
    ext i j
    have hbottom : ∀ c : Fin r, Rhat (Fin.natAdd q c) j = 0 := by
      intro c
      exact hRhatUpper (Fin.natAdd q c) j
        (Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right q c.val))
    unfold matMulRectLeft matMulRect Q2' R
    rw [Fin.sum_univ_add]
    simp [hbottom]
  let Q2 : Fin (r + q) → Fin q → ℝ := fun i j => Q2' (e i) j
  have hQ2 : GramSchmidtOrthonormalColumns Q2 := by
    intro a b
    unfold rectangularGram Q2
    calc
      (∑ i : Fin (r + q), Q2' (e i) a * Q2' (e i) b)
          = ∑ i' : Fin (q + r), Q2' i' a * Q2' i' b := by
              exact Equiv.sum_comp e
                (fun i' : Fin (q + r) => Q2' i' a * Q2' i' b)
      _ = idMatrix q a b := hQ2' a b
  have hfactor :
      rectPermuteCols Fin.revPerm C = matMulRect (r + q) q q Q2 R := by
    ext i j
    have hentry := congrFun (congrFun hThin' (e i)) j
    simpa [Crev, C', Q2, rectPermuteCols, matMulRect] using hentry
  exact GQRAQTallCase.exists_of_qr_reversed_cols C Q2 R hQ2 hR hfactor

/-- Associated-row tall (20.28) construction from a QR factorization of the
    column-reversed block.  This is the same construction as
    `GQRAQTallCase.exists_of_qr_reversed_cols`, transported across the finite
    row associativity equivalence from `k + (p + q)` to `((k + p) + q)`. -/
theorem GQRAQTallAssocCase.exists_of_qr_reversed_cols {k p q : ℕ}
    (C : Fin ((k + p) + q) → Fin (p + q) → ℝ)
    (Q2 : Fin ((k + p) + q) → Fin (p + q) → ℝ)
    (R : Fin (p + q) → Fin (p + q) → ℝ)
    (hQ2 : GramSchmidtOrthonormalColumns Q2)
    (hR : IsUpperTriangular (p + q) R)
    (hfactor : rectPermuteCols Fin.revPerm C =
      matMulRect ((k + p) + q) (p + q) (p + q) Q2 R) :
    ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
      IsOrthogonal ((k + p) + q) U ∧
        Nonempty (GQRAQTallAssocCase k p q
          (matMulRectLeft (matTranspose U) C)) := by
  let e : Fin ((k + p) + q) ≃ Fin (k + (p + q)) :=
    finAddAssocEquiv k p q
  let C' : Fin (k + (p + q)) → Fin (p + q) → ℝ :=
    fun i j => C (e.symm i) j
  let Q2' : Fin (k + (p + q)) → Fin (p + q) → ℝ :=
    fun i j => Q2 (e.symm i) j
  have hQ2' : GramSchmidtOrthonormalColumns Q2' :=
    GramSchmidtOrthonormalColumns.reindexRowsEquiv e hQ2
  have hfactor' :
      rectPermuteCols Fin.revPerm C' =
        matMulRect (k + (p + q)) (p + q) (p + q) Q2' R := by
    ext i j
    have hentry := congrFun (congrFun hfactor (e.symm i)) j
    simpa [C', Q2', rectPermuteCols, matMulRect] using hentry
  rcases GQRAQTallCase.exists_of_qr_reversed_cols
      (r := k) (q := p + q) C' Q2' R hQ2' hR hfactor' with
    ⟨U', hU', hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  let U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ :=
    fun i j => U' (e i) (e j)
  refine ⟨U, IsOrthogonal.reindexRowsColsEquiv e hU', ?_⟩
  refine ⟨⟨hCase.L, hCase.lowerL, ?_⟩⟩
  ext row col
  have hrow_eq :
      matMulRectLeft (matTranspose U) C row col =
        matMulRectLeft (matTranspose U') C' (e row) col := by
    calc
      matMulRectLeft (matTranspose U) C row col
          = ∑ i : Fin ((k + p) + q), U' (e i) (e row) * C i col := by
              simp [matMulRectLeft, matTranspose, U]
      _ = ∑ i' : Fin (k + (p + q)), U' i' (e row) * C (e.symm i') col := by
              exact Equiv.sum_comp e
                (fun i' : Fin (k + (p + q)) =>
                  U' i' (e row) * C (e.symm i') col)
      _ = matMulRectLeft (matTranspose U') C' (e row) col := by
              simp [matMulRectLeft, matTranspose, C']
  have hblock_eq :
      gqrAQTallBlock hCase.L (e row) col =
        gqrAQTallBlockAssoc (k := k) hCase.L row col := by
    refine Fin.addCases
      (motive := fun row : Fin ((k + p) + q) =>
        gqrAQTallBlock hCase.L (e row) col =
          gqrAQTallBlockAssoc (k := k) hCase.L row col)
      ?topRows ?bottomRows row
    · intro row
      refine Fin.addCases
        (motive := fun row : Fin (k + p) =>
          gqrAQTallBlock hCase.L (e (Fin.castAdd q row)) col =
            gqrAQTallBlockAssoc (k := k) hCase.L (Fin.castAdd q row) col)
        ?zeroRows ?middleRows row
      · intro row
        have heq :
            e (Fin.castAdd q (Fin.castAdd p row)) =
              Fin.castAdd (p + q) row := by
          ext
          simp [e, finAddAssocEquiv, Fin.castAdd, Fin.cast]
        rw [heq]
        simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
      · intro row
        have heq :
            e (Fin.castAdd q (Fin.natAdd k row)) =
              Fin.natAdd k (Fin.castAdd q row) := by
          ext
          simp [e, finAddAssocEquiv, Fin.castAdd, Fin.natAdd, Fin.cast]
        rw [heq]
        simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
    · intro row
      have heq :
          e (Fin.natAdd (k + p) row) =
            Fin.natAdd k (Fin.natAdd p row) := by
        ext
        simp [e, finAddAssocEquiv, Fin.natAdd, Fin.cast, Nat.add_assoc]
      rw [heq]
      simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
  calc
    matMulRectLeft (matTranspose U) C row col
        = matMulRectLeft (matTranspose U') C' (e row) col := hrow_eq
    _ = gqrAQTallBlock hCase.L (e row) col := by
          simpa using congrFun (congrFun hCase.aq_eq (e row)) col
    _ = gqrAQTallBlockAssoc (k := k) hCase.L row col := hblock_eq

/-- Exact-Householder associated-row tall (20.28) construction.

    This is the rank-tolerant analogue of
    `GQRAQTallAssocCase.exists_of_mgs_reversed_cols`: the associated-row
    display is constructed from the exact Householder QR panel recursion,
    whose zero-column branch avoids any MGS nonbreakdown hypothesis on the
    transformed `AQ` block. -/
theorem GQRAQTallAssocCase.exists_of_exact_householder_reversed_cols {k p q : ℕ}
    (C : Fin ((k + p) + q) → Fin (p + q) → ℝ) :
    ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
      IsOrthogonal ((k + p) + q) U ∧
        Nonempty (GQRAQTallAssocCase k p q
          (matMulRectLeft (matTranspose U) C)) := by
  let e : Fin ((k + p) + q) ≃ Fin (k + (p + q)) :=
    finAddAssocEquiv k p q
  let C' : Fin (k + (p + q)) → Fin (p + q) → ℝ :=
    fun i j => C (e.symm i) j
  rcases GQRAQTallCase.exists_of_exact_householder_reversed_cols
      (r := k) (q := p + q) C' with
    ⟨U', hU', hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  let U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ :=
    fun i j => U' (e i) (e j)
  refine ⟨U, IsOrthogonal.reindexRowsColsEquiv e hU', ?_⟩
  refine ⟨⟨hCase.L, hCase.lowerL, ?_⟩⟩
  ext row col
  have hrow_eq :
      matMulRectLeft (matTranspose U) C row col =
        matMulRectLeft (matTranspose U') C' (e row) col := by
    calc
      matMulRectLeft (matTranspose U) C row col
          = ∑ i : Fin ((k + p) + q), U' (e i) (e row) * C i col := by
              simp [matMulRectLeft, matTranspose, U]
      _ = ∑ i' : Fin (k + (p + q)), U' i' (e row) * C (e.symm i') col := by
              exact Equiv.sum_comp e
                (fun i' : Fin (k + (p + q)) =>
                  U' i' (e row) * C (e.symm i') col)
      _ = matMulRectLeft (matTranspose U') C' (e row) col := by
              simp [matMulRectLeft, matTranspose, C']
  have hblock_eq :
      gqrAQTallBlock hCase.L (e row) col =
        gqrAQTallBlockAssoc (k := k) hCase.L row col := by
    refine Fin.addCases
      (motive := fun row : Fin ((k + p) + q) =>
        gqrAQTallBlock hCase.L (e row) col =
          gqrAQTallBlockAssoc (k := k) hCase.L row col)
      ?topRows ?bottomRows row
    · intro row
      refine Fin.addCases
        (motive := fun row : Fin (k + p) =>
          gqrAQTallBlock hCase.L (e (Fin.castAdd q row)) col =
            gqrAQTallBlockAssoc (k := k) hCase.L (Fin.castAdd q row) col)
        ?zeroRows ?middleRows row
      · intro row
        have heq :
            e (Fin.castAdd q (Fin.castAdd p row)) =
              Fin.castAdd (p + q) row := by
          ext
          simp [e, finAddAssocEquiv, Fin.castAdd, Fin.cast]
        rw [heq]
        simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
      · intro row
        have heq :
            e (Fin.castAdd q (Fin.natAdd k row)) =
              Fin.natAdd k (Fin.castAdd q row) := by
          ext
          simp [e, finAddAssocEquiv, Fin.castAdd, Fin.natAdd, Fin.cast]
        rw [heq]
        simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
    · intro row
      have heq :
          e (Fin.natAdd (k + p) row) =
            Fin.natAdd k (Fin.natAdd p row) := by
        ext
        simp [e, finAddAssocEquiv, Fin.natAdd, Fin.cast, Nat.add_assoc]
      rw [heq]
      simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
  calc
    matMulRectLeft (matTranspose U) C row col
        = matMulRectLeft (matTranspose U') C' (e row) col := hrow_eq
    _ = gqrAQTallBlock hCase.L (e row) col := by
          simpa using congrFun (congrFun hCase.aq_eq (e row)) col
    _ = gqrAQTallBlockAssoc (k := k) hCase.L row col := hblock_eq

/-- Exact-MGS associated-row tall (20.28) construction.  Nonzero exact-MGS
    stages for the column-reversed full block supply the QR factorization used
    by `GQRAQTallAssocCase.exists_of_qr_reversed_cols`. -/
theorem GQRAQTallAssocCase.exists_of_mgs_reversed_cols {k p q : ℕ}
    (C : Fin ((k + p) + q) → Fin (p + q) → ℝ)
    (hdiag : ∀ j : Fin (p + q),
      gsColumnNorm2
        (modifiedGramSchmidtVectors (rectPermuteCols Fin.revPerm C) j.val j) ≠ 0) :
    ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
      IsOrthogonal ((k + p) + q) U ∧
        Nonempty (GQRAQTallAssocCase k p q
          (matMulRectLeft (matTranspose U) C)) := by
  let Crev : Fin ((k + p) + q) → Fin (p + q) → ℝ :=
    rectPermuteCols Fin.revPerm C
  let Q2 : Fin ((k + p) + q) → Fin (p + q) → ℝ :=
    modifiedGramSchmidtQ Crev
  let R : Fin (p + q) → Fin (p + q) → ℝ :=
    modifiedGramSchmidtR Crev
  have hQ2 : GramSchmidtOrthonormalColumns Q2 :=
    modifiedGramSchmidtQ_orthonormal_columns Crev hdiag
  have hR : IsUpperTriangular (p + q) R :=
    IsUpperTrapezoidal.to_upperTriangular
      (modifiedGramSchmidtR_upper_trapezoidal Crev)
  have hfactor : rectPermuteCols Fin.revPerm C =
      matMulRect ((k + p) + q) (p + q) (p + q) Q2 R := by
    exact modifiedGramSchmidt_exact_factorization Crev hdiag
  exact GQRAQTallAssocCase.exists_of_qr_reversed_cols C Q2 R hQ2 hR hfactor

/-- Higham, 2nd ed., Chapter 20, equation (20.28), supplied wide-case
    shape for `U^T A Q = [X L]`.

    This records the exact displayed block shape once the matrix has already
    been supplied; it does not construct the orthogonal factors. -/
structure GQRAQWideCase (k m : ℕ)
    (M : Fin m → Fin (k + m) → ℝ) where
  /-- Leading block `X`. -/
  X : Fin m → Fin k → ℝ
  /-- Lower-triangular square block `L`. -/
  L : Fin m → Fin m → ℝ
  /-- Source triangularity condition on `L`. -/
  lowerL : IsLowerTriangular L
  /-- Source block identity `M = [X L]`. -/
  aq_eq : M = gqrAQWideBlock X L

/-- Vector-action form of a supplied wide (20.28) shape. -/
theorem GQRAQWideCase.mulVec_eq {k m : ℕ}
    {M : Fin m → Fin (k + m) → ℝ}
    (h : GQRAQWideCase k m M)
    (y1 : Fin k → ℝ) (y2 : Fin m → ℝ) :
    rectMatMulVec M (Fin.append y1 y2) =
      fun i : Fin m => rectMatMulVec h.X y1 i + rectMatMulVec h.L y2 i := by
  rcases h with ⟨X, L, _lowerL, hM⟩
  subst M
  simpa using gqrAQWideBlock_mulVec X L y1 y2

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, exact generalized QR
    factorization data for the block form (20.27).

    This structure records the source factorization shape once the orthogonal
    factors and blocks have been supplied.  It is not the existence theorem for
    GQR, and it does not assert the nonsingularity equivalence from (20.24);
    those remain separate source rows. -/
structure GeneralizedQRFactorization (r p q : ℕ)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) where
  /-- Right orthogonal factor `Q ∈ R^{n×n}`, with `n = p+q`. -/
  Q : Fin (p + q) → Fin (p + q) → ℝ
  /-- Left orthogonal factor `U ∈ R^{m×m}`, with `m = r+q`. -/
  U : Fin (r + q) → Fin (r + q) → ℝ
  /-- Top-left block of `U^T A Q`. -/
  L11 : Fin r → Fin p → ℝ
  /-- Bottom-left block of `U^T A Q`. -/
  L21 : Fin q → Fin p → ℝ
  /-- Bottom-right lower-triangular block of `U^T A Q`. -/
  L22 : Fin q → Fin q → ℝ
  /-- Lower-triangular factor in `B Q = [S 0]`. -/
  S : Fin p → Fin p → ℝ
  /-- `Q` is orthogonal. -/
  orthQ : IsOrthogonal (p + q) Q
  /-- `U` is orthogonal. -/
  orthU : IsOrthogonal (r + q) U
  /-- Source block identity `U^T A Q = [[L11, 0], [L21, L22]]`. -/
  aq_eq :
    matMulRectLeft (matTranspose U)
      (matMulRect (r + q) (p + q) (p + q) A Q) =
        gqrAQBlock L11 L21 L22
  /-- Source block identity `B Q = [S, 0]`. -/
  bq_eq :
    matMulRect p (p + q) (p + q) B Q = gqrBQBlock S
  /-- `L22` is lower triangular. -/
  lowerL22 : IsLowerTriangular L22
  /-- `S` is lower triangular. -/
  lowerS : IsLowerTriangular S

/-- Source matrix obtained by transporting a supplied GQR transformed `A`
    block back through orthogonal factors `U` and `Q`.

    By construction, if `U` and `Q` are orthogonal then
    `Uᵀ * (gqrSourceAFromBlocks Q U L11 L21 L22) * Q =
    [[L11,0],[L21,L22]]`. -/
noncomputable def gqrSourceAFromBlocks {r p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ) :
    Fin (r + q) → Fin (p + q) → ℝ :=
  matMulRectLeft U
    (matMulRectRight (gqrAQBlock L11 L21 L22) (matTranspose Q))

/-- Source constraint matrix obtained by transporting a supplied GQR constraint
    block `[S,0]` back through the orthogonal factor `Q`. -/
noncomputable def gqrSourceBFromBlocks {p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (S : Fin p → Fin p → ℝ) :
    Fin p → Fin (p + q) → ℝ :=
  matMulRectRight (gqrBQBlock S) (matTranspose Q)

/-- Exact GQR factorization built by transporting supplied transformed blocks
    back to source coordinates.

    This is the algebraic constructor behind the Theorem 20.10 supplied-factor
    route: once perturbed triangular blocks are provided, they define source
    matrices whose GQR factors are exactly those blocks.  It does not assert
    that those source matrices are small perturbations of a previously given
    `A` or `B`; that is a separate finite-precision bound. -/
noncomputable def GeneralizedQRFactorization.of_source_blocks
    {r p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (S : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hL22 : IsLowerTriangular L22)
    (hS : IsLowerTriangular S) :
    GeneralizedQRFactorization r p q
      (gqrSourceAFromBlocks Q U L11 L21 L22)
      (gqrSourceBFromBlocks Q S) := by
  let M : Fin (r + q) → Fin (p + q) → ℝ := gqrAQBlock L11 L21 L22
  let C : Fin p → Fin (p + q) → ℝ := gqrBQBlock S
  have hQtQ : rectMatMul (matTranspose Q) Q = idMatrix (p + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using hQ.left_inv i j
  have hUtU : rectMatMul (matTranspose U) U = idMatrix (r + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.left_inv i j
  have hMQ :
      rectMatMul (rectMatMul M (matTranspose Q)) Q = M := by
    calc
      rectMatMul (rectMatMul M (matTranspose Q)) Q =
          rectMatMul M (rectMatMul (matTranspose Q) Q) :=
            rectMatMul_assoc M (matTranspose Q) Q
      _ = rectMatMul M (idMatrix (p + q)) := by rw [hQtQ]
      _ = M := rectMatMul_id_right M
  have hCQ :
      rectMatMul (rectMatMul C (matTranspose Q)) Q = C := by
    calc
      rectMatMul (rectMatMul C (matTranspose Q)) Q =
          rectMatMul C (rectMatMul (matTranspose Q) Q) :=
            rectMatMul_assoc C (matTranspose Q) Q
      _ = rectMatMul C (idMatrix (p + q)) := by rw [hQtQ]
      _ = C := rectMatMul_id_right C
  have hAqQ :
      matMulRect (r + q) (p + q) (p + q)
          (gqrSourceAFromBlocks Q U L11 L21 L22) Q =
        matMulRectLeft U M := by
    calc
      matMulRect (r + q) (p + q) (p + q)
          (gqrSourceAFromBlocks Q U L11 L21 L22) Q =
          rectMatMul
            (rectMatMul U (rectMatMul M (matTranspose Q))) Q := by
            ext i j
            rfl
      _ = rectMatMul U (rectMatMul (rectMatMul M (matTranspose Q)) Q) :=
            rectMatMul_assoc U (rectMatMul M (matTranspose Q)) Q
      _ = rectMatMul U M := by rw [hMQ]
      _ = matMulRectLeft U M := by
            rfl
  refine
    { Q := Q
      U := U
      L11 := L11
      L21 := L21
      L22 := L22
      S := S
      orthQ := hQ
      orthU := hU
      aq_eq := ?_
      bq_eq := ?_
      lowerL22 := hL22
      lowerS := hS }
  · calc
      matMulRectLeft (matTranspose U)
          (matMulRect (r + q) (p + q) (p + q)
            (gqrSourceAFromBlocks Q U L11 L21 L22) Q) =
          matMulRectLeft (matTranspose U) (matMulRectLeft U M) := by
            rw [hAqQ]
      _ = rectMatMul (matTranspose U) (rectMatMul U M) := by
            rfl
      _ = rectMatMul (rectMatMul (matTranspose U) U) M :=
            (rectMatMul_assoc (matTranspose U) U M).symm
      _ = rectMatMul (idMatrix (r + q)) M := by rw [hUtU]
      _ = M := rectMatMul_id_left M
      _ = gqrAQBlock L11 L21 L22 := rfl
  · calc
      matMulRect p (p + q) (p + q) (gqrSourceBFromBlocks Q S) Q =
          rectMatMul (rectMatMul C (matTranspose Q)) Q := by
            ext i j
            rfl
      _ = C := hCQ
      _ = gqrBQBlock S := rfl

/-- Tall-case construction wrapper for Higham, 2nd ed., Theorem 20.9.

    Given the exact QR-derived constraint identity for `Bᵀ`, a supplied
    orthogonal `U` putting `AQ` into the tall (20.28) shape `[0; L]`, and
    lower-triangularity of that square `L`, this packages the corresponding
    (20.27) generalized-QR data. This is still a supplied-factor bridge: it
    does not construct the QR factorization of `Bᵀ` or the Householder product
    `U`. -/
theorem GeneralizedQRFactorization.exists_of_tall_qr_shapes {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (L : Fin (p + q) → Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hAQ : matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q) =
      gqrAQTallBlockAssoc (k := k) L)
    (hL : IsLowerTriangular L) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQTallL22FromEq20_28 L := by
  let L11 := gqrAQTallL11FromEq20_28 (k := k) L
  let L21 := gqrAQTallL21FromEq20_28 L
  let L22 := gqrAQTallL22FromEq20_28 L
  have hAQBlock : gqrAQBlock L11 L21 L22 = gqrAQTallBlockAssoc (k := k) L := by
    simpa [L11, L21, L22] using gqrAQBlock_eq_tallBlockAssoc_of_eq20_28
      (k := k) L hL
  have hBBlock :
      matMulRect p (p + q) (p + q) B Q = gqrBQBlock (matTranspose R) :=
    gqrBQBlock_eq_of_transpose_tall_qr B Q R hqrB
  refine ⟨
    { Q := Q
      U := U
      L11 := L11
      L21 := L21
      L22 := L22
      S := matTranspose R
      orthQ := hQ
      orthU := hU
      aq_eq := ?_
      bq_eq := hBBlock
      lowerL22 := gqrAQTallL22FromEq20_28_lowerTriangular hL
      lowerS := isLowerTriangular_matTranspose_of_isUpperTriangular hR },
    rfl, rfl, rfl, rfl⟩
  rw [hAQ, ← hAQBlock]

/-- Associated-row tall-case construction wrapper for Higham, 2nd ed.,
    Theorem 20.9.

    This consumes a supplied associated-row (20.28) shape record for
    `Uᵀ(AQ) = [0; L]` and packages the corresponding (20.27) generalized-QR
    data. It still does not construct the QR factorization of `Bᵀ` or the
    orthogonal factor `U`. -/
theorem GeneralizedQRFactorization.exists_of_tall_qr_assoc_case {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hCase : GQRAQTallAssocCase k p q
      (matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q))) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQTallL22FromEq20_28 hCase.L := by
  exact GeneralizedQRFactorization.exists_of_tall_qr_shapes
    Q U R hCase.L hQ hU hqrB hR hCase.aq_eq hCase.lowerL

/-- Wide-case construction wrapper for Higham, 2nd ed., Theorem 20.9.

    Given the exact QR-derived constraint identity for `Bᵀ`, a supplied
    orthogonal `U` putting `AQ` into the wide (20.28) shape `[X L]`, and
    lower-triangularity of the trailing square `L`, this packages the
    corresponding (20.27) generalized-QR data. This is still a supplied-factor
    bridge: it does not construct the QR factorization of `Bᵀ` or the
    Householder product `U`. -/
theorem GeneralizedQRFactorization.exists_of_wide_qr_shapes {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hAQ : matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q) =
      gqrAQWideBlockAssoc X L)
    (hL : IsLowerTriangular L) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQWideL22FromEq20_28 L := by
  let L11 := gqrAQWideL11FromEq20_28 X L
  let L21 := gqrAQWideL21FromEq20_28 X L
  let L22 := gqrAQWideL22FromEq20_28 L
  have hAQBlock : gqrAQBlock L11 L21 L22 = gqrAQWideBlockAssoc X L := by
    simpa [L11, L21, L22] using gqrAQBlock_eq_wideBlockAssoc_of_eq20_28
      X L hL
  have hBBlock :
      matMulRect (k + r) ((k + r) + q) ((k + r) + q) B Q =
        gqrBQBlock (matTranspose R) :=
    gqrBQBlock_eq_of_transpose_tall_qr B Q R hqrB
  refine ⟨
    { Q := Q
      U := U
      L11 := L11
      L21 := L21
      L22 := L22
      S := matTranspose R
      orthQ := hQ
      orthU := hU
      aq_eq := ?_
      bq_eq := hBBlock
      lowerL22 := gqrAQWideL22FromEq20_28_lowerTriangular hL
      lowerS := isLowerTriangular_matTranspose_of_isUpperTriangular hR },
    rfl, rfl, rfl, rfl⟩
  rw [hAQ, ← hAQBlock]

/-- Associated-column wide-case construction wrapper for Higham, 2nd ed.,
    Theorem 20.9.

    This consumes a supplied associated-column (20.28) shape record for
    `Uᵀ(AQ) = [X L]` and packages the corresponding (20.27) generalized-QR
    data. It still does not construct the QR factorization of `Bᵀ` or the
    orthogonal factor `U`. -/
theorem GeneralizedQRFactorization.exists_of_wide_qr_assoc_case {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hCase : GQRAQWideAssocCase k r q
      (matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q))) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQWideL22FromEq20_28 hCase.L := by
  exact GeneralizedQRFactorization.exists_of_wide_qr_shapes
    Q U R hCase.X hCase.L hQ hU hqrB hR hCase.aq_eq hCase.lowerL

/-- Tall-case construction wrapper for Higham, 2nd ed., Theorem 20.9:
    exact MGS data for `Bᵀ` supplies the `B Q = [S 0]` side, so the only
    remaining supplied construction is an associated-row shape for `Uᵀ A Q`
    for the completed orthogonal `Q`. -/
theorem GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hdiag : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col) j.val j) ≠ 0)
    (hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q)))) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  rcases exists_gqr_constraint_block_of_mgs B hdiag with
    ⟨Q, S, hQorth, hSlower, hBQ⟩
  rcases hAQ Q hQorth with ⟨U, hUorth, hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  let L11 := gqrAQTallL11FromEq20_28 (k := k) hCase.L
  let L21 := gqrAQTallL21FromEq20_28 hCase.L
  let L22 := gqrAQTallL22FromEq20_28 hCase.L
  have hAQBlock :
      gqrAQBlock L11 L21 L22 =
        gqrAQTallBlockAssoc (k := k) hCase.L := by
    simpa [L11, L21, L22] using
      gqrAQBlock_eq_tallBlockAssoc_of_eq20_28 (k := k)
        hCase.L hCase.lowerL
  refine ⟨
    { Q := Q
      U := U
      L11 := L11
      L21 := L21
      L22 := L22
      S := S
      orthQ := hQorth
      orthU := hUorth
      aq_eq := ?_
      bq_eq := hBQ
      lowerL22 := gqrAQTallL22FromEq20_28_lowerTriangular hCase.lowerL
      lowerS := hSlower }⟩
  rw [hCase.aq_eq, ← hAQBlock]

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 tall-case construction step:
    full row rank of `B` supplies the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; the remaining supplied construction is the associated-row
    `[0; L]` shape for the actual transformed `A Q`. -/
theorem GeneralizedQRFactorization.exists_of_tall_fullRowRank_constraint_and_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q)))) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  have hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  exact
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB hAQ

/-- Tall-case exact-MGS construction wrapper for Higham, 2nd ed.,
    Theorem 20.9.

    Exact MGS data for `Bᵀ` supplies the constraint side `B Q = [S 0]`.
    Exact MGS data for the column-reversed full transformed block `A Q`
    supplies the associated-row (20.28) display `Uᵀ A Q = [0; L]`. -/
theorem GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_full_mgs_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col) j.val j) ≠ 0)
    (hdiagAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∀ j : Fin (p + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))
              j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  have hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))) := by
    intro Q hQ
    exact GQRAQTallAssocCase.exists_of_mgs_reversed_cols
      (matMulRect ((k + p) + q) (p + q) (p + q) A Q)
      (hdiagAQ Q hQ)
  exact
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB hAQ

/-- Tall-case full-row-rank plus full-`AQ` exact-MGS construction wrapper for
    Higham, 2nd ed., Theorem 20.9.

    Full row rank of `B` discharges the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; the remaining explicit assumption is nonbreakdown for the
    column-reversed full transformed block `A Q`. -/
theorem GeneralizedQRFactorization.exists_of_tall_fullRowRank_constraint_and_full_mgs_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hdiagAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∀ j : Fin (p + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))
              j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  have hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  exact
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_full_mgs_assoc_shape
      (A := A) (B := B) hdiagB hdiagAQ

/-- Tall-case exact-Householder construction wrapper for Higham, 2nd ed.,
    Theorem 20.9.

    Exact MGS data for `Bᵀ` supplies the constraint side `B Q = [S 0]`.
    The associated-row (20.28) display for the full transformed block `A Q`
    is then constructed by exact Householder QR, without assuming exact-MGS
    nonbreakdown for that `AQ` block. -/
theorem GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_exact_householder_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col) j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  have hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))) := by
    intro Q _hQ
    exact GQRAQTallAssocCase.exists_of_exact_householder_reversed_cols
      (matMulRect ((k + p) + q) (p + q) (p + q) A Q)
  exact
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB hAQ

/-- Tall-case full-row-rank plus exact-Householder associated display wrapper
    for Higham, 2nd ed., Theorem 20.9.

    Full row rank of `B` discharges the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; exact Householder QR constructs the associated-row display for
    `A Q` without a separate nonbreakdown hypothesis on `AQ`. -/
theorem GeneralizedQRFactorization.exists_of_tall_fullRowRank_constraint_and_exact_householder_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  have hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  exact
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_exact_householder_assoc_shape
      (A := A) (B := B) hdiagB

/-- Wide-case construction wrapper for Higham, 2nd ed., Theorem 20.9:
    exact MGS data for `Bᵀ` supplies the `B Q = [S 0]` side, so the only
    remaining supplied construction is an associated-column shape for `Uᵀ A Q`
    for the completed orthogonal `Q`. -/
theorem GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hdiag : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0)
    (hAQ : ∀ Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ,
      IsOrthogonal ((k + r) + q) Q →
        ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
          IsOrthogonal (r + q) U ∧
            Nonempty (
            GQRAQWideAssocCase k r q
              (matMulRectLeft (matTranspose U)
                (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))) :
    Nonempty (GeneralizedQRFactorization r (k + r) q A B) := by
  rcases exists_gqr_constraint_block_of_mgs B hdiag with
    ⟨Q, S, hQorth, hSlower, hBQ⟩
  rcases hAQ Q hQorth with ⟨U, hUorth, hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  let L11 := gqrAQWideL11FromEq20_28 hCase.X hCase.L
  let L21 := gqrAQWideL21FromEq20_28 hCase.X hCase.L
  let L22 := gqrAQWideL22FromEq20_28 hCase.L
  have hAQBlock :
      gqrAQBlock L11 L21 L22 =
        gqrAQWideBlockAssoc hCase.X hCase.L := by
    simpa [L11, L21, L22] using
      gqrAQBlock_eq_wideBlockAssoc_of_eq20_28 hCase.X hCase.L hCase.lowerL
  refine ⟨
    { Q := Q
      U := U
      L11 := L11
      L21 := L21
      L22 := L22
      S := S
      orthQ := hQorth
      orthU := hUorth
      aq_eq := ?_
      bq_eq := hBQ
      lowerL22 := gqrAQWideL22FromEq20_28_lowerTriangular hCase.lowerL
      lowerS := hSlower }⟩
  rw [hCase.aq_eq, ← hAQBlock]

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 wide-case construction step:
    exact MGS data for `Bᵀ` supplies the constraint side, and exact MGS data
    for the column-reversed trailing square block of the actual transformed
    matrix `A Q` supplies the associated `[X L]` side. -/
theorem GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_trailing_mgs_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hdiagB : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0)
    (hdiagAQ : ∀ Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ,
      IsOrthogonal ((k + r) + q) Q →
        ∀ j : Fin (r + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (gqrAQWideAssocL
                  (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
              j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization r (k + r) q A B) := by
  refine
    GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB ?_
  intro Q hQorth
  exact GQRAQWideAssocCase.exists_of_trailing_mgs_reversed_cols
    (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)
    (hdiagAQ Q hQorth)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 wide-case construction step:
    full row rank of `B` supplies the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; the only remaining MGS nonbreakdown assumption is for the
    column-reversed trailing square block of the actual transformed `A Q`. -/
theorem GeneralizedQRFactorization.exists_of_wide_fullRowRank_constraint_and_trailing_mgs_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hdiagAQ : ∀ Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ,
      IsOrthogonal ((k + r) + q) Q →
        ∀ j : Fin (r + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (gqrAQWideAssocL
                  (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
              j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization r (k + r) q A B) := by
  have hdiagB : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  exact
    GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_trailing_mgs_assoc_shape
      (A := A) (B := B) hdiagB hdiagAQ

/-- Wide-case exact-Householder construction wrapper for Higham, 2nd ed.,
    Theorem 20.9.

    Exact MGS data for `B^T` supplies the constraint side `B Q = [S 0]`.
    Exact Householder QR constructs the associated-column display for the full
    transformed block `A Q` without requiring exact-MGS nonbreakdown for the
    trailing square block. -/
theorem GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_exact_householder_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hdiagB : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization r (k + r) q A B) := by
  refine
    GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB ?_
  intro Q _hQ
  exact GQRAQWideAssocCase.exists_of_trailing_exact_householder_reversed_cols
    (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)

/-- Wide-case full-row-rank plus exact-Householder associated display wrapper
    for Higham, 2nd ed., Theorem 20.9.

    Full row rank of `B` discharges the exact-MGS nonbreakdown hypotheses for
    `B^T`; exact Householder QR constructs the associated-column display for
    `A Q` without a separate nonbreakdown hypothesis on the trailing block. -/
theorem GeneralizedQRFactorization.exists_of_wide_fullRowRank_constraint_and_exact_householder_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hB : LSEFullRowRank B) :
    Nonempty (GeneralizedQRFactorization r (k + r) q A B) := by
  have hdiagB : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  exact
    GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_exact_householder_assoc_shape
      (A := A) (B := B) hdiagB

/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), tall case:
    a supplied `GeneralizedQRFactorization` connects the reconstructed
    `[0; L]` row action to the actual transformed matrix `U^T A Q`.

    This lifts `gqrAQBlock_tall_eq20_28_row_action_of_top_zero` from the raw
    block display to the stored orthogonal factors. It still assumes the
    top-zero and lower-triangular reconstruction hypotheses; it does not prove
    them from QR or construct the GQR factors. -/
theorem GeneralizedQRFactorization.tall_eq20_28_row_action_of_top_zero
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization (k + p) p q A B)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, h.L11 (Fin.castAdd p i) j = 0)
    (hlower : IsLowerTriangular (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22)) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin k),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q))
            (Fin.append y1 y2)
          (Fin.castAdd q (Fin.castAdd p i)) = 0) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin p),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q))
            (Fin.append y1 y2)
          (Fin.castAdd q (Fin.natAdd k i)) =
        rectMatMulVec (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22)
          (Fin.append y1 y2) (Fin.castAdd q i)) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q))
            (Fin.append y1 y2)
          (Fin.natAdd (k + p) i) =
        rectMatMulVec (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22)
          (Fin.append y1 y2) (Fin.natAdd p i)) := by
  have hlink :=
    gqrAQBlock_tall_eq20_28_row_action_of_top_zero
      h.L11 h.L21 h.L22 hzero hlower
  refine ⟨hlink.1, ?_, ?_, ?_⟩
  · intro y1 y2 i
    rw [h.aq_eq]
    exact hlink.2.1 y1 y2 i
  · intro y1 y2 i
    rw [h.aq_eq]
    exact hlink.2.2.1 y1 y2 i
  · intro y1 y2 i
    rw [h.aq_eq]
    exact hlink.2.2.2 y1 y2 i

/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), wide case:
    a supplied `GeneralizedQRFactorization` connects the reconstructed
    `[X L]` row action to the actual transformed matrix `U^T A Q`.

    This lifts `gqrAQBlock_wide_eq20_28_row_action` from the raw block display
    to the stored orthogonal factors. It still assumes lower-triangularity of
    the reconstructed trailing block; it does not prove that hypothesis from
    QR or construct the GQR factors. -/
theorem GeneralizedQRFactorization.wide_eq20_28_row_action
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (h : GeneralizedQRFactorization r (k + r) q A B)
    (hlower : IsLowerTriangular (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22)) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin r),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A h.Q))
            (Fin.append (Fin.append y0 y1) y2)
          (Fin.castAdd q i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 h.L11 h.L21) y0
            (Fin.castAdd q i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22)
            (Fin.append y1 y2) (Fin.castAdd q i)) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A h.Q))
            (Fin.append (Fin.append y0 y1) y2)
          (Fin.natAdd r i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 h.L11 h.L21) y0
            (Fin.natAdd r i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22)
            (Fin.append y1 y2) (Fin.natAdd r i)) := by
  have hlink := gqrAQBlock_wide_eq20_28_row_action h.L11 h.L21 h.L22 hlower
  refine ⟨hlink.1, ?_, ?_⟩
  · intro y0 y1 y2 i
    rw [h.aq_eq]
    exact hlink.2.1 y0 y1 y2 i
  · intro y0 y1 y2 i
    rw [h.aq_eq]
    exact hlink.2.2 y0 y1 y2 i

/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), tall case:
    matrix form of the supplied-GQR reconstruction. Under the explicit
    top-zero and lower-triangular reconstruction hypotheses, the actual
    transformed matrix `U^T A Q` is the associated-row `[0; L]` block from
    (20.28). -/
theorem GeneralizedQRFactorization.tall_eq20_28_matrix_of_top_zero
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization (k + p) p q A B)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, h.L11 (Fin.castAdd p i) j = 0)
    (hlower : IsLowerTriangular (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22)) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22) ∧
      matMulRectLeft (matTranspose h.U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q) =
        gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22) := by
  have hlink :=
    gqrAQBlock_tall_eq20_28_matrix_of_top_zero
      h.L11 h.L21 h.L22 hzero hlower
  refine ⟨hlink.1, ?_⟩
  rw [h.aq_eq, hlink.2]

/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), wide case:
    matrix form of the supplied-GQR reconstruction. Under the explicit
    lower-triangular reconstruction hypothesis, the actual transformed matrix
    `U^T A Q` is the associated-column `[X L]` block from (20.28). -/
theorem GeneralizedQRFactorization.wide_eq20_28_matrix
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (h : GeneralizedQRFactorization r (k + r) q A B)
    (hlower : IsLowerTriangular (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22)) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22) ∧
      matMulRectLeft (matTranspose h.U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A h.Q) =
        gqrAQWideBlockAssoc
          (gqrAQWideXFromEq20_27 h.L11 h.L21)
          (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22) := by
  have hlink := gqrAQBlock_wide_eq20_28_matrix h.L11 h.L21 h.L22 hlower
  refine ⟨hlink.1, ?_⟩
  rw [h.aq_eq, hlink.2]

/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), tall case:
    supplied-GQR row-action reconstruction from source-shaped block
    conditions.  The reconstructed lower-triangular block condition is derived
    from the trailing `L11` block and the stored `lowerL22` field. -/
theorem GeneralizedQRFactorization.tall_eq20_28_row_action_of_block_conditions
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization (k + p) p q A B)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, h.L11 (Fin.castAdd p i) j = 0)
    (hL11 : ∀ i j : Fin p, i.val < j.val →
      h.L11 (Fin.natAdd k i) j = 0) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin k),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q))
            (Fin.append y1 y2)
          (Fin.castAdd q (Fin.castAdd p i)) = 0) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin p),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q))
            (Fin.append y1 y2)
          (Fin.castAdd q (Fin.natAdd k i)) =
        rectMatMulVec (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22)
          (Fin.append y1 y2) (Fin.castAdd q i)) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q))
            (Fin.append y1 y2)
          (Fin.natAdd (k + p) i) =
        rectMatMulVec (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22)
          (Fin.append y1 y2) (Fin.natAdd p i)) := by
  exact h.tall_eq20_28_row_action_of_top_zero hzero
    (gqrAQTallLFromEq20_27_lowerTriangular_of_blocks h.L11 h.L21 h.L22
      hL11 h.lowerL22)

/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), wide case:
    supplied-GQR row-action reconstruction from source-shaped block
    conditions.  The reconstructed lower-triangular block condition is derived
    from the trailing `L11` columns and the stored `lowerL22` field. -/
theorem GeneralizedQRFactorization.wide_eq20_28_row_action_of_block_conditions
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (h : GeneralizedQRFactorization r (k + r) q A B)
    (hL11 : ∀ i j : Fin r, i.val < j.val →
      h.L11 i (Fin.natAdd k j) = 0) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin r),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A h.Q))
            (Fin.append (Fin.append y0 y1) y2)
          (Fin.castAdd q i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 h.L11 h.L21) y0
            (Fin.castAdd q i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22)
            (Fin.append y1 y2) (Fin.castAdd q i)) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A h.Q))
            (Fin.append (Fin.append y0 y1) y2)
          (Fin.natAdd r i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 h.L11 h.L21) y0
            (Fin.natAdd r i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22)
            (Fin.append y1 y2) (Fin.natAdd r i)) := by
  exact h.wide_eq20_28_row_action
    (gqrAQWideLFromEq20_27_lowerTriangular_of_blocks h.L11 h.L21 h.L22
      hL11 h.lowerL22)

/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), tall case:
    supplied-GQR matrix reconstruction from source-shaped block conditions. -/
theorem GeneralizedQRFactorization.tall_eq20_28_matrix_of_block_conditions
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization (k + p) p q A B)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, h.L11 (Fin.castAdd p i) j = 0)
    (hL11 : ∀ i j : Fin p, i.val < j.val →
      h.L11 (Fin.natAdd k i) j = 0) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22) ∧
      matMulRectLeft (matTranspose h.U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q) =
        gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22) := by
  exact h.tall_eq20_28_matrix_of_top_zero hzero
    (gqrAQTallLFromEq20_27_lowerTriangular_of_blocks h.L11 h.L21 h.L22
      hL11 h.lowerL22)

/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), wide case:
    supplied-GQR matrix reconstruction from source-shaped block conditions. -/
theorem GeneralizedQRFactorization.wide_eq20_28_matrix_of_block_conditions
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (h : GeneralizedQRFactorization r (k + r) q A B)
    (hL11 : ∀ i j : Fin r, i.val < j.val →
      h.L11 i (Fin.natAdd k j) = 0) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22) ∧
      matMulRectLeft (matTranspose h.U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A h.Q) =
        gqrAQWideBlockAssoc
          (gqrAQWideXFromEq20_27 h.L11 h.L21)
          (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22) := by
  exact h.wide_eq20_28_matrix
    (gqrAQWideLFromEq20_27_lowerTriangular_of_blocks h.L11 h.L21 h.L22
      hL11 h.lowerL22)

/-- The constraint reduction used by the GQR method after (20.27):
    for `x = Q y` and `y = [y1; y2]`, the constraint becomes `S y1`. -/
theorem GeneralizedQRFactorization.constraint_eq {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec B (matMulVec (p + q) h.Q (Fin.append y1 y2)) =
      rectMatMulVec h.S y1 := by
  let y : Fin (p + q) → ℝ := Fin.append y1 y2
  calc
    rectMatMulVec B (matMulVec (p + q) h.Q y)
        = rectMatMulVec (rectMatMul B h.Q) y := by
            simpa [y, matMulVec] using
              (rectMatMulVec_rectMatMul B h.Q y).symm
    _ = rectMatMulVec (matMulRect p (p + q) (p + q) B h.Q) y := rfl
    _ = rectMatMulVec (gqrBQBlock h.S) y := by rw [h.bq_eq]
    _ = rectMatMulVec h.S y1 := by
            simpa [y] using gqrBQBlock_mulVec h.S y1 y2

/-- If the triangular system `S y1 = d` is solved, then `x = Q [y1; y2]`
    satisfies the original equality constraint `B x = d`. -/
theorem GeneralizedQRFactorization.feasible_of_S_mulVec {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {d : Fin p → ℝ} {y1 : Fin p → ℝ} {y2 : Fin q → ℝ}
    (hy1 : rectMatMulVec h.S y1 = d) :
    LSEFeasible B d (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  intro i
  have hc := congrFun (h.constraint_eq y1 y2) i
  rw [hc]
  exact congrFun hy1 i

/-- The transformed `A` action has exactly the block vector form displayed
    after (20.27). -/
theorem GeneralizedQRFactorization.transformed_A_mulVec_eq_block {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q))
        (Fin.append y1 y2) =
      Fin.append
        (rectMatMulVec h.L11 y1)
        (fun i : Fin q => rectMatMulVec h.L21 y1 i +
          rectMatMulVec h.L22 y2 i) := by
  calc
    rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q))
        (Fin.append y1 y2)
        = rectMatMulVec (gqrAQBlock h.L11 h.L21 h.L22)
            (Fin.append y1 y2) := by
            rw [h.aq_eq]
    _ = Fin.append
        (rectMatMulVec h.L11 y1)
        (fun i : Fin q => rectMatMulVec h.L21 y1 i +
          rectMatMulVec h.L22 y2 i) := by
            exact gqrAQBlock_mulVec h.L11 h.L21 h.L22 y1 y2

/-- The GQR change of variables preserves the least-squares objective:
    minimizing with `x = Q y` is equivalent to minimizing the transformed
    residual for `U^T A Q` and `U^T b`.

    This is exact algebra for the method following (20.27); it assumes supplied
    GQR data and does not assert Theorem 20.9's existence result. -/
theorem GeneralizedQRFactorization.objective_eq_transformed {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    lsObjective
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q))
        (matMulVec (r + q) (matTranspose h.U) b)
        (Fin.append y1 y2) =
      lsObjective A b (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  let y : Fin (p + q) → ℝ := Fin.append y1 y2
  calc
    lsObjective
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q))
        (matMulVec (r + q) (matTranspose h.U) b) y
        = lsObjective
            (matMulRect (r + q) (p + q) (p + q) A h.Q) b y := by
            exact lsObjective_matMulRectLeft_orthogonal
              (matTranspose h.U)
              (matMulRect (r + q) (p + q) (p + q) A h.Q)
              b y h.orthU.transpose
    _ = lsObjective A b (matMulVec (p + q) h.Q y) := by
            simpa [matMulVec, rectMatMulVec] using
              lsObjective_matMulRect_right (r + q) (p + q) (p + q)
                A h.Q b y

/-- Block-form version of `objective_eq_transformed`: after rewriting
    `U^T A Q` by the displayed GQR block in (20.27), the transformed objective
    is still the original objective at `x = Q [y1; y2]`. -/
theorem GeneralizedQRFactorization.objective_eq_block {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    lsObjective (gqrAQBlock h.L11 h.L21 h.L22)
        (matMulVec (r + q) (matTranspose h.U) b)
        (Fin.append y1 y2) =
      lsObjective A b (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  rw [← h.aq_eq]
  exact h.objective_eq_transformed b y1 y2

private theorem vecNorm2Sq_append {r q : ℕ}
    (x : Fin r → ℝ) (y : Fin q → ℝ) :
    vecNorm2Sq (Fin.append x y) = vecNorm2Sq x + vecNorm2Sq y := by
  unfold vecNorm2Sq
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- Higham, 2nd ed., Chapter 20, equation (20.26): coefficient matrix for the
    weighted unconstrained least-squares problem `[A; mu B]`. -/
noncomputable def lseWeightedMatrix {m n p : ℕ}
    (mu : ℝ) (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) :
    Fin (m + p) → Fin n → ℝ :=
  Fin.append A (fun i j => mu * B i j)

/-- Higham, 2nd ed., Chapter 20, equation (20.26): right-hand side `[b; mu d]`
    for the weighted unconstrained least-squares problem. -/
noncomputable def lseWeightedRhs {m p : ℕ}
    (mu : ℝ) (b : Fin m → ℝ) (d : Fin p → ℝ) : Fin (m + p) → ℝ :=
  Fin.append b (fun i => mu * d i)

/-- Constraint residual `Bx - d`, the lower residual block in the weighted
    problem (20.26). -/
noncomputable def lseConstraintResidual {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ) (x : Fin n → ℝ) :
    Fin p → ℝ :=
  fun i => rectMatMulVec B x i - d i

/-- Multiplication by the stacked weighted matrix in (20.26) splits into the
    original LS action and the weighted constraint action. -/
theorem lseWeightedMatrix_mulVec {m n p : ℕ}
    (mu : ℝ) (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (x : Fin n → ℝ) :
    rectMatMulVec (lseWeightedMatrix mu A B) x =
      Fin.append (rectMatMulVec A x) (fun i => mu * rectMatMulVec B x i) := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (m + p) =>
      rectMatMulVec (lseWeightedMatrix mu A B) x i =
        Fin.append (rectMatMulVec A x) (fun i => mu * rectMatMulVec B x i) i)
    ?left ?right i
  · intro i
    unfold rectMatMulVec lseWeightedMatrix
    simp [Fin.append_left]
  · intro i
    unfold rectMatMulVec lseWeightedMatrix
    rw [Fin.append_right, Fin.append_right]
    calc
      ∑ j : Fin n, (mu * B i j) * x j
          = ∑ j : Fin n, mu * (B i j * x j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = mu * ∑ j : Fin n, B i j * x j := by
              rw [Finset.mul_sum]

/-- The residual of the weighted problem (20.26) is the stacked vector
    `[Ax-b; mu (Bx-d)]`. -/
theorem lseWeightedResidual_eq {m n p : ℕ}
    (mu : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ) (x : Fin n → ℝ) :
    lsResidual (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x =
      Fin.append (lsResidual A b x)
        (fun i => mu * lseConstraintResidual B d x i) := by
  ext i
  unfold lsResidual
  rw [show rectMatMulVec (lseWeightedMatrix mu A B) x =
      Fin.append (rectMatMulVec A x) (fun i => mu * rectMatMulVec B x i) by
        exact lseWeightedMatrix_mulVec mu A B x]
  refine Fin.addCases
    (motive := fun i : Fin (m + p) =>
      Fin.append (rectMatMulVec A x) (fun i => mu * rectMatMulVec B x i) i -
          lseWeightedRhs mu b d i =
        Fin.append (lsResidual A b x)
          (fun i => mu * lseConstraintResidual B d x i) i)
    ?left ?right i
  · intro i
    simp [lsResidual, lseWeightedRhs, Fin.append_left]
  · intro i
    simp [lseWeightedRhs, lseConstraintResidual, Fin.append_right]
    ring

/-- Exact squared-objective decomposition for the weighted unconstrained
    problem (20.26):
    `||[A; mu B]x - [b; mu d]||_2^2 =
     ||Ax-b||_2^2 + mu^2 ||Bx-d||_2^2`.

    This is only exact algebra for the weighting method; it does not prove the
    source's limiting statement as `mu → ∞`. -/
theorem lseWeightedObjective_eq {m n p : ℕ}
    (mu : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ) (x : Fin n → ℝ) :
    lsObjective (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x =
      lsObjective A b x + mu ^ 2 * vecNorm2Sq (lseConstraintResidual B d x) := by
  unfold lsObjective
  rw [lseWeightedResidual_eq, vecNorm2Sq_append, vecNorm2Sq_smul]

/-- Feasible points for the constrained problem incur no constraint penalty in
    the weighted objective (20.26). -/
theorem lseWeightedObjective_eq_of_feasible {m n p : ℕ}
    (mu : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ) (x : Fin n → ℝ)
    (hfeas : LSEFeasible B d x) :
    lsObjective (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x =
      lsObjective A b x := by
  rw [lseWeightedObjective_eq]
  have hzero : lseConstraintResidual B d x = 0 := by
    ext i
    simp [lseConstraintResidual, hfeas i]
  rw [hzero]
  simp [vecNorm2Sq]

/-- Coercivity of the weighted formulation (20.26): the weighted
    unconstrained objective dominates the penalty term
    `mu^2 * ||B x - d||_2^2`.  This is the algebraic reason large weights
    force approximate satisfaction of the equality constraint, but it is not
    the full limiting theorem. -/
theorem lseWeightedConstraintPenalty_le_objective {m n p : ℕ}
    (mu : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ) (x : Fin n → ℝ) :
    mu ^ 2 * vecNorm2Sq (lseConstraintResidual B d x) ≤
      lsObjective (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x := by
  rw [lseWeightedObjective_eq]
  have hls : 0 ≤ lsObjective A b x := by
    unfold lsObjective
    exact vecNorm2Sq_nonneg (lsResidual A b x)
  linarith

/-- Objective domination for exact minimizers of the weighted formulation
    (20.26): the unweighted least-squares objective at a weighted minimizer is
    no larger than at any feasible constrained comparator.  This is a
    finite-weight algebraic consequence of the penalty formulation, not a
    convergence theorem for `mu -> infinity`. -/
theorem lseWeightedMinimizer_objective_le_feasibleObjective {m n p : ℕ}
    (mu : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x_mu y : Fin n → ℝ)
    (hmin : IsLeastSquaresMinimizer
      (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x_mu)
    (hyfeas : LSEFeasible B d y) :
    lsObjective A b x_mu ≤ lsObjective A b y := by
  have hweighted :
      lsObjective A b x_mu +
          mu ^ 2 * vecNorm2Sq (lseConstraintResidual B d x_mu) ≤
        lsObjective A b y := by
    calc
      lsObjective A b x_mu +
          mu ^ 2 * vecNorm2Sq (lseConstraintResidual B d x_mu) =
          lsObjective (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x_mu :=
        (lseWeightedObjective_eq mu A b B d x_mu).symm
      _ ≤ lsObjective (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) y :=
        hmin y
      _ = lsObjective A b y :=
        lseWeightedObjective_eq_of_feasible mu A b B d y hyfeas
  have hpen_nonneg :
      0 ≤ mu ^ 2 * vecNorm2Sq (lseConstraintResidual B d x_mu) :=
    mul_nonneg (sq_nonneg mu) (vecNorm2Sq_nonneg (lseConstraintResidual B d x_mu))
  linarith

/-- Specialization of the finite-weight objective domination to an actual LSE
    minimizer used as comparator. -/
theorem lseWeightedMinimizer_objective_le_lseMinimizer {m n p : ℕ}
    (mu : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x_mu y : Fin n → ℝ)
    (hmin : IsLeastSquaresMinimizer
      (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x_mu)
    (hymin : IsLSEMinimizer A b B d y) :
    lsObjective A b x_mu ≤ lsObjective A b y :=
  lseWeightedMinimizer_objective_le_feasibleObjective
    mu A b B d x_mu y hmin hymin.1

private theorem continuous_lseConstraintResidual_apply {n p : ℕ}
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ) (r : Fin p) :
    Continuous (fun x : Fin n → ℝ => lseConstraintResidual B d x r) := by
  unfold lseConstraintResidual rectMatMulVec
  exact (continuous_finset_sum _ (fun j _ =>
    continuous_const.mul (continuous_apply j))).sub continuous_const

private theorem continuous_lsObjective {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Continuous (fun x : Fin n → ℝ => lsObjective A b x) := by
  unfold lsObjective vecNorm2Sq
  exact continuous_finset_sum _ (fun i _ => (((by
    unfold lsResidual rectMatMulVec
    exact (continuous_finset_sum _ (fun j _ =>
      continuous_const.mul (continuous_apply j))).sub continuous_const) :
      Continuous (fun x : Fin n → ℝ => lsResidual A b x i)).pow 2))

/-- If a candidate for the weighted problem (20.26) has objective at most `R`,
    then its squared equality-constraint residual is at most `R / mu^2`.
    This is a finite-weight approximation bound, not the source's limiting
    statement as `mu -> infinity`. -/
theorem lseConstraintResidual_normSq_le_of_weightedObjective_le {m n p : ℕ}
    {mu R : ℝ} (hmu : mu ≠ 0)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ) (x : Fin n → ℝ)
    (hobj :
      lsObjective (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x ≤ R) :
    vecNorm2Sq (lseConstraintResidual B d x) ≤ R / mu ^ 2 := by
  have hpen :
      mu ^ 2 * vecNorm2Sq (lseConstraintResidual B d x) ≤ R :=
    (lseWeightedConstraintPenalty_le_objective
      mu A b B d x).trans hobj
  have hmu_sq_pos : 0 < mu ^ 2 := sq_pos_of_ne_zero hmu
  exact (le_div_iff₀ hmu_sq_pos).2 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpen)

/-- Norm form of the finite-weight constraint control for (20.26). -/
theorem lseConstraintResidual_norm_le_sqrt_div_of_weightedObjective_le
    {m n p : ℕ} {mu R : ℝ} (hmu : mu ≠ 0)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ) (x : Fin n → ℝ)
    (hobj :
      lsObjective (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x ≤ R) :
    vecNorm2 (lseConstraintResidual B d x) ≤ Real.sqrt (R / mu ^ 2) := by
  have hsq :=
    lseConstraintResidual_normSq_le_of_weightedObjective_le
      hmu A b B d x hobj
  simpa [vecNorm2] using Real.sqrt_le_sqrt hsq

/-- Weighted-minimizer consequence for the method of weighting after (20.26):
    if `x_mu` minimizes the weighted unconstrained problem, then any feasible
    constrained point `y` bounds the squared constraint residual of `x_mu` by
    `||A y - b||_2^2 / mu^2`.  This is still finite-weight control, not the
    full `mu -> infinity` convergence theorem. -/
theorem lseWeightedMinimizer_constraintResidual_normSq_le_feasibleObjective_div_mu_sq
    {m n p : ℕ} {mu : ℝ} (hmu : mu ≠ 0)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x_mu y : Fin n → ℝ)
    (hmin : IsLeastSquaresMinimizer
      (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x_mu)
    (hyfeas : LSEFeasible B d y) :
    vecNorm2Sq (lseConstraintResidual B d x_mu) ≤
      lsObjective A b y / mu ^ 2 := by
  have hobj :
      lsObjective (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x_mu ≤
        lsObjective A b y := by
    calc
      lsObjective (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x_mu ≤
          lsObjective (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) y :=
        hmin y
      _ = lsObjective A b y :=
        lseWeightedObjective_eq_of_feasible mu A b B d y hyfeas
  exact lseConstraintResidual_normSq_le_of_weightedObjective_le
    hmu A b B d x_mu hobj

/-- Sequence-level constraint-residual convergence for the method of weighting
    after (20.26).  If the inverse squared weights tend to zero and each
    `x_mu i` is an exact minimizer of the weighted unconstrained problem, then
    the squared equality-constraint residual tends to zero.  This proves only
    feasibility convergence, not convergence to the LSE minimizer itself. -/
theorem lseWeightedMinimizer_constraintResidual_normSq_tendsto_zero_of_inv_mu_sq
    {ι : Type*} {l : Filter ι} {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (mu : ι → ℝ) (x_mu : ι → Fin n → ℝ) (y : Fin n → ℝ)
    (hmu : ∀ i, mu i ≠ 0)
    (hmin : ∀ i, IsLeastSquaresMinimizer
      (lseWeightedMatrix (mu i) A B) (lseWeightedRhs (mu i) b d) (x_mu i))
    (hyfeas : LSEFeasible B d y)
    (hInvSq : Filter.Tendsto (fun i => (mu i ^ 2)⁻¹) l (nhds 0)) :
    Filter.Tendsto
      (fun i => vecNorm2Sq (lseConstraintResidual B d (x_mu i))) l (nhds 0) := by
  have hboundlim :
      Filter.Tendsto (fun i => lsObjective A b y / mu i ^ 2) l (nhds 0) := by
    simpa [div_eq_mul_inv] using hInvSq.const_mul (lsObjective A b y)
  refine squeeze_zero ?hnonneg ?hupper hboundlim
  · intro i
    exact vecNorm2Sq_nonneg (lseConstraintResidual B d (x_mu i))
  · intro i
    exact lseWeightedMinimizer_constraintResidual_normSq_le_feasibleObjective_div_mu_sq
      (hmu i) A b B d (x_mu i) y (hmin i) hyfeas

/-- Norm form of the sequence-level feasibility convergence for the weighted
    method after (20.26).  This remains a constraint-residual theorem only; it
    does not identify the limit of the weighted minimizers. -/
theorem lseWeightedMinimizer_constraintResidual_norm_tendsto_zero_of_inv_mu_sq
    {ι : Type*} {l : Filter ι} {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (mu : ι → ℝ) (x_mu : ι → Fin n → ℝ) (y : Fin n → ℝ)
    (hmu : ∀ i, mu i ≠ 0)
    (hmin : ∀ i, IsLeastSquaresMinimizer
      (lseWeightedMatrix (mu i) A B) (lseWeightedRhs (mu i) b d) (x_mu i))
    (hyfeas : LSEFeasible B d y)
    (hInvSq : Filter.Tendsto (fun i => (mu i ^ 2)⁻¹) l (nhds 0)) :
    Filter.Tendsto
      (fun i => vecNorm2 (lseConstraintResidual B d (x_mu i))) l (nhds 0) := by
  have hsq :=
    lseWeightedMinimizer_constraintResidual_normSq_tendsto_zero_of_inv_mu_sq
      A b B d mu x_mu y hmu hmin hyfeas hInvSq
  simpa [vecNorm2] using Real.continuous_sqrt.tendsto 0 |>.comp hsq

/-- Conditional limiting handoff for the method of weighting after (20.26).
    If exact weighted minimizers have a convergent branch and their constraint
    residuals converge to zero, then the branch limit is an exact LSE
    minimizer.  This supplies the optimization-closure step, while still
    assuming the existence/convergence of the branch and residual convergence. -/
theorem lseWeightedMinimizer_tendsto_isLSEMinimizer_of_constraintResidual_tendsto_zero
    {ι : Type*} {l : Filter ι} [l.NeBot] {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (mu : ι → ℝ) (x_mu : ι → Fin n → ℝ) (x : Fin n → ℝ)
    (hlim : Filter.Tendsto x_mu l (nhds x))
    (hres :
      Filter.Tendsto (fun i => lseConstraintResidual B d (x_mu i)) l (nhds 0))
    (hmin : ∀ i, IsLeastSquaresMinimizer
      (lseWeightedMatrix (mu i) A B) (lseWeightedRhs (mu i) b d) (x_mu i)) :
    IsLSEMinimizer A b B d x := by
  refine ⟨?hfeas, ?hopt⟩
  · intro r
    have hres_x :
        Filter.Tendsto (fun i => lseConstraintResidual B d (x_mu i) r) l
          (nhds (lseConstraintResidual B d x r)) :=
      (continuous_lseConstraintResidual_apply B d r).tendsto x |>.comp hlim
    have hres_zero :
        Filter.Tendsto (fun i => lseConstraintResidual B d (x_mu i) r) l
          (nhds 0) :=
      (continuous_apply r).tendsto (0 : Fin p → ℝ) |>.comp hres
    have hzero : lseConstraintResidual B d x r = 0 :=
      tendsto_nhds_unique hres_x hres_zero
    unfold lseConstraintResidual at hzero
    linarith
  · intro y hyfeas
    have hobj_lim :
        Filter.Tendsto (fun i => lsObjective A b (x_mu i)) l
          (nhds (lsObjective A b x)) :=
      (continuous_lsObjective A b).tendsto x |>.comp hlim
    exact le_of_tendsto' hobj_lim (fun i =>
      lseWeightedMinimizer_objective_le_feasibleObjective
        (mu i) A b B d (x_mu i) y (hmin i) hyfeas)

/-- Limiting theorem for the method of weighting after (20.26).  If exact
    minimizers of the weighted problems have a convergent branch, the weights
    satisfy `(mu^2)^{-1} -> 0`, and the constrained problem has a feasible
    comparator, then the branch limit is an exact LSE minimizer.  This still
    assumes existence/convergence of the exact weighted-minimizer branch; it is
    not a finite-precision stability theorem. -/
theorem lseWeightedMinimizer_tendsto_isLSEMinimizer_of_inv_mu_sq
    {ι : Type*} {l : Filter ι} [l.NeBot] {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (mu : ι → ℝ) (x_mu : ι → Fin n → ℝ) (x y : Fin n → ℝ)
    (hlim : Filter.Tendsto x_mu l (nhds x))
    (hmu : ∀ i, mu i ≠ 0)
    (hmin : ∀ i, IsLeastSquaresMinimizer
      (lseWeightedMatrix (mu i) A B) (lseWeightedRhs (mu i) b d) (x_mu i))
    (hyfeas : LSEFeasible B d y)
    (hInvSq : Filter.Tendsto (fun i => (mu i ^ 2)⁻¹) l (nhds 0)) :
    IsLSEMinimizer A b B d x := by
  have hnorm :
      Filter.Tendsto
        (fun i => vecNorm2 (lseConstraintResidual B d (x_mu i))) l (nhds 0) :=
    lseWeightedMinimizer_constraintResidual_norm_tendsto_zero_of_inv_mu_sq
      A b B d mu x_mu y hmu hmin hyfeas hInvSq
  have hres :
      Filter.Tendsto (fun i => lseConstraintResidual B d (x_mu i)) l (nhds 0) := by
    rw [tendsto_pi_nhds]
    intro r
    have habs :
        Filter.Tendsto
          (fun i => |lseConstraintResidual B d (x_mu i) r|) l (nhds 0) := by
      refine squeeze_zero ?hnonneg ?hupper hnorm
      · intro i
        exact abs_nonneg _
      · intro i
        exact abs_coord_le_vecNorm2 (lseConstraintResidual B d (x_mu i)) r
    exact (tendsto_zero_iff_abs_tendsto_zero (f := fun i =>
      lseConstraintResidual B d (x_mu i) r)).2 habs
  exact
    lseWeightedMinimizer_tendsto_isLSEMinimizer_of_constraintResidual_tendsto_zero
      A b B d mu x_mu x hlim hres hmin

private theorem lsResidual_gqrAQBlock {r p q : ℕ}
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (c : Fin (r + q) → ℝ)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    lsResidual (gqrAQBlock L11 L21 L22) c (Fin.append y1 y2) =
      Fin.append
        (fun i : Fin r => rectMatMulVec L11 y1 i - c (Fin.castAdd q i))
        (fun i : Fin q =>
          rectMatMulVec L21 y1 i + rectMatMulVec L22 y2 i -
            c (Fin.natAdd r i)) := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (r + q) =>
      lsResidual (gqrAQBlock L11 L21 L22) c (Fin.append y1 y2) i =
        Fin.append
          (fun i : Fin r => rectMatMulVec L11 y1 i - c (Fin.castAdd q i))
          (fun i : Fin q =>
            rectMatMulVec L21 y1 i + rectMatMulVec L22 y2 i -
              c (Fin.natAdd r i)) i)
    ?left ?right i
  · intro i
    unfold lsResidual
    rw [gqrAQBlock_mulVec]
    simp [Fin.append_left]
  · intro i
    unfold lsResidual
    rw [gqrAQBlock_mulVec]
    simp [Fin.append_right]

private theorem lsObjective_gqrAQBlock_eq {r p q : ℕ}
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (c : Fin (r + q) → ℝ)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    lsObjective (gqrAQBlock L11 L21 L22) c (Fin.append y1 y2) =
      vecNorm2Sq
        (fun i : Fin r => rectMatMulVec L11 y1 i - c (Fin.castAdd q i)) +
      vecNorm2Sq
        (fun i : Fin q =>
          rectMatMulVec L21 y1 i + rectMatMulVec L22 y2 i -
            c (Fin.natAdd r i)) := by
  unfold lsObjective
  rw [lsResidual_gqrAQBlock]
  exact vecNorm2Sq_append
    (fun i : Fin r => rectMatMulVec L11 y1 i - c (Fin.castAdd q i))
    (fun i : Fin q =>
      rectMatMulVec L21 y1 i + rectMatMulVec L22 y2 i -
        c (Fin.natAdd r i))

private theorem matMulVec_orthogonal_mul_transpose {n : ℕ}
    {Q : Fin n → Fin n → ℝ} (hQ : IsOrthogonal n Q)
    (x : Fin n → ℝ) :
    matMulVec n Q (matMulVec n (matTranspose Q) x) = x := by
  ext i
  calc
    matMulVec n Q (matMulVec n (matTranspose Q) x) i
        = matMulVec n (matMul n Q (matTranspose Q)) x i := by
            exact (matMulVec_matMul n Q (matTranspose Q) x i).symm
    _ = matMulVec n (idMatrix n) x i := by
            have hmat : matMul n Q (matTranspose Q) = idMatrix n := by
              ext a b
              exact hQ.right_inv a b
            rw [hmat]
    _ = x i := by
            rw [matMulVec_id]

private theorem matMulVec_orthogonal_transpose_mul {n : ℕ}
    {Q : Fin n → Fin n → ℝ} (hQ : IsOrthogonal n Q)
    (x : Fin n → ℝ) :
    matMulVec n (matTranspose Q) (matMulVec n Q x) = x := by
  ext i
  calc
    matMulVec n (matTranspose Q) (matMulVec n Q x) i
        = matMulVec n (matMul n (matTranspose Q) Q) x i := by
            exact (matMulVec_matMul n (matTranspose Q) Q x i).symm
    _ = matMulVec n (idMatrix n) x i := by
            have hmat : matMul n (matTranspose Q) Q = idMatrix n := by
              ext a b
              exact hQ.left_inv a b
            rw [hmat]
    _ = x i := by
            rw [matMulVec_id]

private theorem matMulVec_zero {n : ℕ}
    (Q : Fin n → Fin n → ℝ) :
    matMulVec n Q (0 : Fin n → ℝ) = 0 := by
  ext i
  simp [matMulVec]

private theorem rectMatMulVec_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    rectMatMulVec A (0 : Fin n → ℝ) = 0 := by
  ext i
  simp [rectMatMulVec]

private theorem GeneralizedQRFactorization.transformed_A_action_eq
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (y : Fin (p + q) → ℝ) :
    rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q)) y =
      matMulVec (r + q) (matTranspose h.U)
        (rectMatMulVec A (matMulVec (p + q) h.Q y)) := by
  calc
    rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q)) y
        = matMulVec (r + q) (matTranspose h.U)
            (rectMatMulVec
              (matMulRect (r + q) (p + q) (p + q) A h.Q) y) := by
            exact rectMatMulVec_matMulRectLeft
              (matTranspose h.U)
              (matMulRect (r + q) (p + q) (p + q) A h.Q) y
    _ = matMulVec (r + q) (matTranspose h.U)
        (rectMatMulVec A (matMulVec (p + q) h.Q y)) := by
            have hy :
                rectMatMulVec
                    (matMulRect (r + q) (p + q) (p + q) A h.Q) y =
                  rectMatMulVec A (matMulVec (p + q) h.Q y) := by
              simpa [matMulRect, matMulVec] using
                rectMatMulVec_rectMatMul A h.Q y
            rw [hy]

private theorem GeneralizedQRFactorization.transformed_A_zero_of_A_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {y : Fin (p + q) → ℝ}
    (hy : rectMatMulVec A (matMulVec (p + q) h.Q y) = 0) :
    rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q)) y = 0 := by
  rw [h.transformed_A_action_eq y, hy]
  exact matMulVec_zero (matTranspose h.U)

private theorem GeneralizedQRFactorization.A_zero_of_transformed_A_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {y : Fin (p + q) → ℝ}
    (hy :
      rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q)) y = 0) :
    rectMatMulVec A (matMulVec (p + q) h.Q y) = 0 := by
  have haction := h.transformed_A_action_eq y
  rw [haction] at hy
  have hrecover :=
    matMulVec_orthogonal_mul_transpose h.orthU
      (rectMatMulVec A (matMulVec (p + q) h.Q y))
  rw [hy, matMulVec_zero] at hrecover
  exact hrecover.symm

private theorem finAppend_left_right {p q : ℕ}
    (y : Fin (p + q) → ℝ) :
    Fin.append
        (fun i : Fin p => y (Fin.castAdd q i))
        (fun i : Fin q => y (Fin.natAdd p i)) =
      y := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (p + q) =>
      Fin.append
          (fun i : Fin p => y (Fin.castAdd q i))
          (fun i : Fin q => y (Fin.natAdd p i)) i = y i)
    ?left ?right i
  · intro i
    simp [Fin.append_left]
  · intro i
    simp [Fin.append_right]

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof:
    under the supplied GQR block identity `BQ = [S 0]`, injectivity of `S`
    identifies the nullspace of `B` with the `Q₂` coordinate range.

    This is the formal version of the source step
    `null(B) = range(Q₂)` after `S` is nonsingular.  It still assumes supplied
    GQR data and does not construct the orthogonal factors. -/
theorem GeneralizedQRFactorization.null_B_iff_exists_Q2_coord
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hS_inj : Function.Injective (rectMatMulVec h.S))
    (x : Fin (p + q) → ℝ) :
    rectMatMulVec B x = 0 ↔
      ∃ y2 : Fin q → ℝ,
        x = matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2) := by
  constructor
  · intro hBx
    let y : Fin (p + q) → ℝ := matMulVec (p + q) (matTranspose h.Q) x
    let y1 : Fin p → ℝ := fun i => y (Fin.castAdd q i)
    let y2 : Fin q → ℝ := fun i => y (Fin.natAdd p i)
    have hy_append : Fin.append y1 y2 = y := by
      simpa [y1, y2] using finAppend_left_right (p := p) (q := q) y
    have hx_recover :
        matMulVec (p + q) h.Q (Fin.append y1 y2) = x := by
      rw [hy_append]
      exact matMulVec_orthogonal_mul_transpose h.orthQ x
    have hSy1 : rectMatMulVec h.S y1 = 0 := by
      have hc := h.constraint_eq y1 y2
      rw [hx_recover] at hc
      rw [hBx] at hc
      exact hc.symm
    have hy1_zero : y1 = 0 := by
      apply hS_inj
      rw [hSy1, rectMatMulVec_zero]
    refine ⟨y2, ?_⟩
    rw [← hx_recover, hy1_zero]
  · rintro ⟨y2, rfl⟩
    have hc := h.constraint_eq (0 : Fin p → ℝ) y2
    rw [hc]
    exact rectMatMulVec_zero h.S

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    the trailing `Q₂` coordinate block of the transformed data matrix `A Q`.

    Its columns are the last `q` columns of `A Q`, i.e. the action of `A` on
    the source `Q₂` coordinate range used in the proof of
    `null(B) = range(Q₂)`. -/
noncomputable def gqrAQ2Block {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ) :
    Fin (r + q) → Fin q → ℝ :=
  fun i j => matMulRect (r + q) (p + q) (p + q) A Q i (Fin.natAdd p j)

/-- Vector-action form of the `A Q₂` block. -/
theorem gqrAQ2Block_mulVec {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (y2 : Fin q → ℝ) :
    rectMatMulVec (gqrAQ2Block A Q) y2 =
      rectMatMulVec A (matMulVec (p + q) Q (Fin.append (0 : Fin p → ℝ) y2)) := by
  calc
    rectMatMulVec (gqrAQ2Block A Q) y2 =
        rectMatMulVec (matMulRect (r + q) (p + q) (p + q) A Q)
          (Fin.append (0 : Fin p → ℝ) y2) := by
      ext i
      unfold rectMatMulVec gqrAQ2Block
      rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right]
    _ = rectMatMulVec A
        (matMulVec (p + q) Q (Fin.append (0 : Fin p → ℝ) y2)) := by
      exact rectMatMulVec_rectMatMul A Q (Fin.append (0 : Fin p → ℝ) y2)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10 transport algebra:
    any perturbation of the trailing `A Q₂` block can be represented by a
    full source-coordinate perturbation of `A`.

    The proof pads the `A Q₂` perturbation with zero leading `p` columns in
    `Q`-coordinates, then maps it back by right multiplication with `Qᵀ`.
    Multiplication by `Q` recovers the padded perturbation exactly, and the
    Frobenius norm is unchanged because `Qᵀ` is orthogonal. -/
theorem gqrAQ2Block_exists_full_perturbation_of_trailing_delta
    {r p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (DeltaC : Fin (r + q) → Fin q → ℝ)
    (hQ : IsOrthogonal (p + q) Q) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
      (∀ (A : Fin (r + q) → Fin (p + q) → ℝ) i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          gqrAQ2Block A Q i j + DeltaC i j) ∧
      frobNormRect DeltaA =
        frobNormRect (fun i : Fin (r + q) =>
          Fin.append (fun _ : Fin p => 0) (DeltaC i)) := by
  let DeltaAQ : Fin (r + q) → Fin (p + q) → ℝ :=
    fun i => Fin.append (fun _ : Fin p => 0) (DeltaC i)
  let DeltaA : Fin (r + q) → Fin (p + q) → ℝ :=
    matMulRectRight DeltaAQ (matTranspose Q)
  have hleft : rectMatMul (matTranspose Q) Q = idMatrix (p + q) := by
    ext a b
    simpa [rectMatMul, idMatrix] using hQ.left_inv a b
  have hrecover : rectMatMul (rectMatMul DeltaAQ (matTranspose Q)) Q =
      DeltaAQ := by
    calc
      rectMatMul (rectMatMul DeltaAQ (matTranspose Q)) Q =
          rectMatMul DeltaAQ (rectMatMul (matTranspose Q) Q) :=
            rectMatMul_assoc DeltaAQ (matTranspose Q) Q
      _ = rectMatMul DeltaAQ (idMatrix (p + q)) := by
            rw [hleft]
      _ = DeltaAQ := rectMatMul_id_right DeltaAQ
  refine ⟨DeltaA, ?_, ?_⟩
  · intro A i j
    have htrail :
        matMulRect (r + q) (p + q) (p + q) DeltaA Q i
            (Fin.natAdd p j) =
          DeltaC i j := by
      have hentry := congrFun (congrFun hrecover i) (Fin.natAdd p j)
      simpa [DeltaA, DeltaAQ, rectMatMul, matMulRect, matMulRectRight,
        Fin.append_right] using hentry
    have hdist := congrFun (congrFun
      (matMulRect_add_left (r + q) (p + q) (p + q) A DeltaA Q) i)
      (Fin.natAdd p j)
    simpa [gqrAQ2Block, htrail] using hdist
  · simpa [DeltaA, DeltaAQ] using
      (frobNormRect_orthogonal_right DeltaAQ (matTranspose Q)
        (IsOrthogonal.transpose hQ))

/-- Frobenius norm of a rectangular matrix with zero columns prepended. -/
theorem frobNormRect_zeroLeftCols_append {m p q : ℕ}
    (C : Fin m → Fin q → ℝ) :
    frobNormRect (fun i : Fin m =>
      Fin.append (fun _ : Fin p => 0) (C i)) = frobNormRect C := by
  unfold frobNormRect
  apply congrArg Real.sqrt
  unfold frobNormSqRect
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- Frobenius norm of a rectangular matrix with zero columns appended. -/
theorem frobNormRect_zeroRightCols_append {m p q : ℕ}
    (C : Fin m → Fin p → ℝ) :
    frobNormRect (fun i : Fin m =>
      Fin.append (C i) (fun _ : Fin q => 0)) = frobNormRect C := by
  unfold frobNormRect
  apply congrArg Real.sqrt
  unfold frobNormSqRect
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- The block `[S,0]` used in the GQR constraint equation has the same
    Frobenius norm as `S`. -/
theorem frobNormRect_gqrBQBlock {p q : ℕ}
    (S : Fin p → Fin p → ℝ) :
    frobNormRect (gqrBQBlock (q := q) S) = frobNormRect S := by
  simpa [gqrBQBlock] using
    (frobNormRect_zeroRightCols_append (m := p) (p := p) (q := q) S)

/-- The GQR constraint block is additive in its triangular factor. -/
theorem gqrBQBlock_add {p q : ℕ}
    (S DeltaS : Fin p → Fin p → ℝ) :
    gqrBQBlock (q := q) (fun i j => S i j + DeltaS i j) =
      fun i j => gqrBQBlock (q := q) S i j + gqrBQBlock DeltaS i j := by
  ext i j
  refine Fin.addCases
    (motive := fun j : Fin (p + q) =>
      gqrBQBlock (q := q) (fun i j => S i j + DeltaS i j) i j =
        gqrBQBlock (q := q) S i j + gqrBQBlock DeltaS i j)
    ?left ?right j
  · intro j
    simp [gqrBQBlock, Fin.append_left]
  · intro j
    simp [gqrBQBlock, Fin.append_right]

/-- Transporting a perturbation of the GQR `S` block back through `Qᵀ`
    gives the corresponding source-coordinate constraint perturbation. -/
theorem gqrSourceBFromBlocks_perturbation_eq {p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (S DeltaS : Fin p → Fin p → ℝ) :
    (fun i j =>
        gqrSourceBFromBlocks Q (fun i j => S i j + DeltaS i j) i j -
          gqrSourceBFromBlocks Q S i j) =
      matMulRectRight (gqrBQBlock (q := q) DeltaS) (matTranspose Q) := by
  have hblock := gqrBQBlock_add (q := q) S DeltaS
  ext i j
  have hadd := congrFun (congrFun
    (matMulRect_add_left p (p + q) (p + q)
      (gqrBQBlock (q := q) S) (gqrBQBlock (q := q) DeltaS)
      (matTranspose Q)) i) j
  have hsum :
      gqrSourceBFromBlocks Q (fun i j => S i j + DeltaS i j) i j =
        gqrSourceBFromBlocks Q S i j +
          matMulRectRight (gqrBQBlock (q := q) DeltaS) (matTranspose Q) i j := by
    simpa [gqrSourceBFromBlocks, matMulRectRight, hblock] using hadd
  rw [hsum]
  ring

/-- The source-coordinate constraint perturbation induced by perturbing only
    the GQR `S` block has Frobenius norm exactly `‖DeltaS‖_F`. -/
theorem gqrSourceBFromBlocks_perturbation_frobNorm_eq {p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (S DeltaS : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q) :
    frobNormRect
      (fun i j =>
        gqrSourceBFromBlocks Q (fun i j => S i j + DeltaS i j) i j -
          gqrSourceBFromBlocks Q S i j) =
      frobNormRect DeltaS := by
  calc
    frobNormRect
        (fun i j =>
          gqrSourceBFromBlocks Q (fun i j => S i j + DeltaS i j) i j -
            gqrSourceBFromBlocks Q S i j)
        = frobNormRect
            (matMulRectRight (gqrBQBlock (q := q) DeltaS) (matTranspose Q)) := by
          rw [gqrSourceBFromBlocks_perturbation_eq Q S DeltaS]
    _ = frobNormRect (gqrBQBlock (q := q) DeltaS) := by
          exact frobNormRect_orthogonal_right _ _ (IsOrthogonal.transpose hQ)
    _ = frobNormRect DeltaS := frobNormRect_gqrBQBlock DeltaS

/-- A supplied GQR factorization reconstructs its original constraint matrix
    from the displayed `[S,0]` block and `Qᵀ`. -/
theorem GeneralizedQRFactorization.sourceBFromBlocks_eq {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    gqrSourceBFromBlocks h.Q h.S = B := by
  have hbq :
      matMulRectRight B h.Q = gqrBQBlock h.S := by
    simpa [matMulRectRight] using h.bq_eq
  have hright : rectMatMul h.Q (matTranspose h.Q) = idMatrix (p + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using h.orthQ.right_inv i j
  calc
    gqrSourceBFromBlocks h.Q h.S =
        matMulRectRight (gqrBQBlock h.S) (matTranspose h.Q) := rfl
    _ = matMulRectRight (matMulRectRight B h.Q) (matTranspose h.Q) := by
          rw [← hbq]
    _ = rectMatMul (rectMatMul B h.Q) (matTranspose h.Q) := rfl
    _ = rectMatMul B (rectMatMul h.Q (matTranspose h.Q)) :=
          rectMatMul_assoc B h.Q (matTranspose h.Q)
    _ = rectMatMul B (idMatrix (p + q)) := by rw [hright]
    _ = B := rectMatMul_id_right B

/-- In a supplied GQR factorization, the Frobenius norm of the displayed
    constraint block `S` is the source Frobenius norm of `B`. -/
theorem GeneralizedQRFactorization.frobNormRect_S_eq_sourceB {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    frobNormRect h.S = frobNormRect B := by
  have hbq :
      matMulRectRight B h.Q = gqrBQBlock h.S := by
    simpa [matMulRectRight] using h.bq_eq
  calc
    frobNormRect h.S = frobNormRect (gqrBQBlock (q := q) h.S) := by
      exact (frobNormRect_gqrBQBlock h.S).symm
    _ = frobNormRect (matMulRectRight B h.Q) := by rw [← hbq]
    _ = frobNormRect B := frobNormRect_orthogonal_right B h.Q h.orthQ

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    `DeltaB` Frobenius bound from a perturbation of the GQR `S` block.

    This closes the source-shaped `B` side of the constructed-source
    certificate once the triangular solve supplies
    `‖DeltaS‖_F ≤ eta * ‖S‖_F`. -/
theorem GeneralizedQRFactorization.constructed_sourceB_perturbation_frobNorm_bound
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (eta : ℝ) (DeltaS : Fin p → Fin p → ℝ)
    (hDeltaSfrob : frobNormRect DeltaS ≤ eta * frobNormRect h.S) :
    frobNormRect
      (fun i j =>
        gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
          B i j) ≤
      eta * frobNormRect B := by
  have hBsrc := h.sourceBFromBlocks_eq
  have hnorm :
      frobNormRect
        (fun i j =>
          gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
            B i j) =
        frobNormRect DeltaS := by
    calc
      frobNormRect
          (fun i j =>
            gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
              B i j)
          = frobNormRect
              (fun i j =>
                gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
                  gqrSourceBFromBlocks h.Q h.S i j) := by
            congr 1
            ext i j
            rw [hBsrc]
      _ = frobNormRect DeltaS :=
            gqrSourceBFromBlocks_perturbation_frobNorm_eq h.Q h.S DeltaS h.orthQ
  calc
    frobNormRect
        (fun i j =>
          gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
            B i j)
        = frobNormRect DeltaS := hnorm
    _ ≤ eta * frobNormRect h.S := hDeltaSfrob
    _ = eta * frobNormRect B := by rw [h.frobNormRect_S_eq_sourceB]

/-- Frobenius norm of a rectangular matrix with zero rows prepended. -/
theorem frobNormRect_zeroTopRows_append {r q n : ℕ}
    (C : Fin q → Fin n → ℝ) :
    frobNormRect (Fin.append (fun _ : Fin r => fun _ : Fin n => 0) C) =
      frobNormRect C := by
  unfold frobNormRect
  apply congrArg Real.sqrt
  unfold frobNormSqRect
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- The GQR block with only the bottom-right `L22` perturbation nonzero has
    Frobenius norm exactly the Frobenius norm of that perturbation. -/
theorem frobNormRect_gqrAQBlock_only_L22 {r p q : ℕ}
    (DeltaL22 : Fin q → Fin q → ℝ) :
    frobNormRect
      (gqrAQBlock (r := r) (p := p) (q := q)
        (fun _ _ => 0) (fun _ _ => 0) DeltaL22) =
      frobNormRect DeltaL22 := by
  unfold frobNormRect
  apply congrArg Real.sqrt
  unfold frobNormSqRect
  rw [Fin.sum_univ_add]
  simp [gqrAQBlock, Fin.append_left, Fin.append_right, Fin.sum_univ_add]

/-- The displayed GQR `UᵀAQ` block is additive in its bottom-right `L22`
    block when all other perturbation blocks are zero. -/
theorem gqrAQBlock_L22_add {r p q : ℕ}
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 DeltaL22 : Fin q → Fin q → ℝ) :
    gqrAQBlock L11 L21 (fun i j => L22 i j + DeltaL22 i j) =
      fun i j =>
        gqrAQBlock L11 L21 L22 i j +
          gqrAQBlock (r := r) (p := p) (q := q)
            (fun _ _ => 0) (fun _ _ => 0) DeltaL22 i j := by
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin (r + q) =>
      gqrAQBlock L11 L21 (fun i j => L22 i j + DeltaL22 i j) i j =
        gqrAQBlock L11 L21 L22 i j +
          gqrAQBlock (r := r) (p := p) (q := q)
            (fun _ _ => 0) (fun _ _ => 0) DeltaL22 i j)
    ?top ?bottom i
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin (p + q) =>
        gqrAQBlock L11 L21 (fun i j => L22 i j + DeltaL22 i j)
            (Fin.castAdd q i) j =
          gqrAQBlock L11 L21 L22 (Fin.castAdd q i) j +
            gqrAQBlock (r := r) (p := p) (q := q)
              (fun _ _ => 0) (fun _ _ => 0) DeltaL22 (Fin.castAdd q i) j)
      ?top_left ?top_right j
    · intro j
      simp [gqrAQBlock, Fin.append_left]
    · intro j
      simp [gqrAQBlock, Fin.append_left, Fin.append_right]
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin (p + q) =>
        gqrAQBlock L11 L21 (fun i j => L22 i j + DeltaL22 i j)
            (Fin.natAdd r i) j =
          gqrAQBlock L11 L21 L22 (Fin.natAdd r i) j +
            gqrAQBlock (r := r) (p := p) (q := q)
              (fun _ _ => 0) (fun _ _ => 0) DeltaL22 (Fin.natAdd r i) j)
      ?bottom_left ?bottom_right j
    · intro j
      simp [gqrAQBlock, Fin.append_right, Fin.append_left]
    · intro j
      simp [gqrAQBlock, Fin.append_right]

/-- Transporting a perturbation of only the GQR `L22` block back through
    `U` and `Qᵀ` gives the corresponding source-coordinate data perturbation. -/
theorem gqrSourceAFromBlocks_L22_perturbation_eq {r p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 DeltaL22 : Fin q → Fin q → ℝ) :
    (fun i j =>
        gqrSourceAFromBlocks Q U L11 L21 (fun i j => L22 i j + DeltaL22 i j) i j -
          gqrSourceAFromBlocks Q U L11 L21 L22 i j) =
      matMulRectLeft U
        (matMulRectRight
          (gqrAQBlock (r := r) (p := p) (q := q)
            (fun _ _ => 0) (fun _ _ => 0) DeltaL22)
          (matTranspose Q)) := by
  let M : Fin (r + q) → Fin (p + q) → ℝ := gqrAQBlock L11 L21 L22
  let DeltaM : Fin (r + q) → Fin (p + q) → ℝ :=
    gqrAQBlock (r := r) (p := p) (q := q)
      (fun _ _ => 0) (fun _ _ => 0) DeltaL22
  have hblock :
      gqrAQBlock L11 L21 (fun i j => L22 i j + DeltaL22 i j) =
        fun i j => M i j + DeltaM i j := by
    simpa [M, DeltaM] using gqrAQBlock_L22_add L11 L21 L22 DeltaL22
  have hright :
      matMulRectRight
          (gqrAQBlock L11 L21 (fun i j => L22 i j + DeltaL22 i j))
          (matTranspose Q) =
        fun i j =>
          matMulRectRight M (matTranspose Q) i j +
            matMulRectRight DeltaM (matTranspose Q) i j := by
    simpa [matMulRectRight, hblock] using
      (matMulRect_add_left (r + q) (p + q) (p + q)
        M DeltaM (matTranspose Q))
  ext i j
  have hleft := congrFun (congrFun
    (matMulRectLeft_add_right U
      (matMulRectRight M (matTranspose Q))
      (matMulRectRight DeltaM (matTranspose Q))) i) j
  have hsum :
      gqrSourceAFromBlocks Q U L11 L21 (fun i j => L22 i j + DeltaL22 i j) i j =
        gqrSourceAFromBlocks Q U L11 L21 L22 i j +
          matMulRectLeft U (matMulRectRight DeltaM (matTranspose Q)) i j := by
    simpa [gqrSourceAFromBlocks, M, DeltaM, hright] using hleft
  rw [hsum]
  ring

/-- The source-coordinate data perturbation induced by perturbing only the
    GQR `L22` block has Frobenius norm exactly `‖DeltaL22‖_F`. -/
theorem gqrSourceAFromBlocks_L22_perturbation_frobNorm_eq {r p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 DeltaL22 : Fin q → Fin q → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal (r + q) U) :
    frobNormRect
      (fun i j =>
        gqrSourceAFromBlocks Q U L11 L21 (fun i j => L22 i j + DeltaL22 i j) i j -
          gqrSourceAFromBlocks Q U L11 L21 L22 i j) =
      frobNormRect DeltaL22 := by
  let DeltaM : Fin (r + q) → Fin (p + q) → ℝ :=
    gqrAQBlock (r := r) (p := p) (q := q)
      (fun _ _ => 0) (fun _ _ => 0) DeltaL22
  calc
    frobNormRect
        (fun i j =>
          gqrSourceAFromBlocks Q U L11 L21 (fun i j => L22 i j + DeltaL22 i j) i j -
            gqrSourceAFromBlocks Q U L11 L21 L22 i j)
        = frobNormRect
            (matMulRectLeft U (matMulRectRight DeltaM (matTranspose Q))) := by
          rw [gqrSourceAFromBlocks_L22_perturbation_eq Q U L11 L21 L22 DeltaL22]
    _ = frobNormRect (matMulRectRight DeltaM (matTranspose Q)) := by
          exact frobNormRect_orthogonal_left U
            (matMulRectRight DeltaM (matTranspose Q)) hU
    _ = frobNormRect DeltaM := by
          exact frobNormRect_orthogonal_right DeltaM (matTranspose Q)
            (IsOrthogonal.transpose hQ)
    _ = frobNormRect DeltaL22 := frobNormRect_gqrAQBlock_only_L22 DeltaL22

/-- The bottom row block has Frobenius squared norm no larger than the full
    rectangular matrix. -/
theorem frobNormSqRect_bottomRows_le {r q n : ℕ}
    (M : Fin (r + q) → Fin n → ℝ) :
    frobNormSqRect (fun i : Fin q => M (Fin.natAdd r i)) ≤
      frobNormSqRect M := by
  unfold frobNormSqRect
  rw [Fin.sum_univ_add]
  have htop_nonneg :
      0 ≤ ∑ i : Fin r, ∑ j : Fin n, M (Fin.castAdd q i) j ^ 2 := by
    exact Finset.sum_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  linarith

/-- The bottom row block has Frobenius norm no larger than the full
    rectangular matrix. -/
theorem frobNormRect_bottomRows_le {r q n : ℕ}
    (M : Fin (r + q) → Fin n → ℝ) :
    frobNormRect (fun i : Fin q => M (Fin.natAdd r i)) ≤
      frobNormRect M := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt (frobNormSqRect_bottomRows_le M)

/-- The trailing column block has Frobenius norm no larger than the full
    rectangular matrix. -/
theorem frobNormSqRect_trailingCols_le {m p q : ℕ}
    (M : Fin m → Fin (p + q) → ℝ) :
    frobNormSqRect (fun i : Fin m => fun j : Fin q =>
      M i (Fin.natAdd p j)) ≤ frobNormSqRect M := by
  unfold frobNormSqRect
  apply Finset.sum_le_sum
  intro i _
  have hsplit :
      (∑ j : Fin (p + q), M i j ^ 2) =
        (∑ j : Fin p, M i (Fin.castAdd q j) ^ 2) +
          (∑ j : Fin q, M i (Fin.natAdd p j) ^ 2) := by
    rw [Fin.sum_univ_add]
  have hleft_nonneg :
      0 ≤ ∑ j : Fin p, M i (Fin.castAdd q j) ^ 2 := by
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  linarith

/-- The trailing column block has Frobenius norm no larger than the full
    rectangular matrix. -/
theorem frobNormRect_trailingCols_le {m p q : ℕ}
    (M : Fin m → Fin (p + q) → ℝ) :
    frobNormRect (fun i : Fin m => fun j : Fin q =>
      M i (Fin.natAdd p j)) ≤ frobNormRect M := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt (frobNormSqRect_trailingCols_le M)

/-- The `A Q₂` block has Frobenius norm no larger than `A` when `Q` is
    orthogonal. -/
theorem frobNormRect_gqrAQ2Block_le
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q) :
    frobNormRect (gqrAQ2Block A Q) ≤ frobNormRect A := by
  let AQ : Fin (r + q) → Fin (p + q) → ℝ := matMulRectRight A Q
  have htrail :
      gqrAQ2Block A Q =
        fun i : Fin (r + q) => fun j : Fin q => AQ i (Fin.natAdd p j) := by
    ext i j
    rfl
  calc
    frobNormRect (gqrAQ2Block A Q)
        = frobNormRect
            (fun i : Fin (r + q) => fun j : Fin q => AQ i (Fin.natAdd p j)) := by
          rw [htrail]
    _ ≤ frobNormRect AQ := frobNormRect_trailingCols_le AQ
    _ = frobNormRect A := by
          simpa [AQ] using frobNormRect_orthogonal_right A Q hQ

/-- The bottom-right `L22` block in the displayed GQR `UᵀAQ` matrix has
    Frobenius norm no larger than the full displayed block. -/
theorem frobNormRect_gqrAQBlock_L22_le {r p q : ℕ}
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ) :
    frobNormRect L22 ≤ frobNormRect (gqrAQBlock L11 L21 L22) := by
  let bottom : Fin q → Fin (p + q) → ℝ :=
    fun i j => gqrAQBlock L11 L21 L22 (Fin.natAdd r i) j
  have hL22 :
      L22 = fun i : Fin q => fun j : Fin q => bottom i (Fin.natAdd p j) := by
    ext i j
    simp [bottom, gqrAQBlock, Fin.append_right]
  calc
    frobNormRect L22 =
        frobNormRect (fun i : Fin q => fun j : Fin q =>
          bottom i (Fin.natAdd p j)) := by rw [hL22]
    _ ≤ frobNormRect bottom := frobNormRect_trailingCols_le bottom
    _ ≤ frobNormRect (gqrAQBlock L11 L21 L22) :=
          frobNormRect_bottomRows_le (gqrAQBlock L11 L21 L22)

/-- A supplied GQR factorization reconstructs its original data matrix from
    the displayed `UᵀAQ` block and the orthogonal factors `U` and `Qᵀ`. -/
theorem GeneralizedQRFactorization.sourceAFromBlocks_eq {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 h.L22 = A := by
  let M : Fin (r + q) → Fin (p + q) → ℝ :=
    gqrAQBlock h.L11 h.L21 h.L22
  let AQ : Fin (r + q) → Fin (p + q) → ℝ := matMulRectRight A h.Q
  have haq : matMulRectLeft (matTranspose h.U) AQ = M := by
    simpa [M, AQ, matMulRectRight] using h.aq_eq
  have hUright : rectMatMul h.U (matTranspose h.U) = idMatrix (r + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using h.orthU.right_inv i j
  have hQright : rectMatMul h.Q (matTranspose h.Q) = idMatrix (p + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using h.orthQ.right_inv i j
  calc
    gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 h.L22 =
        matMulRectLeft h.U (matMulRectRight M (matTranspose h.Q)) := rfl
    _ = matMulRectLeft h.U
          (matMulRectRight
            (matMulRectLeft (matTranspose h.U) AQ) (matTranspose h.Q)) := by
          rw [haq]
    _ = rectMatMul h.U
          (rectMatMul
            (rectMatMul (matTranspose h.U) (rectMatMul A h.Q))
            (matTranspose h.Q)) := by
          rfl
    _ = rectMatMul h.U
          (rectMatMul (matTranspose h.U)
            (rectMatMul (rectMatMul A h.Q) (matTranspose h.Q))) := by
          rw [rectMatMul_assoc]
    _ = rectMatMul
          (rectMatMul h.U (matTranspose h.U))
          (rectMatMul (rectMatMul A h.Q) (matTranspose h.Q)) := by
          rw [← rectMatMul_assoc]
    _ = rectMatMul
          (idMatrix (r + q))
          (rectMatMul (rectMatMul A h.Q) (matTranspose h.Q)) := by
          rw [hUright]
    _ = rectMatMul (rectMatMul A h.Q) (matTranspose h.Q) := by
          rw [rectMatMul_id_left]
    _ = rectMatMul A (rectMatMul h.Q (matTranspose h.Q)) :=
          rectMatMul_assoc A h.Q (matTranspose h.Q)
    _ = rectMatMul A (idMatrix (p + q)) := by rw [hQright]
    _ = A := rectMatMul_id_right A

/-- In a supplied GQR factorization, the bottom-right displayed block `L22`
    has Frobenius norm no larger than the source data matrix `A`. -/
theorem GeneralizedQRFactorization.frobNormRect_L22_le_sourceA {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    frobNormRect h.L22 ≤ frobNormRect A := by
  let M : Fin (r + q) → Fin (p + q) → ℝ :=
    gqrAQBlock h.L11 h.L21 h.L22
  have haq : matMulRectLeft (matTranspose h.U) (matMulRectRight A h.Q) = M := by
    simpa [M, matMulRectRight] using h.aq_eq
  have hMnorm : frobNormRect M = frobNormRect A := by
    calc
      frobNormRect M =
          frobNormRect
            (matMulRectLeft (matTranspose h.U) (matMulRectRight A h.Q)) := by
            rw [← haq]
      _ = frobNormRect (matMulRectRight A h.Q) := by
            exact frobNormRect_orthogonal_left (matTranspose h.U)
              (matMulRectRight A h.Q) (IsOrthogonal.transpose h.orthU)
      _ = frobNormRect A := frobNormRect_orthogonal_right A h.Q h.orthQ
  calc
    frobNormRect h.L22 ≤ frobNormRect M :=
      frobNormRect_gqrAQBlock_L22_le h.L11 h.L21 h.L22
    _ = frobNormRect A := hMnorm

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    `DeltaA` Frobenius bound from a perturbation of the GQR `L22` block.

    This closes the source-shaped `A` side of the constructed-source
    certificate once the triangular solve supplies
    `‖DeltaL22‖_F ≤ eta * ‖L22‖_F` and `eta` is nonnegative. -/
theorem GeneralizedQRFactorization.constructed_sourceA_L22_perturbation_frobNorm_bound
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (eta : ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (heta_nonneg : 0 ≤ eta)
    (hDeltaL22frob : frobNormRect DeltaL22 ≤ eta * frobNormRect h.L22) :
    frobNormRect
      (fun i j =>
        gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
            (fun i j => h.L22 i j + DeltaL22 i j) i j -
          A i j) ≤
      eta * frobNormRect A := by
  have hAsrc := h.sourceAFromBlocks_eq
  have hnorm :
      frobNormRect
        (fun i j =>
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
              (fun i j => h.L22 i j + DeltaL22 i j) i j -
            A i j) =
        frobNormRect DeltaL22 := by
    calc
      frobNormRect
          (fun i j =>
            gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
                (fun i j => h.L22 i j + DeltaL22 i j) i j -
              A i j)
          = frobNormRect
              (fun i j =>
                gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
                    (fun i j => h.L22 i j + DeltaL22 i j) i j -
                  gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 h.L22 i j) := by
            congr 1
            ext i j
            rw [hAsrc]
      _ = frobNormRect DeltaL22 :=
            gqrSourceAFromBlocks_L22_perturbation_frobNorm_eq
              h.Q h.U h.L11 h.L21 h.L22 DeltaL22 h.orthQ h.orthU
  calc
    frobNormRect
        (fun i j =>
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
              (fun i j => h.L22 i j + DeltaL22 i j) i j -
            A i j)
        = frobNormRect DeltaL22 := hnorm
    _ ≤ eta * frobNormRect h.L22 := hDeltaL22frob
    _ ≤ eta * frobNormRect A :=
          mul_le_mul_of_nonneg_left h.frobNormRect_L22_le_sourceA heta_nonneg

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    the `A Q₂` block has trivial kernel using only the constraint block
    identity `B Q = [S 0]`, orthogonality of `Q`, and the local
    null-intersection condition.

    This is the construction-level form of the `Q₂` kernel bridge: it does not
    assume a complete supplied `GeneralizedQRFactorization`, so it can be used
    immediately after constructing the `Bᵀ` QR side. -/
theorem gqrAQ2_kernel_trivial_of_constraint_block_nullIntersection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Q : Fin (p + q) → Fin (p + q) → ℝ}
    {S : Fin p → Fin p → ℝ}
    (hQ : IsOrthogonal (p + q) Q)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hnull : LSENullIntersectionTrivial A B)
    (y2 : Fin q → ℝ)
    (hAy2 :
      rectMatMulVec A
        (matMulVec (p + q) Q (Fin.append (0 : Fin p → ℝ) y2)) = 0) :
    y2 = 0 := by
  let y : Fin (p + q) → ℝ := Fin.append (0 : Fin p → ℝ) y2
  let x : Fin (p + q) → ℝ := matMulVec (p + q) Q y
  have hBx : rectMatMulVec B x = 0 := by
    calc
      rectMatMulVec B (matMulVec (p + q) Q y)
          = rectMatMulVec (matMulRect p (p + q) (p + q) B Q) y := by
              exact (rectMatMulVec_rectMatMul B Q y).symm
      _ = rectMatMulVec (gqrBQBlock S) y := by
              rw [hBQ]
      _ = rectMatMulVec S (0 : Fin p → ℝ) := by
              simpa [y] using gqrBQBlock_mulVec S (0 : Fin p → ℝ) y2
      _ = 0 := rectMatMulVec_zero S
  have hxzero : x = 0 := hnull x hAy2 hBx
  have hyzero : y = 0 := by
    have hrec := matMulVec_orthogonal_transpose_mul hQ y
    dsimp [x] at hxzero
    rw [hxzero, matMulVec_zero] at hrec
    exact hrec.symm
  ext i
  have hi := congrFun hyzero (Fin.natAdd p i)
  simpa [y, Fin.append_right] using hi

/-- Construction-level injectivity of the `A Q₂` rectangular column map from
    the constraint block identity and the local null-intersection condition. -/
theorem gqrAQ2_rectMatMulVec_injective_of_constraint_block_nullIntersection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Q : Fin (p + q) → Fin (p + q) → ℝ}
    {S : Fin p → Fin p → ℝ}
    (hQ : IsOrthogonal (p + q) Q)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hnull : LSENullIntersectionTrivial A B) :
    Function.Injective (rectMatMulVec (gqrAQ2Block A Q)) := by
  intro y2 z2 hyz
  let w : Fin q → ℝ := fun i => y2 i - z2 i
  have hAw :
      rectMatMulVec A
        (matMulVec (p + q) Q (Fin.append (0 : Fin p → ℝ) w)) = 0 := by
    have hblock : rectMatMulVec (gqrAQ2Block A Q) w = 0 := by
      ext i
      have hi := congrFun hyz i
      have hsub := congrFun (rectMatMulVec_sub (gqrAQ2Block A Q) y2 z2) i
      dsimp [w]
      rw [hsub, hi]
      ring
    simpa [gqrAQ2Block_mulVec A Q w] using hblock
  have hw : w = 0 :=
    gqrAQ2_kernel_trivial_of_constraint_block_nullIntersection
      hQ hBQ hnull w hAw
  ext i
  have hwi := congrFun hw i
  dsimp [w] at hwi
  linarith

/-- Column permutations preserve injectivity of a rectangular matrix-vector
    map.  This is the coordinate-change step needed before applying exact QR
    to the column-reversed `A Q₂` block in the Chapter 20 GQR construction. -/
theorem rectMatMulVec_injective_rectPermuteCols {m n : ℕ}
    (π : Fin n ≃ Fin n) {A : Fin m → Fin n → ℝ}
    (hA : Function.Injective (rectMatMulVec A)) :
    Function.Injective (rectMatMulVec (rectPermuteCols π A)) := by
  intro x y hxy
  have hxy' :
      rectMatMulVec A (vecPermute π.symm x) =
        rectMatMulVec A (vecPermute π.symm y) := by
    calc
      rectMatMulVec A (vecPermute π.symm x)
          = rectMatMulVec (rectPermuteCols π A) x := by
              exact (rectMatMulVec_permuteCols π A x).symm
      _ = rectMatMulVec (rectPermuteCols π A) y := hxy
      _ = rectMatMulVec A (vecPermute π.symm y) := by
              exact rectMatMulVec_permuteCols π A y
  have hperm : vecPermute π.symm x = vecPermute π.symm y := hA hxy'
  have hrecover := congrArg (vecPermute π) hperm
  simpa [vecPermute_vecPermute_symm] using hrecover

/-- Construction-level exact-MGS nonbreakdown for the smaller `A Q₂` block. -/
theorem gqrAQ2_mgs_norm_ne_zero_of_constraint_block_nullIntersection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Q : Fin (p + q) → Fin (p + q) → ℝ}
    {S : Fin p → Fin p → ℝ}
    (hQ : IsOrthogonal (p + q) Q)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hnull : LSENullIntersectionTrivial A B)
    (j : Fin q) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors (gqrAQ2Block A Q) j.val j) ≠ 0 :=
  modifiedGramSchmidtVectors_norm_ne_zero_of_rectMatMulVec_injective
    (gqrAQ2Block A Q)
    (gqrAQ2_rectMatMulVec_injective_of_constraint_block_nullIntersection
      hQ hBQ hnull) j

/-- Construction-level injectivity for the column-reversed smaller `A Q₂`
    block.  This is the precise nonbreakdown route for the QR input that will
    later be converted into the lower-triangular `L₂₂` block in (20.28). -/
theorem gqrAQ2_reversed_rectMatMulVec_injective_of_constraint_block_nullIntersection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Q : Fin (p + q) → Fin (p + q) → ℝ}
    {S : Fin p → Fin p → ℝ}
    (hQ : IsOrthogonal (p + q) Q)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hnull : LSENullIntersectionTrivial A B) :
    Function.Injective
      (rectMatMulVec (rectPermuteCols Fin.revPerm (gqrAQ2Block A Q))) :=
  rectMatMulVec_injective_rectPermuteCols Fin.revPerm
    (gqrAQ2_rectMatMulVec_injective_of_constraint_block_nullIntersection
      hQ hBQ hnull)

/-- Construction-level exact-MGS nonbreakdown for the column-reversed smaller
    `A Q₂` block. -/
theorem gqrAQ2_reversed_mgs_norm_ne_zero_of_constraint_block_nullIntersection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Q : Fin (p + q) → Fin (p + q) → ℝ}
    {S : Fin p → Fin p → ℝ}
    (hQ : IsOrthogonal (p + q) Q)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hnull : LSENullIntersectionTrivial A B)
    (j : Fin q) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors
        (rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)) j.val j) ≠ 0 :=
  modifiedGramSchmidtVectors_norm_ne_zero_of_rectMatMulVec_injective
    (rectPermuteCols Fin.revPerm (gqrAQ2Block A Q))
    (gqrAQ2_reversed_rectMatMulVec_injective_of_constraint_block_nullIntersection
      hQ hBQ hnull) j

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    full row rank of `B` constructs the constraint block side, while stacked
    full column rank supplies exact-MGS nonbreakdown for the smaller `A Q₂`
    block associated with the constructed `Q`. -/
theorem exists_gqr_constraint_block_and_A_Q2_mgs_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S ∧
        ∀ j : Fin q,
          gsColumnNorm2
            (modifiedGramSchmidtVectors (gqrAQ2Block A Q) j.val j) ≠ 0 := by
  have hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  rcases exists_gqr_constraint_block_of_mgs B hdiagB with
    ⟨Q, S, hQ, hS, hBQ⟩
  have hnull : LSENullIntersectionTrivial A B :=
    (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack
  refine ⟨Q, S, hQ, hS, hBQ, ?_⟩
  intro j
  exact
    gqrAQ2_mgs_norm_ne_zero_of_constraint_block_nullIntersection
      hQ hBQ hnull j

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    full row rank of `B` constructs the constraint block side, while stacked
    full column rank supplies exact-MGS nonbreakdown for the column-reversed
    smaller `A Q₂` block. -/
theorem exists_gqr_constraint_block_and_reversed_A_Q2_mgs_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S ∧
        ∀ j : Fin q,
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)) j.val j) ≠ 0 := by
  rcases
    exists_gqr_constraint_block_and_A_Q2_mgs_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨Q, S, hQ, hS, hBQ, _hdiagAQ2⟩
  have hnull : LSENullIntersectionTrivial A B :=
    (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack
  refine ⟨Q, S, hQ, hS, hBQ, ?_⟩
  intro j
  exact
    gqrAQ2_reversed_mgs_norm_ne_zero_of_constraint_block_nullIntersection
      hQ hBQ hnull j

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    after constructing the `Bᵀ` constraint block from full row rank of `B`,
    the smaller `A Q₂` block has an exact MGS QR factorization under the
    source stacked-full-column-rank hypothesis.

    This packages the oracle-recommended smaller-block route as explicit
    QR data for the next associated-shape construction step. -/
theorem exists_gqr_constraint_block_and_A_Q2_mgs_qr_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ)
        (Q2 : Fin (r + q) → Fin q → ℝ) (R2 : Fin q → Fin q → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S ∧
        GramSchmidtOrthonormalColumns Q2 ∧
        IsUpperTriangular q R2 ∧
        gqrAQ2Block A Q = matMulRect (r + q) q q Q2 R2 := by
  rcases
    exists_gqr_constraint_block_and_A_Q2_mgs_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨Q, S, hQ, hS, hBQ, hdiagAQ2⟩
  let C : Fin (r + q) → Fin q → ℝ := gqrAQ2Block A Q
  let Q2 : Fin (r + q) → Fin q → ℝ := modifiedGramSchmidtQ C
  let R2 : Fin q → Fin q → ℝ := modifiedGramSchmidtR C
  have horthQ2 : GramSchmidtOrthonormalColumns Q2 := by
    exact modifiedGramSchmidtQ_orthonormal_columns C hdiagAQ2
  have hR2upper : IsUpperTriangular q R2 := by
    exact IsUpperTrapezoidal.to_upperTriangular
      (modifiedGramSchmidtR_upper_trapezoidal C)
  have hfactor : C = matMulRect (r + q) q q Q2 R2 := by
    exact modifiedGramSchmidt_exact_factorization C hdiagAQ2
  exact ⟨Q, S, Q2, R2, hQ, hS, hBQ, horthQ2, hR2upper, hfactor⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    after constructing the `Bᵀ` constraint block from full row rank of `B`,
    the column-reversed smaller `A Q₂` block has an exact MGS QR factorization
    under the source stacked-full-column-rank hypothesis. -/
theorem exists_gqr_constraint_block_and_reversed_A_Q2_mgs_qr_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ)
        (Q2 : Fin (r + q) → Fin q → ℝ) (R2 : Fin q → Fin q → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S ∧
        GramSchmidtOrthonormalColumns Q2 ∧
        IsUpperTriangular q R2 ∧
        rectPermuteCols Fin.revPerm (gqrAQ2Block A Q) =
          matMulRect (r + q) q q Q2 R2 := by
  rcases
    exists_gqr_constraint_block_and_reversed_A_Q2_mgs_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨Q, S, hQ, hS, hBQ, hdiagAQ2rev⟩
  let C : Fin (r + q) → Fin q → ℝ :=
    rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)
  let Q2 : Fin (r + q) → Fin q → ℝ := modifiedGramSchmidtQ C
  let R2 : Fin q → Fin q → ℝ := modifiedGramSchmidtR C
  have horthQ2 : GramSchmidtOrthonormalColumns Q2 := by
    exact modifiedGramSchmidtQ_orthonormal_columns C hdiagAQ2rev
  have hR2upper : IsUpperTriangular q R2 := by
    exact IsUpperTrapezoidal.to_upperTriangular
      (modifiedGramSchmidtR_upper_trapezoidal C)
  have hfactor : C = matMulRect (r + q) q q Q2 R2 := by
    exact modifiedGramSchmidt_exact_factorization C hdiagAQ2rev
  exact ⟨Q, S, Q2, R2, hQ, hS, hBQ, horthQ2, hR2upper, hfactor⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    after constructing the `Bᵀ` constraint block, the smaller `A Q₂` block can
    be put into the tall associated shape `[0; L₂₂]` by an orthogonal row
    factor.

    This is still a smaller-block result: it does not yet lift the constructed
    `U` to the full transformed matrix `A Q` with its leading `p` columns. -/
theorem exists_gqr_constraint_block_and_A_Q2_tall_assoc_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ)
        (U : Fin (r + q) → Fin (r + q) → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S ∧
        IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQTallCase r q
          (matMulRectLeft (matTranspose U) (gqrAQ2Block A Q))) := by
  rcases
    exists_gqr_constraint_block_and_reversed_A_Q2_mgs_qr_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨Q, S, Q2, R2, hQ, hS, hBQ, hQ2orth, hR2upper, hfactor⟩
  rcases GQRAQTallCase.exists_of_qr_reversed_cols
      (gqrAQ2Block A Q) Q2 R2 hQ2orth hR2upper hfactor with
    ⟨U, hU, hCase⟩
  exact ⟨Q, S, U, hQ, hS, hBQ, hU, hCase⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    a constructed constraint block `B Q = [S 0]` plus a tall associated shape
    for the smaller trailing block `A Q₂` packages the full generalized QR
    block display (20.27).

    The leading blocks `L₁₁` and `L₂₁` are extracted from the already
    transformed full matrix `Uᵀ A Q`; the supplied `A Q₂` tall shape supplies
    exactly the top-right zero block and the lower-triangular `L₂₂`. -/
theorem GeneralizedQRFactorization.exists_of_constraint_and_A_Q2_tall_case
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (S : Fin p → Fin p → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hS : IsLowerTriangular S)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hU : IsOrthogonal (r + q) U)
    (hCase : GQRAQTallCase r q
      (matMulRectLeft (matTranspose U) (gqrAQ2Block A Q))) :
    ∃ h : GeneralizedQRFactorization r p q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = S ∧ h.L22 = hCase.L := by
  rcases hCase with ⟨Lcase, hLcase, hAQ2⟩
  let M : Fin (r + q) → Fin (p + q) → ℝ :=
    matMulRectLeft (matTranspose U)
      (matMulRect (r + q) (p + q) (p + q) A Q)
  let L11 : Fin r → Fin p → ℝ :=
    fun i j => M (Fin.castAdd q i) (Fin.castAdd q j)
  let L21 : Fin q → Fin p → ℝ :=
    fun i j => M (Fin.natAdd r i) (Fin.castAdd q j)
  let L22 : Fin q → Fin q → ℝ := Lcase
  have htrail : ∀ row : Fin (r + q), ∀ j : Fin q,
      M row (Fin.natAdd p j) =
        matMulRectLeft (matTranspose U) (gqrAQ2Block A Q) row j := by
    intro row j
    simp [M, matMulRectLeft, gqrAQ2Block]
  have hAQ : M = gqrAQBlock L11 L21 L22 := by
    ext row col
    refine Fin.addCases
      (motive := fun col : Fin (p + q) =>
        M row col = gqrAQBlock L11 L21 L22 row col)
      ?leftCols ?rightCols col
    · intro col
      refine Fin.addCases
        (motive := fun row : Fin (r + q) =>
          M row (Fin.castAdd q col) =
            gqrAQBlock L11 L21 L22 row (Fin.castAdd q col))
        (fun row => by simp [L11, gqrAQBlock])
        (fun row => by simp [L21, gqrAQBlock])
        row
    · intro col
      refine Fin.addCases
        (motive := fun row : Fin (r + q) =>
          M row (Fin.natAdd p col) =
            gqrAQBlock L11 L21 L22 row (Fin.natAdd p col))
        ?topRows ?bottomRows row
      · intro row
        calc
          M (Fin.castAdd q row) (Fin.natAdd p col)
              =
            matMulRectLeft (matTranspose U) (gqrAQ2Block A Q)
              (Fin.castAdd q row) col := htrail (Fin.castAdd q row) col
          _ = gqrAQTallBlock Lcase (Fin.castAdd q row) col := by
                rw [hAQ2]
          _ = 0 := by
                simp [gqrAQTallBlock]
          _ = gqrAQBlock L11 L21 L22 (Fin.castAdd q row) (Fin.natAdd p col) := by
                simp [gqrAQBlock, L22]
      · intro row
        calc
          M (Fin.natAdd r row) (Fin.natAdd p col)
              =
            matMulRectLeft (matTranspose U) (gqrAQ2Block A Q)
              (Fin.natAdd r row) col := htrail (Fin.natAdd r row) col
          _ = gqrAQTallBlock Lcase (Fin.natAdd r row) col := by
                rw [hAQ2]
          _ = L22 row col := by
                simp [gqrAQTallBlock, L22]
          _ = gqrAQBlock L11 L21 L22 (Fin.natAdd r row) (Fin.natAdd p col) := by
                simp [gqrAQBlock]
  refine ⟨{
    Q := Q
    U := U
    L11 := L11
    L21 := L21
    L22 := L22
    S := S
    orthQ := hQ
    orthU := hU
    aq_eq := ?_
    bq_eq := hBQ
    lowerL22 := hLcase
    lowerS := hS
  }, rfl, rfl, rfl, rfl⟩
  simpa [M] using hAQ

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction theorem for the
    block form (20.27): source full row rank of `B` and full column rank of the
    stacked matrix `[A; B]` construct exact generalized QR factorization data.

    This closes the exact algebraic GQR existence surface for (20.27).  The
    associated (20.28) display, numerical rank equivalences, and computed
    finite-precision GQR stability remain separate rows. -/
theorem GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    Nonempty (GeneralizedQRFactorization r p q A B) := by
  rcases
    exists_gqr_constraint_block_and_A_Q2_tall_assoc_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨Q, S, U, hQ, hS, hBQ, hU, hCase⟩
  rcases hCase with ⟨hCase⟩
  rcases GeneralizedQRFactorization.exists_of_constraint_and_A_Q2_tall_case
      (A := A) (B := B) Q S U hQ hS hBQ hU hCase with
    ⟨h, _hQeq, _hUeq, _hSeq, _hL22eq⟩
  exact ⟨h⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof:
    on the `Q₂` coordinate range, the equation `A x = 0` is equivalent to
    `L22 y₂ = 0`.

    This names the exact algebra behind the source statement
    `AQ₂ = U₂ L22`, which is used to relate
    `null(A) ∩ null(B) = {0}` to nonsingularity of `L22`. -/
theorem GeneralizedQRFactorization.A_Q2_zero_iff_L22_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (y2 : Fin q → ℝ) :
    rectMatMulVec A
        (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2)) = 0 ↔
      rectMatMulVec h.L22 y2 = 0 := by
  constructor
  · intro hAy
    have htrans :=
      h.transformed_A_zero_of_A_zero
        (y := Fin.append (0 : Fin p → ℝ) y2) hAy
    have hblock := h.transformed_A_mulVec_eq_block (0 : Fin p → ℝ) y2
    rw [htrans] at hblock
    ext i
    have hi := congrFun hblock (Fin.natAdd r i)
    have hi0 :
        (0 : Fin (r + q) → ℝ) (Fin.natAdd r i) =
          rectMatMulVec h.L21 (0 : Fin p → ℝ) i +
            rectMatMulVec h.L22 y2 i := by
      simpa [Fin.append_right] using hi
    have hleft : rectMatMulVec h.L21 (0 : Fin p → ℝ) i = 0 := by
      simp [rectMatMulVec]
    have hzero : 0 = rectMatMulVec h.L22 y2 i := by
      simpa [hleft] using hi0
    exact hzero.symm
  · intro hL22
    have hblock :
        rectMatMulVec
          (matMulRectLeft (matTranspose h.U)
            (matMulRect (r + q) (p + q) (p + q) A h.Q))
          (Fin.append (0 : Fin p → ℝ) y2) = 0 := by
      rw [h.transformed_A_mulVec_eq_block (0 : Fin p → ℝ) y2]
      ext i
      refine Fin.addCases
        (motive := fun i : Fin (r + q) =>
          Fin.append (rectMatMulVec h.L11 (0 : Fin p → ℝ))
            (fun i : Fin q =>
              rectMatMulVec h.L21 (0 : Fin p → ℝ) i +
                rectMatMulVec h.L22 y2 i) i =
            (0 : Fin (r + q) → ℝ) i)
        ?left ?right i
      · intro i
        simp [Fin.append_left, rectMatMulVec]
      · intro i
        have hi := congrFun hL22 i
        simpa [Fin.append_right, rectMatMulVec] using hi
    exact h.A_zero_of_transformed_A_zero hblock

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    under the source null-intersection condition, the `Q₂` coordinate block
    has trivial kernel through `A`.

    This is the source-faithful kernel consequence behind the proof step
    `null(B) = range(Q₂)` followed by `AQ₂ = U₂ L22`: if
    `A (Q [0; y₂]) = 0`, then the same vector also satisfies the constraint
    block equation, hence lies in `null(A) ∩ null(B)` and must be zero. -/
theorem GeneralizedQRFactorization.A_Q2_kernel_trivial_of_nullIntersectionTrivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hnull : LSENullIntersectionTrivial A B)
    (y2 : Fin q → ℝ)
    (hAy2 :
      rectMatMulVec A
        (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2)) = 0) :
    y2 = 0 := by
  let y : Fin (p + q) → ℝ := Fin.append (0 : Fin p → ℝ) y2
  let x : Fin (p + q) → ℝ := matMulVec (p + q) h.Q y
  have hBx : rectMatMulVec B x = 0 := by
    have hc := h.constraint_eq (0 : Fin p → ℝ) y2
    change
      rectMatMulVec B
        (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2)) = 0
    rw [hc]
    exact rectMatMulVec_zero h.S
  have hxzero : x = 0 := hnull x hAy2 hBx
  have hyzero : y = 0 := by
    have hrec := matMulVec_orthogonal_transpose_mul h.orthQ y
    dsimp [x] at hxzero
    rw [hxzero, matMulVec_zero] at hrec
    exact hrec.symm
  ext i
  have hi := congrFun hyzero (Fin.natAdd p i)
  simpa [y, Fin.append_right] using hi

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    stacked full column rank gives the same trivial-kernel property for the
    `A Q₂` block, using the repository's equivalence between stacked rank and
    the local null-intersection condition. -/
theorem GeneralizedQRFactorization.A_Q2_kernel_trivial_of_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hstack : LSEStackedFullColumnRank A B)
    (y2 : Fin q → ℝ)
    (hAy2 :
      rectMatMulVec A
        (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2)) = 0) :
    y2 = 0 :=
  h.A_Q2_kernel_trivial_of_nullIntersectionTrivial
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
    y2 hAy2

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    the `A Q₂` block has injective column map under the local
    null-intersection condition. -/
theorem GeneralizedQRFactorization.A_Q2_rectMatMulVec_injective_of_nullIntersectionTrivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hnull : LSENullIntersectionTrivial A B) :
    Function.Injective (rectMatMulVec (gqrAQ2Block A h.Q)) := by
  intro y2 z2 hyz
  let w : Fin q → ℝ := fun i => y2 i - z2 i
  have hAw :
      rectMatMulVec A
        (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) w)) = 0 := by
    have hblock : rectMatMulVec (gqrAQ2Block A h.Q) w = 0 := by
      ext i
      have hi := congrFun hyz i
      have hsub :=
        congrFun (rectMatMulVec_sub (gqrAQ2Block A h.Q) y2 z2) i
      dsimp [w]
      rw [hsub, hi]
      ring
    simpa [gqrAQ2Block_mulVec A h.Q w] using hblock
  have hw : w = 0 :=
    h.A_Q2_kernel_trivial_of_nullIntersectionTrivial hnull w hAw
  ext i
  have hwi := congrFun hw i
  dsimp [w] at hwi
  linarith

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    stacked full column rank gives injectivity of the `A Q₂` column map. -/
theorem GeneralizedQRFactorization.A_Q2_rectMatMulVec_injective_of_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hstack : LSEStackedFullColumnRank A B) :
    Function.Injective (rectMatMulVec (gqrAQ2Block A h.Q)) :=
  h.A_Q2_rectMatMulVec_injective_of_nullIntersectionTrivial
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 exact-MGS A-side bridge:
    the source null-intersection condition supplies every nonzero-stage
    normalizer needed for exact MGS applied to the smaller `A Q₂` block. -/
theorem GeneralizedQRFactorization.A_Q2_mgs_norm_ne_zero_of_nullIntersectionTrivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hnull : LSENullIntersectionTrivial A B)
    (j : Fin q) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors (gqrAQ2Block A h.Q) j.val j) ≠ 0 :=
  modifiedGramSchmidtVectors_norm_ne_zero_of_rectMatMulVec_injective
    (gqrAQ2Block A h.Q)
    (h.A_Q2_rectMatMulVec_injective_of_nullIntersectionTrivial hnull) j

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 exact-MGS A-side bridge:
    stacked full column rank supplies every exact-MGS nonzero-stage normalizer
    for the smaller `A Q₂` block. -/
theorem GeneralizedQRFactorization.A_Q2_mgs_norm_ne_zero_of_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hstack : LSEStackedFullColumnRank A B)
    (j : Fin q) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors (gqrAQ2Block A h.Q) j.val j) ≠ 0 :=
  h.A_Q2_mgs_norm_ne_zero_of_nullIntersectionTrivial
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
    j

/-- Exact GQR method handoff for (20.27):
    if the transformed block vector `[y1; y2]` minimizes the transformed
    least-squares objective among all transformed feasible blocks
    `S z1 = d`, then `x = Q [y1; y2]` is an exact solution of the original
    equality-constrained least-squares problem.

    This is still supplied-factorization algebra.  It does not assert GQR
    existence, triangular nonsingularity, or floating-point stability. -/
theorem GeneralizedQRFactorization.isLSEMinimizer_of_transformed_block_minimizer
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    {y1 : Fin p → ℝ} {y2 : Fin q → ℝ}
    (hy1 : rectMatMulVec h.S y1 = d)
    (hmin : ∀ z1 : Fin p → ℝ, ∀ z2 : Fin q → ℝ,
      rectMatMulVec h.S z1 = d →
        lsObjective (gqrAQBlock h.L11 h.L21 h.L22)
            (matMulVec (r + q) (matTranspose h.U) b)
            (Fin.append y1 y2) ≤
          lsObjective (gqrAQBlock h.L11 h.L21 h.L22)
            (matMulVec (r + q) (matTranspose h.U) b)
            (Fin.append z1 z2)) :
    IsLSEMinimizer A b B d
      (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  refine ⟨h.feasible_of_S_mulVec hy1, ?_⟩
  intro x hx
  let z : Fin (p + q) → ℝ := matMulVec (p + q) (matTranspose h.Q) x
  let z1 : Fin p → ℝ := fun i => z (Fin.castAdd q i)
  let z2 : Fin q → ℝ := fun i => z (Fin.natAdd p i)
  have hz_append : Fin.append z1 z2 = z := by
    simpa [z1, z2] using finAppend_left_right (p := p) (q := q) z
  have hx_recover :
      matMulVec (p + q) h.Q (Fin.append z1 z2) = x := by
    rw [hz_append]
    exact matMulVec_orthogonal_mul_transpose h.orthQ x
  have hz_feasible : rectMatMulVec h.S z1 = d := by
    have hconstraint := h.constraint_eq z1 z2
    rw [hx_recover] at hconstraint
    ext i
    have hi := congrFun hconstraint i
    rw [← hi, hx i]
  calc
    lsObjective A b (matMulVec (p + q) h.Q (Fin.append y1 y2))
        = lsObjective (gqrAQBlock h.L11 h.L21 h.L22)
            (matMulVec (r + q) (matTranspose h.U) b)
            (Fin.append y1 y2) := by
            exact (h.objective_eq_block b y1 y2).symm
    _ ≤ lsObjective (gqrAQBlock h.L11 h.L21 h.L22)
          (matMulVec (r + q) (matTranspose h.U) b)
          (Fin.append z1 z2) := hmin z1 z2 hz_feasible
    _ = lsObjective A b (matMulVec (p + q) h.Q (Fin.append z1 z2)) := by
            exact h.objective_eq_block b z1 z2
    _ = lsObjective A b x := by
            rw [hx_recover]

/-- Exact GQR triangular-solve handoff for the method following (20.27):
    if `S y1 = d` and the lower block equation
    `L22 y2 = c2 - L21 y1` is solved, then the recovered vector
    `x = Q [y1; y2]` is an exact LSE minimizer, provided the displayed
    triangular constraint factor `S` is injective.

    This formalizes the exact algebraic minimization step after the source's
    GQR reduction.  It still assumes supplied GQR data and exact solved
    triangular equations; it does not prove GQR existence, nonsingularity of
    `S` or `L22`, or floating-point GQR stability. -/
theorem GeneralizedQRFactorization.isLSEMinimizer_of_triangular_solve
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    {y1 : Fin p → ℝ} {y2 : Fin q → ℝ}
    (hS_inj : Function.Injective (rectMatMulVec h.S))
    (hy1 : rectMatMulVec h.S y1 = d)
    (hy2 : rectMatMulVec h.L22 y2 =
      fun i : Fin q =>
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
          rectMatMulVec h.L21 y1 i) :
    IsLSEMinimizer A b B d
      (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  refine h.isLSEMinimizer_of_transformed_block_minimizer hy1 ?_
  intro z1 z2 hz1
  let c : Fin (r + q) → ℝ := matMulVec (r + q) (matTranspose h.U) b
  have hz1_eq : z1 = y1 := by
    apply hS_inj
    rw [hz1, hy1]
  subst z1
  have hy_lower_zero :
      (fun i : Fin q =>
        rectMatMulVec h.L21 y1 i + rectMatMulVec h.L22 y2 i -
          c (Fin.natAdd r i)) = 0 := by
    ext i
    have hi := congrFun hy2 i
    dsimp [c] at hi ⊢
    rw [hi]
    ring
  rw [lsObjective_gqrAQBlock_eq, lsObjective_gqrAQBlock_eq, hy_lower_zero]
  have hnonneg :
      0 ≤ vecNorm2Sq
        (fun i : Fin q =>
          rectMatMulVec h.L21 y1 i + rectMatMulVec h.L22 z2 i -
            c (Fin.natAdd r i)) :=
    vecNorm2Sq_nonneg _
  have hzero : vecNorm2Sq (0 : Fin q → ℝ) = 0 := by
    simp [vecNorm2Sq]
  rw [hzero]
  linarith

/-- Exact GQR method solve-existence handoff:
    if the displayed constraint block `S` is bijective as a square solve map
    and the lower block `L22` can solve every right-hand side, then there are
    block variables `y1`, `y2` satisfying the source equations
    `S y1 = d` and `L22 y2 = c2 - L21 y1`, and the recovered
    `x = Q [y1; y2]` is an exact LSE minimizer.

    This is still supplied-factorization, exact-arithmetic algebra.  It does
    not prove that triangular nonsingularity follows from (20.24), construct
    the GQR factors, or analyze a computed GQR method. -/
theorem GeneralizedQRFactorization.exists_isLSEMinimizer_of_solve_maps
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hS_bij : Function.Bijective (rectMatMulVec h.S))
    (hL22_surj : Function.Surjective (rectMatMulVec h.L22)) :
    ∃ y1 : Fin p → ℝ, ∃ y2 : Fin q → ℝ,
      rectMatMulVec h.S y1 = d ∧
      rectMatMulVec h.L22 y2 =
        (fun i : Fin q =>
          matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
            rectMatMulVec h.L21 y1 i) ∧
      IsLSEMinimizer A b B d
        (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  rcases hS_bij.2 d with ⟨y1, hy1⟩
  rcases hL22_surj
      (fun i : Fin q =>
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
          rectMatMulVec h.L21 y1 i) with
    ⟨y2, hy2⟩
  refine ⟨y1, y2, hy1, hy2, ?_⟩
  exact h.isLSEMinimizer_of_triangular_solve hS_bij.1 hy1 hy2

/-- The lower-triangular GQR constraint block `S` is a bijective solve map when
    its diagonal entries are nonzero.  This is the source-facing triangular
    nonsingularity bridge for Theorem 20.9, under supplied GQR data. -/
theorem GeneralizedQRFactorization.s_bijective_of_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hdiag : ∀ i : Fin p, h.S i i ≠ 0) :
    Function.Bijective (rectMatMulVec h.S) :=
  rectMatMulVec_bijective_of_lowerTriangular_diag_ne_zero h.lowerS hdiag

/-- The lower-triangular GQR block `L22` is a bijective solve map when its
    diagonal entries are nonzero.  This is the source-facing triangular
    nonsingularity bridge for Theorem 20.9, under supplied GQR data. -/
theorem GeneralizedQRFactorization.l22_bijective_of_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hdiag : ∀ i : Fin q, h.L22 i i ≠ 0) :
    Function.Bijective (rectMatMulVec h.L22) :=
  rectMatMulVec_bijective_of_lowerTriangular_diag_ne_zero h.lowerL22 hdiag

/-- Converse triangular nonsingularity bridge for the GQR constraint block
    `S`: a bijective square solve map has nonzero diagonal entries. -/
theorem GeneralizedQRFactorization.s_diag_ne_zero_of_bijective
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hbij : Function.Bijective (rectMatMulVec h.S)) :
    ∀ i : Fin p, h.S i i ≠ 0 :=
  rectMatMulVec_diag_ne_zero_of_lowerTriangular_bijective h.lowerS hbij

/-- Converse triangular nonsingularity bridge for the GQR lower block `L22`:
    a bijective square solve map has nonzero diagonal entries. -/
theorem GeneralizedQRFactorization.l22_diag_ne_zero_of_bijective
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hbij : Function.Bijective (rectMatMulVec h.L22)) :
    ∀ i : Fin q, h.L22 i i ≠ 0 :=
  rectMatMulVec_diag_ne_zero_of_lowerTriangular_bijective h.lowerL22 hbij

/-- Supplied-GQR lower-triangular nonsingularity equivalence for the
    constraint block `S`: nonzero diagonal entries are equivalent to bijective
    solvability of `S y = d`. -/
theorem GeneralizedQRFactorization.s_bijective_iff_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    Function.Bijective (rectMatMulVec h.S) ↔
      ∀ i : Fin p, h.S i i ≠ 0 := by
  constructor
  · exact h.s_diag_ne_zero_of_bijective
  · exact h.s_bijective_of_diag_ne_zero

/-- Supplied-GQR lower-triangular nonsingularity equivalence for the lower
    block `L22`: nonzero diagonal entries are equivalent to bijective
    solvability of `L22 y = e`. -/
theorem GeneralizedQRFactorization.l22_bijective_iff_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    Function.Bijective (rectMatMulVec h.L22) ↔
      ∀ i : Fin q, h.L22 i i ≠ 0 := by
  constructor
  · exact h.l22_diag_ne_zero_of_bijective
  · exact h.l22_bijective_of_diag_ne_zero

/-- Exact GQR method solve-existence handoff from triangular nonsingularity:
    if the displayed lower-triangular GQR blocks `S` and `L22` have nonzero
    diagonal entries, then the triangular systems in the method following
    (20.27) have exact solutions and the recovered `x = Q [y1; y2]` is an LSE
    minimizer.

    This proves the exact algebraic consequence of the source's nonsingular
    triangular blocks.  It still assumes supplied GQR factorization data and
    does not construct the factors or analyze floating-point GQR stability. -/
theorem GeneralizedQRFactorization.exists_isLSEMinimizer_of_triangular_nonsingular
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hS_diag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22_diag : ∀ i : Fin q, h.L22 i i ≠ 0) :
    ∃ y1 : Fin p → ℝ, ∃ y2 : Fin q → ℝ,
      rectMatMulVec h.S y1 = d ∧
      rectMatMulVec h.L22 y2 =
        (fun i : Fin q =>
          matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
            rectMatMulVec h.L21 y1 i) ∧
      IsLSEMinimizer A b B d
        (matMulVec (p + q) h.Q (Fin.append y1 y2)) :=
  h.exists_isLSEMinimizer_of_solve_maps
    (h.s_bijective_of_diag_ne_zero hS_diag)
    (h.l22_bijective_of_diag_ne_zero hL22_diag).2

/-- Supplied-GQR equivalence for the first condition in (20.24):
    the local full-row-rank formulation for `B`, namely surjectivity of
    `x ↦ Bx`, is equivalent to surjectivity of the transformed square solve
    map `y1 ↦ S y1` in `B Q = [S 0]`.

    This is exact algebra for supplied GQR data.  It does not construct the
    GQR factors or prove a triangular determinant/numeric-rank theorem. -/
theorem GeneralizedQRFactorization.s_surjective_iff_lseFullRowRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    Function.Surjective (rectMatMulVec h.S) ↔ LSEFullRowRank B := by
  constructor
  · intro hS d
    rcases hS d with ⟨y1, hy1⟩
    let y2 : Fin q → ℝ := 0
    refine ⟨matMulVec (p + q) h.Q (Fin.append y1 y2), ?_⟩
    ext i
    have hc := congrFun (h.constraint_eq y1 y2) i
    simpa [lseConstraintLinearMap, hy1] using hc
  · intro hB d
    rcases hB d with ⟨x, hx⟩
    let z : Fin (p + q) → ℝ := matMulVec (p + q) (matTranspose h.Q) x
    let z1 : Fin p → ℝ := fun i => z (Fin.castAdd q i)
    let z2 : Fin q → ℝ := fun i => z (Fin.natAdd p i)
    refine ⟨z1, ?_⟩
    have hz_append : Fin.append z1 z2 = z := by
      simpa [z1, z2] using finAppend_left_right (p := p) (q := q) z
    have hx_recover :
        matMulVec (p + q) h.Q (Fin.append z1 z2) = x := by
      rw [hz_append]
      exact matMulVec_orthogonal_mul_transpose h.orthQ x
    have hconstraint := h.constraint_eq z1 z2
    rw [hx_recover] at hconstraint
    ext i
    have hc := congrFun hconstraint i
    have hxi := congrFun hx i
    have hxi' : rectMatMulVec B x i = d i := by
      simpa [lseConstraintLinearMap] using hxi
    exact hc.symm.trans hxi'

/-- Supplied-GQR bijective form of the first condition in (20.24):
    because `S` is square, the local full-row-rank condition for `B` is
    equivalent to bijectivity of the solve map `y1 ↦ S y1`.

    The square surjective-to-injective step uses Mathlib finite-dimensional
    linear algebra; no triangular determinant theorem is claimed here. -/
theorem GeneralizedQRFactorization.s_bijective_iff_lseFullRowRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    Function.Bijective (rectMatMulVec h.S) ↔ LSEFullRowRank B := by
  constructor
  · intro hS
    exact (h.s_surjective_iff_lseFullRowRank).1 hS.2
  · intro hB
    have hsurj : Function.Surjective (rectMatMulVec h.S) :=
      (h.s_surjective_iff_lseFullRowRank).2 hB
    have hlinSurj : Function.Surjective (lseConstraintLinearMap h.S) := by
      simpa [lseConstraintLinearMap] using hsurj
    have hlinInj : Function.Injective (lseConstraintLinearMap h.S) :=
      (LinearMap.injective_iff_surjective).mpr hlinSurj
    have hinj : Function.Injective (rectMatMulVec h.S) := by
      simpa [lseConstraintLinearMap] using hlinInj
    exact ⟨hinj, hsurj⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    for supplied GQR data, `B` has full row rank iff the displayed
    lower-triangular constraint block `S` has trivial kernel.

    This is the source proof sentence "B has full rank if and only if S is
    nonsingular" in kernel form.  It does not construct the GQR factors. -/
theorem GeneralizedQRFactorization.lseFullRowRank_iff_s_kernel_trivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    LSEFullRowRank B ↔
      ∀ y1 : Fin p → ℝ, rectMatMulVec h.S y1 = 0 → y1 = 0 := by
  constructor
  · intro hB y1 hy1
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_lseFullRowRank).2 hB
    apply hS_bij.1
    rw [hy1, rectMatMulVec_zero]
  · intro hker
    have hS_inj : Function.Injective (rectMatMulVec h.S) := by
      intro y1 z1 hyz
      let w : Fin p → ℝ := fun i => y1 i - z1 i
      have hSw : rectMatMulVec h.S w = 0 := by
        ext i
        have hi := congrFun hyz i
        have hsub := congrFun (rectMatMulVec_sub h.S y1 z1) i
        dsimp [w]
        rw [hsub, hi]
        ring
      have hw : w = 0 := hker w hSw
      ext i
      have hwi := congrFun hw i
      dsimp [w] at hwi
      linarith
    have hS_diag : ∀ i : Fin p, h.S i i ≠ 0 :=
      rectMatMulVec_diag_ne_zero_of_lowerTriangular_injective
        h.lowerS hS_inj
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_diag_ne_zero).2 hS_diag
    exact (h.s_bijective_iff_lseFullRowRank).1 hS_bij

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    for supplied GQR data, `B` has full row rank iff the lower-triangular
    constraint block `S` has nonzero diagonal entries.

    This is the source proof sentence "B has full rank if and only if S is
    nonsingular" in triangular diagonal form. -/
theorem GeneralizedQRFactorization.lseFullRowRank_iff_s_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    LSEFullRowRank B ↔
      ∀ i : Fin p, h.S i i ≠ 0 := by
  constructor
  · intro hB
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_lseFullRowRank).2 hB
    exact (h.s_bijective_iff_diag_ne_zero).1 hS_bij
  · intro hS_diag
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_diag_ne_zero).2 hS_diag
    exact (h.s_bijective_iff_lseFullRowRank).1 hS_bij

/-- Supplied-GQR equivalence for the second condition in (20.24):
    once the constraint block `S` is injective, the null-intersection
    condition `null(A) ∩ null(B) = {0}` is equivalent to injectivity of the
    lower-right block solve map `y2 ↦ L22 y2`.

    This is the exact block-algebra part of the source statement that the
    assumptions (20.24) correspond to nonsingularity of `S` and `L22`.  It does
    not prove GQR existence, (20.28), or any floating-point stability theorem. -/
theorem GeneralizedQRFactorization.nullIntersectionTrivial_iff_l22_injective
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hS_inj : Function.Injective (rectMatMulVec h.S)) :
    LSENullIntersectionTrivial A B ↔
      Function.Injective (rectMatMulVec h.L22) := by
  constructor
  · intro hnull y2 z2 hyz
    let w : Fin q → ℝ := fun i => y2 i - z2 i
    have hLw : rectMatMulVec h.L22 w = 0 := by
      ext i
      have hi := congrFun hyz i
      have hsub := congrFun (rectMatMulVec_sub h.L22 y2 z2) i
      dsimp [w]
      rw [hsub, hi]
      ring
    let y : Fin (p + q) → ℝ := Fin.append (0 : Fin p → ℝ) w
    let v : Fin (p + q) → ℝ := matMulVec (p + q) h.Q y
    have hBv : rectMatMulVec B v = 0 := by
      have hc := h.constraint_eq (0 : Fin p → ℝ) w
      change
        rectMatMulVec B
          (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) w)) = 0
      rw [hc]
      exact rectMatMulVec_zero h.S
    have hblock :
        rectMatMulVec
          (matMulRectLeft (matTranspose h.U)
            (matMulRect (r + q) (p + q) (p + q) A h.Q)) y = 0 := by
      have hb := h.transformed_A_mulVec_eq_block (0 : Fin p → ℝ) w
      change
        rectMatMulVec
          (matMulRectLeft (matTranspose h.U)
            (matMulRect (r + q) (p + q) (p + q) A h.Q))
          (Fin.append (0 : Fin p → ℝ) w) = 0
      rw [hb]
      ext i
      refine Fin.addCases
        (motive := fun i : Fin (r + q) =>
          Fin.append (rectMatMulVec h.L11 (0 : Fin p → ℝ))
            (fun i : Fin q =>
              rectMatMulVec h.L21 (0 : Fin p → ℝ) i +
                rectMatMulVec h.L22 w i) i =
              (0 : Fin (r + q) → ℝ) i)
        ?left ?right i
      · intro i
        simp [Fin.append_left, rectMatMulVec]
      · intro i
        have hi := congrFun hLw i
        simpa [Fin.append_right, rectMatMulVec] using hi
    have hAv : rectMatMulVec A v = 0 := by
      change rectMatMulVec A (matMulVec (p + q) h.Q y) = 0
      exact h.A_zero_of_transformed_A_zero hblock
    have hvzero : v = 0 := hnull v hAv hBv
    have hyzero : y = 0 := by
      have hrec := matMulVec_orthogonal_transpose_mul h.orthQ y
      dsimp [v] at hvzero
      rw [hvzero, matMulVec_zero] at hrec
      exact hrec.symm
    ext i
    have hwi : w i = 0 := by
      have hi := congrFun hyzero (Fin.natAdd p i)
      simpa [y, w, Fin.append_right] using hi
    dsimp [w] at hwi
    linarith
  · intro hL22 v hAv hBv
    let y : Fin (p + q) → ℝ := matMulVec (p + q) (matTranspose h.Q) v
    let y1 : Fin p → ℝ := fun i => y (Fin.castAdd q i)
    let y2 : Fin q → ℝ := fun i => y (Fin.natAdd p i)
    have hy_append : Fin.append y1 y2 = y := by
      simpa [y1, y2] using finAppend_left_right (p := p) (q := q) y
    have hv_recover :
        matMulVec (p + q) h.Q (Fin.append y1 y2) = v := by
      rw [hy_append]
      exact matMulVec_orthogonal_mul_transpose h.orthQ v
    have hSy1 : rectMatMulVec h.S y1 = 0 := by
      have hc := h.constraint_eq y1 y2
      rw [hv_recover] at hc
      rw [hBv] at hc
      exact hc.symm
    have hy1_zero : y1 = 0 := by
      apply hS_inj
      rw [hSy1, rectMatMulVec_zero]
    have htrans_zero :
        rectMatMulVec
          (matMulRectLeft (matTranspose h.U)
            (matMulRect (r + q) (p + q) (p + q) A h.Q))
          (Fin.append y1 y2) = 0 := by
      have hAv' :
          rectMatMulVec A
            (matMulVec (p + q) h.Q (Fin.append y1 y2)) = 0 := by
        rw [hv_recover]
        exact hAv
      exact h.transformed_A_zero_of_A_zero hAv'
    have hblock := h.transformed_A_mulVec_eq_block y1 y2
    rw [htrans_zero] at hblock
    have hL22y2 : rectMatMulVec h.L22 y2 = 0 := by
      ext i
      have hi := congrFun hblock (Fin.natAdd r i)
      have hi0 :
          (0 : Fin (r + q) → ℝ) (Fin.natAdd r i) =
            rectMatMulVec h.L21 y1 i + rectMatMulVec h.L22 y2 i := by
        simpa [Fin.append_right] using hi
      have hy1i : rectMatMulVec h.L21 y1 i = 0 := by
        rw [hy1_zero]
        simp [rectMatMulVec]
      have hiL : 0 = rectMatMulVec h.L22 y2 i := by
        simpa [hy1i] using hi0
      exact hiL.symm
    have hy2_zero : y2 = 0 := by
      apply hL22
      rw [hL22y2, rectMatMulVec_zero]
    have hy_zero : Fin.append y1 y2 = 0 := by
      rw [hy1_zero, hy2_zero]
      ext i
      exact Fin.addCases
        (motive := fun i : Fin (p + q) =>
          Fin.append (0 : Fin p → ℝ) (0 : Fin q → ℝ) i =
            (0 : Fin (p + q) → ℝ) i)
        (fun i => by simp [Fin.append_left])
        (fun i => by simp [Fin.append_right])
        i
    rw [← hv_recover, hy_zero]
    exact matMulVec_zero h.Q

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    assuming the GQR constraint block `S` is nonsingular, the condition
    `null(A) ∩ null(B) = {0}` is equivalent to the displayed `L22` block
    having trivial kernel.

    This names the source proof step `AQ₂ = U₂ L22` in kernel form, under
    supplied GQR data.  It is not a GQR existence theorem. -/
theorem GeneralizedQRFactorization.nullIntersectionTrivial_iff_l22_kernel_trivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hS_inj : Function.Injective (rectMatMulVec h.S)) :
    LSENullIntersectionTrivial A B ↔
      ∀ y2 : Fin q → ℝ, rectMatMulVec h.L22 y2 = 0 → y2 = 0 := by
  constructor
  · intro hnull y2 hy2
    have hL22_inj : Function.Injective (rectMatMulVec h.L22) :=
      (h.nullIntersectionTrivial_iff_l22_injective hS_inj).1 hnull
    apply hL22_inj
    rw [hy2, rectMatMulVec_zero]
  · intro hker
    have hL22_inj : Function.Injective (rectMatMulVec h.L22) := by
      intro y2 z2 hyz
      let w : Fin q → ℝ := fun i => y2 i - z2 i
      have hLw : rectMatMulVec h.L22 w = 0 := by
        ext i
        have hi := congrFun hyz i
        have hsub := congrFun (rectMatMulVec_sub h.L22 y2 z2) i
        dsimp [w]
        rw [hsub, hi]
        ring
      have hw : w = 0 := hker w hLw
      ext i
      have hwi := congrFun hw i
      dsimp [w] at hwi
      linarith
    exact (h.nullIntersectionTrivial_iff_l22_injective hS_inj).2 hL22_inj

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    for supplied GQR data, the local conditions (20.24) are equivalent to
    trivial kernels of the displayed triangular blocks `S` and `L22`.

    This is the kernel-form version of the source sentence that the
    assumptions (20.24) are equivalent to nonsingularity of `S` and `L22`.
    It assumes supplied GQR data and does not construct the factors. -/
theorem GeneralizedQRFactorization.conditions20_24_iff_s_l22_kernel_trivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    (LSEFullRowRank B ∧ LSENullIntersectionTrivial A B) ↔
      (∀ y1 : Fin p → ℝ, rectMatMulVec h.S y1 = 0 → y1 = 0) ∧
        (∀ y2 : Fin q → ℝ, rectMatMulVec h.L22 y2 = 0 → y2 = 0) := by
  constructor
  · rintro ⟨hB, hnull⟩
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_lseFullRowRank).2 hB
    exact
      ⟨(h.lseFullRowRank_iff_s_kernel_trivial).1 hB,
        (h.nullIntersectionTrivial_iff_l22_kernel_trivial hS_bij.1).1 hnull⟩
  · rintro ⟨hS_kernel, hL22_kernel⟩
    have hB : LSEFullRowRank B :=
      (h.lseFullRowRank_iff_s_kernel_trivial).2 hS_kernel
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_lseFullRowRank).2 hB
    have hnull : LSENullIntersectionTrivial A B :=
      (h.nullIntersectionTrivial_iff_l22_kernel_trivial hS_bij.1).2 hL22_kernel
    exact ⟨hB, hnull⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    once the GQR constraint block `S` is nonsingular, the local
    null-intersection condition is equivalent to nonsingularity of the
    lower-triangular `L22` block, expressed as nonzero diagonal entries.

    This is the conditional form of the source sentence before the combined
    `(20.24)`-to-`S`/`L22` equivalence below. -/
theorem GeneralizedQRFactorization.nullIntersectionTrivial_iff_l22_diag_ne_zero_of_s_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hS_diag : ∀ i : Fin p, h.S i i ≠ 0) :
    LSENullIntersectionTrivial A B ↔
      ∀ i : Fin q, h.L22 i i ≠ 0 := by
  have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
    (h.s_bijective_iff_diag_ne_zero).2 hS_diag
  have hS_inj : Function.Injective (rectMatMulVec h.S) := hS_bij.1
  constructor
  · intro hnull
    have hL22_inj : Function.Injective (rectMatMulVec h.L22) :=
      (h.nullIntersectionTrivial_iff_l22_injective hS_inj).1 hnull
    exact rectMatMulVec_diag_ne_zero_of_lowerTriangular_injective
      h.lowerL22 hL22_inj
  · intro hL22_diag
    have hL22_bij : Function.Bijective (rectMatMulVec h.L22) :=
      (h.l22_bijective_iff_diag_ne_zero).2 hL22_diag
    exact (h.nullIntersectionTrivial_iff_l22_injective hS_inj).2
      hL22_bij.1

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, sentence after (20.28):
    for supplied GQR data, the local conditions (20.24) are equivalent to
    nonsingularity of the lower-triangular blocks `S` and `L22`.

    The source's nonsingularity wording is expressed here as nonzero diagonals
    for the supplied lower-triangular blocks.  This still assumes the GQR
    factors have been supplied; it does not prove their existence or construct
    the (20.28) case split. -/
theorem GeneralizedQRFactorization.conditions20_24_iff_s_l22_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    (LSEFullRowRank B ∧ LSENullIntersectionTrivial A B) ↔
      (∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) := by
  constructor
  · rintro ⟨hB, hnull⟩
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_lseFullRowRank).2 hB
    have hS_diag : ∀ i : Fin p, h.S i i ≠ 0 :=
      (h.s_bijective_iff_diag_ne_zero).1 hS_bij
    have hL22_inj : Function.Injective (rectMatMulVec h.L22) :=
      (h.nullIntersectionTrivial_iff_l22_injective hS_bij.1).1 hnull
    have hL22_diag : ∀ i : Fin q, h.L22 i i ≠ 0 :=
      rectMatMulVec_diag_ne_zero_of_lowerTriangular_injective
        h.lowerL22 hL22_inj
    exact ⟨hS_diag, hL22_diag⟩
  · rintro ⟨hS_diag, hL22_diag⟩
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_diag_ne_zero).2 hS_diag
    have hB : LSEFullRowRank B :=
      (h.s_bijective_iff_lseFullRowRank).1 hS_bij
    have hL22_bij : Function.Bijective (rectMatMulVec h.L22) :=
      (h.l22_bijective_iff_diag_ne_zero).2 hL22_diag
    have hnull : LSENullIntersectionTrivial A B :=
      (h.nullIntersectionTrivial_iff_l22_injective hS_bij.1).2
        hL22_bij.1
    exact ⟨hB, hnull⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, sentence after (20.28):
    the same supplied-GQR local-condition equivalence as
    `conditions20_24_iff_s_l22_diag_ne_zero`, but with nonsingularity stated as
    bijectivity of the triangular solve maps for `S` and `L22`.

    This is the source's "S and L22 are nonsingular" wording in solve-map
    form. It remains a supplied-factor theorem, not the GQR existence proof. -/
theorem GeneralizedQRFactorization.conditions20_24_iff_s_l22_bijective
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    (LSEFullRowRank B ∧ LSENullIntersectionTrivial A B) ↔
      Function.Bijective (rectMatMulVec h.S) ∧
        Function.Bijective (rectMatMulVec h.L22) := by
  constructor
  · intro hcond
    have hdiag :
        (∀ i : Fin p, h.S i i ≠ 0) ∧
          (∀ i : Fin q, h.L22 i i ≠ 0) :=
      (h.conditions20_24_iff_s_l22_diag_ne_zero).1 hcond
    exact
      ⟨(h.s_bijective_iff_diag_ne_zero).2 hdiag.1,
        (h.l22_bijective_iff_diag_ne_zero).2 hdiag.2⟩
  · intro hbij
    have hdiag :
        (∀ i : Fin p, h.S i i ≠ 0) ∧
          (∀ i : Fin q, h.L22 i i ≠ 0) :=
      ⟨(h.s_bijective_iff_diag_ne_zero).1 hbij.1,
        (h.l22_bijective_iff_diag_ne_zero).1 hbij.2⟩
    exact (h.conditions20_24_iff_s_l22_diag_ne_zero).2 hdiag

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    for supplied GQR data, full row rank of `B` and full column rank of the
    local vertical stack `[A; B]` are equivalent to trivial kernels of the
    displayed triangular blocks `S` and `L22`.

    This is the source stacked-rank version of
    `GeneralizedQRFactorization.conditions20_24_iff_s_l22_kernel_trivial`.
    It assumes supplied GQR data and does not construct the factors. -/
theorem GeneralizedQRFactorization.fullRowRank_stackedFullColumnRank_iff_s_l22_kernel_trivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    (LSEFullRowRank B ∧ LSEStackedFullColumnRank A B) ↔
      (∀ y1 : Fin p → ℝ, rectMatMulVec h.S y1 = 0 → y1 = 0) ∧
        (∀ y2 : Fin q → ℝ, rectMatMulVec h.L22 y2 = 0 → y2 = 0) := by
  constructor
  · rintro ⟨hB, hstack⟩
    exact (h.conditions20_24_iff_s_l22_kernel_trivial).1
      ⟨hB, (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack⟩
  · intro hker
    have hcond : LSEFullRowRank B ∧ LSENullIntersectionTrivial A B :=
      (h.conditions20_24_iff_s_l22_kernel_trivial).2 hker
    exact ⟨hcond.1,
      (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).1 hcond.2⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, sentence after (20.28):
    for supplied GQR data, full row rank of `B` and full column rank of the
    local vertical stack `[A; B]` are equivalent to nonzero diagonals of the
    lower-triangular blocks `S` and `L22`.

    This is the source stacked-rank version of
    `GeneralizedQRFactorization.conditions20_24_iff_s_l22_diag_ne_zero`.
    It assumes supplied GQR data and does not construct the factors. -/
theorem GeneralizedQRFactorization.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    (LSEFullRowRank B ∧ LSEStackedFullColumnRank A B) ↔
      (∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) := by
  constructor
  · rintro ⟨hB, hstack⟩
    exact (h.conditions20_24_iff_s_l22_diag_ne_zero).1
      ⟨hB, (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack⟩
  · intro hdiag
    have hcond : LSEFullRowRank B ∧ LSENullIntersectionTrivial A B :=
      (h.conditions20_24_iff_s_l22_diag_ne_zero).2 hdiag
    exact ⟨hcond.1,
      (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).1 hcond.2⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, sentence after (20.28):
    the same supplied-GQR stacked-rank equivalence as
    `fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero`, but with
    nonsingularity stated as bijectivity of the triangular solve maps for `S`
    and `L22`.

    This remains supplied-factor algebra, not the GQR existence proof. -/
theorem GeneralizedQRFactorization.fullRowRank_stackedFullColumnRank_iff_s_l22_bijective
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    (LSEFullRowRank B ∧ LSEStackedFullColumnRank A B) ↔
      Function.Bijective (rectMatMulVec h.S) ∧
        Function.Bijective (rectMatMulVec h.L22) := by
  constructor
  · rintro ⟨hB, hstack⟩
    exact (h.conditions20_24_iff_s_l22_bijective).1
      ⟨hB, (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack⟩
  · intro hbij
    have hcond : LSEFullRowRank B ∧ LSENullIntersectionTrivial A B :=
      (h.conditions20_24_iff_s_l22_bijective).2 hbij
    exact ⟨hcond.1,
      (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).1 hcond.2⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, sentence after (20.28):
    source full row rank of `B` and full column rank of `[A; B]` construct
    exact GQR data whose displayed triangular blocks `S` and `L22` have
    nonzero diagonals.

    This removes the supplied-factor hypothesis from the diagonal
    nonsingularity surface, while remaining exact algebra for (20.27). -/
theorem GeneralizedQRFactorization.exists_with_s_l22_diag_ne_zero_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r p q A B,
      (∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) := by
  rcases
    GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨h⟩
  exact ⟨h,
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1
      ⟨hB, hstack⟩⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, sentence after (20.28):
    source full row rank of `B` and full column rank of `[A; B]` construct
    exact GQR data whose displayed triangular blocks `S` and `L22` are
    bijective solve maps.

    This is the constructed-factor version of the source nonsingularity
    statement, expressed as solvability of the two triangular systems. -/
theorem GeneralizedQRFactorization.exists_with_s_l22_bijective_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r p q A B,
      Function.Bijective (rectMatMulVec h.S) ∧
        Function.Bijective (rectMatMulVec h.L22) := by
  rcases
    GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨h⟩
  exact ⟨h,
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_bijective).1
      ⟨hB, hstack⟩⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, exact supplied-GQR solve
    consequence under the local assumptions (20.24).

    For supplied GQR data, the local full-row-rank/null-intersection
    hypotheses imply the lower-triangular nonsingularity conditions, hence the
    triangular GQR method has exact solution variables `y1`, `y2` and the
    recovered vector `Q [y1; y2]` is an LSE minimizer.  This still assumes the
    GQR factors themselves have been supplied; it does not construct them. -/
theorem GeneralizedQRFactorization.exists_isLSEMinimizer_of_conditions20_24
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hnull : LSENullIntersectionTrivial A B) :
    ∃ y1 : Fin p → ℝ, ∃ y2 : Fin q → ℝ,
      rectMatMulVec h.S y1 = d ∧
      rectMatMulVec h.L22 y2 =
        (fun i : Fin q =>
          matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
            rectMatMulVec h.L21 y1 i) ∧
      IsLSEMinimizer A b B d
        (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  have hdiag :
      (∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) :=
    (h.conditions20_24_iff_s_l22_diag_ne_zero).1 ⟨hB, hnull⟩
  exact h.exists_isLSEMinimizer_of_triangular_nonsingular
    hdiag.1 hdiag.2

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, exact supplied-GQR solve
    consequence stated at the kernel nonsingularity surface after (20.28).

    If the supplied triangular blocks `S` and `L22` have trivial kernels, the
    triangular GQR method has exact solution variables `y1`, `y2` and the
    recovered vector `Q [y1; y2]` is an LSE minimizer.  This is supplied-factor
    algebra only; it does not construct the GQR factors. -/
theorem GeneralizedQRFactorization.exists_isLSEMinimizer_of_s_l22_kernel_trivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hS_kernel : ∀ y1 : Fin p → ℝ, rectMatMulVec h.S y1 = 0 → y1 = 0)
    (hL22_kernel : ∀ y2 : Fin q → ℝ, rectMatMulVec h.L22 y2 = 0 → y2 = 0) :
    ∃ y1 : Fin p → ℝ, ∃ y2 : Fin q → ℝ,
      rectMatMulVec h.S y1 = d ∧
      rectMatMulVec h.L22 y2 =
        (fun i : Fin q =>
          matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
            rectMatMulVec h.L21 y1 i) ∧
      IsLSEMinimizer A b B d
        (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  have hcond : LSEFullRowRank B ∧ LSENullIntersectionTrivial A B :=
    (h.conditions20_24_iff_s_l22_kernel_trivial).2
      ⟨hS_kernel, hL22_kernel⟩
  exact h.exists_isLSEMinimizer_of_conditions20_24 hcond.1 hcond.2

/-- Direct LSE minimizer existence from supplied GQR data and the local
    assumptions (20.24).

    This is the existence-only corollary of
    `GeneralizedQRFactorization.exists_isLSEMinimizer_of_conditions20_24`,
    useful for source statements that do not need to expose the triangular
    solution variables. -/
theorem GeneralizedQRFactorization.exists_lse_minimizer_of_conditions20_24
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hnull : LSENullIntersectionTrivial A B) :
    ∃ x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases h.exists_isLSEMinimizer_of_conditions20_24 hB hnull with
    ⟨y1, y2, _hS, _hL22, hmin⟩
  exact ⟨matMulVec (p + q) h.Q (Fin.append y1 y2), hmin⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, exact supplied-GQR solve
    consequence under the source rank assumptions: full row rank of `B` and
    full column rank of the local vertical stack `[A; B]`.

    This is the stacked-rank version of
    `GeneralizedQRFactorization.exists_isLSEMinimizer_of_conditions20_24`.
    It still assumes supplied GQR data and does not construct the factors. -/
theorem GeneralizedQRFactorization.exists_isLSEMinimizer_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ y1 : Fin p → ℝ, ∃ y2 : Fin q → ℝ,
      rectMatMulVec h.S y1 = d ∧
      rectMatMulVec h.L22 y2 =
        (fun i : Fin q =>
          matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
            rectMatMulVec h.L21 y1 i) ∧
    IsLSEMinimizer A b B d
        (matMulVec (p + q) h.Q (Fin.append y1 y2)) :=
  h.exists_isLSEMinimizer_of_conditions20_24 hB
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 and the GQR method paragraph:
    under supplied GQR data and the source rank assumptions, the triangular
    solve coordinates `y1`, `y2` used by the exact GQR method exist uniquely.

    This formalizes the source wording that the constraint determines `y1` and
    the trailing triangular system determines `y2`. It remains supplied-factor
    algebra: it does not construct the GQR factors or prove computed GQR
    stability. -/
theorem GeneralizedQRFactorization.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
      rectMatMulVec h.S yz.1 = d ∧
      rectMatMulVec h.L22 yz.2 =
        (fun i : Fin q =>
          matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
            rectMatMulVec h.L21 yz.1 i) ∧
      IsLSEMinimizer A b B d
        (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2)) := by
  rcases h.exists_isLSEMinimizer_of_fullRowRank_stackedFullColumnRank hB hstack with
    ⟨y1, y2, hS, hL22, hmin⟩
  have hbij :
      Function.Bijective (rectMatMulVec h.S) ∧
        Function.Bijective (rectMatMulVec h.L22) :=
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_bijective).1
      ⟨hB, hstack⟩
  refine ⟨⟨y1, y2⟩, ⟨hS, hL22, hmin⟩, ?_⟩
  rintro ⟨z1, z2⟩ ⟨hzS, hzL22, _hzmin⟩
  have hz1 : z1 = y1 := hbij.1.1 (by rw [hzS, hS])
  subst z1
  have hz2 : z2 = y2 := hbij.2.1 (by rw [hzL22, hL22])
  subst z2
  rfl

/-- Direct LSE minimizer existence from supplied GQR data and the source rank
    assumptions: full row rank of `B` and full column rank of the local vertical
    stack `[A; B]`.

    This is the existence-only corollary of
    `GeneralizedQRFactorization.exists_isLSEMinimizer_of_fullRowRank_stackedFullColumnRank`.
    It still assumes supplied GQR data and does not construct the factors. -/
theorem GeneralizedQRFactorization.exists_lse_minimizer_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases h.exists_isLSEMinimizer_of_fullRowRank_stackedFullColumnRank hB hstack with
    ⟨y1, y2, _hS, _hL22, hmin⟩
  exact ⟨matMulVec (p + q) h.Q (Fin.append y1 y2), hmin⟩

/-- Higham, 2nd ed., Chapter 20, equations (20.29)-(20.30): the horizontally
    partitioned matrix `[A1 A2]` that appears after the column-pivoted QR
    partition. -/
noncomputable def lseEliminationBlockMatrix {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ) :
    Fin m → Fin (p + q) → ℝ :=
  fun i => Fin.append (A1 i) (A2 i)

/-- Matrix-vector multiplication by the partitioned matrix `[A1 A2]` in
    (20.30) splits into the two block actions. -/
theorem lseEliminationBlockMatrix_mulVec {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (x1 : Fin p → ℝ) (x2 : Fin q → ℝ) :
    rectMatMulVec (lseEliminationBlockMatrix A1 A2) (Fin.append x1 x2) =
      fun i : Fin m => rectMatMulVec A1 x1 i + rectMatMulVec A2 x2 i := by
  ext i
  unfold rectMatMulVec lseEliminationBlockMatrix
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- Higham, 2nd ed., Chapter 20, equation (20.29): with supplied inverse
    action for `R1`, the eliminated leading variables are
    `x1 = R1^{-1}(qtd - R2 x2)`, where `qtd` stands for `Q^T d`. -/
noncomputable def lseEliminationBackSubstitution {p q : ℕ}
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (x2 : Fin q → ℝ) : Fin p → ℝ :=
  rectMatMulVec R1inv (fun i => qtd i - rectMatMulVec R2 x2 i)

/-- The back-substitution vector from (20.29) satisfies the transformed
    constraint `R1 x1 + R2 x2 = qtd` whenever the supplied `R1inv` is a left
    inverse for the displayed triangular factor `R1`. -/
theorem lseEliminationBlockConstraint_eq_qtd_of_left_inverse {p q : ℕ}
    (R1 R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (x2 : Fin q → ℝ)
    (hleft : ∀ v : Fin p → ℝ, rectMatMulVec R1 (rectMatMulVec R1inv v) = v) :
    rectMatMulVec (lseEliminationBlockMatrix R1 R2)
        (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) =
      qtd := by
  ext i
  rw [congrFun
    (lseEliminationBlockMatrix_mulVec R1 R2
      (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) i]
  unfold lseEliminationBackSubstitution
  have hi := congrFun
    (hleft (fun k : Fin p => qtd k - rectMatMulVec R2 x2 k)) i
  rw [hi]
  ring

/-- Higham, 2nd ed., Chapter 20, equation (20.30): action of the Schur
    complement coefficient
    `(A2 - A1 R1^{-1} R2) x2`. -/
noncomputable def lseEliminationReducedAction {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (x2 : Fin q → ℝ) : Fin m → ℝ :=
  fun i =>
    rectMatMulVec A2 x2 i -
      rectMatMulVec A1 (rectMatMulVec R1inv (rectMatMulVec R2 x2)) i

/-- Higham, 2nd ed., Chapter 20, equation (20.30): right-hand side
    `b - A1 R1^{-1} qtd`, with `qtd = Q^T d`. -/
noncomputable def lseEliminationReducedRhs {m p : ℕ}
    (A1 : Fin m → Fin p → ℝ) (R1inv : Fin p → Fin p → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) : Fin m → ℝ :=
  fun i => b i - rectMatMulVec A1 (rectMatMulVec R1inv qtd) i

/-- Exact residual reduction for Higham's elimination method in (20.29)-(20.30):
    substituting `x1 = R1^{-1}(qtd - R2 x2)` into `[A1 A2][x1; x2] - b`
    gives the unconstrained residual
    `(A2 - A1 R1^{-1} R2)x2 - (b - A1 R1^{-1}qtd)`.

    This is exact algebra under supplied partition and inverse-action data; it
    does not construct the pivoted QR factorization in (20.29). -/
theorem lseEliminationResidual_eq_reduced {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ) :
    lsResidual (lseEliminationBlockMatrix A1 A2) b
        (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) =
      fun i : Fin m =>
        lseEliminationReducedAction A1 A2 R1inv R2 x2 i -
          lseEliminationReducedRhs A1 R1inv qtd b i := by
  ext i
  have hback :
      lseEliminationBackSubstitution R1inv R2 qtd x2 =
        fun j : Fin p =>
          rectMatMulVec R1inv qtd j -
            rectMatMulVec R1inv (rectMatMulVec R2 x2) j := by
    ext j
    unfold lseEliminationBackSubstitution
    exact congrFun
      (rectMatMulVec_sub R1inv qtd (rectMatMulVec R2 x2)) j
  have hA1back :
      rectMatMulVec A1 (lseEliminationBackSubstitution R1inv R2 qtd x2) i =
        rectMatMulVec A1 (rectMatMulVec R1inv qtd) i -
          rectMatMulVec A1
            (rectMatMulVec R1inv (rectMatMulVec R2 x2)) i := by
    rw [hback]
    exact congrFun
      (rectMatMulVec_sub A1 (rectMatMulVec R1inv qtd)
        (rectMatMulVec R1inv (rectMatMulVec R2 x2))) i
  calc
    lsResidual (lseEliminationBlockMatrix A1 A2) b
        (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) i
        =
          (rectMatMulVec A1
              (lseEliminationBackSubstitution R1inv R2 qtd x2) i +
            rectMatMulVec A2 x2 i) - b i := by
            unfold lsResidual
            rw [congrFun
              (lseEliminationBlockMatrix_mulVec A1 A2
                (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) i]
    _ = lseEliminationReducedAction A1 A2 R1inv R2 x2 i -
          lseEliminationReducedRhs A1 R1inv qtd b i := by
            rw [hA1back]
            unfold lseEliminationReducedAction lseEliminationReducedRhs
            ring

/-- Squared objective for the reduced unconstrained problem in (20.30). -/
noncomputable def lseEliminationReducedObjective {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ) : ℝ :=
  vecNorm2Sq
    (fun i : Fin m =>
      lseEliminationReducedAction A1 A2 R1inv R2 x2 i -
        lseEliminationReducedRhs A1 R1inv qtd b i)

/-- Exact squared-objective reduction for Higham's elimination method in
    (20.29)-(20.30). -/
theorem lseEliminationObjective_eq_reduced {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ) :
    lsObjective (lseEliminationBlockMatrix A1 A2) b
        (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) =
      lseEliminationReducedObjective A1 A2 R1inv R2 qtd b x2 := by
  unfold lsObjective lseEliminationReducedObjective
  rw [lseEliminationResidual_eq_reduced]

/-- A vector `x2` solves the reduced unconstrained least-squares problem
    displayed in Higham's equation (20.30). -/
def IsLSEEliminationReducedMinimizer {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ) : Prop :=
  ∀ z2 : Fin q → ℝ,
    lseEliminationReducedObjective A1 A2 R1inv R2 qtd b x2 ≤
      lseEliminationReducedObjective A1 A2 R1inv R2 qtd b z2

/-- Conversely to `lseEliminationBlockConstraint_eq_qtd_of_left_inverse`,
    a feasible partitioned vector has its leading block equal to the
    back-substitution value from (20.29), provided the supplied inverse action
    also satisfies `R1inv * R1 = I`. -/
theorem lseEliminationBackSubstitution_eq_of_block_constraint {p q : ℕ}
    (R1 R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (x1 : Fin p → ℝ) (x2 : Fin q → ℝ)
    (hright : ∀ v : Fin p → ℝ, rectMatMulVec R1inv (rectMatMulVec R1 v) = v)
    (hconstraint :
      rectMatMulVec (lseEliminationBlockMatrix R1 R2) (Fin.append x1 x2) =
        qtd) :
    x1 = lseEliminationBackSubstitution R1inv R2 qtd x2 := by
  have hsplit := lseEliminationBlockMatrix_mulVec R1 R2 x1 x2
  have hR1 :
      rectMatMulVec R1 x1 =
        fun i : Fin p => qtd i - rectMatMulVec R2 x2 i := by
    ext i
    have hi := congrFun hconstraint i
    have hsplit_i := congrFun hsplit i
    rw [hsplit_i] at hi
    linarith
  calc
    x1 = rectMatMulVec R1inv (rectMatMulVec R1 x1) := by
      exact (hright x1).symm
    _ = lseEliminationBackSubstitution R1inv R2 qtd x2 := by
      rw [hR1]
      rfl

/-- Higham, 2nd ed., Chapter 20, equations (20.29)-(20.30):
    exact minimizer handoff for the elimination method.

    If `x2` minimizes the reduced unconstrained problem obtained after
    eliminating `x1`, then `[R1^{-1}(qtd - R2 x2); x2]` is an exact minimizer of
    the equality-constrained least-squares problem with coefficient blocks
    `[A1 A2]` and constraint blocks `[R1 R2]`. The theorem assumes the inverse
    action for `R1` is supplied in both orders; it does not construct the
    pivoted QR factorization or prove `R1` nonsingular. -/
theorem lseElimination_isLSEMinimizer_of_reduced_minimizer {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1 R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ)
    (hleft : ∀ v : Fin p → ℝ, rectMatMulVec R1 (rectMatMulVec R1inv v) = v)
    (hright : ∀ v : Fin p → ℝ, rectMatMulVec R1inv (rectMatMulVec R1 v) = v)
    (hmin : IsLSEEliminationReducedMinimizer A1 A2 R1inv R2 qtd b x2) :
    IsLSEMinimizer (lseEliminationBlockMatrix A1 A2) b
      (lseEliminationBlockMatrix R1 R2) qtd
      (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) := by
  refine ⟨?feasible, ?minimal⟩
  · intro i
    exact congrFun
      (lseEliminationBlockConstraint_eq_qtd_of_left_inverse
        R1 R1inv R2 qtd x2 hleft) i
  · intro y hy
    let y1 : Fin p → ℝ := fun i => y (Fin.castAdd q i)
    let y2 : Fin q → ℝ := fun i => y (Fin.natAdd p i)
    have hy_append : Fin.append y1 y2 = y := by
      simpa [y1, y2] using finAppend_left_right (p := p) (q := q) y
    have hy_constraint :
        rectMatMulVec (lseEliminationBlockMatrix R1 R2) (Fin.append y1 y2) =
          qtd := by
      ext i
      rw [hy_append]
      exact hy i
    have hy1_eq :
        y1 = lseEliminationBackSubstitution R1inv R2 qtd y2 :=
      lseEliminationBackSubstitution_eq_of_block_constraint
        R1 R1inv R2 qtd y1 y2 hright hy_constraint
    have hy_eq :
        y = Fin.append (lseEliminationBackSubstitution R1inv R2 qtd y2) y2 := by
      rw [← hy_append, hy1_eq]
    calc
      lsObjective (lseEliminationBlockMatrix A1 A2) b
          (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2)
          =
            lseEliminationReducedObjective A1 A2 R1inv R2 qtd b x2 := by
              exact lseEliminationObjective_eq_reduced A1 A2 R1inv R2 qtd b x2
      _ ≤ lseEliminationReducedObjective A1 A2 R1inv R2 qtd b y2 :=
            hmin y2
      _ =
          lsObjective (lseEliminationBlockMatrix A1 A2) b
            (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd y2) y2) := by
            exact (lseEliminationObjective_eq_reduced
              A1 A2 R1inv R2 qtd b y2).symm
      _ = lsObjective (lseEliminationBlockMatrix A1 A2) b y := by
            rw [hy_eq]

/-- Higham, 2nd ed., Chapter 20, equations (20.29)-(20.30):
    original-coordinate form of the elimination minimizer handoff.

    If column pivoting gives `BΠ = [R1 R2]` and `AΠ = [A1 A2]`, then a
    minimizer of the reduced unconstrained problem in (20.30), combined with
    the back-substitution in (20.29) and pulled back by `Πᵀ`, is an exact
    minimizer of the original equality-constrained problem. The theorem uses
    supplied partition and inverse-action data; it does not construct the
    pivoted QR factorization or prove `R1` nonsingular. -/
theorem lseElimination_isLSEMinimizer_original_of_reduced_minimizer
    {m p q : ℕ} (π : Fin (p + q) ≃ Fin (p + q))
    (A : Fin m → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1 R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ)
    (hAπ : rectPermuteCols π A = lseEliminationBlockMatrix A1 A2)
    (hBπ : rectPermuteCols π B = lseEliminationBlockMatrix R1 R2)
    (hleft : ∀ v : Fin p → ℝ, rectMatMulVec R1 (rectMatMulVec R1inv v) = v)
    (hright : ∀ v : Fin p → ℝ, rectMatMulVec R1inv (rectMatMulVec R1 v) = v)
    (hmin : IsLSEEliminationReducedMinimizer A1 A2 R1inv R2 qtd b x2) :
    IsLSEMinimizer A b B qtd
      (vecPermute π.symm
        (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2)) := by
  apply IsLSEMinimizer.of_permuteCols π
  simpa [hAπ, hBπ] using
    (lseElimination_isLSEMinimizer_of_reduced_minimizer
      A1 A2 R1 R1inv R2 qtd b x2 hleft hright hmin)

/-- Feasible points have feasible difference directions. -/
theorem LSEFeasible.direction_zero {p n : ℕ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hx : LSEFeasible B d x) (hy : LSEFeasible B d y) :
    rectMatMulVec B (fun j => y j - x j) = 0 := by
  ext i
  change rectMatMulVec B (fun j => y j - x j) i = 0
  rw [congrFun (rectMatMulVec_sub B y x) i, hy i, hx i]
  ring

/-- Adding a feasible direction, one in the nullspace of `B`, preserves the
    equality constraint. -/
theorem LSEFeasible.add_null_direction {p n : ℕ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x v : Fin n → ℝ}
    (hx : LSEFeasible B d x) (hv : rectMatMulVec B v = 0) (t : ℝ) :
    LSEFeasible B d (fun j => x j + t * v j) := by
  intro i
  have hvi : rectMatMulVec B v i = 0 := by
    simpa using congrFun hv i
  rw [congrFun (rectMatMulVec_add B x (fun j => t * v j)) i]
  rw [hx i, congrFun (rectMatMulVec_smul B t v) i, hvi]
  ring

private theorem lse_linear_term_eq_zero_of_quadratic_nonneg
    {a c : ℝ} (ha : 0 ≤ a)
    (hquad : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * a) :
    c = 0 := by
  by_contra hc
  let t : ℝ := -c / (a + 1)
  have hden_pos : 0 < a + 1 := by linarith
  have hden_ne : a + 1 ≠ 0 := ne_of_gt hden_pos
  have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hcalc :
      2 * t * c + t ^ 2 * a =
        -(c ^ 2 * (a + 2)) / (a + 1) ^ 2 := by
    dsimp [t]
    field_simp [hden_ne]
    ring
  have hnum_pos : 0 < c ^ 2 * (a + 2) := by nlinarith
  have hden_sq_pos : 0 < (a + 1) ^ 2 := sq_pos_of_pos hden_pos
  have hneg : -(c ^ 2 * (a + 2)) / (a + 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hnum_pos) hden_sq_pos
  have ht := hquad t
  rw [hcalc] at ht
  linarith

private noncomputable def lseDotDual {n : ℕ}
    (g : Fin n → ℝ) : Module.Dual ℝ (Fin n → ℝ) where
  toFun v := ∑ j : Fin n, g j * v j
  map_add' := by
    intro x y
    simp_rw [Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    calc
      ∑ j : Fin n, g j * (a * x j) = a * ∑ j : Fin n, g j * x j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (RingHom.id ℝ) a * ∑ j : Fin n, g j * x j := rfl

private theorem lseConstraintLinearMap_basis {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (j : Fin n) :
    lseConstraintLinearMap B (Pi.single j (1 : ℝ) : Fin n → ℝ) =
      fun r : Fin p => B r j := by
  classical
  ext r
  change (∑ k : Fin n, B r k *
      ((Pi.single j (1 : ℝ) : Fin n → ℝ) k)) = B r j
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk]
    ring
  · intro hj
    simp at hj

private theorem lseDotDual_basis {n : ℕ} (g : Fin n → ℝ) (j : Fin n) :
    lseDotDual g (Pi.single j (1 : ℝ) : Fin n → ℝ) = g j := by
  classical
  change (∑ k : Fin n, g k *
      ((Pi.single j (1 : ℝ) : Fin n → ℝ) k)) = g j
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk]
    ring
  · intro hj
    simp at hj

private theorem lseDual_eval_eq_sum {p : ℕ}
    (psi : Module.Dual ℝ (Fin p → ℝ)) (y : Fin p → ℝ) :
    psi y = ∑ r : Fin p, y r *
      psi (Pi.single r (1 : ℝ) : Fin p → ℝ) := by
  classical
  calc
    psi y = psi (∑ r : Fin p, Pi.single r (y r)) := by
      rw [Finset.univ_sum_single]
    _ = ∑ r : Fin p, psi (Pi.single r (y r)) := by
      rw [map_sum]
    _ = ∑ r : Fin p, y r *
        psi (Pi.single r (1 : ℝ) : Fin p → ℝ) := by
      apply Finset.sum_congr rfl
      intro r _
      have hsingle :
          Pi.single r (y r) =
            y r • (Pi.single r (1 : ℝ) : Fin p → ℝ) := by
        ext s
        by_cases hsr : s = r
        · subst s
          simp
        · simp [Pi.single_eq_of_ne hsr]
      rw [hsingle, map_smul]
      rfl

/-- An exact equality-constrained least-squares minimizer has zero objective
    first variation along every feasible direction `v` satisfying `B v = 0`. -/
theorem IsLSEMinimizer.feasible_direction_stationarity {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x v : Fin n → ℝ}
    (hmin : IsLSEMinimizer A b B d x)
    (hv : rectMatMulVec B v = 0) :
    ∑ j : Fin n, v j * (∑ i : Fin m, A i j * lsResidual A b x i) = 0 := by
  let c : ℝ :=
    ∑ j : Fin n, v j * (∑ i : Fin m, A i j * lsResidual A b x i)
  let a : ℝ := vecNorm2Sq (rectMatMulVec A v)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact vecNorm2Sq_nonneg (rectMatMulVec A v)
  have hquad : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * a := by
    intro t
    let tv : Fin n → ℝ := fun j => t * v j
    have hfeas : LSEFeasible B d (fun j => x j + tv j) := by
      dsimp [tv]
      exact LSEFeasible.add_null_direction hmin.1 hv t
    have hobj := hmin.2 (fun j => x j + tv j) hfeas
    have hexp := lsObjective_add_direction_eq A b x tv
    have hcross :
        (∑ j : Fin n, tv j *
          (∑ i : Fin m, A i j * lsResidual A b x i)) = t * c := by
      dsimp [tv, c]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hnorm : vecNorm2Sq (rectMatMulVec A tv) = t ^ 2 * a := by
      dsimp [tv, a]
      rw [rectMatMulVec_smul, vecNorm2Sq_smul]
    rw [hexp, hcross, hnorm] at hobj
    nlinarith
  exact lse_linear_term_eq_zero_of_quadratic_nonneg ha hquad

/-- Higham, 2nd ed., Chapter 20, Section 20.9:
    the second condition in (20.24), `null(A) ∩ null(B) = {0}`, guarantees
    uniqueness of an equality-constrained least-squares minimizer once
    existence is represented. -/
theorem IsLSEMinimizer.eq_of_nullIntersectionTrivial {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hnull : LSENullIntersectionTrivial A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer A b B d y) :
    x = y := by
  let v : Fin n → ℝ := fun j => y j - x j
  have hBv : rectMatMulVec B v = 0 := by
    dsimp [v]
    exact LSEFeasible.direction_zero hx.1 hy.1
  have hstat := hx.feasible_direction_stationarity hBv
  have hy_eq : y = fun j => x j + v j := by
    ext j
    dsimp [v]
    ring
  have hxy : lsObjective A b x ≤ lsObjective A b y := hx.2 y hy.1
  have hyx : lsObjective A b y ≤ lsObjective A b x := hy.2 x hx.1
  have hobj_eq : lsObjective A b y = lsObjective A b x :=
    le_antisymm hyx hxy
  have hexp := lsObjective_add_direction_eq A b x v
  rw [← hy_eq] at hexp
  have hAv_sq : vecNorm2Sq (rectMatMulVec A v) = 0 := by
    have hnonneg : 0 ≤ vecNorm2Sq (rectMatMulVec A v) :=
      vecNorm2Sq_nonneg (rectMatMulVec A v)
    nlinarith [hobj_eq, hexp, hstat]
  have hAv_norm : vecNorm2 (rectMatMulVec A v) = 0 := by
    have hsquare : vecNorm2 (rectMatMulVec A v) ^ 2 = 0 := by
      rw [vecNorm2_sq, hAv_sq]
    exact sq_eq_zero_iff.mp hsquare
  have hAv : rectMatMulVec A v = 0 := by
    ext i
    change rectMatMulVec A v i = 0
    exact (vecNorm2_eq_zero_iff (rectMatMulVec A v)).mp hAv_norm i
  have hvzero : v = 0 := hnull v hAv hBv
  ext j
  have hvj : v j = 0 := by
    simpa using congrFun hvzero j
  dsimp [v] at hvj
  linarith

/-- Higham, 2nd ed., Chapter 20, equation (20.24), uniqueness bridge:
    once an equality-constrained least-squares minimizer exists, uniqueness is
    equivalent to the null-intersection condition `null(A) ∩ null(B) = {0}`.

    The reverse implication is the source uniqueness guarantee.  The forward
    implication records the exact finite-dimensional necessity proof: a common
    null vector can be added to any minimizer without changing feasibility or
    objective value. -/
theorem exists_unique_isLSEMinimizer_iff_nullIntersectionTrivial_of_exists
    {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    (hex : ∃ x : Fin n → ℝ, IsLSEMinimizer A b B d x) :
    (∃! x : Fin n → ℝ, IsLSEMinimizer A b B d x) ↔
      LSENullIntersectionTrivial A B := by
  constructor
  · intro huniq
    rcases huniq with ⟨x, hx, hunique⟩
    intro v hAv hBv
    let y : Fin n → ℝ := fun j => x j + v j
    have hy_feas : LSEFeasible B d y := by
      intro i
      have hvi : rectMatMulVec B v i = 0 := by
        simpa using congrFun hBv i
      dsimp [y]
      rw [congrFun (rectMatMulVec_add B x v) i, hx.1 i, hvi]
      ring
    have hcross :
        (∑ j : Fin n,
          v j * (∑ i : Fin m, A i j * lsResidual A b x i)) = 0 := by
      calc
        (∑ j : Fin n,
          v j * (∑ i : Fin m, A i j * lsResidual A b x i))
            = ∑ j : Fin n, ∑ i : Fin m,
                v j * (A i j * lsResidual A b x i) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
        _ = ∑ i : Fin m, ∑ j : Fin n,
                v j * (A i j * lsResidual A b x i) := by
              rw [Finset.sum_comm]
        _ = ∑ i : Fin m,
                lsResidual A b x i * rectMatMulVec A v i := by
              apply Finset.sum_congr rfl
              intro i _
              unfold rectMatMulVec
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = 0 := by
              apply Finset.sum_eq_zero
              intro i _
              have hAvi : rectMatMulVec A v i = 0 := by
                simpa using congrFun hAv i
              rw [hAvi]
              ring
    have hAv_sq : vecNorm2Sq (rectMatMulVec A v) = 0 := by
      rw [hAv]
      simp [vecNorm2Sq]
    have hobj_y : lsObjective A b y = lsObjective A b x := by
      dsimp [y]
      rw [lsObjective_add_direction_eq A b x v, hcross, hAv_sq]
      ring
    have hy : IsLSEMinimizer A b B d y := by
      refine ⟨hy_feas, ?_⟩
      intro z hz
      rw [hobj_y]
      exact hx.2 z hz
    have hyx : y = x := hunique y hy
    ext j
    change v j = 0
    have hj := congrFun hyx j
    dsimp [y] at hj
    linarith
  · intro hnull
    rcases hex with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact IsLSEMinimizer.eq_of_nullIntersectionTrivial hnull hy hx

/-- Higham, 2nd ed., Chapter 20, equation (20.24), stacked-rank uniqueness
    bridge:
    once an equality-constrained least-squares minimizer exists, uniqueness is
    equivalent to the local full-column-rank condition for `[A^T, B^T]^T`,
    represented here as injectivity of the vertical stack `[A; B]`.

    This is the source full-column-rank wording combined with the exact
    null-intersection uniqueness bridge. -/
theorem exists_unique_isLSEMinimizer_iff_lseStackedFullColumnRank_of_exists
    {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    (hex : ∃ x : Fin n → ℝ, IsLSEMinimizer A b B d x) :
    (∃! x : Fin n → ℝ, IsLSEMinimizer A b B d x) ↔
      LSEStackedFullColumnRank A B :=
  (exists_unique_isLSEMinimizer_iff_nullIntersectionTrivial_of_exists
    (A := A) (b := b) (B := B) (d := d) hex).trans
    (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B)

/-- Higham, 2nd ed., Chapter 20, equation (20.24), direct stacked-rank
    uniqueness consequence:
    the local full-column-rank condition for `[A^T, B^T]^T`, represented by
    injectivity of `[A; B]`, makes any two exact LSE minimizers equal.

    This is the source uniqueness statement at the stacked-matrix surface.  It
    does not prove full-row-rank consistency or GQR factor construction. -/
theorem IsLSEMinimizer.eq_of_lseStackedFullColumnRank
    {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer A b B d y) :
    x = y :=
  IsLSEMinimizer.eq_of_nullIntersectionTrivial
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
    hx hy

/-- Unique-solution form of the limiting weighting theorem after (20.26).
    Under the local uniqueness condition from (20.24), any supplied convergent
    exact weighted-minimizer branch whose weights satisfy `(mu^2)^{-1} -> 0`
    converges to the unique LSE minimizer.  This identifies the limit of an
    already convergent branch; it does not prove that such a branch exists. -/
theorem lseWeightedMinimizer_tendsto_unique_lseMinimizer_of_inv_mu_sq
    {ι : Type*} {l : Filter ι} [l.NeBot] {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (mu : ι → ℝ) (x_mu : ι → Fin n → ℝ) (x y : Fin n → ℝ)
    (hlim : Filter.Tendsto x_mu l (nhds x))
    (hmu : ∀ i, mu i ≠ 0)
    (hmin : ∀ i, IsLeastSquaresMinimizer
      (lseWeightedMatrix (mu i) A B) (lseWeightedRhs (mu i) b d) (x_mu i))
    (hy : IsLSEMinimizer A b B d y)
    (hnull : LSENullIntersectionTrivial A B)
    (hInvSq : Filter.Tendsto (fun i => (mu i ^ 2)⁻¹) l (nhds 0)) :
    Filter.Tendsto x_mu l (nhds y) := by
  have hx : IsLSEMinimizer A b B d x :=
    lseWeightedMinimizer_tendsto_isLSEMinimizer_of_inv_mu_sq
      A b B d mu x_mu x y hlim hmu hmin hy.1 hInvSq
  have hxy : x = y := IsLSEMinimizer.eq_of_nullIntersectionTrivial hnull hx hy
  simpa [hxy] using hlim

/-- Existence-and-uniqueness form of the limiting weighting theorem after
    (20.26).  Under the local consistency and uniqueness assumptions from
    (20.24), a supplied convergent exact weighted-minimizer branch has a unique
    exact LSE limit.  This removes the need to supply an exact constrained
    minimizer separately, but still assumes the branch exists and converges. -/
theorem lseWeightedMinimizer_exists_unique_lseMinimizer_tendsto_of_inv_mu_sq
    {ι : Type*} {l : Filter ι} [l.NeBot] {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (mu : ι → ℝ) (x_mu : ι → Fin n → ℝ) (x : Fin n → ℝ)
    (hlim : Filter.Tendsto x_mu l (nhds x))
    (hB : LSEFullRowRank B)
    (hnull : LSENullIntersectionTrivial A B)
    (hmu : ∀ i, mu i ≠ 0)
    (hmin : ∀ i, IsLeastSquaresMinimizer
      (lseWeightedMatrix (mu i) A B) (lseWeightedRhs (mu i) b d) (x_mu i))
    (hInvSq : Filter.Tendsto (fun i => (mu i ^ 2)⁻¹) l (nhds 0)) :
    ∃! y : Fin n → ℝ,
      IsLSEMinimizer A b B d y ∧ Filter.Tendsto x_mu l (nhds y) := by
  rcases hB.exists_feasible d with ⟨y0, hy0⟩
  have hx : IsLSEMinimizer A b B d x :=
    lseWeightedMinimizer_tendsto_isLSEMinimizer_of_inv_mu_sq
      A b B d mu x_mu x y0 hlim hmu hmin hy0 hInvSq
  refine ⟨x, ⟨hx, hlim⟩, ?_⟩
  intro y hy
  exact IsLSEMinimizer.eq_of_nullIntersectionTrivial hnull hy.1 hx

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, exact supplied-GQR
    uniqueness consequence under the local assumptions (20.24).

    Supplied GQR data and the local full-row-rank/null-intersection
    hypotheses give existence via the triangular-solve wrapper; the
    null-intersection condition then makes the LSE minimizer unique.  This is
    still a supplied-factor consequence, not a construction of the GQR
    factors. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_conditions20_24
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hnull : LSENullIntersectionTrivial A B) :
    ∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases h.exists_lse_minimizer_of_conditions20_24 hB hnull with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact IsLSEMinimizer.eq_of_nullIntersectionTrivial hnull hy hx

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, supplied-GQR uniqueness
    consequence in the source stacked-rank wording.

    Supplied GQR data and local full-row-rank consistency give existence, while
    full column rank of `[A^T, B^T]^T`, represented as injectivity of `[A; B]`,
    gives uniqueness.  This is still supplied-factor exact algebra; it does not
    construct the GQR factors or prove computed GQR stability. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x :=
  h.exists_unique_lse_minimizer_of_conditions20_24 hB
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall exact-MGS route:
    nonzero MGS stages for `Bᵀ`, a supplied associated-row `[0; L]` shape for
    the actual transformed `A Q`, and the source rank assumptions give the
    unique exact equality-constrained least-squares minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_tall_mgs_constraint_and_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0)
    (hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))))
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB hAQ with
    ⟨h⟩
  exact h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall exact-MGS route:
    full row rank of `B` now supplies the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; together with the source stacked-rank assumption and the remaining
    associated-row `[0; L]` construction for `A Q`, this gives the unique exact
    equality-constrained least-squares minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_tall_fullRowRank_constraint_and_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))))
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases
    GeneralizedQRFactorization.exists_of_tall_fullRowRank_constraint_and_assoc_shape
      (A := A) (B := B) hB hAQ with
    ⟨h⟩
  exact h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide exact-MGS route:
    nonzero MGS stages for `Bᵀ` and for the column-reversed trailing block of
    the actual transformed `A Q`, together with the source rank assumptions,
    give the unique exact equality-constrained least-squares minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_wide_mgs_constraint_and_trailing_mgs_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hdiagB : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0)
    (hdiagAQ : ∀ Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ,
      IsOrthogonal ((k + r) + q) Q →
        ∀ j : Fin (r + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (gqrAQWideAssocL
                  (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
              j.val j) ≠ 0)
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃! x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases
    GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_trailing_mgs_assoc_shape
      (A := A) (B := B) hdiagB hdiagAQ with
    ⟨h⟩
  exact h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide exact-MGS route:
    full row rank of `B` now supplies the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; together with the source stacked-rank assumption and the remaining
    trailing-block MGS hypothesis, this gives the unique exact equality-
    constrained least-squares minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_wide_fullRowRank_constraint_and_trailing_mgs_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hdiagAQ : ∀ Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ,
      IsOrthogonal ((k + r) + q) Q →
        ∀ j : Fin (r + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (gqrAQWideAssocL
                  (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
              j.val j) ≠ 0)
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃! x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases
    GeneralizedQRFactorization.exists_of_wide_fullRowRank_constraint_and_trailing_mgs_assoc_shape
      (A := A) (B := B) hB hdiagAQ with
    ⟨h⟩
  exact h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9:
    supplied-GQR uniqueness consequence stated at the kernel nonsingularity
    surface after (20.28).

    If the supplied triangular `S` and `L22` blocks have trivial kernels, then
    the exact GQR method has a unique equality-constrained least-squares
    minimizer.  This remains supplied-factor algebra; it does not construct the
    GQR factors. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_s_l22_kernel_trivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hS_kernel : ∀ y1 : Fin p → ℝ, rectMatMulVec h.S y1 = 0 → y1 = 0)
    (hL22_kernel : ∀ y2 : Fin q → ℝ, rectMatMulVec h.L22 y2 = 0 → y2 = 0) :
    ∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  have hcond : LSEFullRowRank B ∧ LSENullIntersectionTrivial A B :=
    (h.conditions20_24_iff_s_l22_kernel_trivial).2
      ⟨hS_kernel, hL22_kernel⟩
  exact h.exists_unique_lse_minimizer_of_conditions20_24 hcond.1 hcond.2

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9:
    supplied-GQR uniqueness consequence stated at the triangular nonsingularity
    surface after (20.28).

    If the supplied lower-triangular `S` and `L22` blocks have nonzero diagonals,
    then the exact GQR method has a unique equality-constrained least-squares
    minimizer.  This remains supplied-factor algebra; it does not construct the
    GQR factors. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_triangular_nonsingular
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hS_diag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22_diag : ∀ i : Fin q, h.L22 i i ≠ 0) :
    ∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  have hcond : LSEFullRowRank B ∧ LSENullIntersectionTrivial A B :=
    (h.conditions20_24_iff_s_l22_diag_ne_zero).2 ⟨hS_diag, hL22_diag⟩
  exact h.exists_unique_lse_minimizer_of_conditions20_24 hcond.1 hcond.2

/-- Solve-map version of
    `GeneralizedQRFactorization.exists_unique_lse_minimizer_of_triangular_nonsingular`:
    bijectivity of the supplied triangular solve maps for `S` and `L22` implies a
    unique exact LSE minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_s_l22_bijective
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hS_bij : Function.Bijective (rectMatMulVec h.S))
    (hL22_bij : Function.Bijective (rectMatMulVec h.L22)) :
    ∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  have hdiag :
      (∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) :=
    ⟨(h.s_bijective_iff_diag_ne_zero).1 hS_bij,
      (h.l22_bijective_iff_diag_ne_zero).1 hL22_bij⟩
  exact h.exists_unique_lse_minimizer_of_triangular_nonsingular
    hdiag.1 hdiag.2

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall associated (20.28)
    supplied-shape nonsingularity equivalence:
    under a supplied exact QR identity for `Bᵀ` and a supplied associated-row
    shape `Uᵀ A Q = [0; L]`, the local assumptions (20.24) are equivalent to
    nonzero diagonals of the displayed QR block `R` and the trailing `L22`
    block extracted from `L`.

    This is the source proof sentence after (20.28) at the displayed-block
    surface. It still assumes the QR identity and associated shape record; it
    does not construct the QR/GQR factors or prove computed GQR stability. -/
theorem GeneralizedQRFactorization.tall_qr_assoc_case_conditions20_24_iff_diag_ne_zero
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hCase : GQRAQTallAssocCase k p q
      (matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q))) :
    (LSEFullRowRank B ∧ LSENullIntersectionTrivial A B) ↔
      (∀ i : Fin p, R i i ≠ 0) ∧
        (∀ i : Fin q, hCase.L (Fin.natAdd p i) (Fin.natAdd p i) ≠ 0) := by
  rcases GeneralizedQRFactorization.exists_of_tall_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, _hQ, _hU, hS, hL22⟩
  constructor
  · intro hcond
    have hdiag :
        (∀ i : Fin p, h.S i i ≠ 0) ∧
          (∀ i : Fin q, h.L22 i i ≠ 0) :=
      (h.conditions20_24_iff_s_l22_diag_ne_zero).1 hcond
    constructor
    · intro i
      have hi := hdiag.1 i
      rw [hS] at hi
      simpa [matTranspose] using hi
    · intro i
      have hi := hdiag.2 i
      rw [hL22] at hi
      simpa [gqrAQTallL22FromEq20_28] using hi
  · rintro ⟨hRdiag, hLdiag⟩
    refine (h.conditions20_24_iff_s_l22_diag_ne_zero).2 ⟨?_, ?_⟩
    · intro i
      rw [hS]
      simpa [matTranspose] using hRdiag i
    · intro i
      rw [hL22]
      simpa [gqrAQTallL22FromEq20_28] using hLdiag i

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide associated (20.28)
    supplied-shape nonsingularity equivalence:
    under a supplied exact QR identity for `Bᵀ` and a supplied
    associated-column shape `Uᵀ A Q = [X L]`, the local assumptions (20.24)
    are equivalent to nonzero diagonals of the displayed QR block `R` and the
    trailing `L22` block extracted from `L`.

    This is the wide counterpart of
    `GeneralizedQRFactorization.tall_qr_assoc_case_conditions20_24_iff_diag_ne_zero`.
    It remains supplied-factor algebra and does not construct the QR/GQR
    factors or prove computed GQR stability. -/
theorem GeneralizedQRFactorization.wide_qr_assoc_case_conditions20_24_iff_diag_ne_zero
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hCase : GQRAQWideAssocCase k r q
      (matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q))) :
    (LSEFullRowRank B ∧ LSENullIntersectionTrivial A B) ↔
      (∀ i : Fin (k + r), R i i ≠ 0) ∧
        (∀ i : Fin q, hCase.L (Fin.natAdd r i) (Fin.natAdd r i) ≠ 0) := by
  rcases GeneralizedQRFactorization.exists_of_wide_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, _hQ, _hU, hS, hL22⟩
  constructor
  · intro hcond
    have hdiag :
        (∀ i : Fin (k + r), h.S i i ≠ 0) ∧
          (∀ i : Fin q, h.L22 i i ≠ 0) :=
      (h.conditions20_24_iff_s_l22_diag_ne_zero).1 hcond
    constructor
    · intro i
      have hi := hdiag.1 i
      rw [hS] at hi
      simpa [matTranspose] using hi
    · intro i
      have hi := hdiag.2 i
      rw [hL22] at hi
      simpa [gqrAQWideL22FromEq20_28] using hi
  · rintro ⟨hRdiag, hLdiag⟩
    refine (h.conditions20_24_iff_s_l22_diag_ne_zero).2 ⟨?_, ?_⟩
    · intro i
      rw [hS]
      simpa [matTranspose] using hRdiag i
    · intro i
      rw [hL22]
      simpa [gqrAQWideL22FromEq20_28] using hLdiag i

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall associated (20.28)
    supplied-shape source-rank nonsingularity equivalence:
    under supplied exact QR and associated-row shape data, full row rank of
    `B` together with full column rank of the local vertical stack `[A; B]` is
    equivalent to nonzero diagonals of the displayed QR block `R` and the
    trailing `L22` block extracted from `L`.

    This is the stacked-rank version of
    `GeneralizedQRFactorization.tall_qr_assoc_case_conditions20_24_iff_diag_ne_zero`.
    It remains supplied-factor algebra and does not construct QR/GQR factors or
    prove computed GQR stability. -/
theorem GeneralizedQRFactorization.tall_qr_assoc_case_fullRowRank_stackedFullColumnRank_iff_diag_ne_zero
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hCase : GQRAQTallAssocCase k p q
      (matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q))) :
    (LSEFullRowRank B ∧ LSEStackedFullColumnRank A B) ↔
      (∀ i : Fin p, R i i ≠ 0) ∧
        (∀ i : Fin q, hCase.L (Fin.natAdd p i) (Fin.natAdd p i) ≠ 0) := by
  constructor
  · rintro ⟨hB, hstack⟩
    exact (GeneralizedQRFactorization.tall_qr_assoc_case_conditions20_24_iff_diag_ne_zero
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase).1
      ⟨hB, (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack⟩
  · intro hdiag
    have hcond :=
      (GeneralizedQRFactorization.tall_qr_assoc_case_conditions20_24_iff_diag_ne_zero
        (A := A) (B := B) Q U R hQ hU hqrB hR hCase).2 hdiag
    exact ⟨hcond.1,
      (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).1 hcond.2⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide associated (20.28)
    supplied-shape source-rank nonsingularity equivalence:
    under supplied exact QR and associated-column shape data, full row rank of
    `B` together with full column rank of the local vertical stack `[A; B]` is
    equivalent to nonzero diagonals of the displayed QR block `R` and the
    trailing `L22` block extracted from `L`.

    This is the stacked-rank version of
    `GeneralizedQRFactorization.wide_qr_assoc_case_conditions20_24_iff_diag_ne_zero`.
    It remains supplied-factor algebra and does not construct QR/GQR factors or
    prove computed GQR stability. -/
theorem GeneralizedQRFactorization.wide_qr_assoc_case_fullRowRank_stackedFullColumnRank_iff_diag_ne_zero
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hCase : GQRAQWideAssocCase k r q
      (matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q))) :
    (LSEFullRowRank B ∧ LSEStackedFullColumnRank A B) ↔
      (∀ i : Fin (k + r), R i i ≠ 0) ∧
        (∀ i : Fin q, hCase.L (Fin.natAdd r i) (Fin.natAdd r i) ≠ 0) := by
  constructor
  · rintro ⟨hB, hstack⟩
    exact (GeneralizedQRFactorization.wide_qr_assoc_case_conditions20_24_iff_diag_ne_zero
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase).1
      ⟨hB, (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack⟩
  · intro hdiag
    have hcond :=
      (GeneralizedQRFactorization.wide_qr_assoc_case_conditions20_24_iff_diag_ne_zero
        (A := A) (B := B) Q U R hQ hU hqrB hR hCase).2 hdiag
    exact ⟨hcond.1,
      (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).1 hcond.2⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall supplied-shape
    nonsingular-block case:
    a supplied exact QR identity for `Bᵀ`, a supplied associated-row
    (20.28) shape `Uᵀ A Q = [0; L]`, and nonzero diagonals of the QR block
    `R` and the trailing `L22` block imply a unique exact equality-constrained
    least-squares minimizer.

    This composes the supplied-shape GQR construction with the supplied-GQR
    triangular nonsingularity theorem. It still does not construct the QR/GQR
    factors or prove floating-point GQR stability. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_tall_qr_assoc_case_diag_ne_zero
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hRdiag : ∀ i : Fin p, R i i ≠ 0)
    (hCase : GQRAQTallAssocCase k p q
      (matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q)))
    (hLdiag : ∀ i : Fin q,
      hCase.L (Fin.natAdd p i) (Fin.natAdd p i) ≠ 0)
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ} :
    ∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases GeneralizedQRFactorization.exists_of_tall_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, _hQ, _hU, hS, hL22⟩
  exact h.exists_unique_lse_minimizer_of_triangular_nonsingular
    (by
      intro i
      rw [hS]
      simpa [matTranspose] using hRdiag i)
    (by
      intro i
      rw [hL22]
      simpa [gqrAQTallL22FromEq20_28] using hLdiag i)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide supplied-shape
    nonsingular-block case:
    a supplied exact QR identity for `Bᵀ`, a supplied associated-column
    (20.28) shape `Uᵀ A Q = [X L]`, and nonzero diagonals of the QR block
    `R` and the trailing `L22` block imply a unique exact equality-constrained
    least-squares minimizer.

    This composes the supplied-shape GQR construction with the supplied-GQR
    triangular nonsingularity theorem. It still does not construct the QR/GQR
    factors or prove floating-point GQR stability. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_wide_qr_assoc_case_diag_ne_zero
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hRdiag : ∀ i : Fin (k + r), R i i ≠ 0)
    (hCase : GQRAQWideAssocCase k r q
      (matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
    (hLdiag : ∀ i : Fin q,
      hCase.L (Fin.natAdd r i) (Fin.natAdd r i) ≠ 0)
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ} :
    ∃! x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases GeneralizedQRFactorization.exists_of_wide_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, _hQ, _hU, hS, hL22⟩
  exact h.exists_unique_lse_minimizer_of_triangular_nonsingular
    (by
      intro i
      rw [hS]
      simpa [matTranspose] using hRdiag i)
    (by
      intro i
      rw [hL22]
      simpa [gqrAQWideL22FromEq20_28] using hLdiag i)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall supplied-shape case:
    a supplied exact QR identity for `Bᵀ`, a supplied associated-row
    (20.28) shape `Uᵀ A Q = [0; L]`, and the local assumptions (20.24)
    imply existence and uniqueness of the exact equality-constrained
    least-squares minimizer.

    This composes the supplied-shape GQR construction with the supplied-GQR
    uniqueness theorem. It still does not construct the QR/GQR factors or prove
    floating-point GQR stability. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_tall_qr_assoc_case_conditions20_24
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hCase : GQRAQTallAssocCase k p q
      (matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q)))
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hnull : LSENullIntersectionTrivial A B) :
    ∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases GeneralizedQRFactorization.exists_of_tall_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, _hQ, _hU, _hS, _hL22⟩
  exact h.exists_unique_lse_minimizer_of_conditions20_24 hB hnull

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide supplied-shape case:
    a supplied exact QR identity for `Bᵀ`, a supplied associated-column
    (20.28) shape `Uᵀ A Q = [X L]`, and the local assumptions (20.24)
    imply existence and uniqueness of the exact equality-constrained
    least-squares minimizer.

    This composes the supplied-shape GQR construction with the supplied-GQR
    uniqueness theorem. It still does not construct the QR/GQR factors or prove
    floating-point GQR stability. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_wide_qr_assoc_case_conditions20_24
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hCase : GQRAQWideAssocCase k r q
      (matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hnull : LSENullIntersectionTrivial A B) :
    ∃! x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases GeneralizedQRFactorization.exists_of_wide_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, _hQ, _hU, _hS, _hL22⟩
  exact h.exists_unique_lse_minimizer_of_conditions20_24 hB hnull

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall supplied-shape
    source-rank case:
    a supplied exact QR identity for `Bᵀ`, a supplied associated-row
    (20.28) shape `Uᵀ A Q = [0; L]`, full row rank of `B`, and full column
    rank of the local vertical stack `[A; B]` imply existence and uniqueness
    of the exact equality-constrained least-squares minimizer.

    This is the stacked-rank version of
    `exists_unique_lse_minimizer_of_tall_qr_assoc_case_conditions20_24`.
    It still does not construct the QR/GQR factors or prove floating-point GQR
    stability. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_tall_qr_assoc_case_fullRowRank_stackedFullColumnRank
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hCase : GQRAQTallAssocCase k p q
      (matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q)))
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x :=
  GeneralizedQRFactorization.exists_unique_lse_minimizer_of_tall_qr_assoc_case_conditions20_24
    (A := A) (B := B) Q U R hQ hU hqrB hR hCase hB
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide supplied-shape
    source-rank case:
    a supplied exact QR identity for `Bᵀ`, a supplied associated-column
    (20.28) shape `Uᵀ A Q = [X L]`, full row rank of `B`, and full column
    rank of the local vertical stack `[A; B]` imply existence and uniqueness
    of the exact equality-constrained least-squares minimizer.

    This is the stacked-rank version of
    `exists_unique_lse_minimizer_of_wide_qr_assoc_case_conditions20_24`.
    It still does not construct the QR/GQR factors or prove floating-point GQR
    stability. -/
theorem GeneralizedQRFactorization.exists_unique_lse_minimizer_of_wide_qr_assoc_case_fullRowRank_stackedFullColumnRank
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hCase : GQRAQWideAssocCase k r q
      (matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃! x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x :=
  GeneralizedQRFactorization.exists_unique_lse_minimizer_of_wide_qr_assoc_case_conditions20_24
    (A := A) (B := B) Q U R hQ hU hqrB hR hCase hB
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall associated (20.28)
    supplied-shape method in the source rank wording:
    supplied exact QR and associated-row shape data, full row rank of `B`, and
    full column rank of `[A; B]` yield supplied GQR data together with exact
    triangular solve variables and an LSE minimizer.

    This exposes the constructive solve surface while still assuming the QR and
    associated shape records are supplied. It does not construct `Q`, construct
    `U`, prove the shape records from actual factors, or prove computed GQR
    stability. -/
theorem GeneralizedQRFactorization.exists_isLSEMinimizer_of_tall_qr_assoc_case_fullRowRank_stackedFullColumnRank
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hCase : GQRAQTallAssocCase k p q
      (matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q)))
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQTallL22FromEq20_28 hCase.L ∧
      ∃ y1 : Fin p → ℝ, ∃ y2 : Fin q → ℝ,
        rectMatMulVec h.S y1 = d ∧
        rectMatMulVec h.L22 y2 =
          (fun i : Fin q =>
            matMulVec ((k + p) + q) (matTranspose h.U) b (Fin.natAdd (k + p) i) -
              rectMatMulVec h.L21 y1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  rcases GeneralizedQRFactorization.exists_of_tall_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, hQeq, hUeq, hSeq, hL22eq⟩
  refine ⟨h, hQeq, hUeq, hSeq, hL22eq, ?_⟩
  exact h.exists_isLSEMinimizer_of_fullRowRank_stackedFullColumnRank hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide associated (20.28)
    supplied-shape method in the source rank wording:
    supplied exact QR and associated-column shape data, full row rank of `B`,
    and full column rank of `[A; B]` yield supplied GQR data together with
    exact triangular solve variables and an LSE minimizer.

    This exposes the constructive solve surface while still assuming the QR and
    associated shape records are supplied. It does not construct `Q`, construct
    `U`, prove the shape records from actual factors, or prove computed GQR
    stability. -/
theorem GeneralizedQRFactorization.exists_isLSEMinimizer_of_wide_qr_assoc_case_fullRowRank_stackedFullColumnRank
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hCase : GQRAQWideAssocCase k r q
      (matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQWideL22FromEq20_28 hCase.L ∧
      ∃ y1 : Fin (k + r) → ℝ, ∃ y2 : Fin q → ℝ,
        rectMatMulVec h.S y1 = d ∧
        rectMatMulVec h.L22 y2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 y1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec ((k + r) + q) h.Q (Fin.append y1 y2)) := by
  rcases GeneralizedQRFactorization.exists_of_wide_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, hQeq, hUeq, hSeq, hL22eq⟩
  refine ⟨h, hQeq, hUeq, hSeq, hL22eq, ?_⟩
  exact h.exists_isLSEMinimizer_of_fullRowRank_stackedFullColumnRank hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall associated (20.28)
    supplied-shape method:
    under the source rank assumptions, the exact triangular GQR solve
    coordinates are unique at the supplied associated-shape surface.

    This packages the supplied associated tall case into GQR data and then uses
    the supplied-GQR coordinate-uniqueness theorem. It does not construct the
    factors or prove the associated shape record from actual QR factors. -/
theorem GeneralizedQRFactorization.exists_unique_solve_coordinates_of_tall_qr_assoc_case_fullRowRank_stackedFullColumnRank
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hCase : GQRAQTallAssocCase k p q
      (matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q)))
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQTallL22FromEq20_28 hCase.L ∧
      ∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec ((k + p) + q) (matTranspose h.U) b (Fin.natAdd (k + p) i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2)) := by
  rcases GeneralizedQRFactorization.exists_of_tall_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, hQeq, hUeq, hSeq, hL22eq⟩
  refine ⟨h, hQeq, hUeq, hSeq, hL22eq, ?_⟩
  exact h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide associated (20.28)
    supplied-shape method:
    under the source rank assumptions, the exact triangular GQR solve
    coordinates are unique at the supplied associated-shape surface.

    This packages the supplied associated wide case into GQR data and then uses
    the supplied-GQR coordinate-uniqueness theorem. It does not construct the
    factors or prove the associated shape record from actual QR factors. -/
theorem GeneralizedQRFactorization.exists_unique_solve_coordinates_of_wide_qr_assoc_case_fullRowRank_stackedFullColumnRank
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hCase : GQRAQWideAssocCase k r q
      (matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQWideL22FromEq20_28 hCase.L ∧
      ∃! yz : (Fin (k + r) → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec ((k + r) + q) h.Q (Fin.append yz.1 yz.2)) := by
  rcases GeneralizedQRFactorization.exists_of_wide_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, hQeq, hUeq, hSeq, hL22eq⟩
  refine ⟨h, hQeq, hUeq, hSeq, hL22eq, ?_⟩
  exact h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack

/-- Existence-only corollary of the tall associated supplied-shape source-rank
    Theorem 20.9 wrapper. -/
theorem GeneralizedQRFactorization.exists_lse_minimizer_of_tall_qr_assoc_case_fullRowRank_stackedFullColumnRank
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hCase : GQRAQTallAssocCase k p q
      (matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q)))
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases GeneralizedQRFactorization.exists_unique_lse_minimizer_of_tall_qr_assoc_case_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase hB hstack with
    ⟨x, hx, _huniq⟩
  exact ⟨x, hx⟩

/-- Existence-only corollary of the wide associated supplied-shape source-rank
    Theorem 20.9 wrapper. -/
theorem GeneralizedQRFactorization.exists_lse_minimizer_of_wide_qr_assoc_case_fullRowRank_stackedFullColumnRank
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hCase : GQRAQWideAssocCase k r q
      (matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases GeneralizedQRFactorization.exists_unique_lse_minimizer_of_wide_qr_assoc_case_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase hB hstack with
    ⟨x, hx, _huniq⟩
  exact ⟨x, hx⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall associated (20.28)
    supplied-shape exact method package:
    supplied exact `Bᵀ` QR data, supplied associated-row shape data for
    `Uᵀ A Q = [0; L]`, full row rank of `B`, and full column rank of `[A; B]`
    yield supplied GQR data, unique exact triangular solve coordinates, and a
    unique exact equality-constrained least-squares minimizer.

    This combines the supplied-shape construction, coordinate uniqueness, and
    minimizer uniqueness surfaces. It still does not construct `Q`, construct
    `U`, prove the associated shape record from actual QR factors, or prove
    computed GQR stability. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_tall_qr_assoc_case_fullRowRank_stackedFullColumnRank
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hCase : GQRAQTallAssocCase k p q
      (matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q)))
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQTallL22FromEq20_28 hCase.L ∧
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec ((k + p) + q) (matTranspose h.U) b (Fin.natAdd (k + p) i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases GeneralizedQRFactorization.exists_of_tall_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, hQeq, hUeq, hSeq, hL22eq⟩
  refine ⟨h, hQeq, hUeq, hSeq, hL22eq, ?_, ?_⟩
  · exact h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack
  · exact h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide associated (20.28)
    supplied-shape exact method package:
    supplied exact `Bᵀ` QR data, supplied associated-column shape data for
    `Uᵀ A Q = [X L]`, full row rank of `B`, and full column rank of `[A; B]`
    yield supplied GQR data, unique exact triangular solve coordinates, and a
    unique exact equality-constrained least-squares minimizer.

    This combines the supplied-shape construction, coordinate uniqueness, and
    minimizer uniqueness surfaces. It still does not construct `Q`, construct
    `U`, prove the associated shape record from actual QR factors, or prove
    computed GQR stability. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_wide_qr_assoc_case_fullRowRank_stackedFullColumnRank
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hCase : GQRAQWideAssocCase k r q
      (matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQWideL22FromEq20_28 hCase.L ∧
      (∃! yz : (Fin (k + r) → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec ((k + r) + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases GeneralizedQRFactorization.exists_of_wide_qr_assoc_case
      (A := A) (B := B) Q U R hQ hU hqrB hR hCase with
    ⟨h, hQeq, hUeq, hSeq, hL22eq⟩
  refine ⟨h, hQeq, hUeq, hSeq, hL22eq, ?_, ?_⟩
  · exact h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack
  · exact h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall exact-MGS method package:
    the exact-MGS constraint construction for `Bᵀ`, a supplied associated-row
    `[0; L]` shape for the actual `A Q`, and the source rank assumptions yield
    GQR data, unique exact triangular solve coordinates, and the unique exact
    equality-constrained least-squares minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_tall_mgs_constraint_and_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0)
    (hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))))
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec ((k + p) + q) (matTranspose h.U) b (Fin.natAdd (k + p) i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB hAQ with
    ⟨h⟩
  exact ⟨h,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall exact-MGS method package:
    full row rank of `B` discharges the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; the remaining associated-row `[0; L]` construction for the actual
    transformed `A Q` then yields GQR data, unique exact triangular solve
    coordinates, and the unique exact equality-constrained least-squares
    minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_tall_fullRowRank_constraint_and_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))))
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec ((k + p) + q) (matTranspose h.U) b (Fin.natAdd (k + p) i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_tall_fullRowRank_constraint_and_assoc_shape
      (A := A) (B := B) hB hAQ with
    ⟨h⟩
  exact ⟨h,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall full-associated exact-MGS
    method package.

    Exact MGS data for `Bᵀ` and for the column-reversed full transformed block
    `A Q` construct the associated-row (20.28) display and then yield GQR data,
    unique exact triangular solve coordinates, and the unique exact
    equality-constrained least-squares minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_tall_mgs_constraint_and_full_mgs_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0)
    (hdiagAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∀ j : Fin (p + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))
              j.val j) ≠ 0)
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec ((k + p) + q) (matTranspose h.U) b (Fin.natAdd (k + p) i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_full_mgs_assoc_shape
      (A := A) (B := B) hdiagB hdiagAQ with
    ⟨h⟩
  exact ⟨h,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall full-row-rank
    full-associated exact-MGS method package.

    Full row rank of `B` discharges the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; nonbreakdown for the column-reversed full transformed block `A Q`
    constructs the associated-row (20.28) display and then yields the same
    unique exact method package. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_tall_fullRowRank_constraint_and_full_mgs_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hdiagAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∀ j : Fin (p + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))
              j.val j) ≠ 0)
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec ((k + p) + q) (matTranspose h.U) b (Fin.natAdd (k + p) i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_tall_fullRowRank_constraint_and_full_mgs_assoc_shape
      (A := A) (B := B) hB hdiagAQ with
    ⟨h⟩
  exact ⟨h,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall exact-Householder method
    package.

    Exact MGS data for `Bᵀ` supplies the constraint block.  Exact Householder
    QR supplies the associated-row full `AQ` display without requiring
    exact-MGS nonbreakdown for the transformed `AQ` block. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_tall_mgs_constraint_and_exact_householder_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0)
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec ((k + p) + q) (matTranspose h.U) b (Fin.natAdd (k + p) i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_exact_householder_assoc_shape
      (A := A) (B := B) hdiagB with
    ⟨h⟩
  exact ⟨h,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall full-row-rank plus
    exact-Householder method package.

    Full row rank of `B` discharges the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; exact Householder QR supplies the associated-row full `AQ` display
    without a nonbreakdown assumption on `AQ`. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_tall_fullRowRank_constraint_and_exact_householder_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec ((k + p) + q) (matTranspose h.U) b (Fin.natAdd (k + p) i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_tall_fullRowRank_constraint_and_exact_householder_assoc_shape
      (A := A) (B := B) hB with
    ⟨h⟩
  exact ⟨h,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide exact-MGS method package:
    the exact-MGS constraint construction for `Bᵀ`, the exact-MGS trailing-block
    associated-shape construction for the actual `A Q`, and the source rank
    assumptions yield GQR data, unique exact triangular solve coordinates, and
    the unique exact equality-constrained least-squares minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_wide_mgs_constraint_and_trailing_mgs_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hdiagB : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0)
    (hdiagAQ : ∀ Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ,
      IsOrthogonal ((k + r) + q) Q →
        ∀ j : Fin (r + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (gqrAQWideAssocL
                  (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
              j.val j) ≠ 0)
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      (∃! yz : (Fin (k + r) → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec ((k + r) + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_trailing_mgs_assoc_shape
      (A := A) (B := B) hdiagB hdiagAQ with
    ⟨h⟩
  exact ⟨h,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide exact-MGS method package:
    full row rank of `B` discharges the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; the remaining trailing-block MGS hypothesis for the actual
    transformed `A Q` then yields GQR data, unique exact triangular solve
    coordinates, and the unique exact equality-constrained least-squares
    minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_wide_fullRowRank_constraint_and_trailing_mgs_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hdiagAQ : ∀ Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ,
      IsOrthogonal ((k + r) + q) Q →
        ∀ j : Fin (r + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (gqrAQWideAssocL
                  (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
              j.val j) ≠ 0)
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      (∃! yz : (Fin (k + r) → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec ((k + r) + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_wide_fullRowRank_constraint_and_trailing_mgs_assoc_shape
      (A := A) (B := B) hB hdiagAQ with
    ⟨h⟩
  exact ⟨h,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide exact-Householder method
    package.

    Exact MGS data for `B^T` supplies the constraint block. Exact Householder
    QR supplies the associated-column full `AQ` display without requiring
    exact-MGS nonbreakdown for the trailing square block. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_wide_mgs_constraint_and_exact_householder_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hdiagB : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0)
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      (∃! yz : (Fin (k + r) → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec ((k + r) + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_exact_householder_assoc_shape
      (A := A) (B := B) hdiagB with
    ⟨h⟩
  exact ⟨h,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide full-row-rank plus
    exact-Householder method package.

    Full row rank of `B` discharges the exact-MGS nonbreakdown hypotheses for
    `B^T`; exact Householder QR supplies the associated-column full `AQ`
    display without a nonbreakdown assumption on the trailing square block. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_wide_fullRowRank_constraint_and_exact_householder_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      (∃! yz : (Fin (k + r) → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec ((k + r) + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_wide_fullRowRank_constraint_and_exact_householder_assoc_shape
      (A := A) (B := B) hB with
    ⟨h⟩
  exact ⟨h,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, tall exact-Householder method
    package with the source nonsingularity consequence.

    This attaches the post-(20.28) rank/nonsingularity equivalence to the
    constructed exact-Householder associated-row route: under source full row
    rank of `B` and full column rank of `[A; B]`, the returned exact GQR data
    has nonzero diagonals in the triangular `S` and `L22` blocks and gives the
    unique exact triangular solve coordinates and LSE minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_with_s_l22_diag_ne_zero_of_tall_fullRowRank_constraint_and_exact_householder_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {b : Fin ((k + p) + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      (∀ i : Fin p, h.S i i ≠ 0) ∧
      (∀ i : Fin q, h.L22 i i ≠ 0) ∧
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec ((k + p) + q) (matTranspose h.U) b (Fin.natAdd (k + p) i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_tall_fullRowRank_constraint_and_exact_householder_assoc_shape
      (A := A) (B := B) hB with
    ⟨h⟩
  have hdiag :
      (∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) :=
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1
      ⟨hB, hstack⟩
  exact ⟨h, hdiag.1, hdiag.2,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, wide exact-Householder method
    package with the source nonsingularity consequence.

    This is the associated-column analogue of
    `exists_unique_method_solution_with_s_l22_diag_ne_zero_of_tall_fullRowRank_constraint_and_exact_householder_assoc_shape`.
    Exact Householder QR constructs the wide (20.28) shape, and the source rank
    assumptions give nonzero diagonals in the triangular `S` and `L22` blocks
    together with the unique exact GQR method solution. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_with_s_l22_diag_ne_zero_of_wide_fullRowRank_constraint_and_exact_householder_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    {b : Fin (r + q) → ℝ} {d : Fin (k + r) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      (∀ i : Fin (k + r), h.S i i ≠ 0) ∧
      (∀ i : Fin q, h.L22 i i ≠ 0) ∧
      (∃! yz : (Fin (k + r) → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec ((k + r) + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin ((k + r) + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_wide_fullRowRank_constraint_and_exact_householder_assoc_shape
      (A := A) (B := B) hB with
    ⟨h⟩
  have hdiag :
      (∀ i : Fin (k + r), h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) :=
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1
      ⟨hB, hstack⟩
  exact ⟨h, hdiag.1, hdiag.2,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, constructed exact GQR method
    package for the block form (20.27).

    Unlike the earlier tall/wide method wrappers, this theorem no longer asks
    for supplied GQR factors or supplied associated-shape records: source full
    row rank of `B` and full column rank of `[A; B]` construct exact GQR data,
    unique triangular solve coordinates, and the unique exact
    equality-constrained least-squares minimizer.  The associated (20.28)
    display and finite-precision computed GQR stability remain separate rows. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r p q A B,
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨h⟩
  exact ⟨h,
    h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank hB hstack,
    h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank hB hstack⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, constructed exact GQR method
    package with the associated trailing display used in (20.28).

    This strengthens
    `GeneralizedQRFactorization.exists_unique_method_solution_of_fullRowRank_stackedFullColumnRank`
    by returning, for the same constructed GQR data, the tall associated shape
    for `Uᵀ(AQ₂)` that the construction used internally.  Thus the exact method
    package no longer hides the associated-display witness behind the existence
    theorem. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_with_A_Q2_tall_assoc_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r p q A B,
      Nonempty (GQRAQTallCase r q
        (matMulRectLeft (matTranspose h.U) (gqrAQ2Block A h.Q))) ∧
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    exists_gqr_constraint_block_and_A_Q2_tall_assoc_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨Q, S, U, hQ, hS, hBQ, hU, hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  rcases GeneralizedQRFactorization.exists_of_constraint_and_A_Q2_tall_case
      (A := A) (B := B) Q S U hQ hS hBQ hU hCase with
    ⟨h, hQeq, hUeq, _hSeq, _hL22eq⟩
  refine ⟨h, ?_, ?_, ?_⟩
  · simpa [hQeq, hUeq] using
      (show Nonempty (GQRAQTallCase r q
        (matMulRectLeft (matTranspose U) (gqrAQ2Block A Q))) from ⟨hCase⟩)
  · exact h.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank
      hB hstack
  · exact h.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank
      hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, constructed exact GQR method
    package with the trailing `A Q₂` display and the source nonsingularity
    consequence for the same constructed factors.

    Under source full row rank of `B` and full column rank of `[A; B]`, the
    returned GQR data simultaneously carries the associated smaller-block
    display used in the construction, nonzero diagonals for the displayed
    triangular blocks `S` and `L22`, unique triangular solve coordinates, and
    the unique exact equality-constrained least-squares minimizer. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_with_A_Q2_tall_assoc_s_l22_diag_ne_zero_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r p q A B,
      Nonempty (GQRAQTallCase r q
        (matMulRectLeft (matTranspose h.U) (gqrAQ2Block A h.Q))) ∧
      ((∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0)) ∧
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_unique_method_solution_with_A_Q2_tall_assoc_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) (b := b) (d := d) hB hstack with
    ⟨h, hCase, hyz, hx⟩
  exact ⟨h, hCase,
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1
      ⟨hB, hstack⟩,
    hyz, hx⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, constructed exact GQR method
    package with the trailing `A Q₂` display and bijective triangular solve
    maps for the same constructed factors.

    This is the solve-map version of
    `exists_unique_method_solution_with_A_Q2_tall_assoc_s_l22_diag_ne_zero_of_fullRowRank_stackedFullColumnRank`. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_with_A_Q2_tall_assoc_s_l22_bijective_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ h : GeneralizedQRFactorization r p q A B,
      Nonempty (GQRAQTallCase r q
        (matMulRectLeft (matTranspose h.U) (gqrAQ2Block A h.Q))) ∧
      Function.Bijective (rectMatMulVec h.S) ∧
      Function.Bijective (rectMatMulVec h.L22) ∧
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer A b B d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x) := by
  rcases
    GeneralizedQRFactorization.exists_unique_method_solution_with_A_Q2_tall_assoc_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) (b := b) (d := d) hB hstack with
    ⟨h, hCase, hyz, hx⟩
  have hbij :
      Function.Bijective (rectMatMulVec h.S) ∧
        Function.Bijective (rectMatMulVec h.L22) :=
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_bijective).1
      ⟨hB, hstack⟩
  exact ⟨h, hCase, hbij.1, hbij.2, hyz, hx⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 exact solvability consequence
    with no supplied GQR factor input.

    The source rank assumptions construct the exact GQR method data and hence
    give existence and uniqueness of the equality-constrained least-squares
    minimizer. -/
theorem exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃! x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases
    GeneralizedQRFactorization.exists_unique_method_solution_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) (b := b) (d := d) hB hstack with
    ⟨_h, _hyz, hx⟩
  exact hx

/-- Existence-only corollary of
    `exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank`. -/
theorem exists_lse_minimizer_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ x : Fin (p + q) → ℝ, IsLSEMinimizer A b B d x := by
  rcases exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) (b := b) (d := d) hB hstack with
    ⟨x, hx, _huniq⟩
  exact ⟨x, hx⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, exact perturbed-data
    GQR core for the same-constraint-right-hand-side branch.

    The finite-precision theorem says the computed GQR method produces
    perturbations `DeltaA`, `DeltaB`, `Deltab` for which the computed vector is
    the exact solution of the perturbed LSE problem with the original `d`.
    This theorem isolates the exact algebra behind that sentence: once such
    perturbed data satisfy the source rank conditions, exact GQR constructs the
    method factors, unique triangular coordinates, and unique minimizer for the
    perturbed problem.  It does not prove the floating-point algorithm supplies
    these perturbations or the norm bounds. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_same_d
    {r p q : ℕ}
    (A DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (B DeltaB : Fin p → Fin (p + q) → ℝ)
    (b Deltab : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hB :
      LSEFullRowRank (fun i j => B i j + DeltaB i j))
    (hstack :
      LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j)) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + Deltab i
    ∃ h : GeneralizedQRFactorization r p q Apert Bpert,
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer Apert bpert Bpert d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer Apert bpert Bpert d x) := by
  dsimp
  exact
    GeneralizedQRFactorization.exists_unique_method_solution_of_fullRowRank_stackedFullColumnRank
      (A := fun i j => A i j + DeltaA i j)
      (B := fun i j => B i j + DeltaB i j)
      (b := fun i => b i + Deltab i) (d := d) hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, exact perturbed-data
    GQR core for the perturbed-constraint-right-hand-side branch.

    This is the exact algebraic counterpart of the second formulation in
    Theorem 20.10, where the computed vector solves a perturbed LSE problem
    with `d + Deltad`.  The theorem reuses the constructed exact GQR method
    package for the perturbed `A` and `B`; the remaining finite-precision work
    is to derive the displayed norm bounds for `DeltaA`, `DeltaB`, `Deltab`,
    and `Deltad` from the computed GQR algorithm. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_d
    {r p q : ℕ}
    (A DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (B DeltaB : Fin p → Fin (p + q) → ℝ)
    (b Deltab : Fin (r + q) → ℝ) (d Deltad : Fin p → ℝ)
    (hB :
      LSEFullRowRank (fun i j => B i j + DeltaB i j))
    (hstack :
      LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j)) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + Deltab i
    let dpert : Fin p → ℝ := fun i => d i + Deltad i
    ∃ h : GeneralizedQRFactorization r p q Apert Bpert,
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = dpert ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer Apert bpert Bpert dpert
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer Apert bpert Bpert dpert x) := by
  dsimp
  exact
    GeneralizedQRFactorization.exists_unique_method_solution_of_fullRowRank_stackedFullColumnRank
      (A := fun i j => A i j + DeltaA i j)
      (B := fun i j => B i j + DeltaB i j)
      (b := fun i => b i + Deltab i)
      (d := fun i => d i + Deltad i) hB hstack

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, triangular-solve component:
    the two lower-triangular solves in the exact GQR method have concrete
    finite-precision perturbation witnesses for the actual `fl_forwardSub`
    calls.

    This is a computed-path dependency for Theorem 20.10.  It instantiates the
    already proved forward-substitution backward-error theorem on the displayed
    `S y₁ = d` and `L₂₂ y₂ = Uᵀb - L₂₁y₁` solves.  It does not yet transport
    these factor perturbations back to a final `DeltaX` bound or identify the
    computed `xhat` with the GQR output vector. -/
theorem theorem20_10_gqr_forwardSub_triangular_solve_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    let y1hat : Fin p → ℝ := fl_forwardSub fp p h.S d
    let rhs : Fin q → ℝ :=
      fun i : Fin q =>
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
          rectMatMulVec h.L21 y1hat i
    let y2hat : Fin q → ℝ := fl_forwardSub fp q h.L22 rhs
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      rectMatMulVec (fun i j => h.S i j + DeltaS i j) y1hat = d ∧
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j) y2hat = rhs := by
  dsimp
  let y1hat : Fin p → ℝ := fl_forwardSub fp p h.S d
  let rhs : Fin q → ℝ :=
    fun i : Fin q =>
      matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
        rectMatMulVec h.L21 y1hat i
  let y2hat : Fin q → ℝ := fl_forwardSub fp q h.L22 rhs
  rcases forwardSub_backward_error fp p h.S d hSdiag h.lowerS hvalidS with
    ⟨DeltaS, hDeltaSbound, hSeq⟩
  rcases forwardSub_backward_error fp q h.L22 rhs hL22diag h.lowerL22
      hvalidL22 with
    ⟨DeltaL22, hDeltaL22bound, hL22eq⟩
  refine ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound, ?_, ?_⟩
  · ext i
    simpa [rectMatMulVec, y1hat] using hSeq i
  · ext i
    simpa [rectMatMulVec, y2hat, rhs] using hL22eq i

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, triangular-solve component:
    Frobenius-norm version of the concrete GQR triangular-solve perturbation
    witnesses.

    The underlying forward-substitution theorem gives componentwise relative
    bounds for the two lower-triangular solves.  This wrapper converts those
    entrywise bounds into source-shaped Frobenius bounds for the perturbations
    of `S` and `L₂₂`, while preserving the exact perturbed triangular
    equations for the actual `fl_forwardSub` calls. -/
theorem theorem20_10_gqr_forwardSub_triangular_solve_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    let y1hat : Fin p → ℝ := fl_forwardSub fp p h.S d
    let rhs : Fin q → ℝ :=
      fun i : Fin q =>
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
          rectMatMulVec h.L21 y1hat i
    let y2hat : Fin q → ℝ := fl_forwardSub fp q h.L22 rhs
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      rectMatMulVec (fun i j => h.S i j + DeltaS i j) y1hat = d ∧
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j) y2hat = rhs := by
  dsimp
  rcases theorem20_10_gqr_forwardSub_triangular_solve_perturbation_bound
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound, hSeq, hL22eq⟩
  have hDeltaSfrob :
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S := by
    simpa [frobNormRect_eq_frobNormFn] using
      (frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        DeltaS h.S (gamma_nonneg fp hvalidS) hDeltaSbound)
  have hDeltaL22frob :
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 := by
    simpa [frobNormRect_eq_frobNormFn] using
      (frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        DeltaL22 h.L22 (gamma_nonneg fp hvalidL22) hDeltaL22bound)
  exact
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    first lower-triangular solve `S y₁ = d`. -/
noncomputable def theorem20_10_gqr_y1hat
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (d : Fin p → ℝ) : Fin p → ℝ :=
  fl_forwardSub fp p h.S d

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    right-hand side for the trailing lower-triangular solve. -/
noncomputable def theorem20_10_gqr_rhs2hat
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ) : Fin q → ℝ :=
  fun i : Fin q =>
    matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
      rectMatMulVec h.L21 (theorem20_10_gqr_y1hat fp h d) i

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    second lower-triangular solve `L₂₂ y₂ = Uᵀb - L₂₁y₁`. -/
noncomputable def theorem20_10_gqr_y2hat
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ) : Fin q → ℝ :=
  fl_forwardSub fp q h.L22 (theorem20_10_gqr_rhs2hat fp h b d)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    final computed vector `xhat = Q [y₁hat; y₂hat]` for supplied GQR data.

    This definition names the computed path; it does not by itself prove that
    the vector is a minimizer of a perturbed LSE problem. -/
noncomputable def theorem20_10_gqr_xhat
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ) : Fin (p + q) → ℝ :=
  matMulVec (p + q) h.Q
    (Fin.append
      (theorem20_10_gqr_y1hat fp h d)
      (theorem20_10_gqr_y2hat fp h b d))

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    right-hand side for the trailing lower-triangular solve when the trailing
    transformed vector has already been computed or perturbed.

    This variant is the bridge needed for the rounded Householder RHS path:
    `beta` represents the trailing entries of the transformed right-hand side,
    rather than forcing the exact vector `Uᵀ b`. -/
noncomputable def theorem20_10_gqr_rhs2hat_of_transformed_tail
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (d : Fin p → ℝ) : Fin q → ℝ :=
  fun i : Fin q =>
    beta i - rectMatMulVec h.L21 (theorem20_10_gqr_y1hat fp h d) i

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    second lower-triangular solve driven by a supplied trailing transformed
    right-hand side. -/
noncomputable def theorem20_10_gqr_y2hat_of_transformed_tail
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (d : Fin p → ℝ) : Fin q → ℝ :=
  fl_forwardSub fp q h.L22
    (theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    final vector for the supplied-trailing-RHS computed path. -/
noncomputable def theorem20_10_gqr_xhat_of_transformed_tail
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (d : Fin p → ℝ) : Fin (p + q) → ℝ :=
  matMulVec (p + q) h.Q
    (Fin.append
      (theorem20_10_gqr_y1hat fp h d)
      (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d))

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    the named computed vector carries the same Frobenius-bounded triangular
    perturbation witnesses as the raw `fl_forwardSub` calls.

    This closes the bookkeeping step that identifies the local computed
    `xhat` expression used by the triangular-solve analysis.  It still does
    not prove the final `DeltaX` bound, rank preservation for perturbed source
    data, or exact-minimizer status of the computed vector. -/
theorem theorem20_10_gqr_xhat_triangular_solve_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d ∧
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat fp h b d) =
          theorem20_10_gqr_rhs2hat fp h b d ∧
      theorem20_10_gqr_xhat fp h b d =
        matMulVec (p + q) h.Q
          (Fin.append
            (theorem20_10_gqr_y1hat fp h d)
            (theorem20_10_gqr_y2hat fp h b d)) := by
  rcases theorem20_10_gqr_forwardSub_triangular_solve_frob_perturbation_bound
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_, ?_, rfl⟩
  · simpa [theorem20_10_gqr_y1hat] using hSeq
  · simpa [theorem20_10_gqr_y1hat, theorem20_10_gqr_rhs2hat,
      theorem20_10_gqr_y2hat] using hL22eq

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    triangular-solve perturbation witnesses for the supplied-trailing-RHS
    path.

    The proof is the same forward-substitution backward-error argument as for
    `theorem20_10_gqr_xhat_triangular_solve_frob_perturbation_bound`, but it
    leaves the transformed trailing right-hand side as an explicit `beta`.
    This is a computed-path dependency for routing the rounded Householder RHS
    transform through the GQR certificate. -/
theorem theorem20_10_gqr_xhat_of_transformed_tail_triangular_solve_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d ∧
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d) =
          theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d ∧
      theorem20_10_gqr_xhat_of_transformed_tail fp h beta d =
        matMulVec (p + q) h.Q
          (Fin.append
            (theorem20_10_gqr_y1hat fp h d)
            (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d)) := by
  let y1hat : Fin p → ℝ := theorem20_10_gqr_y1hat fp h d
  let rhs : Fin q → ℝ :=
    theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d
  let y2hat : Fin q → ℝ :=
    theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d
  rcases forwardSub_backward_error fp p h.S d hSdiag h.lowerS hvalidS with
    ⟨DeltaS, hDeltaSbound, hSeq⟩
  rcases forwardSub_backward_error fp q h.L22 rhs hL22diag h.lowerL22
      hvalidL22 with
    ⟨DeltaL22, hDeltaL22bound, hL22eq⟩
  have hDeltaSfrob :
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S := by
    simpa [frobNormRect_eq_frobNormFn] using
      (frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        DeltaS h.S (gamma_nonneg fp hvalidS) hDeltaSbound)
  have hDeltaL22frob :
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 := by
    simpa [frobNormRect_eq_frobNormFn] using
      (frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        DeltaL22 h.L22 (gamma_nonneg fp hvalidL22) hDeltaL22bound)
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_, ?_, rfl⟩
  · ext i
    simpa [rectMatMulVec, y1hat, theorem20_10_gqr_y1hat] using hSeq i
  · ext i
    simpa [rectMatMulVec, rhs, y2hat,
      theorem20_10_gqr_y2hat_of_transformed_tail] using hL22eq i

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    exact-minimizer handoff from supplied perturbed triangular factors.

    If a supplied perturbed GQR factorization has the same recovery `Q`, the
    same lower-left coupling block `L₂₁`, triangular blocks equal to the
    finite-precision backward-error witnesses `S + ΔS` and `L₂₂ + ΔL₂₂`, and
    the trailing transformed right-hand side agrees with the computed one, then
    the named computed vector `xhat = Q [y₁hat; y₂hat]` is an exact LSE
    minimizer for that supplied perturbed problem.  This bridge does not prove
    that such a perturbed source factorization exists; it isolates the exact
    algebra needed once the finite-precision GQR perturbation construction
    supplies those identities. -/
theorem theorem20_10_gqr_xhat_isLSEMinimizer_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i))
    (hS_inj : Function.Injective (rectMatMulVec hpert.S))
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat fp h b d) =
          theorem20_10_gqr_rhs2hat fp h b d) :
    IsLSEMinimizer Apert bpert Bpert dpert
      (theorem20_10_gqr_xhat fp h b d) := by
  let y1hat : Fin p → ℝ := theorem20_10_gqr_y1hat fp h d
  let y2hat : Fin q → ℝ := theorem20_10_gqr_y2hat fp h b d
  have hy1 : rectMatMulVec hpert.S y1hat = dpert := by
    rw [hS, hd]
    exact hSeq
  have hy2 :
      rectMatMulVec hpert.L22 y2hat =
        fun i : Fin q =>
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) -
            rectMatMulVec hpert.L21 y1hat i := by
    ext i
    calc
      rectMatMulVec hpert.L22 y2hat i
          = rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j) y2hat i := by
              rw [hL22]
      _ = theorem20_10_gqr_rhs2hat fp h b d i := by
              simpa [y2hat] using congrFun hL22eq i
      _ = matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) -
            rectMatMulVec hpert.L21 y1hat i := by
              simp [theorem20_10_gqr_rhs2hat, y1hat, hL21, hb_tail i]
  have hmin :
      IsLSEMinimizer Apert bpert Bpert dpert
        (matMulVec (p + q) hpert.Q (Fin.append y1hat y2hat)) :=
    hpert.isLSEMinimizer_of_triangular_solve hS_inj hy1 hy2
  simpa [theorem20_10_gqr_xhat, y1hat, y2hat, hQ] using hmin

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    exact-minimizer handoff for the supplied-trailing-RHS path.

    This is the rounded-RHS analogue of
    `theorem20_10_gqr_xhat_isLSEMinimizer_of_supplied_perturbed_triangular_factors`.
    The transformed trailing right-hand side is supplied as `beta`, so the
    perturbed-factor matching hypothesis asks for `Uᵀ(b + Δb)` to equal `beta`
    on the trailing block instead of the exact source vector `Uᵀ b`. -/
theorem theorem20_10_gqr_xhat_of_transformed_tail_isLSEMinimizer_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (beta : Fin q → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        beta i)
    (hS_inj : Function.Injective (rectMatMulVec hpert.S))
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d) =
          theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d) :
    IsLSEMinimizer Apert bpert Bpert dpert
      (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d) := by
  let y1hat : Fin p → ℝ := theorem20_10_gqr_y1hat fp h d
  let y2hat : Fin q → ℝ :=
    theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d
  have hy1 : rectMatMulVec hpert.S y1hat = dpert := by
    rw [hS, hd]
    exact hSeq
  have hy2 :
      rectMatMulVec hpert.L22 y2hat =
        fun i : Fin q =>
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) -
            rectMatMulVec hpert.L21 y1hat i := by
    ext i
    calc
      rectMatMulVec hpert.L22 y2hat i
          = rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j) y2hat i := by
              rw [hL22]
      _ = theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d i := by
              simpa [y2hat] using congrFun hL22eq i
      _ = matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) -
            rectMatMulVec hpert.L21 y1hat i := by
              simp [theorem20_10_gqr_rhs2hat_of_transformed_tail, y1hat,
                hL21, hb_tail i]
  have hmin :
      IsLSEMinimizer Apert bpert Bpert dpert
        (matMulVec (p + q) hpert.Q (Fin.append y1hat y2hat)) :=
    hpert.isLSEMinimizer_of_triangular_solve hS_inj hy1 hy2
  simpa [theorem20_10_gqr_xhat_of_transformed_tail, y1hat, y2hat, hQ]
    using hmin

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    supplied-trailing-RHS rank and minimizer handoff.

    Nonzero diagonals of the supplied perturbed triangular blocks give the
    perturbed rank assumptions, while the transformed-tail minimizer handoff
    identifies the supplied-trailing-RHS computed vector as an exact minimizer
    of that perturbed problem. -/
theorem theorem20_10_gqr_xhat_of_transformed_tail_rank_and_minimizer_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (beta : Fin q → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        beta i)
    (hSdiag_pert : ∀ i : Fin p, hpert.S i i ≠ 0)
    (hL22diag_pert : ∀ i : Fin q, hpert.L22 i i ≠ 0)
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d) =
          theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d) :
    LSEFullRowRank Bpert ∧
      LSEStackedFullColumnRank Apert Bpert ∧
        IsLSEMinimizer Apert bpert Bpert dpert
          (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d) := by
  have hrank :
      LSEFullRowRank Bpert ∧ LSEStackedFullColumnRank Apert Bpert :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨hSdiag_pert, hL22diag_pert⟩
  have hS_inj : Function.Injective (rectMatMulVec hpert.S) :=
    (hpert.s_bijective_of_diag_ne_zero hSdiag_pert).1
  have hmin :
      IsLSEMinimizer Apert bpert Bpert dpert
        (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d) :=
    theorem20_10_gqr_xhat_of_transformed_tail_isLSEMinimizer_of_supplied_perturbed_triangular_factors
      fp h hpert beta d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hS_inj hSeq hL22eq
  exact ⟨hrank.1, hrank.2, hmin⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), computed GQR method:
    zero forward-error witness for the supplied-trailing-RHS path.

    Once the supplied-trailing-RHS computed vector is known to be the unique
    exact minimizer of the perturbed problem, any exact minimizer `x` equals it,
    so the mixed-stability `DeltaX` witness may again be chosen as zero. -/
theorem theorem20_10_gqr_xhat_of_transformed_tail_zero_deltaX_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (beta : Fin q → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (gammaB : ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        beta i)
    (hSdiag_pert : ∀ i : Fin p, hpert.S i i ≠ 0)
    (hL22diag_pert : ∀ i : Fin q, hpert.L22 i i ≠ 0)
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d) =
          theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d)
    (hgammaB_nonneg : 0 ≤ gammaB)
    {x : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer Apert bpert Bpert dpert x) :
    ∃ DeltaX : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat_of_transformed_tail fp h beta d j =
          x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x := by
  rcases
    theorem20_10_gqr_xhat_of_transformed_tail_rank_and_minimizer_of_supplied_perturbed_triangular_factors
      fp h hpert beta d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hSdiag_pert hL22diag_pert hSeq hL22eq with
    ⟨_hBpert, hstack, hxhat_min⟩
  have hx_eq :
      x = theorem20_10_gqr_xhat_of_transformed_tail fp h beta d :=
    IsLSEMinimizer.eq_of_lseStackedFullColumnRank hstack hx hxhat_min
  refine ⟨(fun _ : Fin (p + q) => 0), ?_, ?_⟩
  · intro j
    simp [hx_eq]
  · rw [vecNorm2_zero]
    exact mul_nonneg hgammaB_nonneg (vecNorm2_nonneg x)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    bounded triangular-solve witnesses plus exact-minimizer handoff.

    This packages the existing forward-substitution backward-error witnesses
    `ΔS` and `ΔL₂₂`, their componentwise and Frobenius bounds, and the exact
    minimizer bridge for any supplied perturbed GQR factorization whose
    triangular blocks match those witnesses.  It advances the computed-vector
    side of Theorem 20.10 while leaving the genuine remaining obligations
    explicit: constructing matching perturbed source factors, proving
    perturbed rank/nonsingularity, and sharpening the printed RHS coefficient. -/
theorem theorem20_10_gqr_xhat_supplied_perturbed_factor_minimizer_certificate
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ {Apert : Fin (r + q) → Fin (p + q) → ℝ}
          {Bpert : Fin p → Fin (p + q) → ℝ}
          (hpert : GeneralizedQRFactorization r p q Apert Bpert)
          (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        dpert = d →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
        Function.Injective (rectMatMulVec hpert.S) →
        IsLSEMinimizer Apert bpert Bpert dpert
          (theorem20_10_gqr_xhat fp h b d)) := by
  rcases theorem20_10_gqr_xhat_triangular_solve_frob_perturbation_bound
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro Apert Bpert hpert bpert dpert hQ hS hL21 hL22 hd hb_tail hS_inj
  exact
    theorem20_10_gqr_xhat_isLSEMinimizer_of_supplied_perturbed_triangular_factors
      fp h hpert b d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hS_inj hSeq hL22eq

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    supplied perturbed-factor rank and minimizer handoff.

    Nonzero diagonals of the supplied perturbed triangular blocks `S` and
    `L₂₂` imply the perturbed source rank assumptions, and the same hypotheses
    used by `theorem20_10_gqr_xhat_isLSEMinimizer_of_supplied_perturbed_triangular_factors`
    identify the named computed `xhat` as an exact minimizer for that perturbed
    problem.  This does not prove that finite-precision perturbations preserve
    the diagonals; it isolates the exact GQR algebra once those perturbed
    blocks have been supplied. -/
theorem theorem20_10_gqr_xhat_rank_and_minimizer_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i))
    (hSdiag_pert : ∀ i : Fin p, hpert.S i i ≠ 0)
    (hL22diag_pert : ∀ i : Fin q, hpert.L22 i i ≠ 0)
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat fp h b d) =
          theorem20_10_gqr_rhs2hat fp h b d) :
    LSEFullRowRank Bpert ∧
      LSEStackedFullColumnRank Apert Bpert ∧
        IsLSEMinimizer Apert bpert Bpert dpert
          (theorem20_10_gqr_xhat fp h b d) := by
  have hrank :
      LSEFullRowRank Bpert ∧ LSEStackedFullColumnRank Apert Bpert :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨hSdiag_pert, hL22diag_pert⟩
  have hS_inj : Function.Injective (rectMatMulVec hpert.S) :=
    (hpert.s_bijective_of_diag_ne_zero hSdiag_pert).1
  have hmin :
      IsLSEMinimizer Apert bpert Bpert dpert
        (theorem20_10_gqr_xhat fp h b d) :=
    theorem20_10_gqr_xhat_isLSEMinimizer_of_supplied_perturbed_triangular_factors
      fp h hpert b d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hS_inj hSeq hL22eq
  exact ⟨hrank.1, hrank.2, hmin⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    bounded triangular-solve witnesses plus supplied-factor rank/minimizer
    handoff.

    This strengthens
    `theorem20_10_gqr_xhat_supplied_perturbed_factor_minimizer_certificate` by
    also returning the perturbed source rank conditions when the supplied
    perturbed triangular factors have nonzero diagonals. -/
theorem theorem20_10_gqr_xhat_supplied_perturbed_factor_rank_minimizer_certificate
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ {Apert : Fin (r + q) → Fin (p + q) → ℝ}
          {Bpert : Fin p → Fin (p + q) → ℝ}
          (hpert : GeneralizedQRFactorization r p q Apert Bpert)
          (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        dpert = d →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
        (∀ i : Fin p, hpert.S i i ≠ 0) →
        (∀ i : Fin q, hpert.L22 i i ≠ 0) →
        LSEFullRowRank Bpert ∧
          LSEStackedFullColumnRank Apert Bpert ∧
            IsLSEMinimizer Apert bpert Bpert dpert
              (theorem20_10_gqr_xhat fp h b d)) := by
  rcases theorem20_10_gqr_xhat_triangular_solve_frob_perturbation_bound
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro Apert Bpert hpert bpert dpert hQ hS hL21 hL22 hd hb_tail
    hSdiag_pert hL22diag_pert
  exact
    theorem20_10_gqr_xhat_rank_and_minimizer_of_supplied_perturbed_triangular_factors
      fp h hpert b d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hSdiag_pert hL22diag_pert hSeq hL22eq

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), computed GQR method:
    zero forward-error witness from supplied perturbed factors.

    Under the supplied perturbed-factor hypotheses, the named computed `xhat`
    is the unique exact minimizer of the supplied perturbed problem.  Therefore
    for any exact minimizer `x`, the mixed-stability `DeltaX` witness may be
    chosen as zero, giving the source-shaped `||DeltaX||₂ <= gammaB ||x||₂`
    bound for every nonnegative `gammaB`. -/
theorem theorem20_10_gqr_xhat_zero_deltaX_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (gammaB : ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i))
    (hSdiag_pert : ∀ i : Fin p, hpert.S i i ≠ 0)
    (hL22diag_pert : ∀ i : Fin q, hpert.L22 i i ≠ 0)
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat fp h b d) =
          theorem20_10_gqr_rhs2hat fp h b d)
    (hgammaB_nonneg : 0 ≤ gammaB)
    {x : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer Apert bpert Bpert dpert x) :
    ∃ DeltaX : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat fp h b d j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x := by
  rcases
    theorem20_10_gqr_xhat_rank_and_minimizer_of_supplied_perturbed_triangular_factors
      fp h hpert b d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hSdiag_pert hL22diag_pert hSeq hL22eq with
    ⟨_hBpert, hstack, hxhat_min⟩
  have hx_eq :
      x = theorem20_10_gqr_xhat fp h b d :=
    IsLSEMinimizer.eq_of_lseStackedFullColumnRank hstack hx hxhat_min
  refine ⟨(fun _ : Fin (p + q) => 0), ?_, ?_⟩
  · intro j
    simp [hx_eq]
  · rw [vecNorm2_zero]
    exact mul_nonneg hgammaB_nonneg (vecNorm2_nonneg x)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), computed GQR method:
    bounded triangular-solve witnesses plus zero-`DeltaX` handoff.

    This packages the actual `fl_forwardSub` perturbation witnesses with the
    exact uniqueness argument showing that, for any supplied perturbed GQR
    factorization satisfying the matching and diagonal hypotheses, the mixed
    forward-error relation can use `DeltaX = 0`. -/
theorem theorem20_10_gqr_xhat_supplied_perturbed_factor_zero_deltaX_certificate
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ {Apert : Fin (r + q) → Fin (p + q) → ℝ}
          {Bpert : Fin p → Fin (p + q) → ℝ}
          (hpert : GeneralizedQRFactorization r p q Apert Bpert)
          (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
          (gammaB : ℝ),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        dpert = d →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
        (∀ i : Fin p, hpert.S i i ≠ 0) →
        (∀ i : Fin q, hpert.L22 i i ≠ 0) →
        0 ≤ gammaB →
        ∀ x : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert dpert x →
            ∃ DeltaX : Fin (p + q) → ℝ,
              (∀ j : Fin (p + q),
                theorem20_10_gqr_xhat fp h b d j = x j + DeltaX j) ∧
              vecNorm2 DeltaX ≤ gammaB * vecNorm2 x) := by
  rcases theorem20_10_gqr_xhat_triangular_solve_frob_perturbation_bound
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro Apert Bpert hpert bpert dpert gammaB hQ hS hL21 hL22 hd
    hb_tail hSdiag_pert hL22diag_pert hgammaB_nonneg x hx
  exact
    theorem20_10_gqr_xhat_zero_deltaX_of_supplied_perturbed_triangular_factors
      fp h hpert b d bpert dpert DeltaS DeltaL22 gammaB hQ hS hL21 hL22 hd
      hb_tail hSdiag_pert hL22diag_pert hSeq hL22eq hgammaB_nonneg hx

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), finite-precision
    perturbation certificate for the mixed-stability branch.

    This is the part of the computed GQR proof that remains to be supplied by
    the floating-point algorithm: concrete perturbations with source-shaped
    norm bounds, perturbed rank assumptions, and a forward-error relation from
    the computed vector to any exact minimizer of the perturbed problem.  The
    exact GQR/minimizer algebra is proved separately below, so this certificate
    deliberately does not assume that the displayed perturbed LSE problem has a
    solution. -/
structure Theorem20_10PartAPerturbationCertificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (gammaA gammaB : ℝ) : Type where
  /-- Perturbation of the least-squares matrix `A`. -/
  DeltaA : Fin (r + q) → Fin (p + q) → ℝ
  /-- Perturbation of the constraint matrix `B`. -/
  DeltaB : Fin p → Fin (p + q) → ℝ
  /-- Perturbation of the least-squares right-hand side `b`. -/
  Deltab : Fin (r + q) → ℝ
  /-- The perturbed constraint matrix keeps the source full-row-rank condition. -/
  hB : LSEFullRowRank (fun i j => B i j + DeltaB i j)
  /-- The perturbed stacked matrix keeps the source uniqueness condition. -/
  hstack :
    LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j)
  /-- The computed vector is close to every exact minimizer of the perturbed
      problem, with the source `gamma_np`-style coefficient `gammaB`. -/
  near_exact_solution :
    ∀ x : Fin (p + q) → ℝ,
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x →
      ∃ DeltaX : Fin (p + q) → ℝ,
        (∀ j : Fin (p + q), xhat j = x j + DeltaX j) ∧
        vecNorm2 DeltaX ≤ gammaB * vecNorm2 x
  /-- Source-shaped Frobenius bound for `DeltaA`. -/
  hDeltaA : frobNormRect DeltaA ≤ gammaA * frobNormRect A
  /-- Source-shaped vector bound for `Deltab`. -/
  hDeltab : vecNorm2 Deltab ≤ gammaA * vecNorm2 b
  /-- Source-shaped Frobenius bound for `DeltaB`. -/
  hDeltaB : frobNormRect DeltaB ≤ gammaB * frobNormRect B

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), supplied-factor
    constructor for the mixed-stability perturbation certificate with a
    supplied transformed trailing right-hand side.

    This is the certificate-level bridge for the rounded Householder RHS route.
    The vector `beta` represents the computed trailing transformed RHS; callers
    must prove that the perturbed source RHS satisfies
    `Uᵀ(b + Deltab) = beta` on the trailing block.  The theorem therefore
    avoids assuming the exact transformed RHS while also not claiming the
    printed `Deltab` coefficient. -/
theorem theorem20_10_partA_certificate_of_supplied_perturbed_factor_zero_deltaX_of_transformed_tail
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (DeltaB : Fin p → Fin (p + q) → ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hDeltaA : frobNormRect DeltaA ≤ gammaA * frobNormRect A)
    (hDeltab : vecNorm2 Deltab ≤ gammaA * vecNorm2 b)
    (hDeltaB : frobNormRect DeltaB ≤ gammaB * frobNormRect B)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ (hpert :
          GeneralizedQRFactorization r p q
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j)),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            beta i) →
        (∀ i : Fin p, hpert.S i i ≠ 0) →
        (∀ i : Fin q, hpert.L22 i i ≠ 0) →
        Nonempty
          (Theorem20_10PartAPerturbationCertificate A B b d
            (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d)
            gammaA gammaB)) := by
  rcases
    theorem20_10_gqr_xhat_of_transformed_tail_triangular_solve_frob_perturbation_bound
      fp h beta d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro hpert hQ hS hL21 hL22 hb_tail hSdiag_pert hL22diag_pert
  have hrank :
      LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
        LSEStackedFullColumnRank
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨hSdiag_pert, hL22diag_pert⟩
  exact
    ⟨{ DeltaA := DeltaA
       DeltaB := DeltaB
       Deltab := Deltab
       hB := hrank.1
       hstack := hrank.2
       near_exact_solution := by
         intro x hx
         exact
           theorem20_10_gqr_xhat_of_transformed_tail_zero_deltaX_of_supplied_perturbed_triangular_factors
             fp h hpert beta d (fun i => b i + Deltab i) d DeltaS DeltaL22
             gammaB hQ hS hL21 hL22 rfl hb_tail hSdiag_pert hL22diag_pert
             hSeq hL22eq hgammaB_nonneg hx
       hDeltaA := hDeltaA
       hDeltab := hDeltab
       hDeltaB := hDeltaB }⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    transformed-tail version of the supplied-factor Part A certificate.

    This removes the external `hpert` input from
    `theorem20_10_partA_certificate_of_supplied_perturbed_factor_zero_deltaX_of_transformed_tail`.
    It is the algebraic bridge needed by the rounded RHS path: the trailing
    transformed vector is an explicit `beta`, and the remaining RHS obligation
    is the honest equality `Uᵀ(b + Deltab) = beta` on the trailing block. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_transformed_tail
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (let Spert : Fin p → Fin p → ℝ :=
          fun i j => h.S i j + DeltaS i j
       let L22pert : Fin q → Fin q → ℝ :=
          fun i j => h.L22 i j + DeltaL22 i j
       let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
       let Bpert : Fin p → Fin (p + q) → ℝ :=
          gqrSourceBFromBlocks h.Q Spert
       let DeltaA : Fin (r + q) → Fin (p + q) → ℝ :=
          fun i j => Apert i j - A i j
       let DeltaB : Fin p → Fin (p + q) → ℝ :=
          fun i j => Bpert i j - B i j
       IsLowerTriangular Spert →
       IsLowerTriangular L22pert →
       (∀ i : Fin p, Spert i i ≠ 0) →
       (∀ i : Fin q, L22pert i i ≠ 0) →
       frobNormRect DeltaA ≤ gammaA * frobNormRect A →
       vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       frobNormRect DeltaB ≤ gammaB * frobNormRect B →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            beta i) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d)
          gammaA gammaB)) := by
  rcases
    theorem20_10_gqr_xhat_of_transformed_tail_triangular_solve_frob_perturbation_bound
      fp h beta d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  dsimp
  intro hSpert_lower hL22pert_lower hSpert_diag hL22pert_diag
    hDeltaA hDeltab hDeltaB hb_tail
  let Spert : Fin p → Fin p → ℝ := fun i j => h.S i j + DeltaS i j
  let L22pert : Fin q → Fin q → ℝ := fun i j => h.L22 i j + DeltaL22 i j
  let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
    gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
  let Bpert : Fin p → Fin (p + q) → ℝ :=
    gqrSourceBFromBlocks h.Q Spert
  let DeltaA_src : Fin (r + q) → Fin (p + q) → ℝ :=
    fun i j => Apert i j - A i j
  let DeltaB_src : Fin p → Fin (p + q) → ℝ :=
    fun i j => Bpert i j - B i j
  let hpert : GeneralizedQRFactorization r p q Apert Bpert :=
    GeneralizedQRFactorization.of_source_blocks
      h.Q h.U h.L11 h.L21 L22pert Spert
      h.orthQ h.orthU hL22pert_lower hSpert_lower
  have hApert_src :
      (fun i j => A i j + DeltaA_src i j) = Apert := by
    ext i j
    dsimp [DeltaA_src]
    ring
  have hBpert_src :
      (fun i j => B i j + DeltaB_src i j) = Bpert := by
    ext i j
    dsimp [DeltaB_src]
    ring
  have hrank :
      LSEFullRowRank Bpert ∧ LSEStackedFullColumnRank Apert Bpert :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨fun i => by simpa [hpert, Spert] using hSpert_diag i,
       fun i => by simpa [hpert, L22pert] using hL22pert_diag i⟩
  have hBcert :
      LSEFullRowRank (fun i j => B i j + DeltaB_src i j) := by
    rw [hBpert_src]
    exact hrank.1
  have hstackcert :
      LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA_src i j)
        (fun i j => B i j + DeltaB_src i j) := by
    rw [hApert_src, hBpert_src]
    exact hrank.2
  exact
    ⟨{ DeltaA := DeltaA_src
       DeltaB := DeltaB_src
       Deltab := Deltab
       hB := hBcert
       hstack := hstackcert
       near_exact_solution := by
         intro x hx
         have hx' : IsLSEMinimizer Apert
             (fun i => b i + Deltab i) Bpert d x := by
           rw [hApert_src, hBpert_src] at hx
           exact hx
         exact
           theorem20_10_gqr_xhat_of_transformed_tail_zero_deltaX_of_supplied_perturbed_triangular_factors
             fp h hpert beta d (fun i => b i + Deltab i) d DeltaS DeltaL22
             gammaB rfl rfl rfl rfl rfl hb_tail
             (fun i => by simpa [hpert, Spert] using hSpert_diag i)
             (fun i => by simpa [hpert, L22pert] using hL22pert_diag i)
             hSeq hL22eq hgammaB_nonneg hx'
       hDeltaA := hDeltaA
       hDeltab := hDeltab
       hDeltaB := hDeltaB }⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), transformed-tail
    constructed-source certificate with triangular preservation and the induced
    source `DeltaA`/`DeltaB` bounds discharged.

    This is the rounded-RHS counterpart of
    `theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds`.
    The only remaining RHS-specific obligations are the source-shaped bound for
    `Deltab` and the transformed-tail equality
    `Uᵀ(b + Deltab) = beta`. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds_transformed_tail
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge : gamma fp q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            beta i) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d)
          gammaA gammaB)) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_transformed_tail
      fp h beta b d gammaA gammaB Deltab hgammaB_nonneg hSdiag hL22diag
      (gammaValid_mono fp (by omega) hvalid2S)
      (gammaValid_mono fp (by omega) hvalid2L22) with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hcert⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  dsimp at hcert ⊢
  intro hDeltab hb_tail
  have hSpert_lower :
      IsLowerTriangular (fun i j => h.S i j + DeltaS i j) :=
    h.lowerS.add_of_entrywise_abs_le_mul_abs hDeltaSbound
  have hL22pert_lower :
      IsLowerTriangular (fun i j => h.L22 i j + DeltaL22 i j) :=
    h.lowerL22.add_of_entrywise_abs_le_mul_abs hDeltaL22bound
  have hSpert_diag :
      ∀ i : Fin p, h.S i i + DeltaS i i ≠ 0 :=
    diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one
      hSdiag (gamma_lt_one fp p hvalid2S) hDeltaSbound
  have hL22pert_diag :
      ∀ i : Fin q, h.L22 i i + DeltaL22 i i ≠ 0 :=
    diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one
      hL22diag (gamma_lt_one fp q hvalid2L22) hDeltaL22bound
  have hgammaq_nonneg : 0 ≤ gamma fp q :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid2L22)
  have hDeltaA_base :
      frobNormRect
        (fun i j =>
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
              (fun i j => h.L22 i j + DeltaL22 i j) i j -
            A i j) ≤
        gamma fp q * frobNormRect A :=
    h.constructed_sourceA_L22_perturbation_frobNorm_bound
      (gamma fp q) DeltaL22 hgammaq_nonneg hDeltaL22frob
  have hDeltaA :
      frobNormRect
        (fun i j =>
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
              (fun i j => h.L22 i j + DeltaL22 i j) i j -
            A i j) ≤
        gammaA * frobNormRect A := by
    exact le_trans hDeltaA_base
      (mul_le_mul_of_nonneg_right hgammaA_ge (frobNormRect_nonneg A))
  have hDeltaB_base :
      frobNormRect
        (fun i j =>
          gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
            B i j) ≤
        gamma fp p * frobNormRect B :=
    h.constructed_sourceB_perturbation_frobNorm_bound
      (gamma fp p) DeltaS hDeltaSfrob
  have hDeltaB :
      frobNormRect
        (fun i j =>
          gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
            B i j) ≤
        gammaB * frobNormRect B := by
    exact le_trans hDeltaB_base
      (mul_le_mul_of_nonneg_right hgammaB_ge (frobNormRect_nonneg B))
  exact
    hcert hSpert_lower hL22pert_lower hSpert_diag hL22pert_diag
      hDeltaA hDeltab hDeltaB hb_tail

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), supplied-factor
    constructor for the mixed-stability perturbation certificate.

    This is the certificate-level handoff for the currently verified supplied
    perturbed-factor boundary.  If separate work supplies source perturbations
    `DeltaA`, `DeltaB`, and `Deltab` with the required norm bounds and a
    perturbed GQR factorization whose displayed triangular blocks match the
    forward-substitution perturbation witnesses, then the named computed GQR
    vector has a full `Theorem20_10PartAPerturbationCertificate`.  The theorem
    deliberately leaves the matching-factor construction as an explicit
    hypothesis rather than claiming the floating-point GQR algorithm already
    supplies it. -/
theorem theorem20_10_partA_certificate_of_supplied_perturbed_factor_zero_deltaX
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (DeltaB : Fin p → Fin (p + q) → ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hDeltaA : frobNormRect DeltaA ≤ gammaA * frobNormRect A)
    (hDeltab : vecNorm2 Deltab ≤ gammaA * vecNorm2 b)
    (hDeltaB : frobNormRect DeltaB ≤ gammaB * frobNormRect B)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ (hpert :
          GeneralizedQRFactorization r p q
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j)),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
        (∀ i : Fin p, hpert.S i i ≠ 0) →
        (∀ i : Fin q, hpert.L22 i i ≠ 0) →
        Nonempty
          (Theorem20_10PartAPerturbationCertificate A B b d
            (theorem20_10_gqr_xhat fp h b d) gammaA gammaB)) := by
  rcases theorem20_10_gqr_xhat_supplied_perturbed_factor_zero_deltaX_certificate
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hzero⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro hpert hQ hS hL21 hL22 hb_tail hSdiag_pert hL22diag_pert
  have hrank :
      LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
        LSEStackedFullColumnRank
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨hSdiag_pert, hL22diag_pert⟩
  exact
    ⟨{ DeltaA := DeltaA
       DeltaB := DeltaB
       Deltab := Deltab
       hB := hrank.1
       hstack := hrank.2
       near_exact_solution := by
         intro x hx
         exact
           hzero hpert (fun i => b i + Deltab i) d gammaB
             hQ hS hL21 hL22 rfl hb_tail hSdiag_pert hL22diag_pert
             hgammaB_nonneg x hx
       hDeltaA := hDeltaA
       hDeltab := hDeltab
       hDeltaB := hDeltaB }⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    version of the supplied-factor Part A certificate.

    This removes the external `hpert` input from
    `theorem20_10_partA_certificate_of_supplied_perturbed_factor_zero_deltaX`.
    The perturbed source matrices are constructed directly by transporting the
    perturbed triangular blocks `S + DeltaS` and `L22 + DeltaL22` back through
    the original orthogonal factors.  The remaining hypotheses are exactly the
    ones not proved by this algebraic construction: lower-triangularity of the
    perturbed blocks, source-shaped bounds for the induced source
    perturbations, and the transformed right-hand-side matching condition. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (let Spert : Fin p → Fin p → ℝ :=
          fun i j => h.S i j + DeltaS i j
       let L22pert : Fin q → Fin q → ℝ :=
          fun i j => h.L22 i j + DeltaL22 i j
       let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
       let Bpert : Fin p → Fin (p + q) → ℝ :=
          gqrSourceBFromBlocks h.Q Spert
       let DeltaA : Fin (r + q) → Fin (p + q) → ℝ :=
          fun i j => Apert i j - A i j
       let DeltaB : Fin p → Fin (p + q) → ℝ :=
          fun i j => Bpert i j - B i j
       IsLowerTriangular Spert →
       IsLowerTriangular L22pert →
       (∀ i : Fin p, Spert i i ≠ 0) →
       (∀ i : Fin q, L22pert i i ≠ 0) →
       frobNormRect DeltaA ≤ gammaA * frobNormRect A →
       vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       frobNormRect DeltaB ≤ gammaB * frobNormRect B →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d) gammaA gammaB)) := by
  rcases theorem20_10_gqr_xhat_supplied_perturbed_factor_zero_deltaX_certificate
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hzero⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  dsimp
  intro hSpert_lower hL22pert_lower hSpert_diag hL22pert_diag
    hDeltaA hDeltab hDeltaB hb_tail
  let Spert : Fin p → Fin p → ℝ := fun i j => h.S i j + DeltaS i j
  let L22pert : Fin q → Fin q → ℝ := fun i j => h.L22 i j + DeltaL22 i j
  let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
    gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
  let Bpert : Fin p → Fin (p + q) → ℝ :=
    gqrSourceBFromBlocks h.Q Spert
  let DeltaA_src : Fin (r + q) → Fin (p + q) → ℝ :=
    fun i j => Apert i j - A i j
  let DeltaB_src : Fin p → Fin (p + q) → ℝ :=
    fun i j => Bpert i j - B i j
  let hpert : GeneralizedQRFactorization r p q Apert Bpert :=
    GeneralizedQRFactorization.of_source_blocks
      h.Q h.U h.L11 h.L21 L22pert Spert
      h.orthQ h.orthU hL22pert_lower hSpert_lower
  have hApert_src :
      (fun i j => A i j + DeltaA_src i j) = Apert := by
    ext i j
    dsimp [DeltaA_src]
    ring
  have hBpert_src :
      (fun i j => B i j + DeltaB_src i j) = Bpert := by
    ext i j
    dsimp [DeltaB_src]
    ring
  have hrank :
      LSEFullRowRank Bpert ∧ LSEStackedFullColumnRank Apert Bpert :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨fun i => by simpa [hpert, Spert] using hSpert_diag i,
       fun i => by simpa [hpert, L22pert] using hL22pert_diag i⟩
  have hBcert :
      LSEFullRowRank (fun i j => B i j + DeltaB_src i j) := by
    rw [hBpert_src]
    exact hrank.1
  have hstackcert :
      LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA_src i j)
        (fun i j => B i j + DeltaB_src i j) := by
    rw [hApert_src, hBpert_src]
    exact hrank.2
  exact
    ⟨{ DeltaA := DeltaA_src
       DeltaB := DeltaB_src
       Deltab := Deltab
       hB := hBcert
       hstack := hstackcert
       near_exact_solution := by
         intro x hx
         have hx' : IsLSEMinimizer Apert
             (fun i => b i + Deltab i) Bpert d x := by
           rw [hApert_src, hBpert_src] at hx
           exact hx
         exact
           hzero hpert (fun i => b i + Deltab i) d gammaB
             rfl rfl rfl rfl rfl hb_tail
             (fun i => by simpa [hpert, Spert] using hSpert_diag i)
             (fun i => by simpa [hpert, L22pert] using hL22pert_diag i)
             hgammaB_nonneg x hx'
       hDeltaA := hDeltaA
       hDeltab := hDeltab
       hDeltaB := hDeltaB }⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    certificate with perturbed triangular nonsingularity discharged by
    `gamma < 1`.

    The forward-substitution perturbation bounds are relative entrywise bounds.
    Therefore the perturbed `S + DeltaS` and `L22 + DeltaL22` blocks remain
    lower triangular; if the relative factors are strictly below one, their
    nonzero diagonals are preserved.  This theorem removes those hypotheses
    from `theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks`,
    leaving only the induced source perturbation bounds and transformed-RHS
    matching condition. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_gamma_lt_one
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q)
    (hgammaS_lt : gamma fp p < 1)
    (hgammaL22_lt : gamma fp q < 1) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (let Spert : Fin p → Fin p → ℝ :=
          fun i j => h.S i j + DeltaS i j
       let L22pert : Fin q → Fin q → ℝ :=
          fun i j => h.L22 i j + DeltaL22 i j
       let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
       let Bpert : Fin p → Fin (p + q) → ℝ :=
          gqrSourceBFromBlocks h.Q Spert
       let DeltaA : Fin (r + q) → Fin (p + q) → ℝ :=
          fun i j => Apert i j - A i j
       let DeltaB : Fin p → Fin (p + q) → ℝ :=
          fun i j => Bpert i j - B i j
       frobNormRect DeltaA ≤ gammaA * frobNormRect A →
       vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       frobNormRect DeltaB ≤ gammaB * frobNormRect B →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d) gammaA gammaB)) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks
      fp h b d gammaA gammaB Deltab hgammaB_nonneg hSdiag hL22diag
      hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hcert⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  dsimp at hcert ⊢
  intro hDeltaA hDeltab hDeltaB hb_tail
  have hSpert_lower :
      IsLowerTriangular (fun i j => h.S i j + DeltaS i j) :=
    h.lowerS.add_of_entrywise_abs_le_mul_abs hDeltaSbound
  have hL22pert_lower :
      IsLowerTriangular (fun i j => h.L22 i j + DeltaL22 i j) :=
    h.lowerL22.add_of_entrywise_abs_le_mul_abs hDeltaL22bound
  have hSpert_diag :
      ∀ i : Fin p, h.S i i + DeltaS i i ≠ 0 :=
    diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one
      hSdiag hgammaS_lt hDeltaSbound
  have hL22pert_diag :
      ∀ i : Fin q, h.L22 i i + DeltaL22 i i ≠ 0 :=
    diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one
      hL22diag hgammaL22_lt hDeltaL22bound
  exact
    hcert hSpert_lower hL22pert_lower hSpert_diag hL22pert_diag
      hDeltaA hDeltab hDeltaB hb_tail

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    certificate with the `gamma < 1` triangular preservation guards derived
    from doubled `gammaValid` hypotheses.

    This is the same certificate surface as
    `theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_gamma_lt_one`,
    but exposes the standard floating-point smallness assumptions
    `gammaValid fp (2*p)` and `gammaValid fp (2*q)` instead of explicit
    inequalities on `gamma`. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (let Spert : Fin p → Fin p → ℝ :=
          fun i j => h.S i j + DeltaS i j
       let L22pert : Fin q → Fin q → ℝ :=
          fun i j => h.L22 i j + DeltaL22 i j
       let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
       let Bpert : Fin p → Fin (p + q) → ℝ :=
          gqrSourceBFromBlocks h.Q Spert
       let DeltaA : Fin (r + q) → Fin (p + q) → ℝ :=
          fun i j => Apert i j - A i j
       let DeltaB : Fin p → Fin (p + q) → ℝ :=
          fun i j => Bpert i j - B i j
       frobNormRect DeltaA ≤ gammaA * frobNormRect A →
       vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       frobNormRect DeltaB ≤ gammaB * frobNormRect B →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d) gammaA gammaB)) := by
  exact
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_gamma_lt_one
      fp h b d gammaA gammaB Deltab hgammaB_nonneg hSdiag hL22diag
      (gammaValid_mono fp (by omega) hvalid2S)
      (gammaValid_mono fp (by omega) hvalid2L22)
      (gamma_lt_one fp p hvalid2S)
      (gamma_lt_one fp q hvalid2L22)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    certificate with the induced source `DeltaA` and `DeltaB` Frobenius bounds
    discharged from the triangular-solve perturbation bounds.

    The remaining visible finite-precision obligations are the source-shaped
    right-hand-side perturbation bound for `Deltab` and the transformed trailing
    right-hand-side matching condition.  The matrix perturbation bounds are
    proved internally using the transported `L22` and `S` perturbations. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge : gamma fp q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d) gammaA gammaB)) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid
      fp h b d gammaA gammaB Deltab hgammaB_nonneg hSdiag hL22diag
      hvalid2S hvalid2L22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hcert⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  dsimp at hcert ⊢
  intro hDeltab hb_tail
  have hgammaq_nonneg : 0 ≤ gamma fp q :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid2L22)
  have hDeltaA_base :
      frobNormRect
        (fun i j =>
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
              (fun i j => h.L22 i j + DeltaL22 i j) i j -
            A i j) ≤
        gamma fp q * frobNormRect A :=
    h.constructed_sourceA_L22_perturbation_frobNorm_bound
      (gamma fp q) DeltaL22 hgammaq_nonneg hDeltaL22frob
  have hDeltaA :
      frobNormRect
        (fun i j =>
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
              (fun i j => h.L22 i j + DeltaL22 i j) i j -
            A i j) ≤
        gammaA * frobNormRect A := by
    exact le_trans hDeltaA_base
      (mul_le_mul_of_nonneg_right hgammaA_ge (frobNormRect_nonneg A))
  have hDeltaB_base :
      frobNormRect
        (fun i j =>
          gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
            B i j) ≤
        gamma fp p * frobNormRect B :=
    h.constructed_sourceB_perturbation_frobNorm_bound
      (gamma fp p) DeltaS hDeltaSfrob
  have hDeltaB :
      frobNormRect
        (fun i j =>
          gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
            B i j) ≤
        gammaB * frobNormRect B := by
    exact le_trans hDeltaB_base
      (mul_le_mul_of_nonneg_right hgammaB_ge (frobNormRect_nonneg B))
  exact hcert hDeltaA hDeltab hDeltaB hb_tail

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), exact transformed-RHS
    specialization of the constructed-source certificate.

    The named supplied-GQR path computes the trailing triangular right-hand side
    from the exact transformed vector `Uᵀ b`, so choosing `Deltab = 0` discharges
    both the source-shaped RHS perturbation bound and the transformed-tail
    matching condition.  This closes the exact-transform certificate branch; the
    separate rounded Householder RHS-transform bridge remains a distinct
    computed-path obligation. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_exact_rhs
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (hgammaA_nonneg : 0 ≤ gammaA)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge : gamma fp q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d) gammaA gammaB) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds
      fp h b d gammaA gammaB (0 : Fin (r + q) → ℝ)
      hgammaB_nonneg hgammaA_ge hgammaB_ge hSdiag hL22diag
      hvalid2S hvalid2L22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hcert⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  have hDeltab0 :
      vecNorm2 (0 : Fin (r + q) → ℝ) ≤ gammaA * vecNorm2 b := by
    change vecNorm2 (fun _ : Fin (r + q) => 0) ≤ gammaA * vecNorm2 b
    rw [vecNorm2_zero]
    exact mul_nonneg hgammaA_nonneg (vecNorm2_nonneg b)
  have hb_tail0 : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose h.U)
          (fun i => b i + (0 : Fin (r + q) → ℝ) i) (Fin.natAdd r i) =
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) := by
    intro i
    simp
  exact hcert hDeltab0 hb_tail0

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), certificate-to-exact-core
    handoff.

    A verified finite-precision GQR perturbation certificate yields an exact
    perturbed LSE minimizer, exact GQR method coordinates for that perturbed
    problem, the mixed forward-error relation for the computed vector, and the
    displayed perturbation bounds.  The only remaining work for the full
    theorem is to prove the certificate from the concrete computed GQR path and
    to instantiate the source `gamma_tilde` coefficients. -/
theorem theorem20_10_partA_mixed_stability_of_perturbation_certificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    {gammaA gammaB : ℝ}
    (cert :
      Theorem20_10PartAPerturbationCertificate A B b d xhat gammaA gammaB) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + cert.DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + cert.DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + cert.Deltab i
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      DeltaA = cert.DeltaA ∧
      DeltaB = cert.DeltaB ∧
      Deltab = cert.Deltab ∧
      (∀ j : Fin (p + q), xhat j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      IsLSEMinimizer Apert bpert Bpert d x ∧
      (∃ h : GeneralizedQRFactorization r p q Apert Bpert,
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec h.S yz.1 = d ∧
          rectMatMulVec h.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
                rectMatMulVec h.L21 yz.1 i) ∧
          IsLSEMinimizer Apert bpert Bpert d
            (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert d x0)) := by
  dsimp
  rcases
    GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_same_d
      A cert.DeltaA B cert.DeltaB b cert.Deltab d cert.hB cert.hstack with
    ⟨h, hyz, hxuniq⟩
  rcases hxuniq with ⟨x, hx, huniq⟩
  rcases cert.near_exact_solution x hx with ⟨DeltaX, hxhat, hDeltaX⟩
  refine ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, DeltaX, x, rfl, rfl, rfl,
    hxhat, hDeltaX, cert.hDeltaA, cert.hDeltab, cert.hDeltaB, hx, ?_⟩
  exact ⟨h, hyz, ⟨x, hx, huniq⟩⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), exact transformed-RHS
    mixed-stability theorem for the constructed-source supplied-GQR path.

    This combines the constructed-source exact-RHS certificate with the generic
    certificate-to-core handoff.  The conclusion exposes the perturbations and
    exact perturbed minimizer directly, without requiring callers to unpack the
    intermediate certificate. -/
theorem theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (hgammaA_nonneg : 0 ≤ gammaA)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge : gamma fp q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat fp h b d j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = d ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x0)) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_exact_rhs
      fp h b d gammaA gammaB hgammaA_nonneg hgammaB_nonneg
      hgammaA_ge hgammaB_ge hSdiag hL22diag hvalid2S hvalid2L22 with
    ⟨_DeltaS, _DeltaL22, _hDeltaSbound, _hDeltaL22bound,
      _hDeltaSfrob, _hDeltaL22frob, hcert⟩
  rcases hcert with ⟨cert⟩
  have hcore :=
    theorem20_10_partA_mixed_stability_of_perturbation_certificate
      A B b d (theorem20_10_gqr_xhat fp h b d) cert
  dsimp at hcore
  rcases hcore with
    ⟨DeltaA, DeltaB, Deltab, DeltaX, x,
      hDeltaAeq, hDeltaBeq, hDeltabeq, hxhat, hDeltaX,
      hDeltaA, hDeltab, hDeltaB, hx, hmethod⟩
  refine
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, DeltaX, x,
      hxhat, hDeltaX, ?_, ?_, ?_, hx, hmethod⟩
  · simpa [hDeltaAeq] using hDeltaA
  · simpa [hDeltabeq] using hDeltab
  · simpa [hDeltaBeq] using hDeltaB

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), finite-precision
    perturbation certificate for the fully backward-stable branch.

    The certificate records the perturbations and the displayed norm bounds
    for the perturbed problem with right-hand side `d + Deltad`.  It does not
    assume that the computed vector is the minimizer; the theorem below proves
    the exact perturbed GQR/minimizer core, leaving the computed-vector
    identification as the remaining algorithmic obligation. -/
structure Theorem20_10PartBPerturbationCertificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (gammaA gammaB : ℝ) : Type where
  /-- Perturbation of the least-squares matrix `A`. -/
  DeltaA : Fin (r + q) → Fin (p + q) → ℝ
  /-- Perturbation of the constraint matrix `B`. -/
  DeltaB : Fin p → Fin (p + q) → ℝ
  /-- Perturbation of the least-squares right-hand side `b`. -/
  Deltab : Fin (r + q) → ℝ
  /-- Perturbation of the constraint right-hand side `d`. -/
  Deltad : Fin p → ℝ
  /-- The perturbed constraint matrix keeps the source full-row-rank condition. -/
  hB : LSEFullRowRank (fun i j => B i j + DeltaB i j)
  /-- The perturbed stacked matrix keeps the source uniqueness condition. -/
  hstack :
    LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j)
  /-- Source-shaped Frobenius bound for `DeltaA`. -/
  hDeltaA : frobNormRect DeltaA ≤ gammaA * frobNormRect A
  /-- Source-shaped Frobenius bound for `DeltaB`. -/
  hDeltaB : frobNormRect DeltaB ≤ gammaB * frobNormRect B
  /-- Source-shaped right-hand-side perturbation bound for `Deltab`. -/
  hDeltab :
    vecNorm2 Deltab ≤
      gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat
  /-- Source-shaped constraint right-hand-side perturbation bound. -/
  hDeltad : vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), certificate-to-exact-core
    handoff.

    A verified finite-precision GQR perturbation certificate gives exact GQR
    method coordinates and a unique exact minimizer for the perturbed problem
    with right-hand side `d + Deltad`, together with the displayed perturbation
    bounds.  The remaining computed-algorithm theorem must prove this
    certificate and identify the actual computed vector with the unique
    minimizer. -/
theorem theorem20_10_partB_backward_error_of_perturbation_certificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    {gammaA gammaB : ℝ}
    (cert :
      Theorem20_10PartBPerturbationCertificate A B b d xhat gammaA gammaB) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + cert.DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + cert.DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + cert.Deltab i
    let dpert : Fin p → ℝ := fun i => d i + cert.Deltad i
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      DeltaA = cert.DeltaA ∧
      DeltaB = cert.DeltaB ∧
      Deltab = cert.Deltab ∧
      Deltad = cert.Deltad ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ h : GeneralizedQRFactorization r p q Apert Bpert,
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec h.S yz.1 = dpert ∧
          rectMatMulVec h.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
                rectMatMulVec h.L21 yz.1 i) ∧
          IsLSEMinimizer Apert bpert Bpert dpert
            (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert dpert x)) := by
  dsimp
  rcases
    GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_d
      A cert.DeltaA B cert.DeltaB b cert.Deltab d cert.Deltad
      cert.hB cert.hstack with
    ⟨h, hyz, hxuniq⟩
  exact
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, cert.Deltad, rfl, rfl, rfl, rfl,
      cert.hDeltaA, cert.hDeltaB, cert.hDeltab, cert.hDeltad,
      ⟨h, hyz, hxuniq⟩⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    Householder `gamma_tilde_mn` coefficient for the `A` and `b` perturbation
    bounds, using the Chapter 19 Householder QR coefficient with the local
    matrix dimensions `m = r + q` and `n = p + q`. -/
noncomputable def theorem20_10_householder_gammaA
    (fp : FPModel) (r p q : ℕ) : ℝ :=
  H19.Theorem19_4.gamma_tilde fp (r + q) (p + q)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    Householder `gamma_tilde_np` coefficient for the `B`, `Delta x`, and
    `Delta d` bounds.  The GQR method first triangularizes `Bᵀ`, whose local
    dimensions are `(p + q) × p`. -/
noncomputable def theorem20_10_householder_gammaB
    (fp : FPModel) (_r p q : ℕ) : ℝ :=
  H19.Theorem19_4.gamma_tilde fp (p + q) p

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete Householder QR perturbation bound for the smaller `A Q₂`
    triangularization step in the GQR path.

    The block later instantiated as `A Q₂` has dimensions `(r+q) × q`, so the
    Chapter 19 Householder QR theorem applies without requiring the full `A`
    matrix to be tall.  The resulting `gamma_tilde_(r+q),q` bound is absorbed
    into the source-facing `gamma_tilde_(r+q),(p+q)` coefficient by gamma
    monotonicity.  This is a computed-path dependency only; it does not yet
    transport the perturbation back through the already computed `Q₂` factor or
    prove the triangular-solve perturbations. -/
theorem theorem20_10_householder_AQ2_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (C : Fin (r + q) → Fin q → ℝ)
    (hq : 0 < q)
    (hvalid :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q))) :
    ∃ DeltaC : Fin (r + q) → Fin q → ℝ,
      (∀ i j,
        C i j + DeltaC i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q C)
            (fl_householderQRPanel_R fp (r + q) q C) i j) ∧
      frobNormRect DeltaC ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect C := by
  let K : ℕ := householderConstructApplyGammaIndex (r + q)
  have hvalid_full : gammaValid fp ((p + q) * K) := by
    simpa [K] using hvalid
  have hq_le_pq : q ≤ p + q := by omega
  have hidx_le : q * K ≤ (p + q) * K :=
    Nat.mul_le_mul_right K hq_le_pq
  have hvalid_q : gammaValid fp (q * K) :=
    gammaValid_mono fp hidx_le hvalid_full
  have hqr :
      H19.Theorem19_4.HouseholderQRBackwardError (r + q) q C
        (fl_householderQRPanel_Q fp (r + q) q C)
        (fl_householderQRPanel_R fp (r + q) q C)
        (H19.Theorem19_4.gamma_tilde fp (r + q) q) := by
    exact
      H19.Theorem19_4.householder_qr_backward_error fp (r + q) q C hq
        (by omega) hvalid_q
  have hgamma_nonneg :
      0 ≤ H19.Theorem19_4.gamma_tilde fp (r + q) q :=
    H19.Theorem19_4.gamma_tilde_nonneg fp hvalid_q
  have hgamma_le :
      H19.Theorem19_4.gamma_tilde fp (r + q) q ≤
        theorem20_10_householder_gammaA fp r p q := by
    simpa [H19.Theorem19_4.gamma_tilde, theorem20_10_householder_gammaA, K]
      using gamma_mono fp hidx_le hvalid_full
  rcases hqr.exists_frobNormRect_perturbation_bound hgamma_nonneg with
    ⟨DeltaC, hrep, hbound⟩
  refine ⟨DeltaC, hrep, le_trans hbound ?_⟩
  exact mul_le_mul_of_nonneg_right hgamma_le (frobNormRect_nonneg C)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete full-`A` perturbation obtained from the smaller `A Q₂`
    Householder QR backward error.

    This combines the smaller-block QR perturbation theorem with the exact
    back-transport through an orthogonal `Q`: the constructed source-coordinate
    `DeltaA` makes the trailing block of `(A + DeltaA)Q` match the computed
    Householder QR product for `A Q₂`, and it satisfies the advertised
    `gamma_tilde_mn * ||A||_F` source-shaped bound.  It is still only the
    `A`-side component of the full Theorem 20.10 certificate. -/
theorem theorem20_10_householder_AQ2_full_A_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hq : 0 < q)
    (hvalid :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q))) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A := by
  let C : Fin (r + q) → Fin q → ℝ := gqrAQ2Block A Q
  rcases theorem20_10_householder_AQ2_frob_perturbation_bound
      fp C hq hvalid with
    ⟨DeltaC, hrep, hDeltaC⟩
  rcases gqrAQ2Block_exists_full_perturbation_of_trailing_delta
      Q DeltaC hQ with
    ⟨DeltaA, hDeltaAtrail, hDeltaAnorm⟩
  refine ⟨DeltaA, ?_, ?_⟩
  · intro i j
    calc
      gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j
          = gqrAQ2Block A Q i j + DeltaC i j := hDeltaAtrail A i j
      _ = matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j := by
          simpa [C] using hrep i j
  · have hpad :
        frobNormRect (fun i : Fin (r + q) =>
          Fin.append (fun _ : Fin p => 0) (DeltaC i)) =
            frobNormRect DeltaC :=
      frobNormRect_zeroLeftCols_append DeltaC
    have hDeltaA_le_C :
        frobNormRect DeltaA ≤
          theorem20_10_householder_gammaA fp r p q * frobNormRect C := by
      rwa [hDeltaAnorm, hpad]
    have hC_le_A : frobNormRect C ≤ frobNormRect A := by
      simpa [C] using frobNormRect_gqrAQ2Block_le A Q hQ
    have hgamma_nonneg :
        0 ≤ theorem20_10_householder_gammaA fp r p q := by
      simpa [theorem20_10_householder_gammaA] using
        H19.Theorem19_4.gamma_tilde_nonneg fp hvalid
    exact le_trans hDeltaA_le_C
      (mul_le_mul_of_nonneg_left hC_le_A hgamma_nonneg)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete right-hand-side perturbation for the smaller `A Q₂`
    Householder transform used in the GQR path.

    This is the source-facing specialization of the QR module's explicit
    RHS-transform certificate to the trailing block `A Q₂`.  The bound is the
    verified recursive implementation budget for that transform; the later
    source-facing `gamma_tilde_mn * ||b||₂` absorption remains a separate
    obligation. -/
theorem theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (hready :
      HouseholderQRPanelReady fp (r + q) q (gqrAQ2Block A Q)) :
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      vecNorm2 Deltab ≤
        Real.sqrt (r + q : ℝ) *
          householderQRRhsPanelBackwardBound fp (r + q) q
            (gqrAQ2Block A Q) b := by
  simpa using
    fl_householderQRPanel_rhs_explicit_vecNorm2_perturbation_bound
      fp (r + q) q (gqrAQ2Block A Q) b hready

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    global-gamma wrapper for the `A Q₂` RHS perturbation certificate.

    A single row-count validity hypothesis supplies the readiness obligations
    for the zero-aware Householder QR panel implementation.  The norm bound is
    still the concrete recursive RHS budget, not the final printed
    `gamma_tilde_mn * ||b||₂` coefficient. -/
theorem theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound_of_global_gammaValid
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (hvalid : gammaValid fp (11 * (r + q) + 23)) :
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      vecNorm2 Deltab ≤
        Real.sqrt (r + q : ℝ) *
          householderQRRhsPanelBackwardBound fp (r + q) q
            (gqrAQ2Block A Q) b := by
  exact
    theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound
      fp A Q b
      (HouseholderQRPanelReady_of_global_gammaValid
        fp (r + q) q (r + q) (gqrAQ2Block A Q) le_rfl hvalid)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    conservative source-norm bound for the `A Q₂` RHS perturbation.

    The half-radius guard for the verified recursive RHS index supplies both
    the Householder panel readiness condition and the accumulated gamma
    comparison.  The result exposes the remaining gap to the printed
    `gamma_tilde_mn * ||b||₂` coefficient as the visible dimension-only factor
    `2 * householderQRRhsPanelGammaClosedGrowthFactor (r+q) q`. -/
theorem theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound_of_gammaFactor
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      vecNorm2 Deltab ≤
        Real.sqrt (r + q : ℝ) *
          (((2 : ℝ) *
              (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) *
              gamma fp (q * householderConstructApplyGammaIndex (r + q))) *
            vecNorm2 b) := by
  let idx : ℕ := householderQRRhsPanelGammaClosedGrowthIndex (r + q) q
  let K : ℕ := householderConstructApplyGammaIndex (r + q)
  let C : ℝ :=
    (2 : ℝ) *
      (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) *
      gamma fp (q * K)
  have hidx_valid : gammaValid fp idx := by
    unfold gammaValid
    exact lt_of_le_of_lt (by simpa [idx] using hhalf) (by norm_num)
  have hprinted_le_idx : q * K ≤ idx := by
    change q * householderConstructApplyGammaIndex (r + q) ≤
      householderQRRhsPanelGammaClosedGrowthIndex (r + q) q
    rw [householderQRRhsPanelGammaClosedGrowthIndex_eq_factor_mul_printedIndex]
    exact Nat.le_mul_of_pos_left _
      (householderQRRhsPanelGammaClosedGrowthFactor_pos
        (m := r + q) (p := q) (by omega))
  have hprinted_valid : gammaValid fp (q * K) :=
    gammaValid_mono fp hprinted_le_idx hidx_valid
  have hbase_le_K :
      11 * (r + q) + 23 ≤ K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hK_le_qK : K ≤ q * K :=
    Nat.le_mul_of_pos_left K hq
  have hbase_valid : gammaValid fp (11 * (r + q) + 23) :=
    gammaValid_mono fp
      (le_trans hbase_le_K (le_trans hK_le_qK hprinted_le_idx))
      hidx_valid
  let Cmat : Fin (r + q) → Fin q → ℝ := gqrAQ2Block A Q
  have hready :
      HouseholderQRPanelReady fp (r + q) q Cmat :=
    HouseholderQRPanelReady_of_global_gammaValid
      fp (r + q) q (r + q) Cmat le_rfl hbase_valid
  rcases
    theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound
      fp A Q b (by simpa [Cmat] using hready) with
    ⟨Deltab, hrep, hbound⟩
  have hm : 0 < r + q := by omega
  have hraw_le_inf :
      householderQRRhsPanelBackwardBound fp (r + q) q Cmat b ≤
        C * infNormVec b := by
    simpa [C, Cmat, K] using
      householderQRRhsPanelBackwardBound_le_gammaClosedGrowthFactor
        fp (r + q) q Cmat b (by omega) hm hhalf hready
  have hsqrt_nonneg : 0 ≤ Real.sqrt (r + q : ℝ) :=
    Real.sqrt_nonneg _
  have hto_inf :
      vecNorm2 Deltab ≤
        Real.sqrt (r + q : ℝ) * (C * infNormVec b) := by
    exact le_trans hbound
      (mul_le_mul_of_nonneg_left (by simpa [Cmat] using hraw_le_inf)
        hsqrt_nonneg)
  have hgamma_nonneg : 0 ≤ gamma fp (q * K) :=
    gamma_nonneg fp hprinted_valid
  have hfactor_nonneg :
      0 ≤ (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) := by
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hfactor_nonneg) hgamma_nonneg
  have hinf_le_vec : infNormVec b ≤ vecNorm2 b :=
    infNormVec_le_of_abs_le b
      (fun i => abs_coord_le_vecNorm2 b i) (vecNorm2_nonneg b)
  have hC_inf_le_vec :
      C * infNormVec b ≤ C * vecNorm2 b :=
    mul_le_mul_of_nonneg_left hinf_le_vec hC_nonneg
  refine ⟨Deltab, hrep, ?_⟩
  exact le_trans hto_inf
    (by
      simpa [C, K] using
        mul_le_mul_of_nonneg_left hC_inf_le_vec hsqrt_nonneg)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    trailing entries of the rounded Householder RHS transform for the `A Q₂`
    panel. -/
noncomputable def theorem20_10_householder_AQ2_rhs_tail
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) : Fin q → ℝ :=
  fun i : Fin q =>
    fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b
      (Fin.natAdd r i)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    conservative scalar coefficient currently proved for the rounded
    Householder RHS transform in the `A Q₂` panel. -/
noncomputable def theorem20_10_householder_rhs_conservative_gamma
    (fp : FPModel) (r _p q : ℕ) : ℝ :=
  Real.sqrt (r + q : ℝ) *
    ((2 : ℝ) *
      (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) *
      gamma fp (q * householderConstructApplyGammaIndex (r + q)))

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    conservative `A`/`b` coefficient for the rounded-Householder-RHS Part A
    route.  It preserves the printed Householder `A`-matrix coefficient while
    making the larger verified RHS coefficient explicit. -/
noncomputable def theorem20_10_householder_gammaA_conservativeRhs
    (fp : FPModel) (r p q : ℕ) : ℝ :=
  max (theorem20_10_householder_gammaA fp r p q)
    (theorem20_10_householder_rhs_conservative_gamma fp r p q)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), rounded Householder RHS
    certificate route with the currently proved conservative RHS coefficient.

    If the supplied GQR factor's `U` is the rounded Householder panel `Q` for
    `A Q₂`, then the verified RHS transform theorem supplies a `Deltab` whose
    transformed trailing block is exactly the computed RHS tail.  The matrix
    perturbation bounds and triangular preservation are discharged by the
    transformed-tail constructed-source wrapper; the RHS coefficient remains
    the explicit conservative bound
    `theorem20_10_householder_rhs_conservative_gamma`. -/
theorem theorem20_10_partA_certificate_of_constructed_source_householder_rhs_conservative_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge_matrix : gamma fp q ≤ gammaA)
    (hgammaA_ge_rhs :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i : Fin q,
        matMulVec (r + q) (matTranspose h.U)
            (fun k => b k + Deltab k) (Fin.natAdd r i) =
          theorem20_10_householder_AQ2_rhs_tail fp A h.Q b i) ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
        (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
        (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
        frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
        frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
        Nonempty
          (Theorem20_10PartAPerturbationCertificate A B b d
            (theorem20_10_gqr_xhat_of_transformed_tail fp h
              (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d)
            gammaA gammaB) := by
  rcases
    theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound_of_gammaFactor
      fp A h.Q b hq hhalf with
    ⟨Deltab, hrep, hDeltab_raw⟩
  have hDeltab_conservative :
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b := by
    simpa [theorem20_10_householder_rhs_conservative_gamma, mul_assoc]
      using hDeltab_raw
  have hDeltab :
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b :=
    le_trans hDeltab_conservative
      (mul_le_mul_of_nonneg_right hgammaA_ge_rhs (vecNorm2_nonneg b))
  have hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose h.U)
          (fun k => b k + Deltab k) (Fin.natAdd r i) =
        theorem20_10_householder_AQ2_rhs_tail fp A h.Q b i := by
    intro i
    simpa [theorem20_10_householder_AQ2_rhs_tail, hUfl] using
      (hrep (Fin.natAdd r i)).symm
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds_transformed_tail
      fp h (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) b d
      gammaA gammaB Deltab hgammaB_nonneg hgammaA_ge_matrix hgammaB_ge
      hSdiag hL22diag hvalid2S hvalid2L22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hcert⟩
  exact
    ⟨Deltab, hb_tail, hDeltab, DeltaS, DeltaL22,
      hDeltaSbound, hDeltaL22bound, hDeltaSfrob, hDeltaL22frob,
      hcert hDeltab hb_tail⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), rounded Householder RHS
    mixed-stability route with the currently proved conservative RHS
    coefficient.

    This unwraps
    `theorem20_10_partA_certificate_of_constructed_source_householder_rhs_conservative_bound`
    through the generic Part A certificate-to-core theorem.  The result is an
    honest computed-RHS Part A surface: the computed vector uses the rounded
    Householder RHS tail, while the `Deltab` coefficient is the explicit
    conservative coefficient supplied through `gammaA`. -/
theorem theorem20_10_partA_mixed_stability_of_constructed_source_householder_rhs_conservative_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge_matrix : gamma fp q ≤ gammaA)
    (hgammaA_ge_rhs :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat_of_transformed_tail fp h
            (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d j =
          x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = d ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x0)) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_source_householder_rhs_conservative_bound
      fp h b d gammaA gammaB hUfl hq hhalf hgammaB_nonneg
      hgammaA_ge_matrix hgammaA_ge_rhs hgammaB_ge
      hSdiag hL22diag hvalid2S hvalid2L22 with
    ⟨_Deltab, _hb_tail, _hDeltab, _DeltaS, _DeltaL22,
      _hDeltaSbound, _hDeltaL22bound, _hDeltaSfrob, _hDeltaL22frob,
      hcert⟩
  rcases hcert with ⟨cert⟩
  have hcore :=
    theorem20_10_partA_mixed_stability_of_perturbation_certificate
      A B b d
      (theorem20_10_gqr_xhat_of_transformed_tail fp h
        (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d)
      cert
  dsimp at hcore
  rcases hcore with
    ⟨DeltaA, DeltaB, Deltab, DeltaX, x,
      hDeltaAeq, hDeltaBeq, hDeltabeq, hxhat, hDeltaX,
      hDeltaA, hDeltab, hDeltaB, hx, hmethod⟩
  refine
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, DeltaX, x,
      hxhat, hDeltaX, ?_, ?_, ?_, hx, hmethod⟩
  · simpa [hDeltaAeq] using hDeltaA
  · simpa [hDeltabeq] using hDeltab
  · simpa [hDeltaBeq] using hDeltaB

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), rounded Householder RHS
    mixed-stability route with source-facing conservative gamma coefficients.

    Compared with
    `theorem20_10_partA_mixed_stability_of_constructed_source_householder_rhs_conservative_bound`,
    this theorem derives the matrix and triangular-solve gamma side conditions
    from the standard Householder validity hypotheses.  The `A`/`b`
    coefficient is
    `theorem20_10_householder_gammaA_conservativeRhs`, the maximum of the
    printed matrix coefficient and the verified conservative RHS coefficient. -/
theorem theorem20_10_partA_mixed_stability_of_constructed_source_householder_rhs_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat_of_transformed_tail fp h
            (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d j =
          x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤
        theorem20_10_householder_gammaB fp r p q * vecNorm2 x ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          vecNorm2 b ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = d ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x0)) := by
  have hKA_ge_two : 2 ≤ householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_ge_two : 2 ≤ householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    omega
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    omega
  have hvalid2S : gammaValid fp (2 * p) := by
    apply gammaValid_mono fp _ hvalidB
    calc
      2 * p = p * 2 := by omega
      _ ≤ p * householderConstructApplyGammaIndex (p + q) :=
          Nat.mul_le_mul_left p hKB_ge_two
  have hvalid2L22 : gammaValid fp (2 * q) := by
    apply gammaValid_mono fp _ hvalidA
    calc
      2 * q ≤ 2 * (p + q) := Nat.mul_le_mul_left 2 (by omega)
      _ = (p + q) * 2 := by omega
      _ ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
          Nat.mul_le_mul_left (p + q) hKA_ge_two
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hidxA_ge_q :
      q ≤ (p + q) * householderConstructApplyGammaIndex (r + q) := by
    exact le_trans (by omega)
      (Nat.le_mul_of_pos_right (p + q) hKA_pos)
  have hidxB_ge_p :
      p ≤ p * householderConstructApplyGammaIndex (p + q) :=
    Nat.le_mul_of_pos_right p hKB_pos
  have hgammaA_printed_ge :
      gamma fp q ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxA_ge_q hvalidA
  have hgammaA_ge_matrix :
      gamma fp q ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q :=
    le_trans hgammaA_printed_ge
      (le_max_left _ _)
  have hgammaA_ge_rhs :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q :=
    le_max_right _ _
  have hgammaB_ge :
      gamma fp p ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxB_ge_p hvalidB
  exact
    theorem20_10_partA_mixed_stability_of_constructed_source_householder_rhs_conservative_bound
      fp h b d
      (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
      (theorem20_10_householder_gammaB fp r p q)
      hUfl hq hhalf hgammaB_nonneg hgammaA_ge_matrix hgammaA_ge_rhs
      hgammaB_ge hSdiag hL22diag hvalid2S hvalid2L22

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete Householder QR perturbation bound for the `Bᵀ` triangularization
    step in the GQR path.

    Applying the Chapter 19 Householder QR backward-error theorem to
    `Bᵀ : R^((p+q)×p)` gives a perturbation of `B` with the advertised
    `gamma_tilde_np` Frobenius bound.  This is a genuine computed-path
    dependency for the Theorem 20.10 certificates; it does not yet prove the
    downstream triangular-solve perturbations or rank preservation. -/
theorem theorem20_10_householder_B_transpose_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (B : Fin p → Fin (p + q) → ℝ)
    (hp : 0 < p)
    (hvalid :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B := by
  have hqr :
      H19.Theorem19_4.HouseholderQRBackwardError (p + q) p (finiteTranspose B)
        (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
        (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B))
        (theorem20_10_householder_gammaB fp r p q) := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.householder_qr_backward_error
        fp (p + q) p (finiteTranspose B) hp (Nat.le_add_right p q) hvalid
  have hgamma_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalid
  rcases
    hqr.exists_frobNormRect_perturbation_bound hgamma_nonneg with
    ⟨DeltaBT, hrep, hbound⟩
  refine ⟨finiteTranspose DeltaBT, ?_, ?_⟩
  · intro i j
    simpa [finiteTranspose] using hrep j i
  · simpa [theorem20_10_householder_gammaB, frobNormRect_finiteTranspose]
      using hbound

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    a constraint-matrix perturbation gives the corresponding constraint
    right-hand-side perturbation at a proposed computed vector.

    Taking `Deltad = DeltaB * xhat` gives the exact action identity for
    `(B + DeltaB) xhat` and the displayed Frobenius/vector norm bound used in
    the backward-error branch. -/
theorem theorem20_10_constraint_rhs_perturbation_bound_of_DeltaB
    {p q : ℕ}
    (B DeltaB : Fin p → Fin (p + q) → ℝ)
    (xhat : Fin (p + q) → ℝ)
    {gammaB : ℝ}
    (hDeltaB : frobNormRect DeltaB ≤ gammaB * frobNormRect B) :
    ∃ Deltad : Fin p → ℝ,
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat := by
  refine ⟨rectMatMulVec DeltaB xhat, ?_, ?_⟩
  · intro i
    unfold rectMatMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · exact le_trans
      (vecNorm2_rectMatMulVec_le_frobNormRect_mul DeltaB xhat)
      (mul_le_mul_of_nonneg_right hDeltaB (vecNorm2_nonneg xhat))

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), Part A certificate to
    Part B certificate bridge.

    A Part A mixed-stability certificate already supplies the source-shaped
    `DeltaA`, `DeltaB`, and `Deltab` bounds and the perturbed rank hypotheses.
    For the Part B backward-error certificate, the only additional perturbation
    component is the constraint right-hand side.  Taking
    `Deltad = DeltaB * xhat` gives the required source-shaped `Deltad` bound;
    the `Deltab` bound is weakened by adding the nonnegative
    `gammaB * ||A||_F * ||xhat||_2` term from the Part B statement. -/
theorem theorem20_10_partB_certificate_of_partA_certificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    {gammaA gammaB : ℝ}
    (hgammaB_nonneg : 0 ≤ gammaB)
    (cert :
      Theorem20_10PartAPerturbationCertificate A B b d xhat gammaA gammaB) :
    ∃ Deltad : Fin p → ℝ,
      (∀ i,
        rectMatMulVec (fun i j => B i j + cert.DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      Nonempty
        (Theorem20_10PartBPerturbationCertificate A B b d xhat
          gammaA gammaB) := by
  rcases theorem20_10_constraint_rhs_perturbation_bound_of_DeltaB
      B cert.DeltaB xhat cert.hDeltaB with
    ⟨Deltad, hDeltad_action, hDeltad⟩
  have htail_nonneg :
      0 ≤ gammaB * frobNormRect A * vecNorm2 xhat := by
    exact mul_nonneg
      (mul_nonneg hgammaB_nonneg (frobNormRect_nonneg A))
      (vecNorm2_nonneg xhat)
  have hDeltab :
      vecNorm2 cert.Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat :=
    le_trans cert.hDeltab (le_add_of_nonneg_right htail_nonneg)
  refine ⟨Deltad, hDeltad_action, hDeltad, ?_⟩
  exact
    ⟨{ DeltaA := cert.DeltaA
       DeltaB := cert.DeltaB
       Deltab := cert.Deltab
       Deltad := Deltad
       hB := cert.hB
       hstack := cert.hstack
       hDeltaA := cert.hDeltaA
       hDeltaB := cert.hDeltaB
       hDeltab := hDeltab
       hDeltad := hDeltad }⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete Householder `Bᵀ` perturbation together with the induced
    constraint right-hand-side perturbation bound.

    This packages the already proved `DeltaB` Frobenius bound with
    `Deltad = DeltaB * xhat`, giving the source-shaped
    `||Deltad||₂ <= gamma_tilde_np ||B||_F ||xhat||₂` component needed by the
    backward-error certificate.  It still does not identify the computed
    `xhat` or prove perturbed rank preservation. -/
theorem theorem20_10_householder_B_transpose_Deltad_bound
    {r p q : ℕ} (fp : FPModel)
    (B : Fin p → Fin (p + q) → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hp : 0 < p)
    (hvalid :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    ∃ (DeltaB : Fin p → Fin (p + q) → ℝ) (Deltad : Fin p → ℝ),
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltad ≤
        theorem20_10_householder_gammaB fp r p q *
          frobNormRect B * vecNorm2 xhat := by
  rcases theorem20_10_householder_B_transpose_frob_perturbation_bound
      fp B hp hvalid with
    ⟨DeltaB, hDeltaBrep, hDeltaBbound⟩
  rcases theorem20_10_constraint_rhs_perturbation_bound_of_DeltaB
      B DeltaB xhat hDeltaBbound with
    ⟨Deltad, hDeltadrep, hDeltadbound⟩
  exact ⟨DeltaB, Deltad, hDeltaBrep, hDeltadrep,
    hDeltaBbound, hDeltadbound⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete Householder perturbation components for the computed GQR path.

    This packages the four currently verified component perturbations:
    the full-source `DeltaA` transported from the trailing `A Q₂` QR step,
    the `DeltaB` perturbation from the `Bᵀ` QR step, the concrete RHS
    perturbation `Deltab` for the `A Q₂` Householder transform, and the induced
    constraint perturbation `Deltad = DeltaB*xhat`.  The `Deltab` coefficient is
    still the conservative recursive RHS factor, so this theorem is a concrete
    component package, not yet the final printed Theorem 20.10 certificate. -/
theorem theorem20_10_householder_concrete_perturbation_components_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        Real.sqrt (r + q : ℝ) *
          (((2 : ℝ) *
              (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) *
              gamma fp (q * householderConstructApplyGammaIndex (r + q))) *
            vecNorm2 b) ∧
      vecNorm2 Deltad ≤
        theorem20_10_householder_gammaB fp r p q *
          frobNormRect B * vecNorm2 xhat := by
  rcases theorem20_10_householder_AQ2_full_A_frob_perturbation_bound
      fp A Q hQ hq hvalidA with
    ⟨DeltaA, hDeltaArep, hDeltaAbound⟩
  rcases theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound_of_gammaFactor
      fp A Q b hq hhalf with
    ⟨Deltab, hDeltabrep, hDeltabbound⟩
  rcases theorem20_10_householder_B_transpose_Deltad_bound
      fp B xhat hp hvalidB with
    ⟨DeltaB, Deltad, hDeltaBrep, hDeltadrep, hDeltaBbound, hDeltadbound⟩
  exact
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaAbound, hDeltaBbound,
      hDeltabbound, hDeltadbound⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), concrete Householder
    component package promoted to the backward-error certificate boundary.

    The verified Householder QR perturbation components already provide
    `DeltaA`, `DeltaB`, `Deltab`, and `Deltad` with source-shaped bounds.  This
    theorem packages those witnesses into the Part B certificate as soon as the
    induced perturbed matrices are known to keep the source rank assumptions.
    Thus the remaining Part B obstruction is isolated to rank preservation and
    computed-vector identification, not to the four finite-precision component
    bounds. -/
theorem theorem20_10_partB_certificate_of_householder_components_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            vecNorm2 b +
          theorem20_10_householder_gammaB fp r p q *
            frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤
        theorem20_10_householder_gammaB fp r p q *
          frobNormRect B * vecNorm2 xhat ∧
      (LSEFullRowRank (fun i j => B i j + DeltaB i j) →
       LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j) →
       Nonempty
        (Theorem20_10PartBPerturbationCertificate A B b d xhat
          (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q))) := by
  rcases theorem20_10_householder_concrete_perturbation_components_bound
      fp A B Q b xhat hQ hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaAraw, hDeltaB, hDeltabraw,
      hDeltad⟩
  have hDeltaA :
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A := by
    exact le_trans hDeltaAraw
      (mul_le_mul_of_nonneg_right
        (le_max_left
          (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_rhs_conservative_gamma fp r p q))
        (frobNormRect_nonneg A))
  have hDeltab_conservative :
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b := by
    simpa [theorem20_10_householder_rhs_conservative_gamma, mul_assoc]
      using hDeltabraw
  have hDeltab_first :
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          vecNorm2 b := by
    exact le_trans hDeltab_conservative
      (mul_le_mul_of_nonneg_right
        (le_max_right
          (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_rhs_conservative_gamma fp r p q))
        (vecNorm2_nonneg b))
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have htail_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q *
          frobNormRect A * vecNorm2 xhat := by
    exact mul_nonneg
      (mul_nonneg hgammaB_nonneg (frobNormRect_nonneg A))
      (vecNorm2_nonneg xhat)
  have hDeltab :
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            vecNorm2 b +
          theorem20_10_householder_gammaB fp r p q *
            frobNormRect A * vecNorm2 xhat :=
    le_trans hDeltab_first (le_add_of_nonneg_right htail_nonneg)
  refine
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaA, hDeltaB, hDeltab, hDeltad, ?_⟩
  intro hB hstack
  exact
    ⟨{ DeltaA := DeltaA
       DeltaB := DeltaB
       Deltab := Deltab
       Deltad := Deltad
       hB := hB
       hstack := hstack
       hDeltaA := hDeltaA
       hDeltaB := hDeltaB
       hDeltab := hDeltab
       hDeltad := hDeltad }⟩

/-- Theorem 20.10(a) certificate handoff specialized to the Householder
    `gamma_tilde_mn` and `gamma_tilde_np` coefficients. -/
theorem theorem20_10_partA_mixed_stability_of_householder_gamma_certificate
    {r p q : ℕ}
    (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (cert :
      Theorem20_10PartAPerturbationCertificate A B b d xhat
        (theorem20_10_householder_gammaA fp r p q)
        (theorem20_10_householder_gammaB fp r p q)) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + cert.DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + cert.DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + cert.Deltab i
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      DeltaA = cert.DeltaA ∧
      DeltaB = cert.DeltaB ∧
      Deltab = cert.Deltab ∧
      (∀ j : Fin (p + q), xhat j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤
        theorem20_10_householder_gammaB fp r p q * vecNorm2 x ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA fp r p q * vecNorm2 b ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      IsLSEMinimizer Apert bpert Bpert d x ∧
      (∃ h : GeneralizedQRFactorization r p q Apert Bpert,
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec h.S yz.1 = d ∧
          rectMatMulVec h.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
                rectMatMulVec h.L21 yz.1 i) ∧
          IsLSEMinimizer Apert bpert Bpert d
            (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert d x0)) :=
  theorem20_10_partA_mixed_stability_of_perturbation_certificate
    A B b d xhat cert

/-- Theorem 20.10(a), exact transformed-RHS constructed-source route specialized
    to the Householder `gamma_tilde_mn` and `gamma_tilde_np` coefficients.

    This is the strongest currently proved source-facing Part A theorem for the
    supplied-GQR path: the matrix perturbations and triangular-solve effects are
    constructed and bounded with the printed coefficient names.  The rounded
    Householder RHS-transform bridge remains separate, so this theorem uses the
    exact transformed RHS named by `theorem20_10_gqr_xhat`. -/
theorem theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs_householder_gamma
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat fp h b d j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤
        theorem20_10_householder_gammaB fp r p q * vecNorm2 x ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA fp r p q * vecNorm2 b ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = d ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x0)) := by
  have hKA_ge_two : 2 ≤ householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_ge_two : 2 ≤ householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    omega
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    omega
  have hvalid2S : gammaValid fp (2 * p) := by
    apply gammaValid_mono fp _ hvalidB
    calc
      2 * p = p * 2 := by omega
      _ ≤ p * householderConstructApplyGammaIndex (p + q) :=
          Nat.mul_le_mul_left p hKB_ge_two
  have hvalid2L22 : gammaValid fp (2 * q) := by
    apply gammaValid_mono fp _ hvalidA
    calc
      2 * q ≤ 2 * (p + q) := Nat.mul_le_mul_left 2 (by omega)
      _ = (p + q) * 2 := by omega
      _ ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
          Nat.mul_le_mul_left (p + q) hKA_ge_two
  have hgammaA_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidA
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hidxA_ge_q :
      q ≤ (p + q) * householderConstructApplyGammaIndex (r + q) := by
    exact le_trans (by omega)
      (Nat.le_mul_of_pos_right (p + q) hKA_pos)
  have hidxB_ge_p :
      p ≤ p * householderConstructApplyGammaIndex (p + q) :=
    Nat.le_mul_of_pos_right p hKB_pos
  have hgammaA_ge :
      gamma fp q ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxA_ge_q hvalidA
  have hgammaB_ge :
      gamma fp p ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxB_ge_p hvalidB
  exact
    theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs
      fp h b d
      (theorem20_10_householder_gammaA fp r p q)
      (theorem20_10_householder_gammaB fp r p q)
      hgammaA_nonneg hgammaB_nonneg hgammaA_ge hgammaB_ge
      hSdiag hL22diag hvalid2S hvalid2L22

/-- Theorem 20.10(b) certificate handoff specialized to the Householder
    `gamma_tilde_mn` and `gamma_tilde_np` coefficients. -/
theorem theorem20_10_partB_backward_error_of_householder_gamma_certificate
    {r p q : ℕ}
    (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (cert :
      Theorem20_10PartBPerturbationCertificate A B b d xhat
        (theorem20_10_householder_gammaA fp r p q)
        (theorem20_10_householder_gammaB fp r p q)) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + cert.DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + cert.DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + cert.Deltab i
    let dpert : Fin p → ℝ := fun i => d i + cert.Deltad i
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      DeltaA = cert.DeltaA ∧
      DeltaB = cert.DeltaB ∧
      Deltab = cert.Deltab ∧
      Deltad = cert.Deltad ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA fp r p q * vecNorm2 b +
          theorem20_10_householder_gammaB fp r p q *
            frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤
        theorem20_10_householder_gammaB fp r p q *
          frobNormRect B * vecNorm2 xhat ∧
      (∃ h : GeneralizedQRFactorization r p q Apert Bpert,
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec h.S yz.1 = dpert ∧
          rectMatMulVec h.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
                rectMatMulVec h.L21 yz.1 i) ∧
          IsLSEMinimizer Apert bpert Bpert dpert
            (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert dpert x)) :=
  theorem20_10_partB_backward_error_of_perturbation_certificate
    A B b d xhat cert

end LeanFpAnalysis.FP
