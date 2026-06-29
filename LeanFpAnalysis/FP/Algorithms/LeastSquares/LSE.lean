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

end LeanFpAnalysis.FP
