/-
Analysis/SylvesterSchurExistence.lean

Complex-path Schur existence for the Chapter 16 Sylvester equation
(Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Section 16.2, equations (16.4)-(16.6)).

MOTIVATION / HONEST SCOPE.

The real-valued Chapter 16 development
(`FP/Algorithms/Sylvester/Higham16.lean`,
`FP/Algorithms/Sylvester/Higham16Spectrum.lean`) proves the Bartels-Stewart
triangular solve only *conditionally* on SUPPLIED Schur factors: the theorem
`existsUnique_isSylvesterSolutionRect_schurTriangular` requires the caller to
hand over real orthogonal `U, V`, a real matrix `R` with `A = U R Uᵀ`, and a
real UPPER-TRIANGULAR `S` with `B = V S Vᵀ`.  That "supplied factors" hypothesis
is genuine and unavoidable there, because a real matrix in general has NO real
upper-triangular Schur form: the real Schur form of Higham (16.4) is only
*quasi*-triangular (2x2 real blocks for complex-conjugate eigenpairs).  The real
file therefore cannot discharge its own supplied-triangular hypothesis, and does
not claim to.

Over `ℂ`, by contrast, the classical Schur triangulation
`LeanFpAnalysis.FP.schur_triangulation` (`FP/Analysis/SchurTriangulation.lean`)
gives, for EVERY complex square matrix, a genuine unitary `U` and a genuine
upper-triangular `T` with `Uᴴ A U = T`.  This file uses that primitive to turn
the complex analogue of the supplied-triangular hypothesis into an
*unconditional existence* statement, and then proves unique solvability of the
complex Sylvester equation `A X - X B = C`.

WHAT IS UNCONDITIONAL HERE (no supplied factors):

* `complexSylvester_schur_factors_exist` — for any `A : ℂ^{m×m}`,
  `B : ℂ^{n×n}` there exist a unitary `U` and upper-triangular `R` with
  `Uᴴ A U = R`, and a unitary `V` and upper-triangular `S` with `Vᴴ B V = S`.
  This is exactly the datum the real file must *assume*; over `ℂ` it is proved.

WHAT REMAINS AN EXPLICIT, NON-TAUTOLOGICAL HYPOTHESIS:

* the per-column shift nonsingularity `det (R - s_kk • I) ≠ 0`.  This is a
  condition on the DIAGONAL ENTRIES of the triangular factors, i.e. on the
  eigenvalues `λ_i(A) ≠ μ_k(B)` (the Sylvester separation / no-common-eigenvalue
  condition of (16.3)).  It is emphatically NOT the conclusion in disguise: it
  constrains only the (supplied-by-Schur) eigenvalues, not the solution `X`.  The
  headline theorem `complexSylvester_exists_unique_of_schur_shift` exposes it as
  a hypothesis phrased in terms of the Schur factors produced by the existence
  step, and states honestly that this is the residual assumption.

WHAT IS NOT CLAIMED:

* No real Schur form, no real quasi-triangular (2x2 block) solve of Higham
  (16.4)/(16.7)-(16.8): those are over `ℝ` and are genuinely different objects.
  This file does not touch, restate, or overclaim the real results.
* No floating-point rounding analysis; all arithmetic is exact over `ℂ`.
* No spectral converse claim beyond what the shift hypothesis encodes.

Everything is stated for the standard Mathlib matrix type `Matrix (Fin _) (Fin _)
ℂ` with ordinary matrix multiplication `*` and `Matrix.mulVec`, so that the
complex Schur primitive (`Uᴴ * A * U = T`) plugs in directly.
-/

import LeanFpAnalysis.FP.Analysis.SchurTriangulation
import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

open scoped BigOperators Matrix

namespace LeanFpAnalysis.FP

-- ============================================================
-- The complex Sylvester operator and solution predicate
-- ============================================================

/-- Higham, 2nd ed., Chapter 16, equation (16.1), complex square form:
    the Sylvester operator `X ↦ A X - X B` on complex square matrices, using
    ordinary Mathlib matrix multiplication so that the complex Schur factors
    `Uᴴ A U` plug in directly. -/
noncomputable def complexSylvesterOp {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  A * X - X * B

/-- Higham, 2nd ed., Chapter 16, equation (16.1), complex square form:
    the predicate `A X - X B = C`. -/
def IsComplexSylvesterSolution {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (C X : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  complexSylvesterOp A B X = C

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2), complex vec/Kronecker
    coefficient `I_n kron A - B^T kron I_m`.  The product index follows
    Mathlib's column-stacking convention: `(j,i)` denotes entry `(i,j)`. -/
noncomputable def complexSylvesterVecCoeff {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) A -
    Matrix.kronecker (Matrix.transpose B) (1 : Matrix (Fin m) (Fin m) ℂ)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.4): upper triangularity for a
    complex square matrix (all strictly-below-diagonal entries vanish).  This is
    the structure produced unconditionally by `schur_triangulation` over `ℂ`. -/
def IsUpperTriangularC {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j : Fin n, j < i → T i j = 0

private def complexSylvesterVecCoeffDualIndexEquiv (m n : ℕ) :
    (Fin n × Fin m) ≃ ((Fin n)ᵒᵈ ×ₗ Fin m) :=
  (Equiv.prodCongr OrderDual.toDual (Equiv.refl (Fin m))).trans toLex

/-- Reversing the block coordinate makes the complex triangular Sylvester vec
    coefficient upper triangular when both Schur factors are upper triangular. -/
theorem complexSylvesterVecCoeff_reindex_upperTriangular {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    (Matrix.reindex (complexSylvesterVecCoeffDualIndexEquiv m n)
        (complexSylvesterVecCoeffDualIndexEquiv m n)
        (complexSylvesterVecCoeff A B)).BlockTriangular id := by
  let e := complexSylvesterVecCoeffDualIndexEquiv m n
  intro x y hyx
  rcases (Prod.Lex.lt_iff.mp hyx) with hblock | ⟨_, hrow⟩
  · have hBzero :
        B ((e.symm y).1) ((e.symm x).1) = 0 := by
      exact hB _ _ (by simpa [e, complexSylvesterVecCoeffDualIndexEquiv] using hblock)
    have hblock_ne :
        (e.symm x).1 ≠ (e.symm y).1 := by
      intro hxy
      have : (ofLex y).1 = (ofLex x).1 := by
        simpa [e, complexSylvesterVecCoeffDualIndexEquiv] using
          congrArg OrderDual.toDual hxy.symm
      exact ne_of_lt hblock this
    simp [e, complexSylvesterVecCoeff, Matrix.reindex_apply, Matrix.sub_apply,
      Matrix.kronecker, Matrix.transpose_apply, hBzero, hblock_ne]
  · have hAzero :
        A ((e.symm x).2) ((e.symm y).2) = 0 := by
      exact hA _ _ hrow
    have hrow_ne :
        (e.symm x).2 ≠ (e.symm y).2 := by
      intro hxy
      have : (ofLex y).2 = (ofLex x).2 := by
        simpa [e, complexSylvesterVecCoeffDualIndexEquiv] using hxy.symm
      exact ne_of_lt hrow this
    simp [e, complexSylvesterVecCoeff, Matrix.reindex_apply, Matrix.sub_apply,
      Matrix.kronecker, Matrix.transpose_apply, hAzero, hrow_ne]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), supplied complex
    triangular case: the vec/Kronecker Sylvester coefficient determinant is
    the product of the pairwise Schur diagonal differences. -/
theorem complexSylvesterVecCoeff_det_eq_prod_of_upperTriangular {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B) =
      ∏ p : Prod (Fin n) (Fin m), (A p.2 p.2 - B p.1 p.1) := by
  let e := complexSylvesterVecCoeffDualIndexEquiv m n
  have htri :
      (Matrix.reindex e e (complexSylvesterVecCoeff A B)).BlockTriangular id :=
    complexSylvesterVecCoeff_reindex_upperTriangular A B hA hB
  have hdet_reindex :
      Matrix.det (Matrix.reindex e e (complexSylvesterVecCoeff A B)) =
        Matrix.det (complexSylvesterVecCoeff A B) :=
    Matrix.det_reindex_self e (complexSylvesterVecCoeff A B)
  rw [← hdet_reindex, Matrix.det_of_upperTriangular htri]
  have hdiag :
      (fun x : (Fin n)ᵒᵈ ×ₗ Fin m =>
        Matrix.reindex e e (complexSylvesterVecCoeff A B) x x) =
      fun x : (Fin n)ᵒᵈ ×ₗ Fin m =>
        A ((e.symm x).2) ((e.symm x).2) -
          B ((e.symm x).1) ((e.symm x).1) := by
    funext x
    simp [e, complexSylvesterVecCoeff, Matrix.reindex_apply, Matrix.kronecker,
      Matrix.transpose_apply]
  rw [hdiag]
  exact e.symm.prod_comp
    (fun p : Prod (Fin n) (Fin m) => A p.2 p.2 - B p.1 p.1)

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), supplied complex
    triangular case: determinant nonsingularity is equivalent to pairwise
    separation of the triangular diagonal entries. -/
theorem complexSylvesterVecCoeff_det_ne_zero_iff_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 ↔
      ∀ i : Fin m, ∀ j : Fin n, A i i ≠ B j j := by
  rw [complexSylvesterVecCoeff_det_eq_prod_of_upperTriangular A B hA hB]
  constructor
  · intro hdet i j hij
    have hfactor :=
      (Finset.prod_ne_zero_iff.mp hdet) (j, i) (Finset.mem_univ _)
    exact hfactor (sub_eq_zero.mpr hij)
  · intro hsep
    exact Finset.prod_ne_zero_iff.mpr
      (fun p _ => sub_ne_zero.mpr (hsep p.2 p.1))

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), supplied complex
    triangular determinant-nonsingularity consequence from pairwise diagonal
    separation. -/
theorem complexSylvesterVecCoeff_det_ne_zero_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B)
    (hsep : ∀ i : Fin m, ∀ j : Fin n, A i i ≠ B j j) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 := by
  exact
    (complexSylvesterVecCoeff_det_ne_zero_iff_of_upperTriangular_diagonal_separation
      A B hA hB).mpr hsep

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2): source-numbered alias for
    the complex vec/Kronecker Sylvester coefficient. -/
theorem H16_eq16_2_complexSylvesterVecCoeff {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    complexSylvesterVecCoeff A B =
      Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) A -
        Matrix.kronecker (Matrix.transpose B) (1 : Matrix (Fin m) (Fin m) ℂ) :=
  rfl

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered alias for
    the supplied complex triangular vec/Kronecker determinant product. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_det_eq_prod_of_upperTriangular
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B) =
      ∏ p : Prod (Fin n) (Fin m), (A p.2 p.2 - B p.1 p.1) :=
  complexSylvesterVecCoeff_det_eq_prod_of_upperTriangular A B hA hB

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered alias for
    the supplied complex triangular determinant/separation equivalence. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_det_ne_zero_iff_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 ↔
      ∀ i : Fin m, ∀ j : Fin n, A i i ≠ B j j :=
  complexSylvesterVecCoeff_det_ne_zero_iff_of_upperTriangular_diagonal_separation
    A B hA hB

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered alias for
    supplied complex triangular nonsingularity from diagonal separation. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_det_ne_zero_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B)
    (hsep : ∀ i : Fin m, ∀ j : Fin n, A i i ≠ B j j) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 :=
  complexSylvesterVecCoeff_det_ne_zero_of_upperTriangular_diagonal_separation
    A B hA hB hsep

-- ============================================================
-- Complex Schur factors exist unconditionally
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equation (16.4), complex Schur factors:
    for any complex square matrices `A` and `B` there exist unitary `U`, `V` and
    upper-triangular `R`, `S` with `Uᴴ A U = R` and `Vᴴ B V = S`.

    This is UNCONDITIONAL: it is exactly the datum that the real-valued file
    `Higham16Spectrum.lean` must supply as a hypothesis, discharged here by the
    complex Schur triangulation `schur_triangulation`.  (Over `ℝ` the analogous
    statement is false — the real Schur form is only quasi-triangular — so no
    real theorem is being restated or overclaimed.) -/
theorem complexSylvester_schur_factors_exist {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (U : Matrix (Fin m) (Fin m) ℂ) (R : Matrix (Fin m) (Fin m) ℂ)
      (V : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin n) (Fin n) ℂ),
      U ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ Uᴴ * A * U = R ∧ IsUpperTriangularC R ∧
      V ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ Vᴴ * B * V = S ∧ IsUpperTriangularC S := by
  obtain ⟨U, R, hUu, hUeq, hRtri⟩ := schur_triangulation A
  obtain ⟨V, S, hVu, hVeq, hStri⟩ := schur_triangulation B
  exact ⟨U, R, V, S, hUu, hUeq, hRtri, hVu, hVeq, hStri⟩

-- ============================================================
-- The transformed equation R Y - Y S = C' in Schur coordinates
-- ============================================================

/-- Conjugation of the Sylvester operator by supplied unitary factors, complex
    form of Higham (16.5).  With `Uᴴ A U = R`, `Vᴴ B V = S`, and `X = U Y Vᴴ`,
    the operator transforms as `A X - X B = U (R Y - Y S) Vᴴ`. -/
theorem complexSylvesterOp_conj {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (Y : Matrix (Fin m) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hR : Uᴴ * A * U = R) (hS : Vᴴ * B * V = S) :
    complexSylvesterOp A B (U * Y * Vᴴ) =
      U * (complexSylvesterOp R S Y) * Vᴴ := by
  have hUU : U * Uᴴ = 1 := by
    have := hU.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hVV : Vᴴ * V = 1 := by
    have := hV.1; rwa [Matrix.star_eq_conjTranspose] at this
  -- express R and S back through A, B
  subst hR
  subst hS
  simp only [complexSylvesterOp, Matrix.mul_sub, Matrix.sub_mul]
  -- U (Uᴴ A U Y - Y Vᴴ B V) Vᴴ = A (U Y Vᴴ) - (U Y Vᴴ) B
  have e1 : U * (Uᴴ * A * U * Y) * Vᴴ = A * (U * Y * Vᴴ) := by
    have : U * (Uᴴ * A * U * Y) * Vᴴ = (U * Uᴴ) * A * (U * Y * Vᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [this, hUU, Matrix.one_mul]
  have e2 : U * (Y * (Vᴴ * B * V)) * Vᴴ = (U * Y * Vᴴ) * B := by
    have : U * (Y * (Vᴴ * B * V)) * Vᴴ = (U * Y * Vᴴ) * B * (V * Vᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [this]
    have hVV' : V * Vᴴ = 1 := by
      have := hV.2; rwa [Matrix.star_eq_conjTranspose] at this
    rw [hVV', Matrix.mul_one]
  rw [e1, e2]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.5), complex form:
    with supplied unitary factors, `X = U Y Vᴴ` solves `A X - X B = C` iff `Y`
    solves the transformed equation `R Y - Y S = Uᴴ C V`. -/
theorem isComplexSylvesterSolution_conj_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C Y : Matrix (Fin m) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hR : Uᴴ * A * U = R) (hS : Vᴴ * B * V = S) :
    IsComplexSylvesterSolution A B C (U * Y * Vᴴ) ↔
      IsComplexSylvesterSolution R S (Uᴴ * C * V) Y := by
  have hUU : U * Uᴴ = 1 := by
    have := hU.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hUhU : Uᴴ * U = 1 := by
    have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hVV : V * Vᴴ = 1 := by
    have := hV.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hVhV : Vᴴ * V = 1 := by
    have := hV.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hconj := complexSylvesterOp_conj A B U V R S Y hU hV hR hS
  constructor
  · intro h
    -- h : A (U Y Vᴴ) - (U Y Vᴴ) B = C, i.e. U (RY - YS) Vᴴ = C
    unfold IsComplexSylvesterSolution at h ⊢
    rw [hconj] at h
    -- Uᴴ (U (RY-YS) Vᴴ) V = RY - YS ; Uᴴ C V is RHS
    have := congrArg (fun M => Uᴴ * M * V) h
    simp only at this
    rw [← this]
    have lhs :
        Uᴴ * (U * complexSylvesterOp R S Y * Vᴴ) * V =
          complexSylvesterOp R S Y := by
      have step : Uᴴ * (U * complexSylvesterOp R S Y * Vᴴ) * V =
          (Uᴴ * U) * complexSylvesterOp R S Y * (Vᴴ * V) := by
        simp only [Matrix.mul_assoc]
      rw [step, hUhU, hVhV, Matrix.one_mul, Matrix.mul_one]
    rw [lhs]
  · intro h
    unfold IsComplexSylvesterSolution at h ⊢
    rw [hconj, h]
    -- U (Uᴴ C V) Vᴴ = C
    have step : U * (Uᴴ * C * V) * Vᴴ = (U * Uᴴ) * C * (V * Vᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [step, hUU, hVV, Matrix.one_mul, Matrix.mul_one]

-- ============================================================
-- The complex Bartels-Stewart column solve
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), complex form: the shifted
    column coefficient `R - s • I` appearing in the column recurrence
    `(R - s_kk I) y_k = ...`. -/
def complexShiftedCoeff {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (s : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  R - s • (1 : Matrix (Fin m) (Fin m) ℂ)

/-- A finite upper-triangular complex matrix with nonzero diagonal has nonzero
    determinant.  This is the complex analogue of the repository's real
    triangular determinant bridge, using the same below-diagonal convention. -/
theorem complex_det_ne_zero_of_upperTriangular_diag_ne_zero {m : ℕ}
    (T : Matrix (Fin m) (Fin m) ℂ)
    (hupper : IsUpperTriangularC T)
    (hdiag : ∀ i : Fin m, T i i ≠ 0) :
    T.det ≠ 0 := by
  classical
  have htri : Matrix.BlockTriangular (M := T) id := by
    intro i j hij
    exact hupper i j (by simpa using hij)
  rw [Matrix.det_of_upperTriangular htri]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)

/-- Shifting an upper-triangular complex matrix by a scalar multiple of the
    identity preserves upper triangularity. -/
theorem complexShiftedCoeff_upperTriangular {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (s : ℂ)
    (hR : IsUpperTriangularC R) :
    IsUpperTriangularC (complexShiftedCoeff R s) := by
  intro i j hji
  have hij : i ≠ j := ne_of_gt hji
  simp [complexShiftedCoeff, Matrix.sub_apply, hR i j hji, hij]

/-- For an upper-triangular complex Schur factor, pairwise separation between a
    scalar `s` and the diagonal entries gives nonsingularity of the shifted
    column coefficient `R - s I`. -/
theorem complexShiftedCoeff_det_ne_zero_of_upperTriangular_diag_ne
    {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (s : ℂ)
    (hR : IsUpperTriangularC R)
    (hgap : ∀ i : Fin m, R i i ≠ s) :
    (complexShiftedCoeff R s).det ≠ 0 := by
  apply complex_det_ne_zero_of_upperTriangular_diag_ne_zero
  · exact complexShiftedCoeff_upperTriangular R s hR
  · intro i
    have hdiag : R i i - s ≠ 0 := sub_ne_zero.mpr (hgap i)
    simpa [complexShiftedCoeff] using hdiag

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), complex Schur diagonal
    separation supplies the per-column shifted determinant hypotheses for the
    triangular Bartels-Stewart solve. -/
theorem complexSylvester_shift_det_ne_zero_of_schur_diagonal_separation
    {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (hR : IsUpperTriangularC R)
    (hsep : ∀ i : Fin m, ∀ k : Fin n, R i i ≠ S k k) :
    ∀ k : Fin n, (complexShiftedCoeff R (S k k)).det ≠ 0 := by
  intro k
  exact complexShiftedCoeff_det_ne_zero_of_upperTriangular_diag_ne
    R (S k k) hR (fun i => hsep i k)

/-- Entrywise column identity: for upper-triangular `S`, applying the shifted
    coefficient to column `k` of `Y` reproduces the `k`-th column of the
    Sylvester operator `R Y - Y S` plus a sum over strictly earlier columns.
    This is the pure algebra behind Higham (16.6). -/
theorem complexSylvester_column_identity {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (Y : Matrix (Fin m) (Fin n) ℂ)
    (hS : IsUpperTriangularC S) (k : Fin n) :
    (complexShiftedCoeff R (S k k)).mulVec (fun i => Y i k) =
      (fun i => complexSylvesterOp R S Y i k +
        ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j) := by
  funext i
  -- expand shifted coefficient
  have hlhs :
      (complexShiftedCoeff R (S k k)).mulVec (fun i => Y i k) i =
        (∑ l : Fin m, R i l * Y l k) - S k k * Y i k := by
    unfold complexShiftedCoeff
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp [Matrix.mulVec, dotProduct]
  rw [hlhs]
  -- split the row sum ∑_j Y_ij S_jk using upper triangularity of S
  have hsplit :
      (∑ j : Fin n, Y i j * S j k) =
        S k k * Y i k +
          ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j := by
    -- keep only j ≤ k, since S j k = 0 for k < j
    have hsub : (∑ j ∈ Finset.univ.filter (fun j => j ≤ k), Y i j * S j k) =
        ∑ j : Fin n, Y i j * S j k := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hjnot
      have hnot : ¬ (j ≤ k) := by
        intro hle
        exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hle⟩)
      have hkj : k < j := not_le.mp hnot
      rw [hS j k hkj, mul_zero]
    rw [← hsub]
    have hset : Finset.univ.filter (fun j => j ≤ k) =
        insert k (Finset.univ.filter (fun j => j < k)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hle
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact Or.inr hlt
        · exact Or.inl heq
      · intro h
        rcases h with heq | hlt
        · exact le_of_eq heq
        · exact le_of_lt hlt
    have hknotmem : k ∉ Finset.univ.filter (fun j => j < k) := by
      intro hmem
      exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl k)
    rw [hset, Finset.sum_insert hknotmem, mul_comm (Y i k) (S k k)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- assemble
  have hop : complexSylvesterOp R S Y i k =
      (∑ l : Fin m, R i l * Y l k) - (∑ j : Fin n, Y i j * S j k) := by
    unfold complexSylvesterOp
    simp [Matrix.mul_apply, Matrix.sub_apply]
  rw [hop, hsplit]
  ring

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), complex form: if `Y` solves
    `R Y - Y S = C` with `S` upper-triangular, then column `k` satisfies the
    Bartels-Stewart forward-substitution equation
    `(R - s_kk I) y_k = c_k + ∑_{j<k} s_jk y_j`. -/
theorem complexSylvester_column_equation {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C Y : Matrix (Fin m) (Fin n) ℂ)
    (hS : IsUpperTriangularC S)
    (hY : IsComplexSylvesterSolution R S C Y) (k : Fin n) :
    (complexShiftedCoeff R (S k k)).mulVec (fun i => Y i k) =
      (fun i => C i k +
        ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j) := by
  rw [complexSylvester_column_identity R S Y hS k]
  funext i
  have : complexSylvesterOp R S Y i k = C i k := by
    unfold IsComplexSylvesterSolution at hY
    exact congrFun (congrFun hY i) k
  rw [this]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.5)-(16.6), complex form:
    for upper-triangular `S`, solving `R Y - Y S = C` is equivalent to
    satisfying every Bartels-Stewart column equation. -/
theorem isComplexSylvesterSolution_iff_columns {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C Y : Matrix (Fin m) (Fin n) ℂ)
    (hS : IsUpperTriangularC S) :
    IsComplexSylvesterSolution R S C Y ↔
      ∀ k : Fin n,
        (complexShiftedCoeff R (S k k)).mulVec (fun i => Y i k) =
          (fun i => C i k +
            ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j) := by
  constructor
  · intro hY k
    exact complexSylvester_column_equation R S C Y hS hY k
  · intro h
    unfold IsComplexSylvesterSolution complexSylvesterOp
    ext i k
    have hk := congrFun (h k) i
    rw [complexSylvester_column_identity R S Y hS k] at hk
    -- hk : op i k + sum = C i k + sum  ⇒ op i k = C i k
    have := add_right_cancel hk
    -- goal: (R*Y - Y*S) i k = C i k
    have hop : complexSylvesterOp R S Y i k = C i k := this
    unfold complexSylvesterOp at hop
    simpa using hop

-- ============================================================
-- Uniqueness and existence of the column solve
-- ============================================================

private theorem complex_mulVec_injective_of_det_ne_zero {m : ℕ}
    {M : Matrix (Fin m) (Fin m) ℂ} (hdet : M.det ≠ 0)
    {x y : Fin m → ℂ}
    (hxy : M.mulVec x = M.mulVec y) : x = y := by
  have h := congrArg (M⁻¹.mulVec) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

private theorem complex_mulVec_surjective_of_det_ne_zero {m : ℕ}
    {M : Matrix (Fin m) (Fin m) ℂ} (hdet : M.det ≠ 0)
    (c : Fin m → ℂ) :
    ∃ x : Fin m → ℂ, M.mulVec x = c := by
  refine ⟨M⁻¹.mulVec c, ?_⟩
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), complex uniqueness half:
    with upper-triangular `S` and every shifted column coefficient `R - s_kk I`
    nonsingular, two solutions of `R Y - Y S = C` coincide, by strong induction
    over columns using the column recurrence. -/
theorem complexSylvester_triangular_solution_unique {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C Y Z : Matrix (Fin m) (Fin n) ℂ)
    (hS : IsUpperTriangularC S)
    (hshift : ∀ k : Fin n, (complexShiftedCoeff R (S k k)).det ≠ 0)
    (hY : IsComplexSylvesterSolution R S C Y)
    (hZ : IsComplexSylvesterSolution R S C Z) :
    Y = Z := by
  have hcol : ∀ N : ℕ, ∀ k : Fin n, k.val < N →
      (fun i => Y i k) = (fun i => Z i k) := by
    intro N
    induction N with
    | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
        intro k hk
        by_cases hlt : k.val < N
        · exact ih k hlt
        · have hYk := complexSylvester_column_equation R S C Y hS hY k
          have hZk := complexSylvester_column_equation R S C Z hS hZ k
          have hrhs :
              (fun i => C i k +
                ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j) =
              (fun i => C i k +
                ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Z i j) := by
            funext i
            have hsum :
                (∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j) =
                  ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Z i j := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk : (j : ℕ) < (k : ℕ) :=
                Fin.lt_def.mp (Finset.mem_filter.mp hj).2
              have hjN : (j : ℕ) < N := by omega
              have hYZ : Y i j = Z i j := congrFun (ih j hjN) i
              rw [hYZ]
            rw [hsum]
          have hmv :
              (complexShiftedCoeff R (S k k)).mulVec (fun i => Y i k) =
                (complexShiftedCoeff R (S k k)).mulVec (fun i => Z i k) := by
            rw [hYk, hZk]; exact hrhs
          exact complex_mulVec_injective_of_det_ne_zero (hshift k) hmv
  funext i k
  exact congrFun (hcol n k k.isLt) i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.6), complex
    Bartels-Stewart existence and uniqueness (supplied triangular `S`): with `S`
    upper-triangular and every shifted column coefficient `R - s_kk I`
    nonsingular, the transformed equation `R Y - Y S = C` has EXACTLY ONE
    solution, built by strong induction over columns from the column inverses.

    Here `S` upper-triangular and the shift nonsingularity are the honest
    residual hypotheses; existence of the triangular factor itself is discharged
    separately by `complexSylvester_schur_factors_exist`. -/
theorem complexSylvester_triangular_exists_unique {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hS : IsUpperTriangularC S)
    (hshift : ∀ k : Fin n, (complexShiftedCoeff R (S k k)).det ≠ 0) :
    ∃! Y : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution R S C Y := by
  -- Build columns by strong induction. `y : Fin n → (Fin m → ℂ)` holds columns.
  have hpartial : ∀ N : ℕ,
      ∃ y : Fin n → Fin m → ℂ,
        ∀ k : Fin n, k.val < N →
          (complexShiftedCoeff R (S k k)).mulVec (y k) =
            fun i => C i k +
              ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * y j i := by
    intro N
    induction N with
    | zero =>
        refine ⟨fun _ _ => 0, ?_⟩
        intro k hk; exact absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
        obtain ⟨y, hy⟩ := ih
        by_cases hN : N < n
        · obtain ⟨yk, hyk⟩ :=
            complex_mulVec_surjective_of_det_ne_zero (hshift ⟨N, hN⟩)
              (fun i => C i ⟨N, hN⟩ +
                ∑ j ∈ Finset.univ.filter (fun j => j < (⟨N, hN⟩ : Fin n)),
                  S j ⟨N, hN⟩ * y j i)
          refine ⟨Function.update y ⟨N, hN⟩ yk, ?_⟩
          intro k hk
          have hupdate_rhs : ∀ k' : Fin n, k'.val ≤ N →
              (fun i => C i k' +
                ∑ j ∈ Finset.univ.filter (fun j => j < k'),
                  S j k' * Function.update y ⟨N, hN⟩ yk j i) =
              (fun i => C i k' +
                ∑ j ∈ Finset.univ.filter (fun j => j < k'),
                  S j k' * y j i) := by
            intro k' hk'
            funext i
            have hsum :
                (∑ j ∈ Finset.univ.filter (fun j => j < k'),
                  S j k' * Function.update y ⟨N, hN⟩ yk j i) =
                ∑ j ∈ Finset.univ.filter (fun j => j < k'), S j k' * y j i := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk : (j : ℕ) < (k' : ℕ) :=
                Fin.lt_def.mp (Finset.mem_filter.mp hj).2
              have hjne : j ≠ (⟨N, hN⟩ : Fin n) := by
                intro hje
                have hjval : (j : ℕ) = N := by rw [hje]
                omega
              rw [Function.update_of_ne hjne]
            rw [hsum]
          by_cases hkval : k.val < N
          · have hkne : k ≠ (⟨N, hN⟩ : Fin n) := by
              intro hke
              have hkv : (k : ℕ) = N := by rw [hke]
              omega
            rw [Function.update_of_ne hkne, hupdate_rhs k (Nat.le_of_lt hkval)]
            exact hy k hkval
          · have hkeq : k = (⟨N, hN⟩ : Fin n) := by
              apply Fin.ext; show (k : ℕ) = N; omega
            rw [hkeq, Function.update_self, hupdate_rhs ⟨N, hN⟩ (Nat.le_refl N)]
            exact hyk
        · refine ⟨y, ?_⟩
          intro k hk
          have hkN : k.val < N := by
            have hkn : k.val < n := k.isLt; omega
          exact hy k hkN
  obtain ⟨y, hy⟩ := hpartial n
  refine ⟨Matrix.of fun i j => y j i, ?_, ?_⟩
  · apply (isComplexSylvesterSolution_iff_columns R S C
      (Matrix.of fun i j => y j i) hS).mpr
    intro k
    have := hy k k.isLt
    simpa [Matrix.of_apply] using this
  · intro Z hZ
    have hconstr : IsComplexSylvesterSolution R S C (Matrix.of fun i j => y j i) := by
      apply (isComplexSylvesterSolution_iff_columns R S C
        (Matrix.of fun i j => y j i) hS).mpr
      intro k
      have := hy k k.isLt
      simpa [Matrix.of_apply] using this
    exact complexSylvester_triangular_solution_unique R S C Z
      (Matrix.of fun i j => y j i) hS hshift hZ hconstr

-- ============================================================
-- Headline: complex Sylvester unique solvability with Schur factors supplied
-- by existence (not by hypothesis)
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.6), complex path,
    supplied-by-Schur factors: if unitary `U`, `V` conjugate `A`, `B` to
    upper-triangular `R`, `S`, and every shifted column coefficient
    `R - s_kk I` is nonsingular, then the complex Sylvester equation
    `A X - X B = C` has exactly one solution.

    This composes the unitary conjugation equivalence
    (`isComplexSylvesterSolution_conj_iff`) with the triangular column solve
    (`complexSylvester_triangular_exists_unique`).  The upper-triangular factors
    `R, S` here are provided UNCONDITIONALLY by
    `complexSylvester_schur_factors_exist`; only the shift nonsingularity (a
    condition on the eigenvalues on the diagonals of `R, S`) is assumed. -/
theorem complexSylvester_exists_unique_of_schur_factors {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hR : Uᴴ * A * U = R) (hS : Vᴴ * B * V = S)
    (hStri : IsUpperTriangularC S)
    (hshift : ∀ k : Fin n, (complexShiftedCoeff R (S k k)).det ≠ 0) :
    ∃! X : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution A B C X := by
  obtain ⟨Y, hYsol, hYuniq⟩ :=
    complexSylvester_triangular_exists_unique R S (Uᴴ * C * V) hStri hshift
  have hUU : U * Uᴴ = 1 := by
    have := hU.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hUhU : Uᴴ * U = 1 := by
    have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hVV : V * Vᴴ = 1 := by
    have := hV.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hVhV : Vᴴ * V = 1 := by
    have := hV.1; rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨U * Y * Vᴴ, ?_, ?_⟩
  · exact (isComplexSylvesterSolution_conj_iff A B U V R S C Y
      hU hV hR hS).mpr hYsol
  · intro X hX
    -- Recover the Schur-coordinate solution of X and match it to Y.
    set W : Matrix (Fin m) (Fin n) ℂ := Uᴴ * X * V with hW
    have hXexpand : U * W * Vᴴ = X := by
      rw [hW]
      have step : U * (Uᴴ * X * V) * Vᴴ = (U * Uᴴ) * X * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      rw [step, hUU, hVV, Matrix.one_mul, Matrix.mul_one]
    have hXsol : IsComplexSylvesterSolution A B C (U * W * Vᴴ) := by
      rw [hXexpand]; exact hX
    have hWsol : IsComplexSylvesterSolution R S (Uᴴ * C * V) W :=
      (isComplexSylvesterSolution_conj_iff A B U V R S C W hU hV hR hS).mp hXsol
    have hWY : W = Y := hYuniq W hWsol
    rw [← hXexpand, hWY]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.6), complex Schur
    factors with explicit diagonal separation: if the Schur diagonals of `R`
    and `S` are pairwise distinct, then the complex Sylvester equation has a
    unique exact solution.  This packages the source-level eigenvalue
    separation condition into the shifted determinant hypotheses used by the
    column recurrence. -/
theorem complexSylvester_exists_unique_of_schur_diagonal_separation {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hA : Uᴴ * A * U = R) (hB : Vᴴ * B * V = S)
    (hRtri : IsUpperTriangularC R)
    (hStri : IsUpperTriangularC S)
    (hsep : ∀ i : Fin m, ∀ k : Fin n, R i i ≠ S k k) :
    ∃! X : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution A B C X := by
  exact complexSylvester_exists_unique_of_schur_factors A B U V R S C
    hU hV hA hB hStri
    (complexSylvester_shift_det_ne_zero_of_schur_diagonal_separation
      R S hRtri hsep)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.6), complex path,
    HEADLINE unconditional-existence form.  For ANY complex square matrices
    `A`, `B` (no supplied factors), Schur triangulation produces unitary
    factors and upper-triangular `R`, `S`; and PROVIDED the resulting shifted
    column coefficients are nonsingular (i.e. no shared eigenvalue between the
    diagonals of `R` and `S`), the complex Sylvester equation `A X - X B = C`
    has exactly one solution.

    The Schur factors are existentially bound rather than assumed: this is the
    genuine content that the real file `Higham16Spectrum.lean` could only obtain
    conditionally on supplied triangular factors, because the real Schur form is
    merely quasi-triangular.  The shift hypothesis is stated in terms of the
    Schur factors and is not the conclusion in disguise — it constrains only the
    eigenvalues, not `X`. -/
theorem complexSylvester_exists_unique_of_schur_shift {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hshift : ∀ (U : Matrix (Fin m) (Fin m) ℂ) (R : Matrix (Fin m) (Fin m) ℂ)
      (V : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin n) (Fin n) ℂ),
      U ∈ Matrix.unitaryGroup (Fin m) ℂ → Uᴴ * A * U = R → IsUpperTriangularC R →
      V ∈ Matrix.unitaryGroup (Fin n) ℂ → Vᴴ * B * V = S → IsUpperTriangularC S →
      ∀ k : Fin n, (complexShiftedCoeff R (S k k)).det ≠ 0) :
    ∃! X : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution A B C X := by
  obtain ⟨U, R, V, S, hUu, hUeq, hRtri, hVu, hVeq, hStri⟩ :=
    complexSylvester_schur_factors_exist A B
  exact complexSylvester_exists_unique_of_schur_factors A B U V R S C
    hUu hVu hUeq hVeq hStri
    (hshift U R V S hUu hUeq hRtri hVu hVeq hStri)

end LeanFpAnalysis.FP
