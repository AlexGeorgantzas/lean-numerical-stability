import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport
import NumStability.Algorithms.TestMatrices.Higham28
import NumStability.Analysis.TestMatrices.RandomSVD.Stewart
import NumStability.Source.Higham.Chapter28.Section03.Theorem01.StewartHaar.Stewart

/-!
# Higham28Stewart (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28Stewart`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped BigOperators

local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private theorem householder_mul_apply_rectangular
    {m n : ℕ} (u : Fin m → ℝ) (beta : ℝ) (S : RMat m n)
    (i : Fin m) (j : Fin n) :
    ((show RSqMat m from householder m u beta) * S) i j =
      S i j - beta * u i * (∑ k : Fin m, u k * S k j) := by
  simp only [Matrix.mul_apply, householder, idMatrix]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  simp
  ring_nf

private theorem rectangular_mul_householder_apply
    {m n : ℕ} (S : RMat m n) (v : Fin n → ℝ) (gamma : ℝ)
    (i : Fin m) (j : Fin n) :
    (S * (show RSqMat n from householder n v gamma)) i j =
      S i j - gamma * (∑ k : Fin n, S i k * v k) * v j := by
  simp only [Matrix.mul_apply, householder, idMatrix]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp
  ring_nf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem singleHouseholder_product_factorization {m n : ℕ}
    (S : RMat m n) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (beta gamma : ℝ) :
    (show RSqMat m from householder m u beta) * S *
        (show RSqMat n from householder n v gamma) =
      S + singleHouseholderRandsvdCorrectionLeft S u v *
        singleHouseholderRandsvdCorrectionRight S u v beta gamma := by
  ext i j
  rw [rectangular_mul_householder_apply]
  simp_rw [householder_mul_apply_rectangular]
  have hsum :
      (∑ x : Fin n,
        (S i x - beta * u i * (∑ k : Fin m, u k * S k x)) * v x) =
        (∑ x : Fin n, S i x * v x) -
          beta * u i *
            (∑ x : Fin n, (∑ k : Fin m, u k * S k x) * v x) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  simp only [Matrix.add_apply, Matrix.mul_apply,
    singleHouseholderRandsvdCorrectionLeft,
    singleHouseholderRandsvdCorrectionRight]
  simp only [Fin.sum_univ_two]
  simp
  ring

/-- Higham's exact warning on p. 518: replacing each random orthogonal factor
by one Householder matrix yields the rectangular diagonal matrix plus an
explicit product through a two-dimensional space. -/
theorem singleHouseholder_randsvd_eq_diagonal_add_rankTwo {m n : ℕ}
    (sigma : ℕ → ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (beta gamma : ℝ) :
    randsvdMatrix (householder m u beta) sigma (householder n v gamma) =
      rectangularDiagonal sigma +
        singleHouseholderRandsvdCorrectionLeft (rectangularDiagonal sigma) u v *
          singleHouseholderRandsvdCorrectionRight
            (rectangularDiagonal sigma) u v beta gamma := by
  have hVsym :
      (show RSqMat n from householder n v gamma).transpose =
        (show RSqMat n from householder n v gamma) := by
    simpa [matTranspose] using householder_symmetric n v gamma
  unfold randsvdMatrix
  rw [hVsym]
  exact singleHouseholder_product_factorization
    (rectangularDiagonal sigma) u v beta gamma

/-- The correction in the preceding decomposition has matrix rank at most
two, including rectangular and degenerate dimensions. -/
theorem singleHouseholder_randsvd_correction_rank_le_two {m n : ℕ}
    (sigma : ℕ → ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (beta gamma : ℝ) :
    Matrix.rank
        (randsvdMatrix (householder m u beta) sigma (householder n v gamma) -
          rectangularDiagonal sigma) ≤ 2 := by
  have hfactor := singleHouseholder_randsvd_eq_diagonal_add_rankTwo
    sigma u v beta gamma
  have hsub :
      randsvdMatrix (householder m u beta) sigma (householder n v gamma) -
          rectangularDiagonal sigma =
        singleHouseholderRandsvdCorrectionLeft (rectangularDiagonal sigma) u v *
          singleHouseholderRandsvdCorrectionRight
            (rectangularDiagonal sigma) u v beta gamma := by
    rw [hfactor]
    abel
  rw [hsub]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width
      (singleHouseholderRandsvdCorrectionLeft
        (rectangularDiagonal sigma) u v))

theorem measurable_stewartEmbeddedHouseholder
    {n : ℕ} (i : Fin n) :
    Measurable (stewartEmbeddedHouseholder i) := by
  unfold stewartEmbeddedHouseholder
  exact measurable_stewartHouseholder.comp
    (measurable_stewartEmbeddedHouseholderVector i)

theorem measurable_stewartSignDiagonal {n : ℕ} :
    Measurable (stewartSignDiagonal : StewartGaussianInputs n → RSqMat n) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  by_cases hij : i = j
  · subst j
    simp only [stewartSignDiagonal, diagMatrix, ↓reduceIte]
    exact measurable_householderSign.comp (measurable_stewartRDiagonal i)
  · simp [stewartSignDiagonal, diagMatrix, hij]

theorem measurable_matMul_of_measurable
    {α : Type*} [MeasurableSpace α] {n : ℕ}
    {A B : α → RSqMat n} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => matMul n (A x) (B x) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact Finset.measurable_fun_sum Finset.univ fun k _ =>
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB))

theorem measurable_matrixListProduct_eval
    {α : Type*} [MeasurableSpace α] {n : ℕ}
    (Ps : List (α → RSqMat n))
    (hPs : ∀ P ∈ Ps, Measurable P) :
    Measurable fun x => matrixListProduct (Ps.map fun P => P x) := by
  induction Ps with
  | nil =>
      change Measurable fun _ : α => idMatrix n
      exact measurable_const
  | cons P Ps ih =>
      simp only [List.map_cons, matrixListProduct]
      exact measurable_matMul_of_measurable
        (hPs P (by simp))
        (ih fun Q hQ => hPs Q (by simp [hQ]))

theorem stewartHouseholderFunctionList_measurable {n : ℕ} :
    ∀ P ∈ (stewartHouseholderFunctionList :
      List (StewartGaussianInputs n → RSqMat n)), Measurable P := by
  intro P hP
  rcases List.mem_ofFn.mp hP with ⟨k, rfl⟩
  dsimp
  exact (measurable_stewartEmbeddedHouseholder _).comp
    (measurable_pi_apply _)

theorem measurable_stewartHouseholderListProduct {n : ℕ} :
    Measurable fun z : StewartGaussianInputs n =>
      matrixListProduct (stewartHouseholderList z) := by
  have h := measurable_matrixListProduct_eval
    (stewartHouseholderFunctionList :
      List (StewartGaussianInputs n → RSqMat n))
    stewartHouseholderFunctionList_measurable
  convert h using 1
  funext z
  exact congrArg matrixListProduct
    (stewartHouseholderFunctionList_map_apply z).symm

theorem measurable_stewartOrthogonalMatrix {n : ℕ} :
    Measurable (stewartOrthogonalMatrix :
      StewartGaussianInputs n → RSqMat n) := by
  unfold stewartOrthogonalMatrix stewartOrthogonalProduct
  exact measurable_matMul_of_measurable measurable_stewartSignDiagonal
    measurable_stewartHouseholderListProduct

theorem measurable_stewartOrthogonalGroupOutput {n : ℕ} :
    Measurable (stewartOrthogonalGroupOutput (n := n)) := by
  unfold stewartOrthogonalGroupOutput
  exact measurable_stewartOrthogonalMatrix.subtype_mk

/-- The exact push-forward law of Stewart's Gaussian-tail producer. -/
noncomputable def stewartOrthogonalGroupLaw (n : ℕ) :
    Measure (Matrix.orthogonalGroup (Fin n) ℝ) :=
  Measure.map (stewartOrthogonalGroupOutput (n := n))
    (stewartGaussianInputMeasure n)

/-- Once measurability of the explicit producer is supplied, normalization of
its push-forward follows from the proved product-Gaussian normalization. -/
theorem stewartOrthogonalGroupLaw_univ_of_measurable (n : ℕ)
    (hmeas : Measurable (stewartOrthogonalGroupOutput (n := n))) :
    stewartOrthogonalGroupLaw n Set.univ = 1 := by
  rw [stewartOrthogonalGroupLaw, Measure.map_apply hmeas MeasurableSet.univ]
  exact stewartGaussianInputMeasure_univ n

/-- The concrete Stewart push-forward is normalized. -/
theorem stewartOrthogonalGroupLaw_univ (n : ℕ) :
    stewartOrthogonalGroupLaw n Set.univ = 1 :=
  stewartOrthogonalGroupLaw_univ_of_measurable n
    measurable_stewartOrthogonalGroupOutput

/-- The exact group-level, normalized Haar endpoint of Theorem 28.1.

The downstream theorem `stewartTheorem28_1HaarConclusion` proves this
proposition by a Gaussian/Householder induction and Haar-fiber uniqueness. -/
def StewartTheorem28_1HaarConclusion (n : ℕ) : Prop :=
  (stewartOrthogonalGroupLaw n).IsHaarMeasure ∧
    stewartOrthogonalGroupLaw n Set.univ = 1

/-- With normalization already built into the concrete push-forward, the
endpoint is equivalent to its Haar-invariance conjunct. -/
theorem stewartTheorem28_1HaarConclusion_iff_isHaarMeasure (n : ℕ) :
    StewartTheorem28_1HaarConclusion n ↔
      (stewartOrthogonalGroupLaw n).IsHaarMeasure := by
  simp [StewartTheorem28_1HaarConclusion, stewartOrthogonalGroupLaw_univ]

end NumStability
