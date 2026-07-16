/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import LeanFpAnalysis.FP.Algorithms.TestMatrices.Higham28
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderReflector
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderSpecSupport
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

namespace LeanFpAnalysis.FP

open MeasureTheory ProbabilityTheory
open scoped BigOperators

local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-! # Higham Chapter 28: Stewart's randsvd producer

This module formalizes the genuine deterministic and input-law precursors to
Stewart's Theorem 28.1.  It does not assert the missing Gaussian push-forward
invariance theorem.
-/

/-! ## Deterministic randsvd algebra -/

/-- Orthogonal left and right factors transport the right Gram matrix of a
randsvd matrix to the diagonal singular-value Gram matrix. -/
theorem randsvdMatrix_transpose_mul_self
    {m n : ℕ} (U : RSqMat m) (V : RSqMat n) (sigma : ℕ → ℝ)
    (hU : IsOrthogonal m U) :
    (randsvdMatrix U sigma V).transpose * randsvdMatrix U sigma V =
      V * ((rectangularDiagonal (m := m) (n := n) sigma).transpose *
        rectangularDiagonal (m := m) (n := n) sigma) * V.transpose := by
  let S := rectangularDiagonal (m := m) (n := n) sigma
  have hUeq : U.transpose * U = (1 : RSqMat m) := by
    ext i j
    simpa [Matrix.mul_apply, matTranspose, Matrix.one_apply, idMatrix] using
      hU.left_inv i j
  change (U * S * V.transpose).transpose * (U * S * V.transpose) =
    V * (S.transpose * S) * V.transpose
  calc
    (U * S * V.transpose).transpose * (U * S * V.transpose) =
        V * (S.transpose * (U.transpose * U) * S) * V.transpose := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc]
    _ = V * (S.transpose * S) * V.transpose := by
      rw [hUeq, Matrix.mul_one]

/-! ## Standard independent Gaussian tails -/

/-- Stewart's independent tail vectors in zero-based form: stage `i` has
dimension `n - i`, corresponding to the source's `x_{i+1} ∈ ℝ^{n-i}`. -/
abbrev StewartGaussianInputs (n : ℕ) :=
  ∀ i : Fin n, Fin (n - i.val) → ℝ

/-- The exact product law of the independent `N(0,1)` tail entries. -/
noncomputable def stewartGaussianInputMeasure (n : ℕ) :
    Measure (StewartGaussianInputs n) :=
  Measure.pi (fun i : Fin n =>
    Measure.pi (fun _ : Fin (n - i.val) => gaussianReal 0 1))

/-- Stewart's input law is a probability measure in every dimension. -/
theorem stewartGaussianInputMeasure_univ (n : ℕ) :
    stewartGaussianInputMeasure n Set.univ = 1 := by
  unfold stewartGaussianInputMeasure
  calc
    (Measure.pi (fun i : Fin n =>
        Measure.pi (fun _ : Fin (n - i.val) => gaussianReal 0 1))) Set.univ =
      ∏ i : Fin n,
        Measure.pi (fun _ : Fin (n - i.val) => gaussianReal 0 1) Set.univ :=
      MeasureTheory.Measure.pi_univ _
    _ = 1 := by simp

instance stewartGaussianInputMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (stewartGaussianInputMeasure n) :=
  ⟨stewartGaussianInputMeasure_univ n⟩

/-! ## Total embedded Householder producer -/

/-- A total `2/(vᵀv)` coefficient.  The zero-vector branch produces the
identity reflector; standard Gaussian inputs reach that branch only on the
later null-event obligation. -/
noncomputable def stewartHouseholderBeta {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  let s := ∑ i : Fin n, v i * v i
  if s = 0 then 0 else 2 / s

/-- The total coefficient always produces an orthogonal Householder matrix. -/
theorem stewartHouseholder_orthogonal {n : ℕ} (v : Fin n → ℝ) :
    IsOrthogonal n (householder n v (stewartHouseholderBeta v)) := by
  by_cases hs : (∑ i : Fin n, v i * v i) = 0
  · have hmatrix : householder n v (stewartHouseholderBeta v) = idMatrix n := by
      ext i j
      simp [householder, stewartHouseholderBeta, hs]
    rw [hmatrix]
    exact IsOrthogonal.id n
  · apply householder_orthogonal
    simp [stewartHouseholderBeta, hs]

/-- The exact local reflector used by the producer really reduces its input
tail to the signed norm on the first coordinate.  This is the source's
`Pbar_i x_i = r_ii e₁`, not merely an orthogonality contract. -/
theorem stewartLocalHouseholder_reduces {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (j : Fin d) :
    matMulVec d
        (householder d (householderVector hd x)
          (stewartHouseholderBeta (householderVector hd x))) x j =
      if j = ⟨0, hd⟩ then householderAlpha hd x else 0 := by
  by_cases hx : x = 0
  · subst x
    simp [matMulVec, householder, stewartHouseholderBeta, householderVector,
      householderScale, householderAlpha, idMatrix]
  · let p : Fin d := ⟨0, hd⟩
    let v := householderVector hd x
    let alpha := householderAlpha hd x
    have hv : v = householderActiveVector d p x alpha := by
      funext k
      by_cases hkp : k = p
      · subst k
        simp [v, p, alpha, householderActiveVector, householderAlpha]
      · simp [v, p, alpha, householderVector, householderActiveVector, hkp]
    have halpha : alpha * alpha = vecNorm2Sq x := by
      unfold alpha householderAlpha
      rw [neg_mul_neg, householderScale_mul_self]
      simp [vecNorm2Sq, pow_two]
    have hv_ne : v ≠ 0 := by
      intro hvzero
      have hv0 := householderVector_zero_ne_zero_of_ne_zero hd x hx
      apply hv0
      simpa [v, p] using congrFun hvzero p
    have hden : (∑ k : Fin d, v k * v k) ≠ 0 := by
      have hpos : 0 < ∑ k : Fin d, v k * v k := by
        simpa [dotProduct] using (dotProduct_self_pos_iff_real d v).2 hv_ne
      exact ne_of_gt hpos
    have hbeta : stewartHouseholderBeta v = householderBetaSpec d v := by
      simp [stewartHouseholderBeta, householderBetaSpec, hden]
    rw [show householderVector hd x = v from rfl, hbeta, hv]
    exact matMulVec_householder_activeVector_eq_alpha_basis
      d p x alpha halpha (by simpa [← hv] using hden) j

/-! ### Measurability of the finite Householder primitives -/

theorem measurable_householderSign : Measurable householderSign := by
  unfold householderSign
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

theorem measurable_householderScale {d : ℕ} (hd : 0 < d) :
    Measurable (householderScale hd) := by
  unfold householderScale
  apply Measurable.mul
  · exact measurable_householderSign.comp
      (measurable_pi_apply (⟨0, hd⟩ : Fin d))
  · apply Measurable.sqrt
    exact Finset.measurable_fun_sum Finset.univ fun k _ =>
      (measurable_pi_apply k).mul (measurable_pi_apply k)

theorem measurable_householderAlpha {d : ℕ} (hd : 0 < d) :
    Measurable (householderAlpha hd) := by
  change Measurable fun x => -householderScale hd x
  exact (measurable_householderScale hd).neg

theorem measurable_householderVector {d : ℕ} (hd : 0 < d) :
    Measurable (householderVector hd) := by
  refine measurable_pi_lambda _ fun k => ?_
  by_cases hk : k = ⟨0, hd⟩
  · subst k
    simp only [householderVector, ↓reduceIte]
    exact (measurable_pi_apply (⟨0, hd⟩ : Fin d)).add
      (measurable_householderScale hd)
  · simpa [householderVector, hk] using (measurable_pi_apply k)

theorem measurable_stewartHouseholderBeta {d : ℕ} :
    Measurable (stewartHouseholderBeta : (Fin d → ℝ) → ℝ) := by
  let s : (Fin d → ℝ) → ℝ := fun v => ∑ k : Fin d, v k * v k
  have hs : Measurable s :=
    Finset.measurable_fun_sum Finset.univ fun k _ =>
      (measurable_pi_apply k).mul (measurable_pi_apply k)
  unfold stewartHouseholderBeta
  exact Measurable.ite (measurableSet_eq_fun hs measurable_const)
    measurable_const (measurable_const.div hs)

theorem measurable_stewartHouseholder {d : ℕ} :
    Measurable fun v : Fin d → ℝ =>
      householder d v (stewartHouseholderBeta v) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  unfold householder
  exact measurable_const.sub
    ((measurable_stewartHouseholderBeta.mul (measurable_pi_apply i)).mul
      (measurable_pi_apply j))

/-- Embed the local Householder vector for stage `i` into the final `n`
coordinates, with an identically zero prefix. -/
noncomputable def stewartEmbeddedHouseholderVector {n : ℕ} (i : Fin n)
    (x : Fin (n - i.val) → ℝ) : Fin n → ℝ :=
  fun j =>
    if h : i.val ≤ j.val then
      householderVector (by omega : 0 < n - i.val) x
        ⟨j.val - i.val, by omega⟩
    else 0

@[simp] theorem stewartEmbeddedHouseholderVector_of_lt
    {n : ℕ} (i j : Fin n) (x : Fin (n - i.val) → ℝ)
    (hji : j.val < i.val) :
    stewartEmbeddedHouseholderVector i x j = 0 := by
  simp [stewartEmbeddedHouseholderVector, not_le_of_gt hji]

/-- The full stage reflector `P_i = diag(I_i, Pbar_i)`. -/
noncomputable def stewartEmbeddedHouseholder {n : ℕ} (i : Fin n)
    (x : Fin (n - i.val) → ℝ) : RSqMat n :=
  let v := stewartEmbeddedHouseholderVector i x
  householder n v (stewartHouseholderBeta v)

theorem stewartEmbeddedHouseholder_orthogonal
    {n : ℕ} (i : Fin n) (x : Fin (n - i.val) → ℝ) :
    IsOrthogonal n (stewartEmbeddedHouseholder i x) := by
  exact stewartHouseholder_orthogonal (stewartEmbeddedHouseholderVector i x)

/-- Rows in the inactive prefix agree exactly with the identity, making the
source's block-diagonal embedding visible. -/
theorem stewartEmbeddedHouseholder_prefix_row
    {n : ℕ} (i a b : Fin n) (x : Fin (n - i.val) → ℝ)
    (hai : a.val < i.val) :
    stewartEmbeddedHouseholder i x a b = idMatrix n a b := by
  simp [stewartEmbeddedHouseholder, householder,
    stewartEmbeddedHouseholderVector_of_lt i a x hai]

theorem measurable_stewartEmbeddedHouseholderVector
    {n : ℕ} (i : Fin n) :
    Measurable (stewartEmbeddedHouseholderVector i) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases hij : i.val ≤ j.val
  · let k : Fin (n - i.val) := ⟨j.val - i.val, by omega⟩
    simpa [stewartEmbeddedHouseholderVector, hij, k] using
      (measurable_pi_apply k).comp
        (measurable_householderVector (by omega : 0 < n - i.val))
  · simp [stewartEmbeddedHouseholderVector, hij]

theorem measurable_stewartEmbeddedHouseholder
    {n : ℕ} (i : Fin n) :
    Measurable (stewartEmbeddedHouseholder i) := by
  unfold stewartEmbeddedHouseholder
  exact measurable_stewartHouseholder.comp
    (measurable_stewartEmbeddedHouseholderVector i)

/-! ## Stewart's source-ordered matrix producer -/

/-- The diagonal quantity `r_ii` used by Stewart.  At the first `n - 1`
stages it is the signed norm to which the Householder transformation reduces
the local Gaussian tail.  The source specifies the final scalar separately as
`r_nn = sign(x_n)`. -/
noncomputable def stewartRDiagonal {n : ℕ} (z : StewartGaussianInputs n)
    (i : Fin n) : ℝ :=
  if h : i.val + 1 < n then
    householderAlpha (by omega : 0 < n - i.val) (z i)
  else
    householderSign (z i ⟨0, by omega⟩)

/-- Stewart's `D = diag(sign(r_ii))`, with the stable convention `sign(0)=1`. -/
noncomputable def stewartSignDiagonal {n : ℕ}
    (z : StewartGaussianInputs n) : RSqMat n :=
  diagMatrix (fun i => householderSign (stewartRDiagonal z i))

theorem stewartSignDiagonal_orthogonal {n : ℕ}
    (z : StewartGaussianInputs n) :
    IsOrthogonal n (stewartSignDiagonal z) := by
  apply IsOrthogonal.diagMatrix_of_sq_eq_one
  intro i
  unfold householderSign
  by_cases h : stewartRDiagonal z i < 0 <;> simp [h]

theorem measurable_stewartRDiagonal {n : ℕ} (i : Fin n) :
    Measurable fun z : StewartGaussianInputs n => stewartRDiagonal z i := by
  unfold stewartRDiagonal
  by_cases hstage : i.val + 1 < n
  · simp only [hstage, ↓reduceDIte]
    exact (measurable_householderAlpha (by omega : 0 < n - i.val)).comp
      (measurable_pi_apply i)
  · simp only [hstage, ↓reduceDIte]
    exact measurable_householderSign.comp
      ((measurable_pi_apply (⟨0, by omega⟩ : Fin (n - i.val))).comp
        (measurable_pi_apply i))

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

/-- The embedded reflectors `P₁,...,P_{n-1}` in the exact source order. -/
noncomputable def stewartHouseholderList {n : ℕ}
    (z : StewartGaussianInputs n) : List (RSqMat n) :=
  List.ofFn fun k : Fin (n - 1) =>
    let i : Fin n := ⟨k.val, by omega⟩
    stewartEmbeddedHouseholder i (z i)

/-- Source stages as a fixed finite list of measurable matrix-valued
functions.  Evaluating this list gives `stewartHouseholderList`. -/
noncomputable def stewartHouseholderFunctionList {n : ℕ} :
    List (StewartGaussianInputs n → RSqMat n) :=
  List.ofFn fun k : Fin (n - 1) => fun z =>
    let i : Fin n := ⟨k.val, by omega⟩
    stewartEmbeddedHouseholder i (z i)

theorem stewartHouseholderFunctionList_map_apply {n : ℕ}
    (z : StewartGaussianInputs n) :
    stewartHouseholderFunctionList.map (fun P => P z) =
      stewartHouseholderList z := by
  simp [stewartHouseholderFunctionList, stewartHouseholderList,
    Function.comp_def]

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

theorem stewartHouseholderList_orthogonal {n : ℕ}
    (z : StewartGaussianInputs n) :
    ∀ P ∈ stewartHouseholderList z, IsOrthogonal n P := by
  intro P hP
  rcases List.mem_ofFn.mp hP with ⟨k, rfl⟩
  dsimp
  exact stewartEmbeddedHouseholder_orthogonal _ _

/-- The executable sample-path map in Theorem 28.1,
`Q = D P₁ ⋯ P_{n-1}`. -/
noncomputable def stewartOrthogonalMatrix {n : ℕ}
    (z : StewartGaussianInputs n) : RSqMat n :=
  stewartOrthogonalProduct (stewartSignDiagonal z) (stewartHouseholderList z)

/-- Every sample path of the total Stewart producer is orthogonal. -/
theorem stewartOrthogonalMatrix_orthogonal {n : ℕ}
    (z : StewartGaussianInputs n) :
    IsOrthogonal n (stewartOrthogonalMatrix z) := by
  exact higham28_theorem28_1_product_orthogonal
    (stewartSignDiagonal z) (stewartHouseholderList z)
    (stewartSignDiagonal_orthogonal z)
    (stewartHouseholderList_orthogonal z)

theorem measurable_stewartOrthogonalMatrix {n : ℕ} :
    Measurable (stewartOrthogonalMatrix :
      StewartGaussianInputs n → RSqMat n) := by
  unfold stewartOrthogonalMatrix stewartOrthogonalProduct
  exact measurable_matMul_of_measurable measurable_stewartSignDiagonal
    measurable_stewartHouseholderListProduct

/-- The same producer, with its codomain strengthened from ambient matrices to
Mathlib's exact orthogonal group. -/
noncomputable def stewartOrthogonalGroupOutput {n : ℕ}
    (z : StewartGaussianInputs n) : Matrix.orthogonalGroup (Fin n) ℝ :=
  ⟨stewartOrthogonalMatrix z, by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    simpa [Matrix.mul_apply, matTranspose, Matrix.one_apply, idMatrix] using
      (stewartOrthogonalMatrix_orthogonal z).right_inv i j⟩

theorem measurable_stewartOrthogonalGroupOutput {n : ℕ} :
    Measurable (stewartOrthogonalGroupOutput (n := n)) := by
  unfold stewartOrthogonalGroupOutput
  exact measurable_stewartOrthogonalMatrix.subtype_mk

/-! ## Exact law and the unclosed Haar endpoint -/

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

This proposition is intentionally left unproved.  Its normalization conjunct
is now discharged by `stewartOrthogonalGroupLaw_univ`; the remaining first
conjunct requires the Gaussian/Householder invariance argument. -/
def StewartTheorem28_1HaarConclusion (n : ℕ) : Prop :=
  (stewartOrthogonalGroupLaw n).IsHaarMeasure ∧
    stewartOrthogonalGroupLaw n Set.univ = 1

/-- After the concrete normalization proof, Theorem 28.1 has exactly one
remaining mathematical obligation: Haar invariance of the push-forward. -/
theorem stewartTheorem28_1HaarConclusion_iff_isHaarMeasure (n : ℕ) :
    StewartTheorem28_1HaarConclusion n ↔
      (stewartOrthogonalGroupLaw n).IsHaarMeasure := by
  simp [StewartTheorem28_1HaarConclusion, stewartOrthogonalGroupLaw_univ]

/-! ## Paired randsvd producer -/

/-- Independent Stewart inputs for the left and right orthogonal factors. -/
abbrev StewartRandsvdInputs (m n : ℕ) :=
  StewartGaussianInputs m × StewartGaussianInputs n

/-- The product Gaussian law driving the two independent randsvd factors. -/
noncomputable def stewartRandsvdInputMeasure (m n : ℕ) :
    Measure (StewartRandsvdInputs m n) :=
  (stewartGaussianInputMeasure m).prod (stewartGaussianInputMeasure n)

theorem stewartRandsvdInputMeasure_univ (m n : ℕ) :
    stewartRandsvdInputMeasure m n Set.univ = 1 := by
  unfold stewartRandsvdInputMeasure
  rw [← Set.univ_prod_univ, Measure.prod_prod,
    stewartGaussianInputMeasure_univ, stewartGaussianInputMeasure_univ]
  norm_num

/-- A genuine randsvd sample path using two independent Stewart producers. -/
noncomputable def stewartRandsvdMatrix {m n : ℕ} (sigma : ℕ → ℝ)
    (z : StewartRandsvdInputs m n) : RMat m n :=
  randsvdMatrix (stewartOrthogonalMatrix z.1) sigma
    (stewartOrthogonalMatrix z.2)

/-- The right Gram matrix of the paired producer is orthogonally similar to
the squared rectangular diagonal, on every Gaussian input sample. -/
theorem stewartRandsvdMatrix_transpose_mul_self
    {m n : ℕ} (sigma : ℕ → ℝ) (z : StewartRandsvdInputs m n) :
    (stewartRandsvdMatrix sigma z).transpose *
        stewartRandsvdMatrix sigma z =
      stewartOrthogonalMatrix z.2 *
        ((rectangularDiagonal (m := m) (n := n) sigma).transpose *
          rectangularDiagonal (m := m) (n := n) sigma) *
        (stewartOrthogonalMatrix z.2).transpose := by
  exact randsvdMatrix_transpose_mul_self _ _ _
    (stewartOrthogonalMatrix_orthogonal z.1)

end LeanFpAnalysis.FP
