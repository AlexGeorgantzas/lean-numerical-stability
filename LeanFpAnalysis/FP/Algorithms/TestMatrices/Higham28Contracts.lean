/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import LeanFpAnalysis.FP.Algorithms.TestMatrices.Higham28Probability
import LeanFpAnalysis.FP.Algorithms.TestMatrices.Higham28Asymptotics
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-! # Higham Chapter 28: explicit-domain deterministic transfers

The exact algebra proved in `Higham28` and `Higham28Exact` is unconditional.
This companion module records the citation-dependent remainder as transfer
theorems whose premises are the genuine upstream minor, partial-fraction,
trigonometric, cyclicity, or low-rank identities.  The printed conclusions are
never themselves assumed.
-/

/-! ## Cauchy minors and total positivity -/

/-- Strict total positivity, stated on every square submatrix selected by
strictly increasing row and column embeddings. -/
def IsStrictlyTotallyPositive {m n : ℕ} (A : RMat m n) : Prop :=
  ∀ (k : ℕ) (_hk : 0 < k) (r : Fin k → Fin m) (c : Fin k → Fin n),
    StrictMono r → StrictMono c →
      0 < Matrix.det (fun i j => A (r i) (c j))

/-- Numerator of the square Cauchy determinant product. -/
noncomputable def cauchyDetNumerator (n : ℕ) (x y : RVec n) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i) * (y j - y i)

/-- Denominator of the square Cauchy determinant product. -/
noncomputable def cauchyDetDenominator (n : ℕ) (x y : RVec n) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, (x i + y j)

theorem cauchyDetFormula_eq_num_div_den (n : ℕ) (x y : RVec n) :
    cauchyDetFormula n x y =
      cauchyDetNumerator n x y / cauchyDetDenominator n x y := rfl

/-- Cauchy's determinant formula transferred from its fraction-free
determinant identity and a nonzero product denominator.  The first premise is
the determinant-induction output, not the quotient conclusion. -/
theorem cauchy_det_formula_of_cross_product
    (n : ℕ) (x y : RVec n)
    (hcross : Matrix.det (cauchyMatrix x y) *
      cauchyDetDenominator n x y = cauchyDetNumerator n x y)
    (hden : cauchyDetDenominator n x y ≠ 0) :
    Matrix.det (cauchyMatrix x y) = cauchyDetFormula n x y := by
  rw [cauchyDetFormula_eq_num_div_den, eq_div_iff hden]
  exact hcross

/-- The partial-fraction summation identity that is the arithmetic upstream
foundation of the printed inverse formula. -/
def CauchyInversePartialFractionIdentity
    (n : ℕ) (x y : RVec n) : Prop :=
  ∀ i j : Fin n,
    (∑ k : Fin n,
      cauchyMatrix x y i k * cauchyInverseEntry n x y k j) =
      if i = j then 1 else 0

/-- The generic printed Cauchy inverse follows entrywise from the genuine
partial-fraction summation identity. -/
theorem cauchy_inverse_formula_of_partialFractions
    (n : ℕ) (x y : RVec n)
    (hpartial : CauchyInversePartialFractionIdentity n x y) :
    cauchyMatrix x y * cauchyInverseFormula n x y = 1 := by
  ext i j
  simpa [Matrix.mul_apply, cauchyInverseFormula, Matrix.one_apply]
    using hpartial i j

/-- The same candidate is a left inverse by finite-dimensional
Dedekind-finiteness. -/
theorem cauchy_inverse_formula_left_of_partialFractions
    (n : ℕ) (x y : RVec n)
    (hpartial : CauchyInversePartialFractionIdentity n x y) :
    cauchyInverseFormula n x y * cauchyMatrix x y = 1 := by
  exact mul_eq_one_comm.mp
    (cauchy_inverse_formula_of_partialFractions n x y hpartial)

/-- The partial-fraction domain has a fully discharged order-one producer. -/
theorem cauchy_order_one_partialFractionIdentity
    (x y : RVec 1) (hxy : x 0 + y 0 ≠ 0) :
    CauchyInversePartialFractionIdentity 1 x y := by
  intro i j
  fin_cases i
  fin_cases j
  simp [cauchyMatrix, cauchyInverseEntry, hxy]

/-- Higham's unit-lower Cauchy `L` candidate, in zero-based indexing. -/
noncomputable def cauchyLowerEntry
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  if j ≤ i then
    ((∏ k ∈ Finset.Iio j, (x i - x k)) /
        (∏ k ∈ Finset.Iio j, (x j - x k))) *
      ((∏ k ∈ Finset.Iic j, (x j + y k)) /
        (∏ k ∈ Finset.Iic j, (x i + y k)))
  else 0

/-- Higham's upper Cauchy `U` candidate, in zero-based indexing. -/
noncomputable def cauchyUpperEntry
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  if i ≤ j then
    ((∏ k ∈ Finset.Iio i, (x i - x k) * (y j - y k)) /
      ((x i + y j) *
        (∏ k ∈ Finset.Iio i, (x i + y k) * (x k + y j))))
  else 0

noncomputable def cauchyLower
    (n : ℕ) (x y : RVec n) : RSqMat n :=
  fun i j => cauchyLowerEntry n x y i j

noncomputable def cauchyUpper
    (n : ℕ) (x y : RVec n) : RSqMat n :=
  fun i j => cauchyUpperEntry n x y i j

theorem cauchyLower_zero_of_lt
    {n : ℕ} (x y : RVec n) (i j : Fin n) (hij : i < j) :
    cauchyLower n x y i j = 0 := by
  simp [cauchyLower, cauchyLowerEntry, show ¬j ≤ i by omega]

theorem cauchyUpper_zero_of_lt
    {n : ℕ} (x y : RVec n) (i j : Fin n) (hji : j < i) :
    cauchyUpper n x y i j = 0 := by
  simp [cauchyUpper, cauchyUpperEntry, show ¬i ≤ j by omega]

/-- The finite rational product-sum identity upstream of the printed Cauchy
LU factorization. -/
def CauchyLUSummationIdentity (n : ℕ) (x y : RVec n) : Prop :=
  ∀ i j : Fin n,
    (∑ k : Fin n,
      cauchyLowerEntry n x y i k * cauchyUpperEntry n x y k j) =
      1 / (x i + y j)

/-- The source LU factorization transferred from its rational product-sum
identity. -/
theorem cauchy_eq_lower_mul_upper_of_summation
    (n : ℕ) (x y : RVec n)
    (hsum : CauchyLUSummationIdentity n x y) :
    cauchyMatrix x y = cauchyLower n x y * cauchyUpper n x y := by
  ext i j
  simpa [Matrix.mul_apply, cauchyMatrix, cauchyLower, cauchyUpper]
    using (hsum i j).symm

/-- The LU product-sum domain also has a concrete order-one producer. -/
theorem cauchy_order_one_LUSummationIdentity
    (x y : RVec 1) (hxy : x 0 + y 0 ≠ 0) :
    CauchyLUSummationIdentity 1 x y := by
  intro i j
  fin_cases i
  fin_cases j
  have hIio : Finset.Iio (0 : Fin 1) = ∅ := by
    ext k
    fin_cases k
    simp
  have hIic : Finset.Iic (0 : Fin 1) = Finset.univ := by
    ext k
    fin_cases k
    simp
  simp [cauchyLowerEntry, cauchyUpperEntry, hIio, hIic, hxy]

/-- Barycentric row sums and their first moment are the upstream rational
facts behind Higham's displayed sum of all inverse entries. -/
theorem cauchy_inverse_entry_sum_of_barycentric_moments
    (n : ℕ) (x y w : RVec n)
    (hrows : ∀ i : Fin n,
      (∑ j : Fin n, cauchyInverseEntry n x y i j) = w i)
    (hmoment : (∑ i : Fin n, w i) =
      (∑ i : Fin n, (x i + y i))) :
    (∑ i : Fin n, ∑ j : Fin n, cauchyInverseEntry n x y i j) =
      (∑ i : Fin n, (x i + y i)) := by
  calc
    (∑ i : Fin n, ∑ j : Fin n, cauchyInverseEntry n x y i j) =
        ∑ i : Fin n, w i := by
          apply Finset.sum_congr rfl
          intro i _
          exact hrows i
    _ = ∑ i : Fin n, (x i + y i) := hmoment

/-- Ordered positive Cauchy nodes make the determinant product strictly
positive. -/
theorem cauchyDetFormula_pos_of_strictMono_of_pos
    {n : ℕ} (x y : RVec n)
    (hx : StrictMono x) (hy : StrictMono y)
    (hsum : ∀ i j, 0 < x i + y j) :
    0 < cauchyDetFormula n x y := by
  rw [cauchyDetFormula_eq_num_div_den]
  apply div_pos
  · unfold cauchyDetNumerator
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    exact mul_pos (sub_pos.mpr (hx hij)) (sub_pos.mpr (hy hij))
  · unfold cauchyDetDenominator
    exact Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => hsum i j

/-- Generic ordered positive Cauchy matrices are strictly totally positive
once the cited Cauchy minor determinant identity is supplied for every
subfamily. -/
theorem cauchy_isStrictlyTotallyPositive_of_minorDeterminants
    {m n : ℕ} (x : RVec m) (y : RVec n)
    (hx : StrictMono x) (hy : StrictMono y)
    (hsum : ∀ i j, 0 < x i + y j)
    (hminor : ∀ (k : ℕ) (r : Fin k → Fin m) (c : Fin k → Fin n),
      StrictMono r → StrictMono c →
        Matrix.det (fun i j => cauchyMatrix x y (r i) (c j)) =
          cauchyDetFormula k (fun i => x (r i)) (fun j => y (c j))) :
    IsStrictlyTotallyPositive (cauchyMatrix x y) := by
  intro k hk r c hr hc
  rw [hminor k r c hr hc]
  apply cauchyDetFormula_pos_of_strictMono_of_pos
  · exact hx.comp hr
  · exact hy.comp hc
  · exact fun i j => hsum (r i) (c j)

/-- The Hilbert total-positivity prose is the consecutive-positive-node
specialization of the genuine generic Cauchy-minor determinant identity. -/
theorem hilbert_isStrictlyTotallyPositive_of_cauchyMinors
    (hminor : ∀ (k : ℕ) (r c : Fin k → ℕ),
      StrictMono r → StrictMono c →
        Matrix.det (fun i j : Fin k =>
          (1 : ℝ) / (r i + c j + 1 : ℕ)) =
          cauchyDetFormula k
            (fun i => (r i : ℝ)) (fun j => (c j + 1 : ℕ))) :
    ∀ n, IsStrictlyTotallyPositive (hilbertMatrix n) := by
  intro n k hk r c hr hc
  let rn : Fin k → ℕ := fun i => (r i).val
  let cn : Fin k → ℕ := fun i => (c i).val
  have hrn : StrictMono rn := fun _ _ hij => by
    exact_mod_cast hr hij
  have hcn : StrictMono cn := fun _ _ hij => by
    exact_mod_cast hc hij
  change 0 < Matrix.det (fun i j : Fin k =>
    (1 : ℝ) / (rn i + cn j + 1 : ℕ))
  rw [hminor k rn cn hrn hcn]
  apply cauchyDetFormula_pos_of_strictMono_of_pos
  · exact fun _ _ hij => by exact_mod_cast hrn hij
  · exact fun _ _ hij => by
      exact_mod_cast Nat.add_lt_add_right (hcn hij) 1
  · intro i j
    positivity

/-! ## Pascal similarity, perturbation, and cube roots -/

/-- The signed Pascal involution conjugates the symmetric Pascal matrix to
its proved inverse.  Unlike the citation-dependent spectral consequence,
this matrix identity follows entirely from the local binomial algebra. -/
theorem signedPascal_conj_pascalMatrix (n : ℕ) :
    signedPascal n * pascalMatrix n * signedPascal n =
      (signedPascal n).transpose * signedPascal n := by
  rw [pascalMatrix_eq_lower_mul_transpose,
    signedPascal_eq_lower_mul_signDiagonal]
  have hleft := pascal_lower_sign_lower_eq_sign n
  calc
    (pascalLower n * pascalSignDiagonal n) *
        (pascalLower n * (pascalLower n).transpose) *
        (pascalLower n * pascalSignDiagonal n) =
      (pascalLower n * pascalSignDiagonal n * pascalLower n) *
        ((pascalLower n).transpose * pascalLower n) *
        pascalSignDiagonal n := by noncomm_ring
    _ = pascalSignDiagonal n *
        ((pascalLower n).transpose * pascalLower n) *
        pascalSignDiagonal n := by rw [hleft]
    _ = (pascalLower n * pascalSignDiagonal n).transpose *
        (pascalLower n * pascalSignDiagonal n) := by
      rw [Matrix.transpose_mul, pascalSignDiagonal_transpose]
      noncomm_ring

/-- The reciprocal-eigenvalue consequence of the proved Pascal similarity.
No spectral theorem is assumed: the proof applies the explicit inverse and
the signed involution directly to an eigenvector. -/
theorem pascal_reciprocal_eigenpair
    {n : ℕ} (lambda : ℝ) (v : RVec n)
    (hlambda : lambda ≠ 0) (hv : v ≠ 0)
    (heigen : Matrix.mulVec (pascalMatrix n) v = lambda • v) :
    let w := Matrix.mulVec (signedPascal n) v
    w ≠ 0 ∧ Matrix.mulVec (pascalMatrix n) w = lambda⁻¹ • w := by
  let P := pascalMatrix n
  let S := signedPascal n
  let B := (signedPascal n).transpose * signedPascal n
  let w := Matrix.mulVec S v
  have heigenP : Matrix.mulVec P v = lambda • v := by
    simpa [P] using heigen
  have hSS : S * S = (1 : RSqMat n) := signedPascal_mul_self n
  have hPw : P * B = (1 : RSqMat n) := pascalMatrix_mul_signedGram n
  have hsim : S * P * S = B := signedPascal_conj_pascalMatrix n
  have hSw : Matrix.mulVec S w = v := by
    rw [show w = Matrix.mulVec S v by rfl, Matrix.mulVec_mulVec, hSS,
      Matrix.one_mulVec]
  have hw : w ≠ 0 := by
    intro hw0
    apply hv
    rw [← hSw, hw0]
    simp
  have hBw : Matrix.mulVec B w = lambda • w := by
    calc
      Matrix.mulVec B w = Matrix.mulVec (S * P * S) w := by rw [hsim]
      _ = Matrix.mulVec (S * P) (Matrix.mulVec S w) := by
        exact (Matrix.mulVec_mulVec w (S * P) S).symm
      _ = Matrix.mulVec S (Matrix.mulVec P (Matrix.mulVec S w)) := by
        exact (Matrix.mulVec_mulVec (Matrix.mulVec S w) S P).symm
      _ = Matrix.mulVec S (Matrix.mulVec P v) := by rw [hSw]
      _ = Matrix.mulVec S (lambda • v) := by rw [heigenP]
      _ = lambda • w := by rw [Matrix.mulVec_smul]
  have happly := congrArg (Matrix.mulVec P) hBw
  have hscale : w = lambda • Matrix.mulVec P w := by
    simpa [Matrix.mulVec_mulVec, hPw, Matrix.mulVec_smul] using happly
  change w ≠ 0 ∧ Matrix.mulVec P w = lambda⁻¹ • w
  refine ⟨hw, ?_⟩
  funext i
  have hi := congrFun hscale i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  calc
    Matrix.mulVec P w i = lambda⁻¹ * (lambda * Matrix.mulVec P w i) := by
      field_simp
    _ = lambda⁻¹ * w i := by rw [← hi]
    _ = (lambda⁻¹ • w) i := by simp

/-- A concrete coordinate certificate for a singular rank-one perturbation.
The cancellation premise is the upstream entrywise arithmetic calculation,
not a matrix-singularity assumption. -/
theorem singular_rankOne_perturbation_of_coordinate_cancellation
    {n : ℕ} (A : RSqMat n) (u v z : RVec n)
    (hz : z ≠ 0)
    (hcancel : ∀ i : Fin n,
      (∑ j : Fin n, (A i j + u i * v j) * z j) = 0) :
    ∃ E : RSqMat n, (∀ i j, E i j = u i * v j) ∧
      ∃ z ≠ 0, Matrix.mulVec (A + E) z = 0 := by
  refine ⟨fun i j => u i * v j, fun _ _ => rfl, z, hz, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hcancel i

/-- The rank-one perturbation contract is nonvacuous already for the
order-one Pascal matrix: subtracting its sole entry makes it singular. -/
theorem pascal_order_one_has_singular_rankOne_perturbation :
    ∃ E : RSqMat 1, (∀ i j, E i j = (-1 : ℝ) * 1) ∧
      ∃ z ≠ 0, Matrix.mulVec (pascalMatrix 1 + E) z = 0 := by
  apply singular_rankOne_perturbation_of_coordinate_cancellation
    (pascalMatrix 1) (fun _ => -1) (fun _ => 1) (fun _ => 1)
  · intro h
    have := congrFun h (0 : Fin 1)
    norm_num at this
  · intro i
    fin_cases i
    norm_num [pascalMatrix, Fin.sum_univ_succ]

/-- Two source-specific intermediate product identities are sufficient for a
printed Pascal cube-root candidate.  Neither premise is the final cube
identity. -/
theorem pascal_cubeRoot_of_square_and_final_product
    {n : ℕ} (R S : RSqMat n)
    (hsquare : R * R = S)
    (hfinal : S * R = pascalMatrix n) :
    R * R * R = pascalMatrix n := by
  rw [hsquare, hfinal]

/-- Concrete producer for the cube-root transfer domain at order one. -/
theorem pascal_order_one_cubeRoot_producer :
    (1 : RSqMat 1) * 1 = 1 ∧
      (1 : RSqMat 1) * 1 = pascalMatrix 1 := by
  constructor
  · simp
  · ext i j
    fin_cases i
    fin_cases j
    norm_num [pascalMatrix]

/-! ## Toeplitz discrete-sine and companion transfers -/

/-- The displayed sine vector for the symmetric tridiagonal Toeplitz family. -/
noncomputable def toeplitzSineVector (n : ℕ) (k : Fin n) : RVec n :=
  fun i => Real.sin (((i.val + 1 : ℕ) * (k.val + 1 : ℕ) : ℝ) *
    Real.pi / (n + 1 : ℕ))

/-- The displayed eigenvalue `d + 2c cos(k*pi/(n+1))`, with source index
`k=1,...,n` translated to `Fin n`. -/
noncomputable def symmetricToeplitzEigenvalue
    (n : ℕ) (c d : ℝ) (k : Fin n) : ℝ :=
  d + 2 * c * Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi /
    (n + 1 : ℕ))

/-- The trigonometric component summation is the genuine upstream fact; this
theorem packages it as the printed matrix eigenvector equation. -/
theorem symmetricToeplitz_eigenpair_of_sine_component_identity
    {n : ℕ} (c d : ℝ)
    (hcomponent : ∀ (k i : Fin n),
      (∑ j : Fin n, tridiagonalToeplitz n c d c i j *
        toeplitzSineVector n k j) =
        symmetricToeplitzEigenvalue n c d k * toeplitzSineVector n k i) :
    ∀ k : Fin n,
      Matrix.mulVec (tridiagonalToeplitz n c d c)
        (toeplitzSineVector n k) =
      symmetricToeplitzEigenvalue n c d k • toeplitzSineVector n k := by
  intro k
  funext i
  simpa [Matrix.mulVec, dotProduct] using hcomponent k i

/-- At order one the displayed sine eigenpair is fully discharged, providing
a concrete instance of the discrete-sine transfer domain. -/
theorem symmetricToeplitz_order_one_sine_eigenpair (c d : ℝ) :
    Matrix.mulVec (tridiagonalToeplitz 1 c d c)
        (toeplitzSineVector 1 0) =
      symmetricToeplitzEigenvalue 1 c d 0 • toeplitzSineVector 1 0 := by
  funext i
  fin_cases i
  norm_num [Matrix.mulVec, dotProduct, tridiagonalToeplitz,
    toeplitzSineVector, symmetricToeplitzEigenvalue]

/-- Adding the independent-vector theorem to the sine component identity
produces the full explicit eigenbasis certificate used by the spectrum and
condition-number arguments. -/
theorem symmetricToeplitz_has_discreteSine_eigenbasis
    {n : ℕ} (c d : ℝ)
    (hcomponent : ∀ (k i : Fin n),
      (∑ j : Fin n, tridiagonalToeplitz n c d c i j *
        toeplitzSineVector n k j) =
        symmetricToeplitzEigenvalue n c d k * toeplitzSineVector n k i)
    (hindependent : LinearIndependent ℝ (toeplitzSineVector n)) :
    (∀ k : Fin n,
      Matrix.mulVec (tridiagonalToeplitz n c d c)
        (toeplitzSineVector n k) =
          symmetricToeplitzEigenvalue n c d k • toeplitzSineVector n k) ∧
      LinearIndependent ℝ (toeplitzSineVector n) :=
  ⟨symmetricToeplitz_eigenpair_of_sine_component_identity c d hcomponent,
    hindependent⟩

/-- The monic polynomial encoded by the companion matrix: `X^n - sum a_k X^k`. -/
noncomputable def companionCharacteristicFormula
    (n : ℕ) (a : ℕ → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ n -
    ∑ k ∈ Finset.range n, Polynomial.monomial k (a k)

theorem companionCharacteristicFormula_coeff
    (n : ℕ) (a : ℕ → ℂ) (k : ℕ) :
    (companionCharacteristicFormula n a).coeff k =
      if k = n then 1 else if k < n then -a k else 0 := by
  have hsum :
      (∑ b ∈ Finset.range n, Polynomial.monomial b (a b)).coeff k =
        if k < n then a k else 0 := by
    rw [Polynomial.finset_sum_coeff]
    by_cases hk : k < n
    · rw [Finset.sum_eq_single k]
      · simp [hk]
      · intro b hb hbk
        simp [Polynomial.coeff_monomial, hbk]
      · simp [hk]
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro b hb
      rw [Polynomial.coeff_monomial]
      simp only [ite_eq_right_iff]
      intro hbk
      subst b
      exact (hk (Finset.mem_range.mp hb)).elim
  rw [companionCharacteristicFormula, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, hsum]
  by_cases hkn : k = n
  · subst k
    simp
  · by_cases hk : k < n <;> simp [hkn, hk]

/-- A determinant recurrence normally yields this coefficient identity.
Once supplied, polynomial extensionality gives the printed characteristic
polynomial without assuming polynomial equality itself. -/
theorem companion_charpoly_of_determinant_coefficient_recurrence
    (n : ℕ) (a : ℕ → ℂ)
    (hcoeff : ∀ k : ℕ,
      (Matrix.charpoly (companionMatrix n a)).coeff k =
        if k = n then 1 else if k < n then -a k else 0) :
    Matrix.charpoly (companionMatrix n a) =
      companionCharacteristicFormula n a := by
  ext k
  rw [hcoeff, companionCharacteristicFormula_coeff]

/-- Cyclicity is the standard explicit-domain bridge to the companion
matrix's nonderogatory property. -/
def IsCyclicFor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : Prop :=
  LinearIndependent ℂ (fun k : Fin n => Matrix.mulVec (A ^ k.val) v)

def IsNonderogatoryByCyclicity {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ v, IsCyclicFor A v

/-- The explicit Krylov-basis calculation, rather than nonderogatoriness, is
the genuine upstream premise. -/
theorem companion_isNonderogatory_of_krylov_cyclic
    {n : ℕ} (a : ℕ → ℂ) (v : Fin n → ℂ)
    (hcyclic : LinearIndependent ℂ
      (fun k : Fin n => Matrix.mulVec ((companionMatrix n a) ^ k.val) v)) :
    IsNonderogatoryByCyclicity (companionMatrix n a) :=
  ⟨v, hcyclic⟩

/-- The cyclicity domain is inhabited for every order-one companion matrix. -/
theorem companion_order_one_isNonderogatoryByCyclicity (a : ℕ → ℂ) :
    IsNonderogatoryByCyclicity (companionMatrix 1 a) := by
  refine ⟨fun _ => 1, ?_⟩
  unfold IsCyclicFor
  rw [linearIndependent_unique_iff]
  intro hzero
  have hz := congrFun hzero (0 : Fin 1)
  norm_num [IsCyclicFor, Matrix.one_mulVec] at hz

/-- `1 + sum |a_k|^2`, the trace parameter in the two exceptional squared
singular values of a companion matrix. -/
noncomputable def companionSingularAlpha (n : ℕ) (a : ℕ → ℂ) : ℝ :=
  1 + ∑ k ∈ Finset.range n, ‖a k‖ ^ 2

/-- The polynomial whose roots are the two exceptional squared singular
values; the other `n-2` roots of the Gram characteristic polynomial are one. -/
noncomputable def companionExceptionalSingularSqPolynomial
    (n : ℕ) (a : ℕ → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ 2 -
    Polynomial.C (companionSingularAlpha n a : ℂ) * Polynomial.X +
    Polynomial.C ((‖a 0‖ ^ 2 : ℝ) : ℂ)

/-- Explicit-domain transfer of the companion singular-value formula from
the two genuine upstream low-rank calculations: an exact Gram identity and
the characteristic polynomial of that low-rank Gram form. -/
theorem companion_gram_charpoly_of_lowRank_identity
    {n : ℕ} (a : ℕ → ℂ) (G : Matrix (Fin n) (Fin n) ℂ)
    (hgram : (companionMatrix n a).conjTranspose * companionMatrix n a = G)
    (hlowRank : Matrix.charpoly G =
      (Polynomial.X - 1) ^ (n - 2) *
        companionExceptionalSingularSqPolynomial n a) :
    Matrix.charpoly
        ((companionMatrix n a).conjTranspose * companionMatrix n a) =
      (Polynomial.X - 1) ^ (n - 2) *
        companionExceptionalSingularSqPolynomial n a := by
  rw [hgram, hlowRank]

end LeanFpAnalysis.FP
