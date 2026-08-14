import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- Euclidean norm in the finite real-vector notation used by P07. -/
noncomputable def p07VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Rectangular matrix-vector multiplication. -/
noncomputable def p07MatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Product of two compatible finite rectangular matrices. -/
noncomputable def p07RectMatMul {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ) :
    Fin m → Fin p → ℝ :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Homogeneous rectangular operator-2 upper-bound certificate. -/
def p07RectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x, p07VecNorm2 (p07MatVec A x) ≤ c * p07VecNorm2 x

/-- Homogeneous lower singular-value certificate. -/
def p07RectLowerBound {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x, c * p07VecNorm2 x ≤ p07VecNorm2 (p07MatVec A x)

/-- A rectangular matrix acts isometrically on Euclidean vectors. -/
def p07Isometry {m n : ℕ} (Q : Fin m → Fin n → ℝ) : Prop :=
  ∀ x, p07VecNorm2 (p07MatVec Q x) = p07VecNorm2 x

/-- Paired lower/upper singular-value certificate used to express the
condition-number identity in P07 Lemma 2.1 without choosing singular values. -/
def p07ConditionCertificate {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (lower upper : ℝ) : Prop :=
  p07RectLowerBound A lower ∧ p07RectOpNorm2Le A upper

/-- Identity matrix in P07's finite real-matrix notation. -/
noncomputable def p07FiniteId {n : ℕ} : Fin n → Fin n → ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Pointwise addition of rectangular matrices. -/
def p07RectAdd {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j ↦ A i j + B i j

/-- Pointwise subtraction of rectangular matrices. -/
def p07RectSub {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j ↦ A i j - B i j

/-- Upper-triangularity of the computed factor inherited from Lemma 3.1. -/
def p07UpperTriangular {n : ℕ} (R : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, j.val < i.val → R i j = 0

/-- Scalar floating-point operations used by the forward-substitution trace.
Each operation has the standard relative-error semantics used in section 2. -/
structure P07ScalarArithmeticModel where
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  flAdd : ℝ → ℝ → ℝ
  flSub : ℝ → ℝ → ℝ
  flMul : ℝ → ℝ → ℝ
  flDiv : ℝ → ℝ → ℝ
  add_model : ∀ x y, ∃ delta, |delta| ≤ unitRoundoff ∧
    flAdd x y = (x + y) * (1 + delta)
  sub_model : ∀ x y, ∃ delta, |delta| ≤ unitRoundoff ∧
    flSub x y = (x - y) * (1 + delta)
  mul_model : ∀ x y, ∃ delta, |delta| ≤ unitRoundoff ∧
    flMul x y = (x * y) * (1 + delta)
  div_model : ∀ x y, y ≠ 0 → ∃ delta, |delta| ≤ unitRoundoff ∧
    flDiv x y = (x / y) * (1 + delta)

/-- Rounded dot product over the entries preceding column `j`. -/
noncomputable def p07RoundedPrefixDot
    (model : P07ScalarArithmeticModel) {m n : ℕ}
    (Y : Fin m → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  recursiveSum model.flAdd j.val fun k : Fin j.val ↦
    let k' : Fin n := ⟨k.val, lt_trans k.isLt j.isLt⟩
    model.flMul (Y i k') (R k' j)

/-- A row-wise finite-precision forward-substitution execution for `Y R = A`.
For upper triangular `R`, each output entry uses only earlier columns. -/
structure P07ForwardSubstitutionTrace
    (model : P07ScalarArithmeticModel) {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (R : Fin n → Fin n → ℝ) where
  output : Fin m → Fin n → ℝ
  diagonal_nonzero : ∀ j, R j j ≠ 0
  recurrence : ∀ i j,
    output i j =
      model.flDiv
        (model.flSub (A i j) (p07RoundedPrefixDot model output R i j))
        (R j j)

/-- The finite-precision sketch multiplication and Householder QR output from
Lemma 3.1 whose computed inverse is used in Lemma 3.2. -/
structure P07Lemma31ComputedPreconditioner (m s n : ℕ) where
  columns_pos : 0 < n
  sketch_gt_columns : n < s
  rows_gt_sketch : s < m
  A : Fin m → Fin n → ℝ
  S : Fin s → Fin m → ℝ
  computedSketch : Fin s → Fin n → ℝ
  sketchError : Fin s → Fin n → ℝ
  qrError : Fin s → Fin n → ℝ
  Qtilde : Fin s → Fin n → ℝ
  RHat : Fin n → Fin n → ℝ
  RHatInv : Fin n → Fin n → ℝ
  A_full_column_rank : Function.Injective (p07MatVec A)
  sketch_full_column_rank :
    Function.Injective (p07MatVec (p07RectMatMul S A))
  sketch_multiplication :
    computedSketch = p07RectAdd (p07RectMatMul S A) sketchError
  computed_householder_qr :
    p07RectMatMul Qtilde RHat = p07RectAdd computedSketch qrError
  qtilde_isometry : p07Isometry Qtilde
  rhat_upper_triangular : p07UpperTriangular RHat
  rhat_inverse_left : p07RectMatMul RHat RHatInv = p07FiniteId
  rhat_inverse_right : p07RectMatMul RHatInv RHat = p07FiniteId

/-- The exact preconditioned matrix `A RHat^{-1}` in Lemma 3.2. -/
noncomputable def p07ExactPreconditionedMatrix {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n) :
    Fin m → Fin n → ℝ :=
  p07RectMatMul pre.A pre.RHatInv

/-- The finite-precision forward-substitution output and its exact additive
error `DeltaY = YHat - A RHat^{-1}` from Lemma 3.2. -/
structure P07Lemma32ForwardRun {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    (model : P07ScalarArithmeticModel) where
  forwardSubstitution : P07ForwardSubstitutionTrace model pre.A pre.RHat
  DeltaY : Fin m → Fin n → ℝ
  deltaY_definition :
    DeltaY = p07RectSub forwardSubstitution.output
      (p07ExactPreconditionedMatrix pre)

/-- Exact attained largest and smallest singular-value data for a finite
rectangular matrix. The bound-plus-attainment pairs prevent the values from
being arbitrary loose certificates. -/
structure P07RectSpectralExtrema {m n : ℕ}
    (A : Fin m → Fin n → ℝ) where
  upper : ℝ
  lower : ℝ
  upper_nonneg : 0 ≤ upper
  lower_nonneg : 0 ≤ lower
  upper_bound : p07RectOpNorm2Le A upper
  lower_bound : p07RectLowerBound A lower
  upper_attained : ∃ x : Fin n → ℝ,
    p07VecNorm2 x = 1 ∧ p07VecNorm2 (p07MatVec A x) = upper
  lower_attained : ∃ x : Fin n → ℝ,
    p07VecNorm2 x = 1 ∧ p07VecNorm2 (p07MatVec A x) = lower

/-- The four Penrose equations identifying an actual Moore--Penrose
pseudoinverse, rather than an arbitrary left inverse. -/
structure P07MoorePenrosePseudoinverse {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ) : Prop where
  reproduces_matrix :
    p07RectMatMul (p07RectMatMul A Aplus) A = A
  reproduces_pseudoinverse :
    p07RectMatMul (p07RectMatMul Aplus A) Aplus = Aplus
  range_projection_symmetric :
    Matrix.transpose (p07RectMatMul A Aplus) = p07RectMatMul A Aplus
  domain_projection_symmetric :
    Matrix.transpose (p07RectMatMul Aplus A) = p07RectMatMul Aplus A

/-- Exact spectral data for a matrix and its Moore--Penrose pseudoinverse.
When the smallest singular value is nonzero, the final field records the
standard identity `||A^dagger||_2 = 1 / sigma_min(A)`. -/
structure P07MatrixPseudoinverseSpectralData {m n : ℕ}
    (A : Fin m → Fin n → ℝ) where
  matrixSpectrum : P07RectSpectralExtrema A
  pseudoinverse : Fin n → Fin m → ℝ
  pseudoinverse_penrose :
    P07MoorePenrosePseudoinverse A pseudoinverse
  pseudoinverseSpectrum : P07RectSpectralExtrema pseudoinverse
  pseudoinverse_norm_eq_reciprocal :
    matrixSpectrum.lower ≠ 0 →
      pseudoinverseSpectrum.upper = matrixSpectrum.lower⁻¹

/-- Spectral 2-norm condition number represented using the actual
Moore--Penrose pseudoinverse. -/
noncomputable def p07ConditionNumber2 {m n : ℕ}
    {A : Fin m → Fin n → ℝ}
    (data : P07MatrixPseudoinverseSpectralData A) : ℝ :=
  data.matrixSpectrum.upper * data.pseudoinverseSpectrum.upper

/-- The exact perturbation parameter
`epsilon_2 = ||DeltaY||_2 ||(A RHat^{-1})^dagger||_2`. -/
noncomputable def p07Lemma32Epsilon {m n : ℕ}
    {A : Fin m → Fin n → ℝ}
    (exactData : P07MatrixPseudoinverseSpectralData A)
    {DeltaY : Fin m → Fin n → ℝ}
    (errorSpectrum : P07RectSpectralExtrema DeltaY) : ℝ :=
  errorSpectrum.upper * exactData.pseudoinverseSpectrum.upper

/-- Exact error matrix expanded in the proof of P07 Theorem 3.5. -/
noncomputable def p07BackwardError {m n : ℕ}
    (Y ΔY : Fin m → Fin n → ℝ)
    (R ΔR : Fin n → Fin n → ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j ↦
    (p07RectMatMul Y R i j - A i j) +
      (p07RectMatMul ΔY R i j +
        (p07RectMatMul Y ΔR i j + p07RectMatMul ΔY ΔR i j))

/-- Pointwise vector addition for the perturbed right-hand side in P07
Theorem 3.5. -/
def p07VecAdd {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ x i + y i

/-- The normal equation characterizing a least-squares solution. This is the
well-defined perturbed-data relation used for Theorem 3.5's tall system. -/
def p07LeastSquaresNormalEquation {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ j : Fin n,
    ∑ i : Fin m, A i j * (p07MatVec A x i - b i) = 0

/-- The backward-error witness assumed for unpreconditioned LSQR in equation
(3.9). `DeltaYHat` is distinct from the forward-substitution error in
`P07Lemma32ForwardRun`. -/
structure P07LSQRBackwardWitness {m n : ℕ}
    (YHat : Fin m → Fin n → ℝ) (b : Fin m → ℝ) where
  DeltaYHat : Fin m → Fin n → ℝ
  deltaB : Fin m → ℝ
  zHat : Fin n → ℝ
  perturbedPseudoinverse : Fin n → Fin m → ℝ
  pseudoinverse_penrose :
    P07MoorePenrosePseudoinverse
      (p07RectAdd YHat DeltaYHat) perturbedPseudoinverse
  iterate_relation :
    zHat = p07MatVec perturbedPseudoinverse (p07VecAdd b deltaB)

/-- Equation (2.6) for the final back substitution in Algorithm 1.3. -/
structure P07Equation26BackSubstitution {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    (u : ℝ) (rSpectrum : P07RectSpectralExtrema pre.RHat)
    (zHat : Fin n → ℝ) where
  DeltaRHat : Fin n → Fin n → ℝ
  xHat : Fin n → ℝ
  perturbedRInv : Fin n → Fin n → ℝ
  inverse_left :
    p07RectMatMul (p07RectAdd pre.RHat DeltaRHat) perturbedRInv =
      p07FiniteId
  inverse_right :
    p07RectMatMul perturbedRInv (p07RectAdd pre.RHat DeltaRHat) =
      p07FiniteId
  backward_equation :
    p07MatVec (p07RectAdd pre.RHat DeltaRHat) xHat = zHat
  deltaR_bound :
    p07RectOpNorm2Le DeltaRHat
      (Real.sqrt n * gamma u n * rSpectrum.upper)

/-- Rowwise forward-substitution error used in the proof of Theorem 3.5,
including the exact spectral consequence stated immediately after it. -/
structure P07ForwardFormationError {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    {model : P07ScalarArithmeticModel}
    (forwardRun : P07Lemma32ForwardRun pre model)
    (u : ℝ) (rSpectrum : P07RectSpectralExtrema pre.RHat)
    (ySpectrum : P07RectSpectralExtrema
      forwardRun.forwardSubstitution.output) where
  rowPerturbation : Fin m → Fin n → Fin n → ℝ
  row_relation : ∀ i j,
    p07RectMatMul forwardRun.forwardSubstitution.output pre.RHat i j -
        pre.A i j =
      -∑ k : Fin n,
        forwardRun.forwardSubstitution.output i k * rowPerturbation i k j
  componentwise_bound : ∀ i j k,
    |rowPerturbation i j k| ≤ gamma u n * |pre.RHat j k|
  residual_bound :
    p07RectOpNorm2Le
      (fun i j ↦
        p07RectMatMul forwardRun.forwardSubstitution.output pre.RHat i j -
          pre.A i j)
      ((n : ℝ) * gamma u n * rSpectrum.upper * ySpectrum.upper)

/-- The Algorithm 1.3 execution data needed by the unnumbered backward-error
result in the proof of Theorem 3.5. LSQR is applied directly to the explicitly
formed `YHat`; no SAS initialization is represented. -/
structure P07SAABlendenpikRun {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    (model : P07ScalarArithmeticModel)
    (forwardRun : P07Lemma32ForwardRun pre model)
    (u : ℝ) where
  unit_roundoff : model.unitRoundoff = u
  gamma_valid : GammaValid u n
  b : Fin m → ℝ
  rSpectrum : P07RectSpectralExtrema pre.RHat
  ySpectrum : P07RectSpectralExtrema forwardRun.forwardSubstitution.output
  formationError :
    P07ForwardFormationError pre forwardRun u rSpectrum ySpectrum
  lsqr : P07LSQRBackwardWitness forwardRun.forwardSubstitution.output b
  lsqrDeltaSpectrum : P07RectSpectralExtrema lsqr.DeltaYHat
  backSubstitution :
    P07Equation26BackSubstitution pre u rSpectrum lsqr.zHat

/-- The exact four-term `DeltaA` in the proof of P07 Theorem 3.5. -/
noncomputable def p07Theorem35DeltaA {m s n : ℕ}
    {pre : P07Lemma31ComputedPreconditioner m s n}
    {model : P07ScalarArithmeticModel}
    {forwardRun : P07Lemma32ForwardRun pre model} {u : ℝ}
    (run : P07SAABlendenpikRun pre model forwardRun u) :
    Fin m → Fin n → ℝ :=
  p07BackwardError forwardRun.forwardSubstitution.output
    run.lsqr.DeltaYHat pre.RHat run.backSubstitution.DeltaRHat pre.A

/-- The perturbed matrix `A + DeltaA` associated with the SAA output. -/
noncomputable def p07Theorem35PerturbedA {m s n : ℕ}
    {pre : P07Lemma31ComputedPreconditioner m s n}
    {model : P07ScalarArithmeticModel}
    {forwardRun : P07Lemma32ForwardRun pre model} {u : ℝ}
    (run : P07SAABlendenpikRun pre model forwardRun u) :
    Fin m → Fin n → ℝ :=
  p07RectAdd pre.A (p07Theorem35DeltaA run)

/-- The matrix `YHat + DeltaYHat` in the assumed LSQR backward error. -/
def p07Theorem35PerturbedY {m s n : ℕ}
    {pre : P07Lemma31ComputedPreconditioner m s n}
    {model : P07ScalarArithmeticModel}
    {forwardRun : P07Lemma32ForwardRun pre model} {u : ℝ}
    (run : P07SAABlendenpikRun pre model forwardRun u) :
    Fin m → Fin n → ℝ :=
  p07RectAdd forwardRun.forwardSubstitution.output run.lsqr.DeltaYHat

/-- The matrix `RHat + DeltaRHat` in the final back substitution. -/
def p07Theorem35PerturbedR {m s n : ℕ}
    {pre : P07Lemma31ComputedPreconditioner m s n}
    {model : P07ScalarArithmeticModel}
    {forwardRun : P07Lemma32ForwardRun pre model} {u : ℝ}
    (run : P07SAABlendenpikRun pre model forwardRun u) :
    Fin n → Fin n → ℝ :=
  p07RectAdd pre.RHat run.backSubstitution.DeltaRHat

/-- The perturbed right-hand side `b + deltaB` retained by Theorem 3.5. -/
def p07Theorem35PerturbedB {m s n : ℕ}
    {pre : P07Lemma31ComputedPreconditioner m s n}
    {model : P07ScalarArithmeticModel}
    {forwardRun : P07Lemma32ForwardRun pre model} {u : ℝ}
    (run : P07SAABlendenpikRun pre model forwardRun u) : Fin m → ℝ :=
  p07VecAdd run.b run.lsqr.deltaB

end HighamBench
