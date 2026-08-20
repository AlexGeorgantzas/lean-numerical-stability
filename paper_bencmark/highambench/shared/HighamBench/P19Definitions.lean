import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed

namespace HighamBench

open scoped BigOperators Matrix.Norms.L2Operator Matrix.Norms.Frobenius

/-- A finite square real matrix in the P19 model. -/
abbrev P19Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A finite rectangular real matrix in the P19 model. -/
abbrev P19RectMatrix (m k : ℕ) := Matrix (Fin m) (Fin k) ℝ

/-- A finite real vector in the P19 model. -/
abbrev P19Vector (n : ℕ) := Fin n → ℝ

/-- Paper-scoped squared Euclidean norm for finite GMRES error vectors. -/
noncomputable def p19VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Paper-scoped Euclidean norm for finite GMRES error vectors. -/
noncomputable def p19VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p19VecNorm2Sq x)

/-- Add two paper-scoped finite error vectors. -/
def p19Add {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i + y i

/-- Scale a paper-scoped finite error vector. -/
def p19Scale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a * x i

/-- Exact scalar envelope corresponding to `ξ` in equation (3.8). -/
def p19ModularEnvelope (alpha beta lambda epsilonC epsilonB ug epsilonX : ℝ) : ℝ :=
  alpha * epsilonC + beta * epsilonB + beta * ug + lambda * epsilonX

/-- Exact finite matrix-vector multiplication. -/
noncomputable def p19MatVec {n : ℕ} (A : P19Matrix n)
    (x : P19Vector n) : P19Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Exact finite rectangular matrix-vector multiplication. -/
noncomputable def p19RectMatVec {m k : ℕ} (A : P19RectMatrix m k)
    (x : P19Vector k) : P19Vector m :=
  fun i ↦ ∑ j : Fin k, A i j * x j

/-- Exact multiplication of a square matrix by a rectangular matrix. -/
noncomputable def p19SquareRectMul {n k : ℕ} (A : P19Matrix n)
    (B : P19RectMatrix n k) : P19RectMatrix n k :=
  fun i j ↦ ∑ q : Fin n, A i q * B q j

/-- Exact multiplication of two conforming rectangular matrices. -/
noncomputable def p19RectMatMul {m k q : ℕ} (A : P19RectMatrix m k)
    (B : P19RectMatrix k q) : P19RectMatrix m q :=
  fun i j ↦ ∑ r : Fin k, A i r * B r j

/-- The Frobenius norm used by the matrix perturbation models in (3.2)-(3.8). -/
noncomputable def p19FrobNorm {m k : ℕ} (A : P19RectMatrix m k) : ℝ :=
  ‖A‖

/-- A matrix column represented as a finite vector. -/
def p19Column {m k : ℕ} (A : P19RectMatrix m k) (j : Fin k) : P19Vector m :=
  fun i ↦ A i j

/-- Append a vector as the first column of a rectangular matrix. -/
noncomputable def p19Augment {n k : ℕ} (b : P19Vector n)
    (C : P19RectMatrix n k) : P19RectMatrix n (k + 1) :=
  fun i ↦ Fin.cases (b i) (fun j ↦ C i j)

/-- The vector `beta * e_1` in the MGS factorization (3.1). -/
def p19ScaledFirstBasisVector {k : ℕ} (beta : ℝ) : P19Vector (k + 1) :=
  fun i ↦ if i.val = 0 then beta else 0

/-- The structural upper-Hessenberg condition on the MGS factor. -/
def p19IsUpperHessenberg {k : ℕ}
    (H : P19RectMatrix (k + 1) k) : Prop :=
  ∀ i j, j.val + 1 < i.val → H i j = 0

/-- Two square matrices are certified inverses through their exact actions. -/
def p19InversePair {n : ℕ} (A Ainv : P19Matrix n) : Prop :=
  (∀ x : P19Vector n, p19MatVec Ainv (p19MatVec A x) = x) ∧
    ∀ x : P19Vector n, p19MatVec A (p19MatVec Ainv x) = x

/-- Exact least-squares optimality for line 3 of Algorithm 2. -/
def p19IsLeastSquaresSolution {m k : ℕ} (A : P19RectMatrix m k)
    (b : P19Vector m) (y : P19Vector k) : Prop :=
  ∀ z : P19Vector k,
    p19VecNorm2 (b - p19RectMatVec A y) ≤
      p19VecNorm2 (b - p19RectMatVec A z)

/-- A rectangular matrix has full column rank when its exact action is injective. -/
def p19FullColumnRank {m k : ℕ} (A : P19RectMatrix m k) : Prop :=
  Function.Injective (p19RectMatVec A)

/-- Certified extremal singular values for a finite real matrix. The gain and
attainment clauses give the exact Euclidean meanings of `sigma_min` and
`sigma_max` without depending on a particular SVD implementation. -/
structure P19SingularValueData {m k : ℕ} (A : P19RectMatrix m k) where
  sigmaMin : ℝ
  sigmaMax : ℝ
  sigmaMin_nonneg : 0 ≤ sigmaMin
  sigmaMax_nonneg : 0 ≤ sigmaMax
  lower_gain : ∀ x : P19Vector k,
    sigmaMin * p19VecNorm2 x ≤ p19VecNorm2 (p19RectMatVec A x)
  upper_gain : ∀ x : P19Vector k,
    p19VecNorm2 (p19RectMatVec A x) ≤ sigmaMax * p19VecNorm2 x
  min_attained : 0 < k → ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧ p19VecNorm2 (p19RectMatVec A x) = sigmaMin
  max_attained : 0 < k → ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧ p19VecNorm2 (p19RectMatVec A x) = sigmaMax

/-- One explicit nonnegative low-degree polynomial represented by `c(n,k)`. -/
structure P19PolynomialFactor where
  degreeN : ℕ
  degreeK : ℕ
  coefficient : Fin (degreeN + 1) → Fin (degreeK + 1) → ℝ
  coefficient_nonneg : ∀ i j, 0 ≤ coefficient i j

/-- Evaluation of the recorded low-degree polynomial factor. -/
noncomputable def p19PolynomialFactorValue (c : P19PolynomialFactor)
    (n k : ℕ) : ℝ :=
  ∑ i : Fin (c.degreeN + 1), ∑ j : Fin (c.degreeK + 1),
    c.coefficient i j * (n : ℝ) ^ (i : ℕ) * (k : ℝ) ^ (j : ℕ)

/-- A scalar remainder that is second order in the combined precision scale. -/
def p19SecondOrderAt {ι : Type*} (l : Filter ι)
    (scale remainder : ι → ℝ) : Prop :=
  remainder =O[l] fun t ↦ scale t ^ 2

/-- A precise version of the paper's `lesssim`: an inequality modulo an
otherwise unspecified second-order remainder. -/
def p19FirstOrderLeAt {ι : Type*} (l : Filter ι)
    (scale lhs rhs : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    p19SecondOrderAt l scale remainder ∧
      ∀ᶠ t in l, lhs t ≤ rhs t + |remainder t|

/-- The paper's qualitative `theta << 1` along a precision regime. -/
def p19MuchLessThanOneAt {ι : Type*} (l : Filter ι)
    (theta : ι → ℝ) : Prop :=
  Filter.Tendsto theta l (nhds 0) ∧
    ∀ᶠ t in l, 0 ≤ theta t ∧ theta t < 1

/-- An increasing family of full-rank search bases. Successive members agree
on all previously present columns. -/
structure P19IncreasingBasisFamily (n : ℕ) (ι : Type*) where
  basis : (k : ℕ) → ι → P19RectMatrix n k
  full_rank : ∀ (k : ℕ), k ≤ n → ∀ (t : ι), p19FullColumnRank (basis k t)
  column_prefix : ∀ (k : ℕ) (t : ι) (i : Fin n) (j : Fin k), k < n →
    basis k t i j = basis (k + 1) t i j.castSucc

/-- Frobenius-to-smallest-singular-value condition measure for a rectangular
matrix. This is the paper's `kappa_F,2` interpretation of an unqualified
rectangular `kappa`. -/
noncomputable def p19RectConditionF2 {m k : ℕ}
    (A : P19RectMatrix m k) (sigmaMin : ℝ) : ℝ :=
  p19FrobNorm A / sigmaMin

/-- Frobenius condition number represented using a certified inverse. -/
noncomputable def p19ConditionNumberF {n : ℕ}
    (A Ainv : P19Matrix n) : ℝ :=
  p19FrobNorm Ainv * p19FrobNorm A

/-- One precision-parametrized execution of Algorithm 2 at the key dimension
selected by the MGS analysis used in Theorem 3.1. The fields through
`solution_small` are precisely the four modules (3.2)-(3.6). The final defect
fields record the near-orthogonality estimate recalled from the MGS analysis;
they do not assume either displayed `4/3` conclusion. -/
structure P19ModularGMRESRun {n : ℕ} {ι : Type*} (l : Filter ι) where
  dimension_pos : 0 < n
  A : P19Matrix n
  Ainv : P19Matrix n
  ML : P19Matrix n
  MLinv : P19Matrix n
  b : P19Vector n
  xExact : P19Vector n
  A_inverse : p19InversePair A Ainv
  ML_inverse : p19InversePair ML MLinv
  b_nonzero : b ≠ 0
  exact_solution : p19MatVec A xExact = b
  basisFamily : P19IncreasingBasisFamily n ι
  keyDimension : ℕ
  keyDimension_pos : 0 < keyDimension
  keyDimension_le : keyDimension ≤ n
  polynomialFactor : P19PolynomialFactor
  epsilonC : ι → ℝ
  epsilonB : ι → ℝ
  ug : ι → ℝ
  epsilonX : ι → ℝ
  accuracy_nonneg : ∀ t,
    0 ≤ epsilonC t ∧ 0 ≤ epsilonB t ∧ 0 ≤ ug t ∧ 0 ≤ epsilonX t
  accuracy_tendsto_zero :
    Filter.Tendsto epsilonC l (nhds 0) ∧
      Filter.Tendsto epsilonB l (nhds 0) ∧
      Filter.Tendsto ug l (nhds 0) ∧
      Filter.Tendsto epsilonX l (nhds 0)
  computedC : ι → P19RectMatrix n keyDimension
  deltaC : ι → P19RectMatrix n keyDimension
  computation_equation : ∀ t,
    computedC t =
      p19SquareRectMul MLinv
          (p19SquareRectMul A (basisFamily.basis keyDimension t)) +
        deltaC t
  computation_error_bound : ∀ t,
    p19FrobNorm (deltaC t) ≤
      epsilonC t *
        p19FrobNorm
          (p19SquareRectMul MLinv
            (p19SquareRectMul A (basisFamily.basis keyDimension t)))
  computedB : ι → P19Vector n
  deltaB : ι → P19Vector n
  rhs_equation : ∀ t,
    computedB t = p19MatVec MLinv b + deltaB t
  rhs_error_bound : ∀ t,
    p19VecNorm2 (deltaB t) ≤ epsilonB t * p19VecNorm2 (p19MatVec MLinv b)
  vHat : ι → P19RectMatrix n keyDimension
  vHatNext : ι → P19RectMatrix n (keyDimension + 1)
  beta : ι → ℝ
  hessenberg : ι → P19RectMatrix (keyDimension + 1) keyDimension
  hessenberg_upper : ∀ t, p19IsUpperHessenberg (hessenberg t)
  mgs_givens_relation : ∀ t,
    p19Augment (computedB t) (computedC t) =
      p19RectMatMul (vHatNext t)
        (p19Augment (p19ScaledFirstBasisVector (beta t)) (hessenberg t))
  vHat_prefix : ∀ t i (j : Fin keyDimension),
    vHat t i j = vHatNext t i j.castSucc
  leastSquaresDeltaB : ι → P19Vector n
  leastSquaresDeltaC : ι → P19RectMatrix n keyDimension
  yHat : ι → P19Vector keyDimension
  least_squares_solution : ∀ t,
    p19IsLeastSquaresSolution
      (computedC t + leastSquaresDeltaC t)
      (computedB t + leastSquaresDeltaB t) (yHat t)
  least_squares_column_bound : ∀ t (j : Fin (keyDimension + 1)),
    p19VecNorm2
        (p19Column
          (p19Augment (leastSquaresDeltaB t) (leastSquaresDeltaC t)) j) ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension * ug t *
        p19VecNorm2
          (p19Column (p19Augment (computedB t) (computedC t)) j)
  computedCSpectrum : ∀ t, P19SingularValueData (computedC t)
  computedC_numerically_nonsingular :
    p19MuchLessThanOneAt l (fun t ↦
      ug t *
        p19RectConditionF2 (computedC t)
          (computedCSpectrum t).sigmaMin)
  exactCSpectrum : ∀ t,
    P19SingularValueData
      (p19SquareRectMul MLinv
        (p19SquareRectMul A (basisFamily.basis keyDimension t)))
  combined_model_small :
    p19MuchLessThanOneAt l (fun t ↦
      (epsilonC t + epsilonB t + ug t) *
        p19RectConditionF2
          (p19SquareRectMul MLinv
            (p19SquareRectMul A (basisFamily.basis keyDimension t)))
          (exactCSpectrum t).sigmaMin)
  xHat : ι → P19Vector n
  deltaX : ι → P19Vector n
  solution_equation : ∀ t,
    xHat t = p19RectMatVec (basisFamily.basis keyDimension t) (yHat t) + deltaX t
  solution_error_bound : ∀ t,
    p19VecNorm2 (deltaX t) ≤
      epsilonX t *
        p19VecNorm2
          (p19RectMatVec (basisFamily.basis keyDimension t) (yHat t))
  solution_small : p19MuchLessThanOneAt l epsilonX
  vHatSpectrum : ∀ t, P19SingularValueData (vHat t)
  mgsOrthogonalityDefect : ι → ℝ
  mgs_defect_nonneg : ∀ t, 0 ≤ mgsOrthogonalityDefect t
  mgs_defect_small : ∀ᶠ t in l, mgsOrthogonalityDefect t ≤ 7 / 16
  mgs_sigmaMin_sq_lower : ∀ t,
    1 - mgsOrthogonalityDefect t ≤ (vHatSpectrum t).sigmaMin ^ 2
  mgs_sigmaMax_sq_upper : ∀ t,
    (vHatSpectrum t).sigmaMax ^ 2 ≤ 1 + mgsOrthogonalityDefect t

/-- The combined precision scale used to classify the omitted second-order
terms in Theorem 3.1. -/
noncomputable def p19PrecisionScale {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) : ι → ℝ :=
  fun t ↦ run.epsilonC t + run.epsilonB t + run.ug t + run.epsilonX t

/-- The exact left-preconditioned basis product in (3.2). -/
noncomputable def p19ExactC {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) (t : ι) :
    P19RectMatrix n run.keyDimension :=
  p19SquareRectMul run.MLinv
    (p19SquareRectMul run.A (run.basisFamily.basis run.keyDimension t))

/-- The split-preconditioned operator `M_L^{-1} A M_R^{-1}`. -/
noncomputable def p19SplitOperator {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) (MRinv : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul run.MLinv (p19SquareRectMul run.A MRinv)

/-- Its certified inverse `M_R A^{-1} M_L`. -/
noncomputable def p19SplitInverse {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) (MR : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul MR (p19SquareRectMul run.Ainv run.ML)

/-- The normalized forward error (2.1). -/
noncomputable def p19ForwardError {n : ℕ}
    (x xHat : P19Vector n) : ℝ :=
  p19VecNorm2 (xHat - x) / p19VecNorm2 x

/-- Exact singular-value data needed to instantiate `alpha` and `beta` for one
arbitrary nonsingular analytical right preconditioner. -/
structure P19RightPreconditionedQuantities {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n) where
  mrzSpectrum : ∀ t,
    P19SingularValueData
      (p19SquareRectMul MR
        (run.basisFamily.basis run.keyDimension t))
  mrz_sigmaMin_pos : ∀ t, 0 < (mrzSpectrum t).sigmaMin

/-- The coefficient `alpha` below equation (3.8). -/
noncomputable def p19Alpha {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n)
    (q : P19RightPreconditionedQuantities run MR MRinv) (t : ι) : ℝ :=
  (p19ConditionNumberF MR MRinv / (q.mrzSpectrum t).sigmaMin) *
    (p19FrobNorm (p19ExactC run t) /
      p19FrobNorm (p19SplitOperator run MRinv))

/-- The coefficient `beta` below equation (3.8). -/
noncomputable def p19Beta {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n)
    (q : P19RightPreconditionedQuantities run MR MRinv) (t : ι) : ℝ :=
  max 1
      ((p19FrobNorm (p19ExactC run t) /
          p19FrobNorm (p19SplitOperator run MRinv)) /
        (q.mrzSpectrum t).sigmaMin) *
    p19ConditionNumberF MR MRinv

/-- The coefficient `lambda` below equation (3.8). -/
noncomputable def p19Lambda {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n) : ℝ :=
  1 /
    p19ConditionNumberF
      (p19SplitOperator run MRinv) (p19SplitInverse run MR)

/-- The exact four-source quantity `xi` in equation (3.8). -/
noncomputable def p19Xi {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n)
    (q : P19RightPreconditionedQuantities run MR MRinv) (t : ι) : ℝ :=
  p19ModularEnvelope (p19Alpha run MR MRinv q t)
    (p19Beta run MR MRinv q t) (p19Lambda run MR MRinv)
    (run.epsilonC t) (run.epsilonB t) (run.ug t) (run.epsilonX t)

/-- Appendix-A propagation certificate for the four heterogeneous Algorithm 2
errors. Each contribution is formally tied to its source perturbation; their
sum, rather than the final forward-error inequality, is recorded. -/
structure P19ForwardAnalysis {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n) where
  quantities : P19RightPreconditionedQuantities run MR MRinv
  computationPropagation : ι →
    P19RectMatrix n run.keyDimension → P19Vector n
  rhsPropagation : ι → P19Vector n → P19Vector n
  leastSquaresBPropagation : ι → P19Vector n → P19Vector n
  leastSquaresCPropagation : ι →
    P19RectMatrix n run.keyDimension → P19Vector n
  solutionPropagation : ι → P19Vector n → P19Vector n
  computationContribution : ι → P19Vector n
  rhsContribution : ι → P19Vector n
  gmresContribution : ι → P19Vector n
  solutionContribution : ι → P19Vector n
  remainder : ι → P19Vector n
  computation_link : ∀ t,
    computationContribution t = computationPropagation t (run.deltaC t)
  rhs_link : ∀ t, rhsContribution t = rhsPropagation t (run.deltaB t)
  gmres_link : ∀ t,
    gmresContribution t =
      leastSquaresBPropagation t (run.leastSquaresDeltaB t) +
        leastSquaresCPropagation t (run.leastSquaresDeltaC t)
  solution_link : ∀ t,
    solutionContribution t = solutionPropagation t (run.deltaX t)
  computationPropagation_zero : ∀ t, computationPropagation t 0 = 0
  rhsPropagation_zero : ∀ t, rhsPropagation t 0 = 0
  leastSquaresBPropagation_zero : ∀ t, leastSquaresBPropagation t 0 = 0
  leastSquaresCPropagation_zero : ∀ t, leastSquaresCPropagation t 0 = 0
  solutionPropagation_zero : ∀ t, solutionPropagation t 0 = 0
  error_decomposition : ∀ t,
    run.xHat t - run.xExact =
      computationContribution t + rhsContribution t + gmresContribution t +
        solutionContribution t + remainder t
  computation_bound : ∀ t,
    p19VecNorm2 (computationContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Alpha run MR MRinv quantities t * run.epsilonC t)
  rhs_bound : ∀ t,
    p19VecNorm2 (rhsContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Beta run MR MRinv quantities t * run.epsilonB t)
  gmres_bound : ∀ t,
    p19VecNorm2 (gmresContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Beta run MR MRinv quantities t * run.ug t)
  solution_bound : ∀ t,
    p19VecNorm2 (solutionContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Lambda run MR MRinv * run.epsilonX t)
  remainder_second_order :
    p19SecondOrderAt l (p19PrecisionScale run)
      (fun t ↦ p19VecNorm2 (remainder t) / p19VecNorm2 run.xExact)

/-- A complete proof-carrying execution of the hypotheses and intermediate
Appendix-A propagation used by Theorem 3.1. -/
structure P19Theorem31Execution {n : ℕ} {ι : Type*} (l : Filter ι) where
  run : P19ModularGMRESRun (n := n) l
  forwardAnalysis : ∀ (MR MRinv : P19Matrix n),
    p19InversePair MR MRinv → P19ForwardAnalysis run MR MRinv

/-- Paper-scoped exact matrix operator 2-norm. -/
noncomputable def p19OpNorm2 {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  @norm (Matrix (Fin n) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm
    (A : Matrix (Fin n) (Fin n) ℝ)

/-- Paper-scoped condition-number product for a matrix and inverse candidate. -/
noncomputable def p19Kappa2 {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  p19OpNorm2 A * p19OpNorm2 Ainv

/-- Exact scalar envelope represented by the right-preconditioned bound (3.17). -/
noncomputable def p19RightEnvelope {n : ℕ}
    (ug um ua etaR rhoA : ℝ)
    (AMRinv AMRinvInv MR MRinv A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  ug * p19Kappa2 AMRinv AMRinvInv * p19Kappa2 MR MRinv +
    um * etaR * p19Kappa2 MR MRinv +
      ua * p19Kappa2 A Ainv * rhoA

/-- Exact scalar envelope represented by the flexible-preconditioned bound (3.20). -/
noncomputable def p19FlexibleEnvelope {n : ℕ}
    (ug ua rhoA : ℝ)
    (AMRinv AMRinvInv MR MRinv A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  ug * p19Kappa2 AMRinv AMRinvInv * p19Kappa2 MR MRinv +
    ua * p19Kappa2 A Ainv * rhoA

end HighamBench
