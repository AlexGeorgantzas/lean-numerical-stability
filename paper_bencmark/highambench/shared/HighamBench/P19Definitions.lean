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

/-- Static semantics for the source's qualitative first-order notation. The
paper deliberately supplies neither a limiting parameter nor a numerical
smallness threshold, so both predicates remain part of the interpretation. -/
structure P19FirstOrderSemantics where
  small : ℝ → Prop
  secondOrder : ℝ → Prop
  zero_secondOrder : secondOrder 0

/-- The source relation `lhs lesssim rhs`: an exact inequality after retaining
one term classified as negligible and second order by the chosen semantics. -/
def p19FirstOrderLe (semantics : P19FirstOrderSemantics)
    (lhs rhs : ℝ) : Prop :=
  ∃ remainder : ℝ,
    semantics.secondOrder remainder ∧ lhs ≤ rhs + |remainder|

/-- A ratio that remains defined when its reference magnitude is zero. Source
error inequalities force the numerator to vanish in that case. -/
noncomputable def p19SafeRelativeMagnitude (actual reference : ℝ) : ℝ :=
  if reference = 0 then 0 else actual / reference

/-- A dimension admitted by Theorem 3.1. -/
abbrev P19Theorem31Dimension (n : ℕ) :=
  {k : ℕ // 0 < k ∧ k ≤ n}

/-- Static nonsingular linear-system data shared by all Algorithm 2
dimensions. -/
structure P19Theorem31System (n : ℕ) where
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

/-- The increasing full-rank search-space input from Theorem 3.1. -/
structure P19Theorem31BasisFamily {n : ℕ}
    (system : P19Theorem31System n) where
  basis : (k : ℕ) → P19RectMatrix n k
  full_rank : ∀ k, 0 < k → k ≤ n → p19FullColumnRank (basis k)
  column_prefix : ∀ k, k < n → ∀ i (j : Fin k),
    basis k i j = basis (k + 1) i j.castSucc

/-- Exact left-preconditioned basis product in equation (3.2). -/
noncomputable def p19StaticExactC {n k : ℕ}
    (system : P19Theorem31System n) (Z : P19RectMatrix n k) :
    P19RectMatrix n k :=
  p19SquareRectMul system.MLinv (p19SquareRectMul system.A Z)

/-- Exact left-preconditioned right-hand side in equation (3.3). -/
noncomputable def p19StaticExactB {n : ℕ}
    (system : P19Theorem31System n) : P19Vector n :=
  p19MatVec system.MLinv system.b

/-- One fixed-precision execution of all four modules of Algorithm 2 at one
positive dimension. No selected key dimension or final error bound is stored. -/
structure P19Algorithm2Iteration {n : ℕ}
    (system : P19Theorem31System n)
    (semantics : P19FirstOrderSemantics)
    (basisFamily : P19Theorem31BasisFamily system)
    (k : P19Theorem31Dimension n) where
  dimensionFactor : ℝ
  dimensionFactor_one_le : 1 ≤ dimensionFactor
  epsilonC : ℝ
  epsilonB : ℝ
  ug : ℝ
  epsilonX : ℝ
  computedC : P19RectMatrix n k.1
  deltaC : P19RectMatrix n k.1
  computation_equation :
    computedC = p19StaticExactC system (basisFamily.basis k.1) + deltaC
  computedB : P19Vector n
  deltaB : P19Vector n
  rhs_equation : computedB = p19StaticExactB system + deltaB
  vHat : P19RectMatrix n k.1
  vHatNext : P19RectMatrix n (k.1 + 1)
  beta : ℝ
  hessenberg : P19RectMatrix (k.1 + 1) k.1
  hessenberg_upper : p19IsUpperHessenberg hessenberg
  mgs_givens_relation :
    p19Augment computedB computedC =
      p19RectMatMul vHatNext
        (p19Augment (p19ScaledFirstBasisVector beta) hessenberg)
  vHat_prefix : ∀ i (j : Fin k.1),
    vHat i j = vHatNext i j.castSucc
  leastSquaresDeltaB : P19Vector n
  leastSquaresDeltaC : P19RectMatrix n k.1
  yHat : P19Vector k.1
  computedCSpectrum : P19SingularValueData computedC
  exactCSpectrum :
    P19SingularValueData
      (p19StaticExactC system (basisFamily.basis k.1))
  xHat : P19Vector n
  deltaX : P19Vector n
  solution_equation :
    xHat = p19RectMatVec (basisFamily.basis k.1) yHat + deltaX
  vHatSpectrum : P19SingularValueData vHat

/-- Equations (3.2)-(3.6) and the MGS/Givens least-squares model at one
specific Algorithm 2 dimension. Theorem 3.1 requires these only at the
dimension selected by the MGS argument. -/
structure P19Algorithm2Conditions {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) where
  accuracy_nonneg :
    0 ≤ iteration.epsilonC ∧ 0 ≤ iteration.epsilonB ∧
      0 ≤ iteration.ug ∧ 0 ≤ iteration.epsilonX
  computation_error_bound :
    p19FrobNorm iteration.deltaC ≤
      iteration.epsilonC *
        p19FrobNorm (p19StaticExactC system (basisFamily.basis k.1))
  rhs_error_bound :
    p19VecNorm2 iteration.deltaB ≤
      iteration.epsilonB * p19VecNorm2 (p19StaticExactB system)
  least_squares_solution :
    p19IsLeastSquaresSolution
      (iteration.computedC + iteration.leastSquaresDeltaC)
      (iteration.computedB + iteration.leastSquaresDeltaB) iteration.yHat
  least_squares_column_bound : ∀ j : Fin (k.1 + 1),
    p19VecNorm2
        (p19Column
          (p19Augment iteration.leastSquaresDeltaB
            iteration.leastSquaresDeltaC) j) ≤
      iteration.dimensionFactor * iteration.ug *
        p19VecNorm2
          (p19Column
            (p19Augment iteration.computedB iteration.computedC) j)
  computedC_numerically_nonsingular :
    semantics.small
      (iteration.ug *
        p19RectConditionF2 iteration.computedC
          iteration.computedCSpectrum.sigmaMin)
  combined_model_small :
    semantics.small
      ((iteration.epsilonC + iteration.epsilonB + iteration.ug) *
        p19RectConditionF2
          (p19StaticExactC system (basisFamily.basis k.1))
          iteration.exactCSpectrum.sigmaMin)
  solution_error_bound :
    p19VecNorm2 iteration.deltaX ≤
      iteration.epsilonX *
        p19VecNorm2 (p19RectMatVec (basisFamily.basis k.1) iteration.yHat)
  solution_small : semantics.small iteration.epsilonX

/-- The two explicit conditioning inequalities in equation (3.7). -/
def p19IterationWellConditioned {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) : Prop :=
  1 / iteration.vHatSpectrum.sigmaMin ≤ 4 / 3 ∧
    iteration.vHatSpectrum.sigmaMax ≤ 4 / 3

/-- Witness form of an upper bound on the smallest singular value. -/
def p19NearRankDeficient {m k : ℕ} (A : P19RectMatrix m k)
    (threshold : ℝ) : Prop :=
  ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧
      p19VecNorm2 (p19RectMatVec A x) < threshold

/-- The input-near-dependence alternative (A.1), required only before the
full dimension. -/
def p19MGSNearDependence {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) : Prop :=
  ∀ phi : ℝ, 0 < phi →
    p19NearRankDeficient
      (p19Augment
        (fun i ↦ p19StaticExactB system i * phi)
        (p19StaticExactC system (basisFamily.basis k.1)))
      (iteration.dimensionFactor * (iteration.ug + iteration.epsilonC) *
        p19FrobNorm
          (p19Augment
            (fun i ↦ p19StaticExactB system i * phi)
            (p19StaticExactC system (basisFamily.basis k.1))))

/-- Static Algorithm 2 executions at every increasing dimension. -/
structure P19Theorem31Family (n : ℕ)
    (semantics : P19FirstOrderSemantics) where
  system : P19Theorem31System n
  basisFamily : P19Theorem31BasisFamily system
  iteration : ∀ k : P19Theorem31Dimension n,
    P19Algorithm2Iteration system semantics basisFamily k

/-- The reusable MGS result invoked through [11, equations (5.15)-(5.17)] and
the Paige MGS analysis: the first basis is well conditioned, and loss at the
next dimension forces (A.1) for the current input. It contains no selected
dimension. -/
structure P19MGSSelectionLaw {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) where
  first_dimension_good :
    p19IterationWellConditioned
      (family.iteration
        ⟨1, Nat.zero_lt_one, family.system.dimension_pos⟩)
  loss_implies_near_dependence : ∀ (k : ℕ)
      (hkpos : 0 < k) (hklt : k < n),
    let current : P19Theorem31Dimension n :=
      ⟨k, hkpos, Nat.le_of_lt hklt⟩
    let next : P19Theorem31Dimension n :=
      ⟨k + 1, Nat.succ_pos k, Nat.succ_le_iff.mpr hklt⟩
    ¬ p19IterationWellConditioned (family.iteration next) →
      p19MGSNearDependence (family.iteration current)

/-- The split-preconditioned operator for the static Theorem 3.1 model. -/
noncomputable def p19StaticSplitOperator {n : ℕ}
    (system : P19Theorem31System n) (MRinv : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul system.MLinv (p19SquareRectMul system.A MRinv)

/-- A certified inverse of the static split-preconditioned operator. -/
noncomputable def p19StaticSplitInverse {n : ℕ}
    (system : P19Theorem31System n) (MR : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul MR (p19SquareRectMul system.Ainv system.ML)

/-- Singular-value and positivity evidence used to interpret the displayed
`alpha`, `beta`, and `lambda` for one analytical right preconditioner. -/
structure P19StaticRightQuantities {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (k : P19Theorem31Dimension n)
    (MR MRinv : P19Matrix n) where
  mrzSpectrum :
    P19SingularValueData
      (p19SquareRectMul MR (family.basisFamily.basis k.1))
  mrz_sigmaMin_pos : 0 < mrzSpectrum.sigmaMin
  exactC_norm_pos :
    0 < p19FrobNorm
      (p19StaticExactC family.system (family.basisFamily.basis k.1))
  split_operator_norm_pos :
    0 < p19FrobNorm (p19StaticSplitOperator family.system MRinv)
  mr_condition_pos : 0 < p19ConditionNumberF MR MRinv
  split_condition_pos :
    0 < p19ConditionNumberF
      (p19StaticSplitOperator family.system MRinv)
      (p19StaticSplitInverse family.system MR)

/-- `alpha` below equation (3.8), with the paper-authorized Frobenius
interpretation of unqualified square condition numbers. -/
noncomputable def p19StaticAlpha {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  (p19ConditionNumberF MR MRinv / q.mrzSpectrum.sigmaMin) *
    (p19FrobNorm
        (p19StaticExactC family.system (family.basisFamily.basis k.1)) /
      p19FrobNorm (p19StaticSplitOperator family.system MRinv))

/-- `beta` below equation (3.8). -/
noncomputable def p19StaticBeta {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  max 1
      ((p19FrobNorm
          (p19StaticExactC family.system (family.basisFamily.basis k.1)) /
          p19FrobNorm (p19StaticSplitOperator family.system MRinv)) /
        q.mrzSpectrum.sigmaMin) *
    p19ConditionNumberF MR MRinv

/-- `lambda` below equation (3.8). -/
noncomputable def p19StaticLambda {n : ℕ}
    (system : P19Theorem31System n) (MR MRinv : P19Matrix n) : ℝ :=
  1 /
    p19ConditionNumberF
      (p19StaticSplitOperator system MRinv)
      (p19StaticSplitInverse system MR)

/-- The exact four-source coefficient `xi` in equation (3.8). -/
noncomputable def p19StaticXi {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  let run := family.iteration k
  p19ModularEnvelope (p19StaticAlpha MR MRinv q)
    (p19StaticBeta MR MRinv q)
    (p19StaticLambda family.system MR MRinv)
    run.epsilonC run.epsilonB run.ug run.epsilonX

/-- Raw Appendix-A first-order expansion. Its gain bounds are expressed in
terms of the actual module-relative errors. In particular, none of the four
source epsilons and no final Theorem 3.1 inequality is stored here. -/
structure P19StaticAppendixAExpansion {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (k : P19Theorem31Dimension n)
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) where
  computationContribution : P19Vector n
  rhsContribution : P19Vector n
  gmresContribution : P19Vector n
  solutionContribution : P19Vector n
  remainder : P19Vector n
  error_decomposition :
    (family.iteration k).xHat - family.system.xExact =
      computationContribution + rhsContribution + gmresContribution +
        solutionContribution + remainder
  remainder_second_order :
    semantics.secondOrder
      (p19VecNorm2 remainder / p19VecNorm2 family.system.xExact)
  computation_gain_bound :
    p19VecNorm2 computationContribution /
          p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticAlpha MR MRinv q *
          p19SafeRelativeMagnitude
            (p19FrobNorm (family.iteration k).deltaC)
            (p19FrobNorm
              (p19StaticExactC family.system
                (family.basisFamily.basis k.1))))
  rhs_gain_bound :
    p19VecNorm2 rhsContribution / p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticBeta MR MRinv q *
          p19SafeRelativeMagnitude
            (p19VecNorm2 (family.iteration k).deltaB)
            (p19VecNorm2 (p19StaticExactB family.system)))
  gmres_gain_bound :
    p19VecNorm2 gmresContribution / p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticBeta MR MRinv q * (family.iteration k).ug)
  solution_gain_bound :
    p19VecNorm2 solutionContribution /
          p19VecNorm2 family.system.xExact ≤
      p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticLambda family.system MR MRinv *
          p19SafeRelativeMagnitude
            (p19VecNorm2 (family.iteration k).deltaX)
            (p19VecNorm2
              (p19RectMatVec (family.basisFamily.basis k.1)
                (family.iteration k).yHat)))

/-- The reusable Appendix-A analysis invoked by Theorem 3.1. It is uniform in
the dimension and right preconditioner and supplies only the raw expansion
above, not a selected dimension or the theorem's collected bound. -/
structure P19StaticAppendixATheory {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) where
  rightQuantities : ∀ (k : P19Theorem31Dimension n)
      (MR MRinv : P19Matrix n), p19InversePair MR MRinv →
    P19StaticRightQuantities family k MR MRinv
  expansion : ∀ (k : P19Theorem31Dimension n),
    p19IterationWellConditioned (family.iteration k) →
    (k.1 = n ∨ p19MGSNearDependence (family.iteration k)) →
    P19Algorithm2Conditions (family.iteration k) →
    ∀ (MR MRinv : P19Matrix n) (hMR : p19InversePair MR MRinv),
      P19StaticAppendixAExpansion family k MR MRinv
        (rightQuantities k MR MRinv hMR)

/-- Paper-scoped exact matrix operator 2-norm. -/
noncomputable def p19OpNorm2 {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  @norm (Matrix (Fin n) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm
    (A : Matrix (Fin n) (Fin n) ℝ)

/-- Paper-scoped condition-number product for a matrix and inverse candidate. -/
noncomputable def p19Kappa2 {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  p19OpNorm2 A * p19OpNorm2 Ainv

/-- The initial residual used when Algorithm 1 is read as Algorithm 2 applied
to the correction equation. -/
noncomputable def p19InitialResidual {n : ℕ} (A : P19Matrix n)
    (b xInitial : P19Vector n) : P19Vector n :=
  b - p19MatVec A xInitial

/-- Componentwise absolute matrix-vector product from equation (3.15). -/
noncomputable def p19AbsRectMatVec {m k : ℕ} (A : P19RectMatrix m k)
    (x : P19Vector k) : P19Vector m :=
  fun i ↦ ∑ j : Fin k, |A i j| * |x j|

/-- A nonsingular system with one fixed, nonsingular, nonidentity right
preconditioner. The product-inverse certificate prevents condition numbers
from being formed from unrelated matrices. -/
structure P19FixedRightSystem (n : ℕ) where
  dimension_pos : 0 < n
  A : P19Matrix n
  Ainv : P19Matrix n
  MR : P19Matrix n
  MRinv : P19Matrix n
  A_inverse : p19InversePair A Ainv
  MR_inverse : p19InversePair MR MRinv
  right_operator_inverse :
    p19InversePair (p19SquareRectMul A MRinv) (p19SquareRectMul MR Ainv)
  right_preconditioner_nontrivial : MR ≠ 1
  b : P19Vector n
  xExact : P19Vector n
  xInitial : P19Vector n
  b_nonzero : b ≠ 0
  exact_solution : p19MatVec A xExact = b
  initial_residual_nonzero : p19InitialResidual A b xInitial ≠ 0

/-- The actual right-preconditioned operator `A M_R^{-1}`. -/
noncomputable def p19RightOperator {n : ℕ}
    (system : P19FixedRightSystem n) : P19Matrix n :=
  p19SquareRectMul system.A system.MRinv

/-- The certified inverse `M_R A^{-1}` of the right-preconditioned operator. -/
noncomputable def p19RightOperatorInverse {n : ℕ}
    (system : P19FixedRightSystem n) : P19Matrix n :=
  p19SquareRectMul system.MR system.Ainv

/-- Induced-2 condition number of `A M_R^{-1}`. -/
noncomputable def p19RightOperatorKappa2 {n : ℕ}
    (system : P19FixedRightSystem n) : ℝ :=
  p19Kappa2 (p19RightOperator system) (p19RightOperatorInverse system)

/-- Induced-2 condition number of the fixed right preconditioner. -/
noncomputable def p19RightPreconditionerKappa2 {n : ℕ}
    (system : P19FixedRightSystem n) : ℝ :=
  p19Kappa2 system.MR system.MRinv

/-- Induced-2 condition number of the original system matrix. -/
noncomputable def p19SystemKappa2 {n : ℕ}
    (system : P19FixedRightSystem n) : ℝ :=
  p19Kappa2 system.A system.Ainv

/-- The five-term maximum in condition (3.16). -/
noncomputable def p19Condition316Value {n : ℕ}
    (system : P19FixedRightSystem n)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  max (ug * p19RightOperatorKappa2 system)
    (max (ug * p19RightPreconditionerKappa2 system)
      (max (um * etaR * p19RightPreconditionerKappa2 system)
        (max (ua * p19SystemKappa2 system * rhoAR)
          (ua * p19RightOperatorKappa2 system *
            p19RightPreconditionerKappa2 system))))

/-- The three first-order sources in the right-preconditioned bound (3.17). -/
noncomputable def p19RightAttainableEnvelope {n : ℕ}
    (system : P19FixedRightSystem n)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  ug * p19RightOperatorKappa2 system *
      p19RightPreconditionerKappa2 system +
    um * etaR * p19RightPreconditionerKappa2 system +
      ua * p19SystemKappa2 system * rhoAR

/-- The two first-order sources in the flexible-preconditioned bound (3.20). -/
noncomputable def p19FlexibleAttainableEnvelope {n : ℕ}
    (system : P19FixedRightSystem n)
    (ug ua rhoAR : ℝ) : ℝ :=
  ug * p19RightOperatorKappa2 system *
      p19RightPreconditionerKappa2 system +
    ua * p19SystemKappa2 system * rhoAR

/-- A computed right-preconditioned MGS-GMRES transcript through the least-
squares stage. It records (3.14), the products with `A`, equation (3.15), and
the complete condition (3.16). -/
structure P19FixedRightGMRESRun {n : ℕ} {ι : Type*}
    (system : P19FixedRightSystem n) (l : Filter ι) where
  keyDimension : ℕ
  keyDimension_pos : 0 < keyDimension
  keyDimension_le : keyDimension ≤ n
  polynomialFactor : P19PolynomialFactor
  ug : ι → ℝ
  um : ι → ℝ
  ua : ι → ℝ
  etaR : ι → ℝ
  rhoAR : ι → ℝ
  parameters_nonneg : ∀ t,
    0 ≤ ug t ∧ 0 ≤ um t ∧ 0 ≤ ua t ∧ 0 ≤ etaR t ∧ 0 ≤ rhoAR t
  vHat : ι → P19RectMatrix n keyDimension
  vHatNext : ι → P19RectMatrix n (keyDimension + 1)
  zHat : ι → P19RectMatrix n keyDimension
  computedAZ : ι → P19RectMatrix n keyDimension
  beta : ι → ℝ
  hessenberg : ι → P19RectMatrix (keyDimension + 1) keyDimension
  hessenberg_upper : ∀ t, p19IsUpperHessenberg (hessenberg t)
  mgs_relation : ∀ t,
    p19Augment (p19InitialResidual system.A system.b system.xInitial)
        (computedAZ t) =
      p19RectMatMul (vHatNext t)
        (p19Augment (p19ScaledFirstBasisVector (beta t)) (hessenberg t))
  vHat_prefix : ∀ t i (j : Fin keyDimension),
    vHat t i j = vHatNext t i j.castSucc
  leastSquaresDeltaB : ι → P19Vector n
  leastSquaresDeltaC : ι → P19RectMatrix n keyDimension
  yHat : ι → P19Vector keyDimension
  least_squares_solution : ∀ t,
    p19IsLeastSquaresSolution
      (computedAZ t + leastSquaresDeltaC t)
      (p19InitialResidual system.A system.b system.xInitial +
        leastSquaresDeltaB t) (yHat t)
  least_squares_column_bound : ∀ t (j : Fin (keyDimension + 1)),
    p19VecNorm2
        (p19Column
          (p19Augment (leastSquaresDeltaB t) (leastSquaresDeltaC t)) j) ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension * ug t *
        p19VecNorm2
          (p19Column
            (p19Augment
              (p19InitialResidual system.A system.b system.xInitial)
              (computedAZ t)) j)
  zHat_full_rank : ∀ t, p19FullColumnRank (zHat t)
  preconditionerDelta : ι → Fin keyDimension → P19Matrix n
  preconditioner_application : ∀ t j,
    p19Column (zHat t) j =
      p19MatVec (system.MRinv + preconditionerDelta t j)
        (p19Column (vHat t) j)
  preconditioner_error_bound : ∀ t j,
    p19FrobNorm (preconditionerDelta t j) ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension *
        um t * etaR t * p19FrobNorm system.MRinv
  matrixDelta : ι → Fin keyDimension → P19Matrix n
  matrix_application : ∀ t j,
    p19Column (computedAZ t) j =
      p19MatVec (system.A + matrixDelta t j) (p19Column (zHat t) j)
  matrix_error_bound : ∀ t j i q,
    |matrixDelta t j i q| ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension *
        ua t * |system.A i q|
  rho_denominator_pos : ∀ t,
    0 < p19VecNorm2 (p19RectMatVec (zHat t) (yHat t))
  rho_equation : ∀ t,
    rhoAR t =
      p19VecNorm2 (p19AbsRectMatVec (zHat t) (yHat t)) /
        p19VecNorm2 (p19RectMatVec (zHat t) (yHat t))
  condition316 :
    p19MuchLessThanOneAt l (fun t ↦
      p19Condition316Value system (ug t) (um t) (ua t) (etaR t) (rhoAR t))

/-- Right-preconditioned line 4: form `V_hat y_hat` in precision `u_g` and
then apply the fixed right preconditioner again in precision `u_m`. -/
structure P19RightGMRESRun {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    (run : P19FixedRightGMRESRun system l) where
  solutionBasisDelta : ι → P19RectMatrix n run.keyDimension
  solutionPreconditionerDelta : ι → P19Matrix n
  xHat : ι → P19Vector n
  solution_basis_error_bound : ∀ t i j,
    |solutionBasisDelta t i j| ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        run.ug t * |run.vHat t i j|
  solution_preconditioner_error_bound : ∀ t,
    p19FrobNorm (solutionPreconditionerDelta t) ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        run.um t * run.etaR t * p19FrobNorm system.MRinv
  solution_equation : ∀ t,
    xHat t = p19Add system.xInitial
      (p19MatVec (system.MRinv + solutionPreconditionerDelta t)
        (p19RectMatVec (run.vHat t + solutionBasisDelta t) (run.yHat t)))

/-- Flexible line 4: reuse the stored preconditioned basis and form
`Z_hat y_hat` directly in precision `u_g`, with no fresh preconditioner
application. -/
structure P19FlexibleGMRESRun {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    (run : P19FixedRightGMRESRun system l) where
  solutionBasisDelta : ι → P19RectMatrix n run.keyDimension
  xHat : ι → P19Vector n
  solution_basis_error_bound : ∀ t i j,
    |solutionBasisDelta t i j| ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        run.ug t * |run.zHat t i j|
  solution_equation : ∀ t,
    xHat t = p19Add system.xInitial
      (p19RectMatVec (run.zHat t + solutionBasisDelta t) (run.yHat t))

/-- Appendix-C contribution certificate. Each first-order contribution is
linked to the perturbation family that generates it; the final three-term
forward-error inequality is not stored. -/
structure P19RightForwardAnalysis {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    {run : P19FixedRightGMRESRun system l}
    (algorithm : P19RightGMRESRun run) where
  gmresPropagation : ι → P19Vector n →
    P19RectMatrix n run.keyDimension →
    P19RectMatrix n run.keyDimension → P19Vector n
  reapplicationPropagation : ι → P19Matrix n → P19Vector n
  matrixPropagation : ι →
    (Fin run.keyDimension → P19Matrix n) → P19Vector n
  gmresContribution : ι → P19Vector n
  reapplicationContribution : ι → P19Vector n
  matrixContribution : ι → P19Vector n
  remainder : ι → P19Vector n
  gmres_link : ∀ t,
    gmresContribution t =
      gmresPropagation t (run.leastSquaresDeltaB t)
        (run.leastSquaresDeltaC t) (algorithm.solutionBasisDelta t)
  reapplication_link : ∀ t,
    reapplicationContribution t =
      reapplicationPropagation t (algorithm.solutionPreconditionerDelta t)
  matrix_link : ∀ t,
    matrixContribution t = matrixPropagation t (run.matrixDelta t)
  gmresPropagation_zero : ∀ t, gmresPropagation t 0 0 0 = 0
  reapplicationPropagation_zero : ∀ t, reapplicationPropagation t 0 = 0
  matrixPropagation_zero : ∀ t,
    matrixPropagation t (fun _ ↦ 0) = 0
  error_decomposition : ∀ t,
    algorithm.xHat t - system.xExact =
      gmresContribution t + reapplicationContribution t +
        matrixContribution t + remainder t
  gmres_bound : ∀ t,
    p19VecNorm2 (gmresContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ug t * p19RightOperatorKappa2 system *
          p19RightPreconditionerKappa2 system)
  reapplication_bound : ∀ t,
    p19VecNorm2 (reapplicationContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.um t * run.etaR t * p19RightPreconditionerKappa2 system)
  matrix_bound : ∀ t,
    p19VecNorm2 (matrixContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ua t * p19SystemKappa2 system * run.rhoAR t)
  remainder_second_order :
    p19SecondOrderAt l
      (fun t ↦ p19Condition316Value system
        (run.ug t) (run.um t) (run.ua t) (run.etaR t) (run.rhoAR t))
      (fun t ↦ p19VecNorm2 (remainder t) / p19VecNorm2 system.xExact)

/-- Appendix-D contribution certificate for flexible GMRES. Its first-order
decomposition has no preconditioner-reapplication contribution. -/
structure P19FlexibleForwardAnalysis {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    {run : P19FixedRightGMRESRun system l}
    (algorithm : P19FlexibleGMRESRun run) where
  gmresPropagation : ι → P19Vector n →
    P19RectMatrix n run.keyDimension →
    P19RectMatrix n run.keyDimension → P19Vector n
  matrixPropagation : ι →
    (Fin run.keyDimension → P19Matrix n) → P19Vector n
  gmresContribution : ι → P19Vector n
  matrixContribution : ι → P19Vector n
  remainder : ι → P19Vector n
  gmres_link : ∀ t,
    gmresContribution t =
      gmresPropagation t (run.leastSquaresDeltaB t)
        (run.leastSquaresDeltaC t) (algorithm.solutionBasisDelta t)
  matrix_link : ∀ t,
    matrixContribution t = matrixPropagation t (run.matrixDelta t)
  gmresPropagation_zero : ∀ t, gmresPropagation t 0 0 0 = 0
  matrixPropagation_zero : ∀ t,
    matrixPropagation t (fun _ ↦ 0) = 0
  error_decomposition : ∀ t,
    algorithm.xHat t - system.xExact =
      gmresContribution t + matrixContribution t + remainder t
  gmres_bound : ∀ t,
    p19VecNorm2 (gmresContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ug t * p19RightOperatorKappa2 system *
          p19RightPreconditionerKappa2 system)
  matrix_bound : ∀ t,
    p19VecNorm2 (matrixContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ua t * p19SystemKappa2 system * run.rhoAR t)
  remainder_second_order :
    p19SecondOrderAt l
      (fun t ↦ p19Condition316Value system
        (run.ug t) (run.um t) (run.ua t) (run.etaR t) (run.rhoAR t))
      (fun t ↦ p19VecNorm2 (remainder t) / p19VecNorm2 system.xExact)

/-- A proof-carrying right-preconditioned execution of Theorem 3.3. -/
structure P19RightTheorem33Execution {n : ℕ} {ι : Type*}
    (system : P19FixedRightSystem n) (l : Filter ι) where
  run : P19FixedRightGMRESRun system l
  algorithm : P19RightGMRESRun run
  analysis : P19RightForwardAnalysis algorithm

/-- A proof-carrying fixed-preconditioner flexible execution of Theorem 3.4. -/
structure P19FlexibleTheorem34Execution {n : ℕ} {ι : Type*}
    (system : P19FixedRightSystem n) (l : Filter ι) where
  run : P19FixedRightGMRESRun system l
  algorithm : P19FlexibleGMRESRun run
  analysis : P19FlexibleForwardAnalysis algorithm

end HighamBench
