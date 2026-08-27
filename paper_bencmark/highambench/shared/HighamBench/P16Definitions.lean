import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Matrix.Normed

/-!
# HighamBench P16 definitions

Paper-scoped finite-dimensional notation for the modular backward-error
analysis of GMRES and restarted GMRES.
-/

namespace HighamBench

open scoped BigOperators Matrix.Norms.Frobenius

/-- A finite square real matrix in the P16 model. -/
abbrev P16Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A finite real vector in the P16 model. -/
abbrev P16Vector (n : ℕ) := Fin n → ℝ

/-- Exact finite matrix-vector multiplication. -/
noncomputable def p16MatVec {n : ℕ} (A : P16Matrix n)
    (x : P16Vector n) : P16Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Frobenius norm used in the paper's normwise backward error. -/
noncomputable def p16FrobNorm {n : ℕ} (A : P16Matrix n) : ℝ :=
  ‖A‖

/-- Euclidean vector norm. -/
noncomputable def p16VecNorm {n : ℕ} (x : P16Vector n) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Exact residual `b - A x`. -/
noncomputable def p16Residual {n : ℕ} (A : P16Matrix n)
    (b x : P16Vector n) : P16Vector n :=
  b - p16MatVec A x

/-- A square matrix is nonsingular when its exact matrix-vector action is a
bijection. -/
def p16IsNonsingular {n : ℕ} (A : P16Matrix n) : Prop :=
  Function.Bijective (p16MatVec A)

/-- The shared relative perturbation condition in the paper's normwise
backward-error definition. -/
def p16NormwiseBackwardErrorAdmissible {n : ℕ}
    (A : P16Matrix n) (b xHat : P16Vector n) (epsilon : ℝ) : Prop :=
  ∃ deltaA : P16Matrix n, ∃ deltaB : P16Vector n,
    p16MatVec (A + deltaA) xHat = b + deltaB ∧
      p16FrobNorm deltaA ≤ epsilon * p16FrobNorm A ∧
      p16VecNorm deltaB ≤ epsilon * p16VecNorm b

/-- The normalized residual on the right-hand side of the paper's exact
normwise backward-error formula. -/
noncomputable def p16NormalizedResidual {n : ℕ}
    (A : P16Matrix n) (b xHat : P16Vector n) : ℝ :=
  p16VecNorm (p16Residual A b xHat) /
    (p16FrobNorm A * p16VecNorm xHat + p16VecNorm b)

/-- A scalar remainder that is second order in `scale` along `l`. Dimensions
and the fixed refinement iteration are outside the limit, so the hidden Big-O
constant may depend on them exactly as in the paper's convention. -/
def p16SecondOrderAt {ι : Type*} (l : Filter ι) (scale remainder : ι → ℝ) : Prop :=
  remainder =O[l] fun t ↦ scale t ^ 2

/-- A precise interpretation of the paper's `≲`: the inequality holds after
adding an otherwise unspecified second-order remainder. -/
def p16FirstOrderLeAt {ι : Type*} (l : Filter ι) (scale lhs rhs : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    p16SecondOrderAt l scale remainder ∧
      ∀ᶠ t in l, lhs t ≤ rhs t + |remainder t|

/-- One computed generic iterative-refinement step in the backward-error
clause of Lemma 4.2. It records exactly the normwise operation models (4.1),
(4.2), and (4.14). The additional iterate comparison needed by the published
proof is deliberately kept outside this structure. -/
structure P16Lemma42BackwardStep {n : ℕ} {ι : Type*}
    (l : Filter ι) (scale : ι → ℝ)
    (A : P16Matrix n) (b : P16Vector n) (_iteration : ℕ) where
  xHat : ι → P16Vector n
  correctionHat : ι → P16Vector n
  xHatNext : ι → P16Vector n
  residualHat : ι → P16Vector n
  deltaR : ι → P16Vector n
  deltaX : ι → P16Vector n
  epsilonR : ι → ℝ
  epsilonU : ι → ℝ
  w : ι → ℝ
  omega : ι → ℝ
  residual_equation : ∀ t,
    residualHat t = p16Residual A b (xHat t) + deltaR t
  update_equation : ∀ t,
    xHatNext t = xHat t + correctionHat t + deltaX t
  correction_residual_bound : ∀ t,
    p16VecNorm (residualHat t - p16MatVec A (correctionHat t)) ≤
      w t * p16VecNorm (p16Residual A b (xHat t)) +
        omega t *
          (p16VecNorm b + p16FrobNorm A * p16VecNorm (xHatNext t))
  residual_error_bound : ∀ t,
    p16VecNorm (deltaR t) ≤
      epsilonR t *
        (p16VecNorm b + p16FrobNorm A * p16VecNorm (xHat t))
  update_error_bound : ∀ t,
    p16VecNorm (deltaX t) ≤ epsilonU t * p16VecNorm (xHatNext t)
  epsilonR_nonneg : ∀ t, 0 ≤ epsilonR t
  epsilonU_nonneg : ∀ t, 0 ≤ epsilonU t
  w_nonneg : ∀ t, 0 ≤ w t
  omega_nonneg : ∀ t, 0 ≤ omega t
  epsilonR_tendsto_zero : Filter.Tendsto epsilonR l (nhds 0)
  epsilonU_tendsto_zero : Filter.Tendsto epsilonU l (nhds 0)

/-- Frobenius condition number `kappa_F(A)` represented with the certified
inverse that occurs in the T3 execution model. -/
noncomputable def p16ConditionNumberF {n : ℕ}
    (A Ainv : P16Matrix n) : ℝ :=
  p16FrobNorm Ainv * p16FrobNorm A

/-- A rectangular real matrix used for one Arnoldi restart. -/
abbrev P16RectMatrix (m k : ℕ) := Matrix (Fin m) (Fin k) ℝ

/-- Exact rectangular matrix-vector multiplication. -/
noncomputable def p16RectMatVec {m k : ℕ} (A : P16RectMatrix m k)
    (x : P16Vector k) : P16Vector m :=
  fun i ↦ ∑ j : Fin k, A i j * x j

/-- Exact multiplication of a square matrix by a rectangular matrix. -/
noncomputable def p16SquareRectMul {n k : ℕ} (A : P16Matrix n)
    (B : P16RectMatrix n k) : P16RectMatrix n k :=
  fun i j ↦ ∑ q : Fin n, A i q * B q j

/-- Exact multiplication of two conforming rectangular matrices. -/
noncomputable def p16RectMatMul {m k q : ℕ} (A : P16RectMatrix m k)
    (B : P16RectMatrix k q) : P16RectMatrix m q :=
  fun i j ↦ ∑ r : Fin k, A i r * B r j

/-- Frobenius norm for a rectangular matrix. -/
noncomputable def p16RectFrobNorm {m k : ℕ}
    (A : P16RectMatrix m k) : ℝ :=
  ‖A‖

/-- Append a scaled right-hand side to a rectangular matrix. This is the
matrix `[b * phi, C]` occurring in the key-dimension condition (3.7). -/
noncomputable def p16Augment {n k : ℕ} (b : P16Vector n)
    (phi : ℝ) (C : P16RectMatrix n k) : P16RectMatrix n (k + 1) :=
  fun i ↦ Fin.cases (b i * phi) (fun j ↦ C i j)

/-- A lower-gain certificate. It is the inequality form of a lower bound on
the smallest singular value and avoids choosing singular vectors. -/
def p16MinGainAtLeast {m k : ℕ} (A : P16RectMatrix m k)
    (sigma : ℝ) : Prop :=
  ∀ x : P16Vector k, sigma * p16VecNorm x ≤ p16VecNorm (p16RectMatVec A x)

/-- A unit vector witnessing numerical rank deficiency at tolerance `delta`.
This is the witness form of the upper singular-value condition (3.7). -/
def p16NearRankDeficient {m k : ℕ} (A : P16RectMatrix m k)
    (delta : ℝ) : Prop :=
  ∃ x : P16Vector k,
    p16VecNorm x = 1 ∧ p16VecNorm (p16RectMatVec A x) ≤ delta

/-- Exact least-squares optimality, used to record line 6 of restarted
MOD-GMRES without prescribing a particular solver implementation. -/
def p16IsLeastSquaresSolution {m k : ℕ} (A : P16RectMatrix m k)
    (b : P16Vector m) (y : P16Vector k) : Prop :=
  ∀ z : P16Vector k,
    p16VecNorm (b - p16RectMatVec A y) ≤
      p16VecNorm (b - p16RectMatVec A z)

/-- One explicit nonnegative bivariate polynomial standing for an occurrence
of the paper's unspecified low-degree factor `c(n,k)`. -/
structure P16PolynomialFactor where
  degreeN : ℕ
  degreeK : ℕ
  coefficient : Fin (degreeN + 1) → Fin (degreeK + 1) → ℝ
  coefficient_nonneg : ∀ i j, 0 ≤ coefficient i j

/-- Evaluation of a recorded low-degree polynomial factor. -/
noncomputable def p16PolynomialFactorValue (c : P16PolynomialFactor)
    (n k : ℕ) : ℝ :=
  ∑ i : Fin (c.degreeN + 1), ∑ j : Fin (c.degreeK + 1),
    c.coefficient i j * (n : ℝ) ^ (i : ℕ) * (k : ℝ) ^ (j : ℕ)

/-- The paper's qualitative `Lambda << 1`: along the precision regime,
`Lambda` tends to zero and is eventually a nonnegative strict contraction. -/
def p16MuchLessThanOneAt {ι : Type*} (l : Filter ι)
    (lambda : ι → ℝ) : Prop :=
  Filter.Tendsto lambda l (nhds 0) ∧
    ∀ᶠ t in l, 0 ≤ lambda t ∧ lambda t < 1

/-- Actual forward error from printed page 1942. -/
noncomputable def p16ForwardError {n : ℕ} (x xHat : P16Vector n) : ℝ :=
  p16VecNorm (xHat - x) / p16VecNorm x

/-- The normalized true residual used as the actual backward error throughout
the paper. -/
noncomputable def p16BackwardError {n : ℕ} (A : P16Matrix n)
    (b xHat : P16Vector n) : ℝ :=
  p16NormalizedResidual A b xHat

/-- One fully stored, low-precision MGS-Arnoldi correction solve at a restart.

The raw fields record lines 4--7 of Algorithm 2, the residual cast, the
Arnoldi relation, the backward-stable least-squares solve, correction
formation, and witness forms of conditions (3.5)--(3.8). The last fields are
the correction-level consequences supplied by the Section 5.3 MGS-GMRES
analysis. They stop before the high-precision residual/update composition that
is the conclusion of Theorem 6.3. -/
structure P16LowPrecisionMGSRestart {n : ℕ} {ι : Type*}
    (l : Filter ι) (scale : ι → ℝ)
    (A Ainv : P16Matrix n) (b xExact : P16Vector n)
    (xCurrent xNext residualHat correctionHat : ι → P16Vector n)
    (uLow : ι → ℝ) (poly : P16PolynomialFactor) where
  keyDimension : ℕ
  keyDimension_pos : 0 < keyDimension
  keyDimension_le : keyDimension ≤ n
  basis : ι → P16RectMatrix n keyDimension
  basisNext : ι → P16RectMatrix n (keyDimension + 1)
  hessenberg : ι → P16RectMatrix (keyDimension + 1) keyDimension
  arnoldiError : ι → P16RectMatrix n keyDimension
  arnoldi_relation : ∀ t,
    p16SquareRectMul A (basis t) =
      p16RectMatMul (basisNext t) (hessenberg t) + arnoldiError t
  residualLow : ι → P16Vector n
  residualCastError : ι → P16Vector n
  residual_cast_equation : ∀ t,
    residualLow t = residualHat t + residualCastError t
  residual_cast_bound : ∀ t,
    p16VecNorm (residualCastError t) ≤ uLow t * p16VecNorm (residualHat t)
  arnoldiProduct : ι → P16RectMatrix n keyDimension
  arnoldiProductError : ι → P16RectMatrix n keyDimension
  arnoldi_product_equation : ∀ t,
    arnoldiProduct t = p16SquareRectMul A (basis t) + arnoldiProductError t
  epsilonC : ι → ℝ
  epsilonB : ι → ℝ
  epsilonLS : ι → ℝ
  epsilonX : ι → ℝ
  arnoldi_product_bound : ∀ t,
    p16RectFrobNorm (arnoldiProductError t) ≤
      epsilonC t * p16RectFrobNorm (p16SquareRectMul A (basis t))
  leastSquaresRhsError : ι → P16Vector n
  leastSquaresMatrixError : ι → P16RectMatrix n keyDimension
  leastSquaresY : ι → P16Vector keyDimension
  least_squares_solution : ∀ t,
    p16IsLeastSquaresSolution
      (arnoldiProduct t + leastSquaresMatrixError t)
      (residualLow t + leastSquaresRhsError t) (leastSquaresY t)
  least_squares_rhs_bound : ∀ t,
    p16VecNorm (leastSquaresRhsError t) ≤
      epsilonLS t * p16VecNorm (residualLow t)
  least_squares_matrix_bound : ∀ t,
    p16RectFrobNorm (leastSquaresMatrixError t) ≤
      epsilonLS t * p16RectFrobNorm (arnoldiProduct t)
  correctionFormationError : ι → P16Vector n
  correction_formation_equation : ∀ t,
    correctionHat t =
      p16RectMatVec (basis t) (leastSquaresY t) + correctionFormationError t
  correction_formation_bound : ∀ t,
    p16VecNorm (correctionFormationError t) ≤
      epsilonX t *
        p16RectFrobNorm (basis t) * p16VecNorm (leastSquaresY t)
  accuracy_nonneg : ∀ t,
    0 ≤ epsilonC t ∧ 0 ≤ epsilonB t ∧ 0 ≤ epsilonLS t ∧ 0 ≤ epsilonX t
  accuracy_tendsto_zero :
    Filter.Tendsto epsilonC l (nhds 0) ∧
      Filter.Tendsto epsilonB l (nhds 0) ∧
      Filter.Tendsto epsilonLS l (nhds 0) ∧
      Filter.Tendsto epsilonX l (nhds 0)
  basisLowerGain : ι → ℝ
  imageLowerGain : ι → ℝ
  basis_gain : ∀ t, p16MinGainAtLeast (basis t) (basisLowerGain t)
  image_gain : ∀ t,
    p16MinGainAtLeast (p16SquareRectMul A (basis t)) (imageLowerGain t)
  basis_not_numerically_rank_deficient : ∀ t,
    epsilonX t * p16RectFrobNorm (basis t) < basisLowerGain t
  key_near_dependence : keyDimension < n → ∀ t phi, 0 < phi →
    p16NearRankDeficient
      (p16Augment (residualLow t) phi (arnoldiProduct t))
      (p16PolynomialFactorValue poly n keyDimension *
        (epsilonC t + epsilonB t + epsilonLS t) *
        p16RectFrobNorm
          (p16Augment (residualLow t) phi (arnoldiProduct t)))
  key_image_full_rank : ∀ t,
    (epsilonC t + epsilonB t + epsilonLS t) *
        p16RectFrobNorm (arnoldiProduct t) < imageLowerGain t
  localFactor : ℝ
  localFactor_nonneg : 0 ≤ localFactor
  localFactor_polynomial_bound :
    localFactor ≤ p16PolynomialFactorValue poly n keyDimension
  localFactor_uniform_bound :
    p16PolynomialFactorValue poly n keyDimension ≤
      p16PolynomialFactorValue poly n n
  backwardFactor : ι → ℝ
  forwardFactor : ι → ℝ
  factors_nonneg : ∀ t, 0 ≤ backwardFactor t ∧ 0 ≤ forwardFactor t
  backward_factor_bound : ∀ t,
    backwardFactor t ≤
      localFactor * uLow t * p16ConditionNumberF A Ainv
  forward_factor_bound : ∀ t,
    forwardFactor t ≤
      localFactor * uLow t * p16ConditionNumberF A Ainv
  backward_correction_bound :
    p16FirstOrderLeAt l scale
      (fun t ↦
        p16VecNorm (residualHat t - p16MatVec A (correctionHat t)) /
          (p16VecNorm b + p16FrobNorm A * p16VecNorm (xNext t)))
      (fun t ↦ backwardFactor t * p16BackwardError A b (xCurrent t))
  forward_correction_bound :
    p16FirstOrderLeAt l scale
      (fun t ↦
        p16VecNorm (xCurrent t + correctionHat t - xExact) /
          p16VecNorm xExact)
      (fun t ↦ forwardFactor t * p16ForwardError xExact (xCurrent t))

/-- A complete abstract-real execution certificate for the unpreconditioned
mixed-precision restarted MGS-GMRES process of Theorem 6.3. The equations are
the paper's standard-model equations; using reals means underflow, overflow,
NaNs, and infinities are excluded. -/
structure P16MixedPrecisionGMRESRun {n : ℕ} {ι : Type*} (l : Filter ι) where
  dimension_pos : 0 < n
  A : P16Matrix n
  Ainv : P16Matrix n
  b : P16Vector n
  xExact : P16Vector n
  xHat : ℕ → ι → P16Vector n
  residualHat : ℕ → ι → P16Vector n
  correctionHat : ℕ → ι → P16Vector n
  residualError : ℕ → ι → P16Vector n
  updateError : ℕ → ι → P16Vector n
  uHigh : ι → ℝ
  uLow : ι → ℝ
  polynomialFactor : P16PolynomialFactor
  b_nonzero : b ≠ 0
  nonsingular : p16IsNonsingular A
  left_inverse_action : ∀ (z : P16Vector n),
    p16MatVec Ainv (p16MatVec A z) = z
  right_inverse_action : ∀ (z : P16Vector n),
    p16MatVec A (p16MatVec Ainv z) = z
  exact_solution : p16MatVec A xExact = b
  uHigh_nonneg : ∀ t, 0 ≤ uHigh t
  uLow_nonneg : ∀ t, 0 ≤ uLow t
  uHigh_le_uLow : ∀ t, uHigh t ≤ uLow t
  uHigh_tendsto_zero : Filter.Tendsto uHigh l (nhds 0)
  uLow_tendsto_zero : Filter.Tendsto uLow l (nhds 0)
  high_gamma_valid : ∀ t, GammaValid (uHigh t) n
  residual_equation : ∀ i t,
    residualHat i t = p16Residual A b (xHat i t) + residualError i t
  residual_error_bound : ∀ i t j,
    |residualError i t j| ≤
      gamma (uHigh t) n *
        (|b j| +
          p16MatVec (fun row col ↦ |A row col|)
            (fun col ↦ |xHat i t col|) j)
  update_equation : ∀ i t,
    xHat (i + 1) t = xHat i t + correctionHat i t + updateError i t
  update_error_bound : ∀ i t j,
    |updateError i t j| ≤ uHigh t * |xHat (i + 1) t j|
  restart : ∀ i,
    P16LowPrecisionMGSRestart l (fun t ↦ uHigh t + uLow t)
      A Ainv b xExact (xHat i) (xHat (i + 1))
      (residualHat i) (correctionHat i) uLow polynomialFactor
  iterate_norm_current_next : ∀ i,
    p16FirstOrderLeAt l (fun t ↦ uHigh t + uLow t)
      (fun t ↦ p16VecNorm (xHat i t))
      (fun t ↦ p16VecNorm (xHat (i + 1) t))
  iterate_norm_next_solution : ∀ i,
    p16FirstOrderLeAt l (fun t ↦ uHigh t + uLow t)
      (fun t ↦ p16VecNorm (xHat (i + 1) t))
      (fun _ ↦ p16VecNorm xExact)
  backward_high_roundoff_bound : ∀ i,
    p16FirstOrderLeAt l (fun t ↦ uHigh t + uLow t)
      (fun t ↦
        (p16VecNorm (residualError i t) +
            p16VecNorm (p16MatVec A (updateError i t))) /
          (p16VecNorm b + p16FrobNorm A * p16VecNorm (xHat (i + 1) t)))
      (fun t ↦
        p16PolynomialFactorValue polynomialFactor n n * uHigh t)
  forward_high_roundoff_bound : ∀ i,
    p16FirstOrderLeAt l (fun t ↦ uHigh t + uLow t)
      (fun t ↦ p16VecNorm (updateError i t) / p16VecNorm xExact)
      (fun t ↦
        p16PolynomialFactorValue polynomialFactor n n * uHigh t *
          p16ConditionNumberF A Ainv)

/-- Combined high/low precision scale used for retained second-order terms. -/
noncomputable def p16MixedScale {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P16MixedPrecisionGMRESRun (n := n) l) : ι → ℝ :=
  fun t ↦ run.uHigh t + run.uLow t

/-- Uniform contraction envelope in equation (6.17). The value at `(n,n)`
dominates every restart-dependent `c(n,k_i)` recorded by the run. -/
noncomputable def p16MixedContraction {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P16MixedPrecisionGMRESRun (n := n) l) : ι → ℝ :=
  fun t ↦
    p16PolynomialFactorValue run.polynomialFactor n n * run.uLow t *
      p16ConditionNumberF run.A run.Ainv

/-- High-precision backward-error floor in equation (6.18). -/
noncomputable def p16BackwardFloor {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P16MixedPrecisionGMRESRun (n := n) l) : ι → ℝ :=
  fun t ↦ p16PolynomialFactorValue run.polynomialFactor n n * run.uHigh t

/-- High-precision forward-error floor in equation (6.18). -/
noncomputable def p16ForwardFloor {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P16MixedPrecisionGMRESRun (n := n) l) : ι → ℝ :=
  fun t ↦
    p16PolynomialFactorValue run.polynomialFactor n n * run.uHigh t *
      p16ConditionNumberF run.A run.Ainv

/-- One column of the augmented least-squares data `[rhs, C]`. This is the
columnwise object bounded in condition (3.3). -/
def p16AugmentedColumn {n k : ℕ} (rhs : P16Vector n)
    (C : P16RectMatrix n k) (j : Fin (k + 1)) : P16Vector n :=
  Fin.cases rhs (fun q row ↦ C row q) j

/-- One fixed-precision, fully stored MGS-GMRES correction solve at an outer
restart. The raw fields encode the low-precision residual cast, MGS Arnoldi
projection/update order, augmented-column least-squares model (3.3), rounded
correction formation, and key-dimension conditions. The final two fields are
the correction-level estimates inherited from the earlier MGS-GMRES analysis;
they stop before the high-precision composition in Theorem 6.3. -/
structure P16FixedLowPrecisionMGSRestart {n : ℕ}
    (A Ainv : P16Matrix n) (b xExact xCurrent xNext residualHat
      correctionHat : P16Vector n)
    (uLow : ℝ) (dimensionFactor : P16PolynomialFactor) where
  keyDimension : ℕ
  keyDimension_pos : 0 < keyDimension
  keyDimension_le : keyDimension ≤ n
  basis : P16RectMatrix n keyDimension
  basisNext : P16RectMatrix n (keyDimension + 1)
  hessenberg : P16RectMatrix (keyDimension + 1) keyDimension
  arnoldiProduct : P16RectMatrix n keyDimension
  arnoldiProductError : P16RectMatrix n keyDimension
  arnoldi_product_equation :
    arnoldiProduct = p16SquareRectMul A basis + arnoldiProductError
  basis_fully_stored : ∀ row col,
    basis row col = basisNext row col.castSucc
  mgsWork : Fin keyDimension → ℕ → P16Vector n
  mgsProjectionError : Fin keyDimension → Fin keyDimension → ℝ
  mgsUpdateError : Fin keyDimension → Fin keyDimension → P16Vector n
  mgsNormalizationError : Fin keyDimension → P16Vector n
  mgs_work_initial : ∀ j row,
    mgsWork j 0 row = arnoldiProduct row j
  mgs_projection : ∀ j q, q.1 ≤ j.1 →
    hessenberg q.castSucc j =
      (∑ row : Fin n, basisNext row q.castSucc * mgsWork j q.1 row) +
        mgsProjectionError j q
  mgs_projection_error_bound : ∀ j q, q.1 ≤ j.1 →
    |mgsProjectionError j q| ≤
      gamma uLow n *
        (∑ row : Fin n, |basisNext row q.castSucc * mgsWork j q.1 row|)
  mgs_update : ∀ j q, q.1 ≤ j.1 →
    mgsWork j (q.1 + 1) =
      mgsWork j q.1 -
        (fun row ↦ hessenberg q.castSucc j * basisNext row q.castSucc) +
          mgsUpdateError j q
  mgs_update_error_bound : ∀ j q, q.1 ≤ j.1 →
    p16VecNorm (mgsUpdateError j q) ≤
      uLow *
        (p16VecNorm (mgsWork j q.1) +
          |hessenberg q.castSucc j| *
            p16VecNorm (fun row ↦ basisNext row q.castSucc))
  mgs_normalization : ∀ j,
    (fun row ↦ hessenberg j.succ j * basisNext row j.succ) =
      mgsWork j (j.1 + 1) + mgsNormalizationError j
  mgs_normalization_error_bound : ∀ j,
    p16VecNorm (mgsNormalizationError j) ≤
      uLow * p16VecNorm (mgsWork j (j.1 + 1))
  epsilonC : ℝ
  epsilonB : ℝ
  epsilonLS : ℝ
  epsilonX : ℝ
  residualLow : P16Vector n
  residualCastError : P16Vector n
  residual_cast_equation : residualLow = residualHat + residualCastError
  residual_cast_bound :
    p16VecNorm residualCastError ≤ uLow * p16VecNorm residualHat
  residualNorm : ℝ
  residualNorm_eq : residualNorm = p16VecNorm residualLow
  residual_starts_basis : ∀ row,
    residualLow row = residualNorm * basisNext row 0
  epsilonB_eq : epsilonB = uLow
  product_error_bound :
    p16RectFrobNorm arnoldiProductError ≤
      epsilonC * p16RectFrobNorm (p16SquareRectMul A basis)
  leastSquaresRhsError : P16Vector n
  leastSquaresMatrixError : P16RectMatrix n keyDimension
  leastSquaresY : P16Vector keyDimension
  least_squares_solution :
    p16IsLeastSquaresSolution
      (arnoldiProduct + leastSquaresMatrixError)
      (residualLow + leastSquaresRhsError) leastSquaresY
  least_squares_column_bound : ∀ j : Fin (keyDimension + 1),
    p16VecNorm
        (p16AugmentedColumn leastSquaresRhsError leastSquaresMatrixError j) ≤
      epsilonLS *
        p16VecNorm (p16AugmentedColumn residualLow arnoldiProduct j)
  correctionFormationError : P16Vector n
  correction_formation_equation :
    correctionHat = p16RectMatVec basis leastSquaresY +
      correctionFormationError
  correction_formation_bound :
    p16VecNorm correctionFormationError ≤
      epsilonX * p16RectFrobNorm basis * p16VecNorm leastSquaresY
  accuracy_nonneg :
    0 ≤ epsilonC ∧ 0 ≤ epsilonB ∧ 0 ≤ epsilonLS ∧ 0 ≤ epsilonX
  productWeight : ℝ
  leastSquaresWeight : ℝ
  correctionWeight : ℝ
  weights_nonneg :
    0 ≤ productWeight ∧ 0 ≤ leastSquaresWeight ∧ 0 ≤ correctionWeight
  epsilonC_le : epsilonC ≤ productWeight * uLow
  epsilonLS_le : epsilonLS ≤ leastSquaresWeight * uLow
  epsilonX_le : epsilonX ≤ correctionWeight * uLow
  basisLowerGain : ℝ
  imageLowerGain : ℝ
  basisLowerGain_pos : 0 < basisLowerGain
  basis_gain : p16MinGainAtLeast basis basisLowerGain
  image_gain : p16MinGainAtLeast (p16SquareRectMul A basis) imageLowerGain
  basis_not_numerically_rank_deficient :
    epsilonX * p16RectFrobNorm basis < basisLowerGain
  key_near_dependence : keyDimension < n → ∀ phi, 0 < phi →
    p16NearRankDeficient
      (p16Augment residualLow phi arnoldiProduct)
      ((epsilonC + epsilonB + epsilonLS) *
        p16PolynomialFactorValue dimensionFactor n keyDimension *
          p16RectFrobNorm (p16Augment residualLow phi arnoldiProduct))
  key_image_full_rank :
    (epsilonC + epsilonB + epsilonLS) *
        p16RectFrobNorm arnoldiProduct < imageLowerGain
  alpha : ℝ
  beta : ℝ
  lambda : ℝ
  coefficients_nonneg : 0 ≤ alpha ∧ 0 ≤ beta ∧ 0 ≤ lambda
  alpha_eq :
    alpha = p16RectFrobNorm arnoldiProduct /
      (basisLowerGain * p16FrobNorm A)
  beta_eq : beta = max 1 alpha
  lambda_eq : lambda = p16RectFrobNorm basis / basisLowerGain
  modularAccuracy : ℝ
  modular_accuracy_eq :
    modularAccuracy =
      alpha * epsilonC + beta * epsilonB + beta * epsilonLS +
        lambda * epsilonX
  dimension_factor_bound :
    alpha * productWeight + beta * (1 + leastSquaresWeight) +
        lambda * correctionWeight ≤
      p16PolynomialFactorValue dimensionFactor n keyDimension
  backward_correction_bound :
    p16VecNorm (residualHat - p16MatVec A correctionHat) /
        (p16VecNorm b + p16FrobNorm A * p16VecNorm xNext) ≤
      (p16PolynomialFactorValue dimensionFactor n keyDimension * uLow *
          p16ConditionNumberF A Ainv) *
        p16BackwardError A b xCurrent
  forward_correction_bound :
    p16VecNorm (xCurrent + correctionHat - xExact) /
        p16VecNorm xExact ≤
      (p16PolynomialFactorValue dimensionFactor n keyDimension * uLow *
          p16ConditionNumberF A Ainv) *
        p16ForwardError xExact xCurrent

/-- One fixed-precision execution of unpreconditioned restarted MGS-GMRES in
Theorem 6.3. The same positive unit roundoffs and system are used at every
restart, while each restart may select its own key dimension. -/
structure P16FixedMixedPrecisionGMRESRun (n : ℕ) where
  dimension_pos : 0 < n
  A : P16Matrix n
  Ainv : P16Matrix n
  b : P16Vector n
  xExact : P16Vector n
  xHat : ℕ → P16Vector n
  residualHat : ℕ → P16Vector n
  correctionHat : ℕ → P16Vector n
  residualError : ℕ → P16Vector n
  updateError : ℕ → P16Vector n
  uHigh : ℝ
  uLow : ℝ
  dimensionFactor : P16PolynomialFactor
  b_nonzero : b ≠ 0
  nonsingular : p16IsNonsingular A
  left_inverse_action : ∀ z : P16Vector n,
    p16MatVec Ainv (p16MatVec A z) = z
  right_inverse_action : ∀ z : P16Vector n,
    p16MatVec A (p16MatVec Ainv z) = z
  exact_solution : p16MatVec A xExact = b
  uHigh_pos : 0 < uHigh
  uLow_pos : 0 < uLow
  residual_equation : ∀ i,
    residualHat i = p16Residual A b (xHat i) + residualError i
  residual_error_bound : ∀ i j,
    |residualError i j| ≤
      gamma uHigh n *
        (|b j| +
          p16MatVec (fun row col ↦ |A row col|)
            (fun col ↦ |xHat i col|) j)
  update_equation : ∀ i,
    xHat (i + 1) = xHat i + correctionHat i + updateError i
  update_error_bound : ∀ i j,
    |updateError i j| ≤ uHigh * |xHat (i + 1) j|
  restart : ∀ i,
    P16FixedLowPrecisionMGSRestart A Ainv b xExact
      (xHat i) (xHat (i + 1)) (residualHat i) (correctionHat i)
      uLow dimensionFactor
  backward_high_roundoff_bound : ∀ i,
    (p16VecNorm (residualError i) +
          p16VecNorm (p16MatVec A (updateError i))) /
        (p16VecNorm b + p16FrobNorm A * p16VecNorm (xHat (i + 1))) ≤
      p16PolynomialFactorValue dimensionFactor n
          (restart i).keyDimension * uHigh
  forward_high_roundoff_bound : ∀ i,
    p16VecNorm (updateError i) / p16VecNorm xExact ≤
      p16PolynomialFactorValue dimensionFactor n
          (restart i).keyDimension * uHigh *
        p16ConditionNumberF A Ainv

/-- The restart-local contraction scale in equation (6.17), with the paper's
generic dimension factor evaluated at the actual key dimension `k_i`. -/
noncomputable def p16FixedMixedContraction {n : ℕ}
    (run : P16FixedMixedPrecisionGMRESRun n) (i : ℕ) : ℝ :=
  p16PolynomialFactorValue run.dimensionFactor n
      (run.restart i).keyDimension * run.uLow *
    p16ConditionNumberF run.A run.Ainv

/-- The restart-local high-precision backward-error floor in equation (6.18). -/
noncomputable def p16FixedBackwardFloor {n : ℕ}
    (run : P16FixedMixedPrecisionGMRESRun n) (i : ℕ) : ℝ :=
  p16PolynomialFactorValue run.dimensionFactor n
      (run.restart i).keyDimension * run.uHigh

/-- The restart-local high-precision forward-error floor in equation (6.18). -/
noncomputable def p16FixedForwardFloor {n : ℕ}
    (run : P16FixedMixedPrecisionGMRESRun n) (i : ℕ) : ℝ :=
  p16PolynomialFactorValue run.dimensionFactor n
      (run.restart i).keyDimension * run.uHigh *
    p16ConditionNumberF run.A run.Ainv

end HighamBench
