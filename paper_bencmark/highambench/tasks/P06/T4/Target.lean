import HighamBench.P06Definitions

namespace HighamBench

open MeasureTheory

open scoped BigOperators

/-- P06 Lemma 1.2 and equation (1.5): a product of factors with
exponents plus or minus one has a relative perturbation bounded by gamma_n
when every local error is bounded by u and n*u is below one. -/
theorem p06_t4_signed_product_bound
    {n : ℕ} (u : ℝ) (delta : Fin n → ℝ)
    (positiveExponent : Fin n → Bool)
    (hu : 0 ≤ u) (hsmall : (n : ℝ) * u < 1)
    (hdelta : ∀ i, |delta i| ≤ u) :
    ∃ theta : ℝ,
      p06SignedProduct delta positiveExponent = 1 + theta ∧
        |theta| ≤ p06Gamma n u := by
  -- PROOF_START P06-T4-H001
  sorry

/-- P06 Lemma 1.4 and equation (1.7): under Model 1.5 the same signed
product has the probabilistic gamma bound with the paper's explicit success
probability. -/
theorem p06_t4_probabilistic_signed_product_bound
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (n : ℕ) (u lambdaParam : ℝ)
    (delta : ℕ → Omega → ℝ) (positiveExponent : Fin n → Bool)
    (hlambda : 0 < lambdaParam) (hu : u < 1)
    (hmodel : p06RoundingErrorModel mu n u delta) :
    p06ProbabilityAtLeast mu
      (fun omega ↦
        ∃ theta : ℝ,
          p06SignedProduct (fun i : Fin n ↦ delta i omega) positiveExponent =
              1 + theta ∧
            |theta| ≤ p06ProbGamma n u lambdaParam)
      (p06ProductSuccessProbability lambdaParam) := by
  -- PROOF_START P06-T4-H002
  sorry



/-- P06 equation (1.3), also the deterministic aggregation step used in
equation (4.20). A common nonnegative relative 2-norm bound on every column
implies the same relative Frobenius bound. -/
theorem p06_t4_columnwise_to_frobenius
    {m n : ℕ} (A deltaA : Fin m → Fin n → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hcol : p06ColumnwiseRelativeError A deltaA eta) :
    p06FrobNorm deltaA ≤ eta * p06FrobNorm A := by
  -- PROOF_START P06-T4-H003
  sorry

/-- P06 equation (3.4), expressed without introducing an eigenvalue API:
rectangular operator control is equivalent to scalar-identity Loewner control
of the symmetric dilation at every nonnegative threshold. -/
theorem p06_t4_self_adjoint_dilation_norm_bridge
    {m n : ℕ} (M : Fin m → Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    p06RectOpNorm2Le M L ↔
      p06FiniteLoewnerLe (p06SelfAdjointDilation M)
        (fun a b : Fin m ⊕ Fin n ↦ L * p06FiniteId a b) := by
  -- PROOF_START P06-T4-H004
  sorry

/-- P06 equations (4.8)--(4.9): the fully perturbed product is its exact
part plus every single-perturbation insertion and an explicit term containing
all contributions of order at least two. -/
theorem p06_t4_householder_product_first_order_expansion
    {m : ℕ} (t : ℝ)
    (P E : ℕ → Fin m → Fin m → ℝ) (b : Fin m → ℝ) :
    ∀ r i,
      p06PerturbedState t P E b r i =
        p06ExactState P b r i +
          t * p06FirstOrderState P E b r i +
          t ^ 2 * p06HigherOrderState t P E b r i := by
  -- PROOF_START P06-T4-H005
  sorry

/-- The exact comparison underlying equations (4.18)--(4.19): for m at least
n and nonnegative u, the probabilistic higher-order scale
sqrt(m) * n * sqrt(n) * u is no larger than the worst-case scale m*n*u. -/
theorem p06_t4_higher_order_scale_comparison
    (m n u : ℝ) (hm : 0 ≤ m) (hn : 0 ≤ n) (hnm : n ≤ m) (hu : 0 ≤ u) :
    Real.sqrt m * n * Real.sqrt n * u ≤ m * n * u := by
  -- PROOF_START P06-T4-H006
  sorry

/-- P06 equation (5.2): if P has both orthogonality identities, then the
separate left- and right-application backward errors combine exactly as
deltaA1 + P-transpose*deltaA2. -/
theorem p06_t4_two_sided_backward_error_composition
    {n : ℕ}
    (P A deltaA1 deltaA2 : Fin n → Fin n → ℝ)
    (hleft : p06MatMul P (p06Transpose P) = p06IdMatrix) :
    p06MatMul
        (p06MatAdd (p06MatMul P (p06MatAdd A deltaA1)) deltaA2)
        (p06Transpose P) =
      p06MatMul
        (p06MatMul P
          (p06MatAdd A
            (p06MatAdd deltaA1 (p06MatMul (p06Transpose P) deltaA2))))
        (p06Transpose P) := by
  -- PROOF_START P06-T4-H007
  sorry

/-- P06 Theorem 3.1 and equations (3.1)--(3.2), the quoted
matrix Azuma--Hoeffding inequality in the paper's finite real-matrix setting. -/
theorem p06_t4_matrix_azuma_hoeffding
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {d r : ℕ}
    (X : ℕ → Omega → Fin d → Fin d → ℝ)
    (Afixed : ℕ → Fin d → Fin d → ℝ)
    (t sigmaSq : ℝ)
    (ht : 0 ≤ t)
    (hXsym : ∀ k, k < r → ∀ᵐ omega ∂mu, p06Symmetric (X k omega))
    (hAsym : ∀ k, k < r → p06Symmetric (Afixed k))
    (hXint : ∀ k, k < r → ∀ i j,
      Integrable (fun omega ↦ X k omega i j) mu)
    (hmean : p06MatrixConditionalMeanZero mu X r)
    (hsquare : ∀ k, k < r → ∀ᵐ omega ∂mu,
      p06FiniteLoewnerLe (p06MatrixSquare (X k omega))
        (p06MatrixSquare (Afixed k)))
    (hsigma : sigmaSq =
      p06OperatorNorm2
        (p06MatrixSum (fun k : Fin r ↦ p06MatrixSquare (Afixed k)))) :
    mu {omega |
        p06LambdaMaxGe
          (p06MatrixSum (fun k : Fin r ↦ X k omega)) t} ≤
      ENNReal.ofReal
        ((d : ℝ) * Real.exp (-(t ^ 2) / (8 * sigmaSq))) := by
  -- PROOF_START P06-T4-H008
  sorry


/-- P06 Theorem 3.2 and equations (3.5)--(3.6), obtained for
rectangular matrices through the symmetric dilation. This transparent report
preserves the literal source assertion without asserting its false sigma=0 edge. -/
def p06_t4_rectangular_matrix_concentration_source_report
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {d1 d2 r : ℕ}
    (X : ℕ → Omega → Fin d1 → Fin d2 → ℝ)
    (Afixed : ℕ → Fin d1 → Fin d2 → ℝ)
    (lambdaParam sigma : ℝ)
    (hlambda : 0 ≤ lambdaParam) (hsigmaNonneg : 0 ≤ sigma)
    (hXint : ∀ k, k < r → ∀ i j,
      Integrable (fun omega ↦ X k omega i j) mu)
    (hmean : p06MatrixConditionalMeanZero mu
      (fun k omega ↦ p06SelfAdjointDilation (X k omega)) r)
    (hleftSquare : ∀ k, k < r → ∀ᵐ omega ∂mu,
      p06FiniteLoewnerLe
        (p06MatMul (X k omega) (p06Transpose (X k omega)))
        (p06MatMul (Afixed k) (p06Transpose (Afixed k))))
    (hrightSquare : ∀ k, k < r → ∀ᵐ omega ∂mu,
      p06FiniteLoewnerLe
        (p06MatMul (p06Transpose (X k omega)) (X k omega))
        (p06MatMul (p06Transpose (Afixed k)) (Afixed k)))
    (hsigma : sigma ^ 2 =
      max
        (p06OperatorNorm2
          (p06MatrixSum (fun k : Fin r ↦
            p06MatMul (Afixed k) (p06Transpose (Afixed k)))))
        (p06OperatorNorm2
          (p06MatrixSum (fun k : Fin r ↦
            p06MatMul (p06Transpose (Afixed k)) (Afixed k))))) : Prop :=
    mu {omega |
        2 * Real.sqrt 2 * sigma * lambdaParam ≤
          p06OperatorNorm2
            (p06RectMatrixSum (fun k : Fin r ↦ X k omega))} ≤
      ENNReal.ofReal
        (((d1 : ℝ) + d2) * Real.exp (-(lambdaParam ^ 2)))


/-- P06 Theorem 6.1: for nonsingular diagonal weights, the transpose
of an orthogonal polar factor of B*D^2*A-transpose minimizes the weighted
orthogonal Procrustes objective. -/
theorem p06_t4_weighted_procrustes_polar_minimizer
    {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) (d : Fin n → ℝ)
    (U : Fin m → Fin m → ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hpolar : p06IsPolarFactor U
      (p06MatMul
        (p06MatMul B
          (p06MatMul (p06DiagonalMatrix d) (p06DiagonalMatrix d)))
        (p06Transpose A))) :
    p06Orthogonal (p06Transpose U) ∧
      ∀ Q : Fin m → Fin m → ℝ, p06Orthogonal Q →
        p06WeightedQRError A B (p06Transpose U) d ≤
          p06WeightedQRError A B Q d := by
  -- PROOF_START P06-T4-H010
  sorry


/-- The first subtlety in the proof of Theorem 4.4: explicitly replacing
selected output rows by zero cannot increase any valid operator-2 threshold. -/
theorem p06_t4_zeroed_rows_do_not_increase_operator_bound
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (keepRow : Fin m → Bool) (L : ℝ) (hL : 0 ≤ L)
    (hA : p06RectOpNorm2Le A L) :
    p06RectOpNorm2Le
      (fun i j ↦ if keepRow i then A i j else 0) L := by
  -- PROOF_START P06-T4-H011
  sorry

/-- The SVD construction following Theorem 6.1: U*V-transpose is an
orthogonal polar factor of a matrix with SVD U*Sigma*V-transpose. -/
theorem p06_t4_svd_gives_polar_factor
    {n : ℕ}
    (C U V : Fin n → Fin n → ℝ) (singularValues : Fin n → ℝ)
    (hsvd : p06IsSingularValueDecomposition C U V singularValues) :
    p06IsPolarFactor (p06MatMul U (p06Transpose V)) C := by
  -- PROOF_START P06-T4-H012
  sorry

/-- The cancellation-prone singular-value identity following Theorem 6.1. -/
theorem p06_t4_weighted_qr_error_singular_value_formula
    {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) (d : Fin n → ℝ)
    (U V : Fin m → Fin m → ℝ) (singularValues : Fin m → ℝ)
    (hsvd : p06IsSingularValueDecomposition
      (p06MatMul
        (p06MatMul B
          (p06MatMul (p06DiagonalMatrix d) (p06DiagonalMatrix d)))
        (p06Transpose A))
      U V singularValues) :
    p06WeightedQRError A B
        (p06Transpose (p06MatMul U (p06Transpose V))) d ^ 2 =
      p06FrobNorm (p06MatMul A (p06DiagonalMatrix d)) ^ 2 +
        p06FrobNorm (p06MatMul B (p06DiagonalMatrix d)) ^ 2 -
          2 * ∑ i : Fin m, singularValues i := by
  -- PROOF_START P06-T4-H013
  sorry


end HighamBench
