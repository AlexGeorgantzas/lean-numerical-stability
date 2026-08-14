import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- The mixed-precision block-FMA coefficient occurring in P04 equations
(3.4)--(3.6). -/
noncomputable def p04BlockFmaCoeff
    (uFma u : ℝ) (q n : ℕ) : ℝ :=
  gamma uFma q + gamma u n + gamma uFma q * gamma u n

/-- The prioritized effective output-rounding parameter in P04 equation (3.3).
The first branch takes priority when the final output precision is coarser than
the block-FMA output precision. -/
noncomputable def p04EffectiveFmaRoundoff
    (uBar uFma uOut : ℝ) : ℝ :=
  if uFma < uOut then uOut
  else if uFma ≤ uBar then 0
  else uFma

/-- Exact finite dot product used in the scalar-entry analysis of Algorithm
3.1. -/
noncomputable def p04Dot {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, x i * y i

/-- The componentwise data scale `|x|ᵀ|y|` in P04 equation (3.4). This is a
dot product of entrywise absolute values, not a norm. -/
noncomputable def p04AbsDot {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |x i| * |y i|

/-- A scalar output of the chained block-FMA loop in Algorithm 3.1, represented
by the compact perturbation factorization immediately preceding equation
(3.4). The certificate is the paper's finite real standard-model semantics:
underflow, overflow, exceptional IEEE values, and the omitted second output
rounding are outside this model.

The unconditional `beta_bound` records the paper's statement that (3.4) is
valid for every evaluation order admitted by its analysis. `rightToLeft`
marks the blocked right-to-left case for which the paper supplies the sharper
`q+b-1` bound. -/
structure P04BlockFmaDotRun (n b q : ℕ) where
  dimension_pos : 0 < n
  block_size_pos : 0 < b
  block_count_pos : 0 < q
  dimension_eq : n = q * b
  x : Fin n → ℝ
  y : Fin n → ℝ
  computed : ℝ
  uBar : ℝ
  uFma : ℝ
  uOut : ℝ
  uBar_nonneg : 0 ≤ uBar
  uFma_nonneg : 0 ≤ uFma
  uOut_nonneg : 0 ≤ uOut
  uBar_le_uFma : uBar ≤ uFma
  effective_gamma_valid :
    GammaValid (p04EffectiveFmaRoundoff uBar uFma uOut) q
  internal_gamma_valid : GammaValid uBar n
  alpha : Fin n → ℝ
  beta : Fin n → ℝ
  algorithm3_1_factorization :
    computed = ∑ i : Fin n,
      x i * y i * (1 + alpha i) * (1 + beta i)
  alpha_bound : ∀ i,
    |alpha i| ≤ gamma (p04EffectiveFmaRoundoff uBar uFma uOut) q
  beta_bound : ∀ i, |beta i| ≤ gamma uBar n
  rightToLeft : Prop
  right_to_left_gamma_valid :
    rightToLeft → GammaValid uBar (q + b - 1)
  right_to_left_beta_bound :
    rightToLeft → ∀ i, |beta i| ≤ gamma uBar (q + b - 1)

/-- Rectangular matrix multiplication in the notation of P04 Theorem 3.2. -/
noncomputable def p04RectMatMul {m n t : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin t → ℝ) :
    Fin m → Fin t → ℝ :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- The ordinary matrix product `|A||B|` in P04 equation (3.6), with absolute
values taken componentwise. This is not a matrix norm. -/
noncomputable def p04AbsRectMatMul {m n t : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin t → ℝ) :
    Fin m → Fin t → ℝ :=
  fun i j ↦ ∑ k : Fin n, |A i k| * |B k j|

/-- An execution of P04 Algorithm 3.1 for inputs not necessarily stored in the
low precision, represented by the standard-model certificates used to derive
Theorem 3.2. The `deltaA` and `deltaB` fields record line 1's componentwise
rounding errors. The indexed `alpha` and `beta` fields record the compact
factorization of every output entry derived from the chained block FMAs.

All values are finite reals. Thus this certificate has exactly the paper's
stated analysis scope: underflow, overflow, exceptional IEEE values, and the
second output rounding omitted in section 3.2 are outside the model. -/
structure P04MixedInputMatMulRun
    (m n t b1 b b2 p q r : ℕ) where
  row_dimension_pos : 0 < m
  inner_dimension_pos : 0 < n
  column_dimension_pos : 0 < t
  row_block_size_pos : 0 < b1
  inner_block_size_pos : 0 < b
  column_block_size_pos : 0 < b2
  row_block_count_pos : 0 < p
  inner_block_count_pos : 0 < q
  column_block_count_pos : 0 < r
  row_partition : m = p * b1
  inner_partition : n = q * b
  column_partition : t = r * b2
  A : Fin m → Fin n → ℝ
  B : Fin n → Fin t → ℝ
  convertedA : Fin m → Fin n → ℝ
  convertedB : Fin n → Fin t → ℝ
  deltaA : Fin m → Fin n → ℝ
  deltaB : Fin n → Fin t → ℝ
  computed : Fin m → Fin t → ℝ
  uLow : ℝ
  uBar : ℝ
  uFma : ℝ
  uOut : ℝ
  uLow_nonneg : 0 ≤ uLow
  uBar_nonneg : 0 ≤ uBar
  uFma_nonneg : 0 ≤ uFma
  uOut_nonneg : 0 ≤ uOut
  uBar_le_uFma : uBar ≤ uFma
  effective_gamma_valid :
    GammaValid (p04EffectiveFmaRoundoff uBar uFma uOut) q
  internal_gamma_valid : GammaValid uBar n
  convertedA_eq : ∀ i k, convertedA i k = A i k + deltaA i k
  convertedB_eq : ∀ k j, convertedB k j = B k j + deltaB k j
  deltaA_bound : ∀ i k, |deltaA i k| ≤ uLow * |A i k|
  deltaB_bound : ∀ k j, |deltaB k j| ≤ uLow * |B k j|
  alpha : Fin m → Fin t → Fin n → ℝ
  beta : Fin m → Fin t → Fin n → ℝ
  algorithm3_1_factorization : ∀ i j,
    computed i j = ∑ k : Fin n,
      convertedA i k * convertedB k j *
        (1 + alpha i j k) * (1 + beta i j k)
  alpha_bound : ∀ i j k,
    |alpha i j k| ≤
      gamma (p04EffectiveFmaRoundoff uBar uFma uOut) q
  beta_bound : ∀ i j k, |beta i j k| ≤ gamma uBar n

/-- The factorization-stage coefficient in P04 equations (4.4) and (4.7). -/
noncomputable def p04FactorizationCoeff
    (uLow uBar uFma uWork : ℝ) (q n b : ℕ) : ℝ :=
  2 * uLow + uLow ^ 2 +
    max
      (p04BlockFmaCoeff
        (p04EffectiveFmaRoundoff uBar uFma uWork)
        uBar (q - 1) (n - b + 1))
      (gamma uWork b) * (1 + uLow) ^ 2

/-- Square matrix multiplication in the paper's finite-index notation. -/
noncomputable def p04MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- Matrix-vector multiplication in the paper's finite-index notation. -/
noncomputable def p04MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, A i j * x j

/-- The componentwise absolute product `|L||U|` in P04 equations (4.4) and
(4.7). -/
noncomputable def p04AbsMatMul {n : ℕ}
    (L U : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, |L i k| * |U k j|

/-- The mandatory componentwise scale `|A| + |Lhat||Uhat|` in P04 equations
(4.4) and (4.7). -/
noncomputable def p04LUSolveScale {n : ℕ}
    (A LHat UHat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => |A i j| + p04AbsMatMul LHat UHat i j

/-- Entrywise lower-triangularity for the computed factor in Algorithm 4.1. -/
def p04IsLowerTriangular {n : ℕ} (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, i.val < j.val → L i j = 0

/-- Entrywise upper-triangularity for the computed factor in Algorithm 4.1. -/
def p04IsUpperTriangular {n : ℕ} (U : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, j.val < i.val → U i j = 0

/-- A complete finite-real execution certificate for P04 Algorithm 4.1 followed
by forward and backward substitution, as used in Theorem 4.4. The factorization
fields record Theorem 4.3's consequence for the computed factors; the solve
fields record the standard triangular-substitution backward errors invoked in
the proof of Theorem 4.4. The final perturbation from equation (4.7) is not a
field and must be constructed by the target theorem.

The certificate represents successful execution in the paper's standard model.
Underflow, overflow, exceptional IEEE values, and the double-rounding effect
omitted by the paper are outside this finite-real model. -/
structure P04BlockLUSolveRun (n b q : ℕ) where
  dimension_pos : 0 < n
  block_size_pos : 0 < b
  block_count_pos : 0 < q
  dimension_eq : n = q * b
  A : Fin n → Fin n → ℝ
  LHat : Fin n → Fin n → ℝ
  UHat : Fin n → Fin n → ℝ
  lower_triangular : p04IsLowerTriangular LHat
  upper_triangular : p04IsUpperTriangular UHat
  lower_unit_diagonal : ∀ i, LHat i i = 1
  upper_diagonal_nonzero : ∀ i, UHat i i ≠ 0
  uLow : ℝ
  uBar : ℝ
  uFma : ℝ
  uWork : ℝ
  uLow_nonneg : 0 ≤ uLow
  uBar_nonneg : 0 ≤ uBar
  uFma_nonneg : 0 ≤ uFma
  uWork_nonneg : 0 ≤ uWork
  uBar_le_uFma : uBar ≤ uFma
  effective_factor_gamma_valid :
    GammaValid (p04EffectiveFmaRoundoff uBar uFma uWork) (q - 1)
  internal_factor_gamma_valid : GammaValid uBar (n - b + 1)
  working_block_gamma_valid : GammaValid uWork b
  working_solve_gamma_valid : GammaValid uWork n
  factorError : Fin n → Fin n → ℝ
  algorithm4_1_factorization : p04MatMul LHat UHat = A + factorError
  factor_error_bound : ∀ i j,
    |factorError i j| ≤
      p04FactorizationCoeff uLow uBar uFma uWork q n b *
        p04LUSolveScale A LHat UHat i j
  xHat : Fin n → ℝ
  yHat : Fin n → ℝ
  rhs : Fin n → ℝ
  deltaL : Fin n → Fin n → ℝ
  deltaU : Fin n → Fin n → ℝ
  forward_substitution : p04MatVec (LHat + deltaL) yHat = rhs
  backward_substitution : p04MatVec (UHat + deltaU) xHat = yHat
  deltaL_bound : ∀ i j,
    |deltaL i j| ≤ gamma uWork n * |LHat i j|
  deltaU_bound : ∀ i j,
    |deltaU i j| ≤ gamma uWork n * |UHat i j|

end HighamBench
