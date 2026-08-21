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

/-- Evaluation-order cases discussed after P04 equation (3.4). The `other`
constructor represents any further parenthesization covered by the paper's
unsharpened all-orders bound. -/
inductive P04BlockEvaluationOrder where
  | leftToRight
  | rightToLeft
  | other (code : ℕ)
  deriving DecidableEq

/-- Exact dot product in the block indexing of recurrence (3.1). -/
noncomputable def p04BlockedDot {q b : ℕ}
    (x y : Fin q → Fin b → ℝ) : ℝ :=
  ∑ k : Fin q, ∑ j : Fin b, x k j * y k j

/-- The componentwise scale `|x|ᵀ|y|` in block indexing. -/
noncomputable def p04BlockedAbsDot {q b : ℕ}
    (x y : Fin q → Fin b → ℝ) : ℝ :=
  ∑ k : Fin q, ∑ j : Fin b, |x k j| * |y k j|

/-- Extend a block-indexed error by zero outside its valid natural range. -/
noncomputable def p04ErrorAt {q : ℕ} (error : Fin q → ℝ) (k : ℕ) : ℝ :=
  if h : k < q then error ⟨k, h⟩ else 0

/-- Product of the modeled output-rounding factors from block `k` onward. -/
noncomputable def p04InclusiveErrorProduct {q : ℕ}
    (error : Fin q → ℝ) (k : Fin q) : ℝ :=
  ∏ l ∈ Finset.Ico k.val q, (1 + p04ErrorAt error l)

/-- Product of the modeled carry factors strictly after block `k`. -/
noncomputable def p04StrictErrorProduct {q : ℕ}
    (error : Fin q → ℝ) (k : Fin q) : ℝ :=
  ∏ l ∈ Finset.Ico (k.val + 1) q, (1 + p04ErrorAt error l)

/-- A finite-real execution of the scalar recurrence (3.1) underlying P04
Algorithm 3.1.

Each `state_step` is the local standard-model representation (3.2): the old
state and the `b` products carry internal-precision `theta` factors, followed
by the single output-rounding factor `delta`. For the first block, `s₀ = 0`
removes one operation and all term paths fit in `gamma uBar b`; later term
paths fit in `gamma uBar (b+1)`. A generic carry path fits in `gamma uBar b`,
while right-to-left evaluation gives the one-operation carry path responsible
for the `q+b-1` refinement.

The structure contains no compact `alpha`/`beta` witnesses and no final error
bound. Those are consequences of the trace. As in the paper's analysis, the
real-valued local model excludes underflow, overflow, and exceptional IEEE
values and represents the deliberate single-rounding simplification. -/
structure P04BlockFmaDotRun (n b q : ℕ) where
  dimension_pos : 0 < n
  block_size_pos : 0 < b
  block_count_pos : 0 < q
  dimension_eq : n = q * b
  x : Fin q → Fin b → ℝ
  y : Fin q → Fin b → ℝ
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
  order : P04BlockEvaluationOrder
  state : ℕ → ℝ
  carryTheta : Fin q → ℝ
  termTheta : Fin q → Fin b → ℝ
  delta : Fin q → ℝ
  state_zero : state 0 = 0
  state_step : ∀ k : Fin q,
    state (k.val + 1) =
      (state k.val * (1 + carryTheta k) +
        ∑ j : Fin b, x k j * y k j * (1 + termTheta k j)) *
          (1 + delta k)
  delta_bound : ∀ k,
    |delta k| ≤ p04EffectiveFmaRoundoff uBar uFma uOut
  carry_theta_bound : ∀ k, |carryTheta k| ≤ gamma uBar b
  term_theta_bound : ∀ k j,
    |termTheta k j| ≤ gamma uBar (if k.val = 0 then b else b + 1)
  right_to_left_carry_bound :
    order = P04BlockEvaluationOrder.rightToLeft →
      ∀ k, |carryTheta k| ≤ gamma uBar 1
  innerPathError : Fin q → Fin b → Fin n → ℝ
  inner_path_error_bound : ∀ k j r, |innerPathError k j r| ≤ uBar
  inner_path_factor : ∀ k j,
    (∏ r : Fin n, (1 + innerPathError k j r)) =
      (1 + termTheta k j) * p04StrictErrorProduct carryTheta k
  rightToLeftPathError : Fin q → Fin b → Fin (q + b - 1) → ℝ
  right_to_left_path_error_bound :
    order = P04BlockEvaluationOrder.rightToLeft →
      ∀ k j r, |rightToLeftPathError k j r| ≤ uBar
  right_to_left_path_factor :
    order = P04BlockEvaluationOrder.rightToLeft →
      ∀ k j,
        (∏ r : Fin (q + b - 1),
          (1 + rightToLeftPathError k j r)) =
            (1 + termTheta k j) *
              p04StrictErrorProduct carryTheta k

/-- The final state of the modeled Algorithm 3.1 scalar recurrence. -/
noncomputable def P04BlockFmaDotRun.computed
    {n b q : ℕ} (run : P04BlockFmaDotRun n b q) : ℝ :=
  run.state q

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
