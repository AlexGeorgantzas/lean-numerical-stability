import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- Square matrix-vector multiplication in the notation used for P08. -/
noncomputable def p08MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Square matrix multiplication in the notation used for P08. -/
noncomputable def p08MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Identity matrix for the paper-scoped matrix powers. -/
noncomputable def p08IdMatrix (n : ℕ) : Fin n → Fin n → ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Matrix powers used in the finite recurrence certificate for Lemma 4.3. -/
noncomputable def p08MatPow {n : ℕ}
    (B : Fin n → Fin n → ℝ) : ℕ → Fin n → Fin n → ℝ
  | 0 => p08IdMatrix n
  | k + 1 => p08MatMul B (p08MatPow B k)

/-- Componentwise absolute matrix action, `(abs A) (abs x)`. -/
noncomputable def p08AbsAction {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, |A i j| * |x j|

/-- The expanded componentwise action `(abs A) (abs Ainv) (abs q)`. -/
noncomputable def p08AbsProductAction {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) (q : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, |A i j| * p08AbsAction Ainv q j

/-- Pointwise vector addition. -/
def p08VecAdd {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ x i + y i

/-- Pointwise vector subtraction. -/
def p08VecSub {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ x i - y i

/-- Scalar multiplication of a vector. -/
def p08VecScale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ a * x i

/-- Componentwise absolute value of a vector. -/
def p08AbsVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ |x i|

/-- Pointwise matrix addition. -/
def p08MatAdd {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ A i j + B i j

/-- Pointwise matrix subtraction. -/
def p08MatSub {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ A i j - B i j

/-- Scalar multiplication of a matrix. -/
def p08MatScale {n : ℕ}
    (a : ℝ) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ a * A i j

/-- Componentwise absolute value of a matrix. -/
def p08AbsMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ |A i j|

/-- Entrywise nonnegativity for source-defined `C_i` matrices. -/
def p08MatNonnegative {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, 0 ≤ A i j

/-- Single- or double-precision residual accumulation from section 4. -/
inductive P08ResidualPrecision where
  | single
  | double
  deriving DecidableEq

/-- The paper's precision-dependent residual unit roundoff `ubar`. -/
def p08ResidualUnitRoundoff (precision : P08ResidualPrecision)
    (u : ℝ) : ℝ :=
  match precision with
  | .single => u
  | .double => u ^ 2

/-- A total real-valued floating-point model with the relative-error
semantics assumed by P08. Totality excludes NaN, infinity, and undefined
operations from represented executions. -/
structure P08ScalarArithmeticModel where
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

/-- A rounded row dot product in the residual-accumulation precision. -/
noncomputable def p08RoundedDot
    (model : P08ScalarArithmeticModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  recursiveSum model.flAdd n fun j : Fin n ↦ model.flMul (A i j) (x j)

/-- A residual computation with the subtraction by `b` performed after the
rounded matrix-vector product. In the double variant the result is then
converted to working precision. -/
structure P08SubtractionLastResidualTrace {n : ℕ}
    (precision : P08ResidualPrecision)
    (residualModel : P08ScalarArithmeticModel)
    (convert : ℝ → ℝ) (A : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ) where
  roundedAx : Fin n → ℝ
  beforeConversion : Fin n → ℝ
  output : Fin n → ℝ
  roundedAx_relation : ∀ i,
    roundedAx i = p08RoundedDot residualModel A x i
  subtraction_last : ∀ i,
    beforeConversion i = residualModel.flSub (roundedAx i) (b i)
  output_relation : output =
    match precision with
    | .single => beforeConversion
    | .double => fun i ↦ convert (beforeConversion i)

/-- Swap two rows of a square matrix. -/
def p08SwapRowsMatrix {n : ℕ} (A : Fin n → Fin n → ℝ)
    (r s : Fin n) : Fin n → Fin n → ℝ :=
  fun i j ↦ if i = r then A s j else if i = s then A r j else A i j

/-- Swap two entries of a vector. -/
def p08SwapRowsVector {n : ℕ} (b : Fin n → ℝ)
    (r s : Fin n) : Fin n → ℝ :=
  fun i ↦ if i = r then b s else if i = s then b r else b i

/-- One rounded elimination step after the largest active entry in column
`k` has been moved into the pivot position. -/
noncomputable def p08ColumnPivotedMatrixStep
    (model : P08ScalarArithmeticModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k pivot : Fin n) :
    Fin n → Fin n → ℝ :=
  let swapped := p08SwapRowsMatrix A k pivot
  fun i j ↦
    if i.val ≤ k.val then
      swapped i j
    else if j.val < k.val then
      swapped i j
    else if j = k then
      0
    else
      model.flSub (swapped i j)
        (model.flMul (model.flDiv (swapped i k) (swapped k k))
          (swapped k j))

/-- The rounded right-hand-side update paired with one elimination step. -/
noncomputable def p08ColumnPivotedRhsStep
    (model : P08ScalarArithmeticModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (k pivot : Fin n) : Fin n → ℝ :=
  let swappedA := p08SwapRowsMatrix A k pivot
  let swappedB := p08SwapRowsVector b k pivot
  fun i ↦
    if i.val ≤ k.val then
      swappedB i
    else
      model.flSub (swappedB i)
        (model.flMul (model.flDiv (swappedA i k) (swappedA k k))
          (swappedB k))

/-- Embed an index in the strict tail following row `i`. -/
def p08UpperTailIndex {n : ℕ} (i : Fin n)
    (j : Fin (n - (i.val + 1))) : Fin n :=
  ⟨i.val + 1 + j.val, by omega⟩

/-- Rounded upper-triangular tail dot product used by back substitution. -/
noncomputable def p08RoundedUpperTailDot
    (model : P08ScalarArithmeticModel) {n : ℕ}
    (U : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  recursiveSum model.flAdd (n - (i.val + 1)) fun j ↦
    model.flMul (U i (p08UpperTailIndex i j))
      (x (p08UpperTailIndex i j))

/-- An operational Gaussian-elimination trace with column pivoting in the
paper's terminology: at stage `k`, the largest active entry in column `k` is
moved to the diagonal, the trailing system is updated in working arithmetic,
and the final triangular system is solved by rounded back substitution. -/
structure P08ColumnPivotedGaussianEliminationTrace
    (model : P08ScalarArithmeticModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (rhs output : Fin n → ℝ) where
  matrixState : ℕ → Fin n → Fin n → ℝ
  rhsState : ℕ → Fin n → ℝ
  pivotRow : Fin n → Fin n
  initial_matrix : matrixState 0 = A
  initial_rhs : rhsState 0 = rhs
  pivot_active : ∀ k, k.val ≤ (pivotRow k).val
  pivot_largest : ∀ k i, k.val ≤ i.val →
    |matrixState k.val i k| ≤ |matrixState k.val (pivotRow k) k|
  pivot_nonzero : ∀ k, matrixState k.val (pivotRow k) k ≠ 0
  matrix_step : ∀ k,
    matrixState (k.val + 1) =
      p08ColumnPivotedMatrixStep model (matrixState k.val) k (pivotRow k)
  rhs_step : ∀ k,
    rhsState (k.val + 1) =
      p08ColumnPivotedRhsStep model (matrixState k.val)
        (rhsState k.val) k (pivotRow k)
  final_upper_triangular : ∀ i j, j.val < i.val → matrixState n i j = 0
  final_diagonal_nonzero : ∀ i, matrixState n i i ≠ 0
  back_substitution : ∀ i,
    output i = model.flDiv
      (model.flSub (rhsState n i)
        (p08RoundedUpperTailDot model (matrixState n) output i))
      (matrixState n i i)

/-- The componentwise backward-error certificate supplied by an operational
column-pivoted Gaussian-elimination solve. -/
structure P08ColumnPivotedSolveCertificate {n : ℕ}
    (model : P08ScalarArithmeticModel)
    (A : Fin n → Fin n → ℝ) (rhs : Fin n → ℝ)
    (C1 : Fin n → Fin n → ℝ) (u : ℝ) where
  output : Fin n → ℝ
  execution :
    P08ColumnPivotedGaussianEliminationTrace model A rhs output
  backwardError : Fin n → ℝ
  equation : p08MatVec A output = p08VecAdd rhs backwardError
  backward_error_bound : ∀ i,
    |backwardError i| ≤
      u * p08MatVec C1 (p08AbsAction A output) i

/-- A source-linked execution of section 4's column-pivoted iterative
refinement. Index `m` on `iterate`, `computedResidual`, and `correction`
denotes the paper's `x_m`, `r_m`, and `d_m`. -/
structure P08IterativeRefinementRun (n : ℕ) where
  dimension_pos : 0 < n
  precision : P08ResidualPrecision
  u : ℝ
  u_pos : 0 < u
  dimension_roundoff_small : (n : ℝ) * u ≤ 1 / 100
  workingModel : P08ScalarArithmeticModel
  working_roundoff : workingModel.unitRoundoff = u
  residualModel : P08ScalarArithmeticModel
  residual_roundoff :
    residualModel.unitRoundoff = p08ResidualUnitRoundoff precision u
  convert : ℝ → ℝ
  conversion_model : ∀ x, ∃ delta, |delta| ≤ u ∧
    convert x = x * (1 + delta)
  A : Fin n → Fin n → ℝ
  Ainv : Fin n → Fin n → ℝ
  inverse_left : p08MatMul Ainv A = p08IdMatrix n
  inverse_right : p08MatMul A Ainv = p08IdMatrix n
  b : Fin n → ℝ
  exactSolution : Fin n → ℝ
  exact_system : p08MatVec A exactSolution = b
  C1 : Fin n → Fin n → ℝ
  C1_nonnegative : p08MatNonnegative C1
  initialSolve : P08ColumnPivotedSolveCertificate workingModel A b C1 u
  iterate : ℕ → Fin n → ℝ
  computedResidual : ℕ → Fin n → ℝ
  correction : ℕ → Fin n → ℝ
  iterate_zero : iterate 0 = fun _ ↦ 0
  iterate_one : iterate 1 = initialSolve.output
  residual_zero : computedResidual 0 = fun i ↦ -b i
  correction_zero : correction 0 = fun i ↦ -iterate 1 i
  residualTrace : ∀ m,
    P08SubtractionLastResidualTrace precision residualModel convert
      A b (iterate (m + 1))
  residual_trace_output : ∀ m,
    computedResidual (m + 1) = (residualTrace m).output
  correctionSolve : ∀ m,
    P08ColumnPivotedSolveCertificate workingModel A (computedResidual m) C1 u
  correction_output : ∀ m, correction m = (correctionSolve m).output
  update_computation : ∀ m i,
    iterate (m + 1) i = workingModel.flSub (iterate m i) (correction m i)

/-- Skeel's exact residual `q_(m+1) = A(x_m-d_m)-b`. The Lean index `m`
is the paper's iteration index, so no artificial `q_0` is introduced. -/
noncomputable def p08ExactResidualAfterCorrection {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) : Fin n → ℝ :=
  p08VecSub (p08MatVec run.A
    (p08VecSub (run.iterate m) (run.correction m))) run.b

/-- A basis vector for the paper's normalized absolute-norm convention. -/
def p08BasisVector {n : ℕ} (j : Fin n) : Fin n → ℝ :=
  fun i ↦ if i = j then 1 else 0

/-- The absolute monotone vector norm and its induced matrix norm used in the
paper's nonstandard condition quantity. -/
structure P08AbsoluteMonotoneNorm (n : ℕ) where
  vecNorm : (Fin n → ℝ) → ℝ
  matrixNorm : (Fin n → Fin n → ℝ) → ℝ
  vec_norm_nonnegative : ∀ x, 0 ≤ vecNorm x
  vec_norm_eq_zero : ∀ x, vecNorm x = 0 ↔ x = 0
  vec_norm_add : ∀ x y,
    vecNorm (p08VecAdd x y) ≤ vecNorm x + vecNorm y
  vec_norm_scale : ∀ a x,
    vecNorm (p08VecScale a x) = |a| * vecNorm x
  vec_norm_absolute : ∀ x, vecNorm (p08AbsVec x) = vecNorm x
  vec_norm_monotone : ∀ x y,
    (∀ i, |x i| ≤ |y i|) → vecNorm x ≤ vecNorm y
  basis_normalized : ∀ j, vecNorm (p08BasisVector j) = 1
  matrix_norm_nonnegative : ∀ A, 0 ≤ matrixNorm A
  matrix_action_bound : ∀ A x,
    vecNorm (p08MatVec A x) ≤ matrixNorm A * vecNorm x
  matrix_norm_least : ∀ A c,
    0 ≤ c → (∀ x, vecNorm (p08MatVec A x) ≤ c * vecNorm x) →
      matrixNorm A ≤ c

/-- The paper's nonstandard `kappa(A^{-1}) = || |A| |A^{-1}| ||`. -/
noncomputable def p08KappaInverse {n : ℕ}
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n) : ℝ :=
  norm.matrixNorm (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))

/-- The scalar `c_3` from the Note following Lemma 4.1. -/
noncomputable def p08Lemma43c3 {n : ℕ}
    (run : P08IterativeRefinementRun n) : ℝ :=
  match run.precision with
  | .single =>
      (1 + run.u) * ((1 + run.u) ^ n - 1) / run.u ^ 2 - n / run.u
  | .double =>
      (1 + run.u) * (1 + run.u ^ 2) *
        ((1 + run.u ^ 2) ^ n - 1) / run.u ^ 2 - n

/-- The scalar `c_4` from the Note following Lemma 4.1. -/
def p08Lemma43c4 {n : ℕ} (run : P08IterativeRefinementRun n) : ℝ :=
  match run.precision with
  | .single => 0
  | .double => 1 + run.u

/-- Uniform envelopes for the anonymous scalar and matrix quantities.  The
functions are fixed across problem data and depend only on the dimension. -/
structure P08DimensionOnlyConstantBounds where
  scalar : ℕ → ℝ
  matrixEntry : ℕ → ℝ
  scalar_nonnegative : ∀ n, 0 ≤ scalar n
  matrixEntry_nonnegative : ∀ n, 0 ≤ matrixEntry n

/-- The source-defined matrices and resolvents used in Lemma 4.3. The exact
equalities mirror the Notes on printed pages 823, 826, and 827. -/
structure P08Lemma43Constants {n : ℕ}
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (dimensionBounds : P08DimensionOnlyConstantBounds) where
  C2 : Fin n → Fin n → ℝ
  C6 : Fin n → Fin n → ℝ
  C7 : Fin n → Fin n → ℝ
  C8 : Fin n → Fin n → ℝ
  C9 : Fin n → Fin n → ℝ
  C10 : Fin n → Fin n → ℝ
  C11 : Fin n → Fin n → ℝ
  C12 : Fin n → Fin n → ℝ
  c1 : ℝ
  c5 : ℝ
  c8 : ℝ
  C2ResolventInv : Fin n → Fin n → ℝ
  C11ResolventInv : Fin n → Fin n → ℝ
  c1_definition : c1 = norm.matrixNorm run.C1
  c5_definition : c5 =
    n + (p08Lemma43c3 run + p08Lemma43c4 run) * run.u ^ 2 /
      p08ResidualUnitRoundoff run.precision run.u
  C2_resolvent_left :
    p08MatMul
      (p08MatSub (p08IdMatrix n)
        (p08MatScale run.u
          (p08MatMul run.C1
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))))
      C2ResolventInv = p08IdMatrix n
  C2_resolvent_right :
    p08MatMul C2ResolventInv
      (p08MatSub (p08IdMatrix n)
        (p08MatScale run.u
          (p08MatMul run.C1
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))))) =
      p08IdMatrix n
  C2_definition : C2 = p08MatMul C2ResolventInv run.C1
  C6_definition : C6 =
    p08MatAdd C2
      (p08MatScale
        (1 + c5 * p08ResidualUnitRoundoff run.precision run.u / run.u)
        (p08MatAdd (p08IdMatrix n)
          (p08MatScale run.u
            (p08MatMul C2
              (p08MatMul (p08AbsMatrix run.A)
                (p08AbsMatrix run.Ainv))))))
  C7_definition : C7 =
    p08MatScale
      (n + p08Lemma43c3 run * run.u ^ 2 /
        p08ResidualUnitRoundoff run.precision run.u) C2
  C8_definition : C8 = p08MatScale (1 + run.u) C6
  c8_definition : c8 = norm.matrixNorm C8
  C9_definition : C9 =
    p08MatAdd C6 (p08MatScale (p08Lemma43c3 run) (p08IdMatrix n))
  C10_definition : C10 =
    p08MatAdd
      (p08MatAdd C6
        (p08MatScale
          (n * p08ResidualUnitRoundoff run.precision run.u / run.u +
            p08Lemma43c3 run * run.u)
          (p08IdMatrix n)))
      (p08MatScale (p08ResidualUnitRoundoff run.precision run.u)
        (p08MatMul C7
          (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))))
  C11_resolvent_left :
    p08MatMul
      (p08MatSub (p08IdMatrix n)
        (p08MatScale run.u
          (p08MatMul C8
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))))
      C11ResolventInv = p08IdMatrix n
  C11_resolvent_right :
    p08MatMul C11ResolventInv
      (p08MatSub (p08IdMatrix n)
        (p08MatScale run.u
          (p08MatMul C8
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))))) =
      p08IdMatrix n
  C11_definition : C11 = p08MatMul C11ResolventInv C9
  C12_definition : C12 =
    p08MatMul C11ResolventInv
      (p08MatAdd (p08MatScale n C8) C7)
  C11_fixed_point : C11 =
    p08MatAdd C9
      (p08MatMul
        (p08MatScale run.u
          (p08MatMul C8
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))))
        C11)
  C12_fixed_point : C12 =
    p08MatAdd (p08MatAdd (p08MatScale n C8) C7)
      (p08MatMul
        (p08MatScale run.u
          (p08MatMul C8
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))))
        C12)
  C2_nonnegative : p08MatNonnegative C2
  C6_nonnegative : p08MatNonnegative C6
  C7_nonnegative : p08MatNonnegative C7
  C8_nonnegative : p08MatNonnegative C8
  C9_nonnegative : p08MatNonnegative C9
  C10_nonnegative : p08MatNonnegative C10
  C11_nonnegative : p08MatNonnegative C11
  C12_nonnegative : p08MatNonnegative C12
  c1_nonnegative : 0 ≤ c1
  c8_nonnegative : 0 ≤ c8
  c1_le_c8 : c1 ≤ c8
  C1_dimension_bound : ∀ i j, run.C1 i j ≤ dimensionBounds.matrixEntry n
  C2_dimension_bound : ∀ i j, C2 i j ≤ dimensionBounds.matrixEntry n
  C6_dimension_bound : ∀ i j, C6 i j ≤ dimensionBounds.matrixEntry n
  C7_dimension_bound : ∀ i j, C7 i j ≤ dimensionBounds.matrixEntry n
  C8_dimension_bound : ∀ i j, C8 i j ≤ dimensionBounds.matrixEntry n
  C9_dimension_bound : ∀ i j, C9 i j ≤ dimensionBounds.matrixEntry n
  C10_dimension_bound : ∀ i j, C10 i j ≤ dimensionBounds.matrixEntry n
  C11_dimension_bound : ∀ i j, C11 i j ≤ dimensionBounds.matrixEntry n
  C12_dimension_bound : ∀ i j, C12 i j ≤ dimensionBounds.matrixEntry n
  c1_dimension_bound : c1 ≤ dimensionBounds.scalar n
  c5_dimension_bound : c5 ≤ dimensionBounds.scalar n
  c8_dimension_bound : c8 ≤ dimensionBounds.scalar n

/-- The propagation matrix `u C_8 |A| |A^{-1}|`. -/
noncomputable def p08Lemma43Propagation {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) :
    Fin n → Fin n → ℝ :=
  p08MatScale run.u
    (p08MatMul constants.C8
      (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))

/-- The first vector `u C_10 |A| |x|` in Lemma 4.3. -/
noncomputable def p08Lemma43InitialVector {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) : Fin n → ℝ :=
  p08VecScale run.u
    (p08MatVec (p08MatMul constants.C10 (p08AbsMatrix run.A))
      (p08AbsVec run.exactSolution))

/-- The forcing vector in the one-step recurrence displayed in the proof of
Lemma 4.3. -/
noncomputable def p08Lemma43RecurrenceForcing {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) : Fin n → ℝ :=
  let absA := p08AbsMatrix run.A
  let absAinv := p08AbsMatrix run.Ainv
  let absx := p08AbsVec run.exactSolution
  let ubar := p08ResidualUnitRoundoff run.precision run.u
  p08VecAdd
    (p08VecScale (n * ubar) (p08MatVec absA absx))
    (p08VecAdd
      (p08VecScale (run.u ^ 2)
        (p08MatVec (p08MatMul constants.C9 absA) absx))
      (p08VecScale (ubar * run.u)
        (p08MatVec
          (p08MatMul
            (p08MatMul constants.C7
              (p08MatMul absA absAinv)) absA) absx)))

/-- The three non-iteration terms in Lemma 4.3, retaining their exact orders
in `u` and the residual precision `ubar`. -/
noncomputable def p08Lemma43StationaryVector {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) : Fin n → ℝ :=
  let absA := p08AbsMatrix run.A
  let absAinv := p08AbsMatrix run.Ainv
  let absx := p08AbsVec run.exactSolution
  let ubar := p08ResidualUnitRoundoff run.precision run.u
  p08VecAdd
    (p08VecScale (n * ubar) (p08MatVec absA absx))
    (p08VecAdd
      (p08VecScale (run.u ^ 2)
        (p08MatVec (p08MatMul constants.C11 absA) absx))
      (p08VecScale (ubar * run.u)
        (p08MatVec
          (p08MatMul
            (p08MatMul constants.C12
              (p08MatMul absA absAinv)) absA) absx)))

/-- The exact four-term right-hand side of P08 Lemma 4.3. -/
noncomputable def p08Lemma43Bound {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (m : ℕ) : Fin n → ℝ :=
  p08VecAdd
    (p08MatVec (p08MatPow (p08Lemma43Propagation constants) m)
      (p08Lemma43InitialVector constants))
    (p08Lemma43StationaryVector constants)

/-- Local residual-accumulation and correction-solve errors used in the proofs
of Lemmas 4.1 and 4.2.  This records the two operation-level error relations;
it does not contain either lemma, the Lemma 4.3 recurrence, or its conclusion. -/
structure P08Lemma43RoundoffAnalysis {n : ℕ}
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (constants : P08Lemma43Constants run norm dimensionBounds) where
  residualError : ℕ → Fin n → ℝ
  residual_equation : ∀ m,
    run.computedResidual m =
      p08VecAdd
        (p08VecSub (p08MatVec run.A (run.iterate m)) run.b)
        (residualError m)
  residual_error_bound : ∀ m i,
    |residualError m i| ≤
      (n * p08ResidualUnitRoundoff run.precision run.u +
          p08Lemma43c3 run * run.u ^ 2) *
        p08MatVec (p08AbsMatrix run.A)
          (p08AbsVec run.exactSolution) i +
      constants.c5 * p08ResidualUnitRoundoff run.precision run.u *
        p08MatVec (p08AbsMatrix run.A)
          (p08AbsVec (p08VecSub (run.iterate m) run.exactSolution)) i +
      run.u *
        |p08MatVec run.A
          (p08VecSub (run.iterate m) run.exactSolution) i|
  correction_error_bound :
    constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2 →
      ∀ m i,
        |(run.correctionSolve m).backwardError i| ≤
          run.u * p08MatVec
            (p08MatMul constants.C2 (p08AbsMatrix run.A))
            (p08AbsVec
              (p08VecSub (run.iterate m) run.exactSolution)) i +
          run.u * p08MatVec
            (p08MatMul
              (p08MatMul constants.C2 (p08AbsMatrix run.A))
              (p08AbsMatrix run.Ainv))
            (p08AbsVec (residualError m)) i

end HighamBench
