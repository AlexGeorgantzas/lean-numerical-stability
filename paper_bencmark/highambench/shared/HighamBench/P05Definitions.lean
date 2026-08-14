import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- The finite square matrix product used in P05's LU and Cholesky bounds. -/
noncomputable def p05MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- Matrix transpose in P05's finite-index notation. -/
noncomputable def p05Transpose {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A j i

/-- The componentwise absolute product `|A||B|` used by both factorization
backward-error bounds in P05. -/
noncomputable def p05AbsMatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, |A i k| * |B k j|

/-- A finite radix format interface sufficient to state P05 Lemma 4.1's
round-to-nearest execution. `safeRange` excludes underflow and overflow for an
exact operation result. -/
structure P05FiniteRoundToNearestFormat where
  radix : ℕ
  precision : ℕ
  minExponent : ℤ
  maxExponent : ℤ
  radix_ge_two : 2 ≤ radix
  precision_pos : 0 < precision
  exponent_range_nonempty : minExponent < maxExponent
  representable : ℝ → Prop
  representable_finite : Set.Finite {x | representable x}
  safeRange : ℝ → Prop
  round : ℝ → ℝ
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  unitRoundoff_scale :
    unitRoundoff * (2 * (radix : ℝ) ^ (precision - 1)) = 1
  zero_representable : representable 0
  one_representable : representable 1
  round_representable : ∀ x, safeRange x → representable (round x)
  round_nearest : ∀ x, safeRange x → ∀ z, representable z →
    |x - round x| ≤ |x - z|
  round_exact : ∀ x, representable x → round x = x

/-- A binary tree encoding an arbitrary pairwise evaluation order for a
nonempty finite sum. -/
inductive P05SumTree : ℕ → Type
  | leaf : P05SumTree 1
  | node {m n : ℕ} : P05SumTree m → P05SumTree n → P05SumTree (m + n)

/-- Evaluation of a P05 summation tree, rounding at every internal addition. -/
noncomputable def p05SumTreeEval
    (fmt : P05FiniteRoundToNearestFormat) {n : ℕ}
    (tree : P05SumTree n) (v : Fin n → ℝ) : ℝ :=
  match tree with
  | .leaf => v ⟨0, by norm_num⟩
  | .node left right =>
      fmt.round
        (p05SumTreeEval fmt left (fun i => v (Fin.castAdd _ i)) +
          p05SumTreeEval fmt right (fun i => v (Fin.natAdd _ i)))

/-- Every exact internal addition in a tree lies in the format's range, which
is the paper's no-underflow/no-overflow requirement for summation. -/
def p05SumTreeSafe
    (fmt : P05FiniteRoundToNearestFormat) {n : ℕ}
    (tree : P05SumTree n) (v : Fin n → ℝ) : Prop :=
  match tree with
  | .leaf => fmt.representable (v ⟨0, by norm_num⟩)
  | .node left right =>
      p05SumTreeSafe fmt left (fun i => v (Fin.castAdd _ i)) ∧
      p05SumTreeSafe fmt right (fun i => v (Fin.natAdd _ i)) ∧
      fmt.safeRange
        (p05SumTreeEval fmt left (fun i => v (Fin.castAdd _ i)) +
          p05SumTreeEval fmt right (fun i => v (Fin.natAdd _ i)))

/-- Rounded products appearing in the computed numerator of P05 Lemma 4.1. -/
noncomputable def p05RoundedProducts {m : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (a b : Fin m → ℝ) : Fin m → ℝ :=
  fun i => fmt.round (a i * b i)

/-- The summands `c,-fl(a₁b₁),...,-fl(aₘbₘ)` supplied to an
arbitrary summation tree in P05 Lemma 4.1, where the paper's `k=m+1`. -/
noncomputable def p05Lemma41Summands {m : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (a b : Fin m → ℝ) (c : ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases c (fun i => -p05RoundedProducts fmt a b i)

/-- The two perturbable source families in Lemma 4.1. The protected input `c`
is deliberately absent. -/
noncomputable def p05BackwardSource {m : ℕ}
    (computedProduct : ℝ) (products : Fin m → ℝ) :
    Option (Fin m) → ℝ
  | none => computedProduct
  | some i => products i

/-- A complete finite execution certificate for P05 Lemma 4.1. The tree and
permutation encode every permitted summation order. Product, addition, and
division range fields state the absence of underflow and overflow. The two
residual fields are exactly the consequences of Theorem 3.1 and Corollary 3.2
used by the paper to construct Lemma 4.1's coefficients; neither field contains
those coefficients or the target conclusion. -/
structure P05Lemma41Run (m : ℕ) where
  format : P05FiniteRoundToNearestFormat
  a : Fin m → ℝ
  b : Fin m → ℝ
  bK : ℝ
  c : ℝ
  a_representable : ∀ i, format.representable (a i)
  b_representable : ∀ i, format.representable (b i)
  bK_representable : format.representable bK
  c_representable : format.representable c
  bK_nonzero : bK ≠ 0
  product_safe : ∀ i, format.safeRange (a i * b i)
  tree : P05SumTree (m + 1)
  order : Equiv.Perm (Fin (m + 1))
  tree_safe : p05SumTreeSafe format tree
    (fun i => p05Lemma41Summands format a b c (order i))
  numerator : ℝ
  numerator_eq : numerator = p05SumTreeEval format tree
    (fun i => p05Lemma41Summands format a b c (order i))
  yHat : ℝ
  no_division_when_unit : bK = 1 → yHat = numerator
  division_safe : bK ≠ 1 → format.safeRange (numerator / bK)
  rounded_division : bK ≠ 1 → yHat = format.round (numerator / bK)
  general_residual_bound :
    |(c - ∑ i : Fin m, a i * b i) - bK * yHat| ≤
      ((m + 1 : ℕ) : ℝ) * format.unitRoundoff *
        (|bK * yHat| + ∑ i : Fin m, |a i * b i|)
  unit_residual_bound : bK = 1 →
    |(c - ∑ i : Fin m, a i * b i) - yHat| ≤
      (m : ℝ) * format.unitRoundoff *
        (|yHat| + ∑ i : Fin m, |a i * b i|)

/-- Exact rectangular matrix multiplication for P05 Theorem 4.2. -/
noncomputable def p05RectMatMul {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, L i k * U k j

/-- The componentwise absolute product `|L_hat||U_hat|` in Theorem 4.2. -/
noncomputable def p05RectAbsMatMul {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, |L i k| * |U k j|

/-- Embed a Doolittle pivot-row index into the rectangular row index. -/
def p05RectRow {m n : ℕ} (hmn : n ≤ m) (k : Fin n) : Fin m :=
  Fin.castLE hmn k

/-- Embed an index strictly preceding Doolittle stage `k` into `Fin n`. -/
def p05PrefixIndex {n : ℕ} (k : Fin n) (s : Fin k.val) : Fin n :=
  ⟨s.val, lt_trans s.isLt k.isLt⟩

/-- The exact dot product over entries strictly preceding Doolittle stage `k`. -/
noncomputable def p05DoolittlePrefixDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) : ℝ :=
  ∑ s : Fin k.val, L i (p05PrefixIndex k s) * U (p05PrefixIndex k s) j

/-- The corresponding absolute-value prefix dot product. -/
noncomputable def p05DoolittlePrefixAbsDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) : ℝ :=
  ∑ s : Fin k.val,
    |L i (p05PrefixIndex k s)| * |U (p05PrefixIndex k s) j|

/-- The exact local product through stage `k`, matching the sums in (4.3). -/
noncomputable def p05DoolittleThroughPivotDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) : ℝ :=
  p05DoolittlePrefixDot L U i j k + L i k * U k j

/-- The absolute local product through stage `k`, matching the right sides of
equations (4.3a) and (4.3b). -/
noncomputable def p05DoolittleThroughPivotAbsDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) : ℝ :=
  p05DoolittlePrefixAbsDot L U i j k + |L i k| * |U k j|

/-- One completed upper-row Doolittle evaluation at stage `k`. The nested
Lemma 4.1 run computes `U_hat[k,j]` from the protected input `A[k,j]`, the
already computed prefix products, and unit denominator. -/
structure P05DoolittleUpperEntry {m n : ℕ}
    (fmt : P05FiniteRoundToNearestFormat) (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) where
  execution : P05Lemma41Run k.val
  format_eq : execution.format = fmt
  left_input_eq : ∀ s,
    execution.a s = L (p05RectRow hmn k) (p05PrefixIndex k s)
  right_input_eq : ∀ s,
    execution.b s = U (p05PrefixIndex k s) j
  denominator_eq : execution.bK = 1
  protected_input_eq : execution.c = A (p05RectRow hmn k) j
  computed_output_eq : execution.yHat = U k j

/-- One completed below-diagonal Doolittle evaluation at stage `k`. The nested
Lemma 4.1 run computes `L_hat[i,k]` after division by the computed pivot
`U_hat[k,k]`. -/
structure P05DoolittleLowerEntry {m n : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) where
  execution : P05Lemma41Run k.val
  format_eq : execution.format = fmt
  left_input_eq : ∀ s,
    execution.a s = L i (p05PrefixIndex k s)
  right_input_eq : ∀ s,
    execution.b s = U (p05PrefixIndex k s) k
  denominator_eq : execution.bK = U k k
  protected_input_eq : execution.c = A i k
  computed_output_eq : execution.yHat = L i k

/-- A completed rectangular floating-point Doolittle run used in the proof of
P05 Theorem 4.2. Every stored upper and lower entry has its own arbitrary-order,
range-certified Lemma 4.1 execution. Thus completion, round-to-nearest
arithmetic, and the absence of underflow and overflow are explicit without
storing a Doolittle-specific local estimate or the final matrix bound. -/
structure P05DoolittleRun (m n : ℕ) where
  format : P05FiniteRoundToNearestFormat
  rows_ge_columns : n ≤ m
  columns_pos : 0 < n
  A : Fin m → Fin n → ℝ
  LHat : Fin m → Fin n → ℝ
  UHat : Fin n → Fin n → ℝ
  A_representable : ∀ i j, format.representable (A i j)
  LHat_representable : ∀ i j, format.representable (LHat i j)
  UHat_representable : ∀ i j, format.representable (UHat i j)
  LHat_diag : ∀ k : Fin n, LHat (p05RectRow rows_ge_columns k) k = 1
  LHat_upper_zero : ∀ i j, i.val < j.val → LHat i j = 0
  UHat_lower_zero : ∀ i j, j.val < i.val → UHat i j = 0
  upper_entry : ∀ k j, k.val ≤ j.val →
    P05DoolittleUpperEntry format rows_ge_columns A LHat UHat k j
  lower_entry : ∀ i k, k.val < i.val →
    P05DoolittleLowerEntry format A LHat UHat i k

end HighamBench
