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

end HighamBench
