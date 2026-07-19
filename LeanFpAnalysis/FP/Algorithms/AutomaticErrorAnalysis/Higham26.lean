/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Analysis.FloatingPointArithmetic
import Mathlib.Tactic.FieldSimp

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-! # Higham, Chapter 26: Automatic Error Analysis

The chapter is predominantly a survey of software and numerical experiments.
This file records its reusable exact core: direct-search specifications, the
printed stopping tests, the exact cubic identities, the residual objective, and
the elementary interval-arithmetic definitions.
-/

/-- Higham, 2nd ed., Section 26.1, p. 472, equation (26.1): a point is a
global maximizer of a real objective on the unconstrained search space. -/
def IsGlobalMax {α : Type*} (f : α → ℝ) (x : α) : Prop :=
  ∀ y, f y ≤ f x

/-- Optional global-optimality postcondition for equation (26.1), retained as
general vocabulary.  This is not an operational direct-search specification,
and no Chapter 26 algorithm assumes or produces this certificate. -/
def DirectSearchSpec {α : Type*} (search : (α → ℝ) → α) : Prop :=
  ∀ f, IsGlobalMax f (search f)

/-- Higham, 2nd ed., Section 26.2, p. 475, equation (26.2): the alternating-
directions relative-increase stopping test. -/
def adConverged (tol fPrev fNow : ℝ) : Prop :=
  fNow - fPrev ≤ tol * |fPrev|

/-- The finite-dimensional vector 1-norm used in equation (26.3). -/
noncomputable def vecOneNorm {n : ℕ} (x : RVec n) : ℝ :=
  ∑ i, |x i|

/-- Higham, 2nd ed., Section 26.2, p. 476, equation (26.3): relative size of
an MDS simplex.  The outer function norm is the maximum over the `n` non-base
vertices (and is zero in the vacuous zero-dimensional case). -/
noncomputable def mdsRelativeSize {n : ℕ} (v0 : RVec n)
    (v : Fin n → RVec n) : ℝ :=
  ‖fun i => vecOneNorm (fun j => v i j - v0 j)‖ / max 1 (vecOneNorm v0)

/-- Equation (26.3), exposed as the exact convergence predicate. -/
def mdsConverged {n : ℕ} (tol : ℝ) (v0 : RVec n)
    (v : Fin n → RVec n) : Prop :=
  mdsRelativeSize v0 v ≤ tol

/-! ### Multidirectional-search iteration (Section 26.2) -/

/-- An `n`-dimensional MDS simplex is stored as its distinguished vertex
`v₀` together with the other `n` vertices.  The source reorders these `n+1`
vertices after a successful trial so that `v₀` has maximal objective value. -/
structure MDSSimplex (n : ℕ) where
  base : RVec n
  other : Fin n → RVec n

namespace MDSSimplex

/-- All `n+1` vertices, with source vertex zero represented by `base`. -/
def point {n : ℕ} (s : MDSSimplex n) : Fin (n + 1) → RVec n :=
  Fin.cases s.base s.other

@[simp] theorem point_zero {n : ℕ} (s : MDSSimplex n) :
    s.point 0 = s.base := rfl

@[simp] theorem point_succ {n : ℕ} (s : MDSSimplex n) (i : Fin n) :
    s.point i.succ = s.other i := rfl

/-- The source ordering invariant `f(v₀) = maxᵢ f(vᵢ)`. -/
def OrderedFor {n : ℕ} (s : MDSSimplex n) (f : RVec n → ℝ) : Prop :=
  ∀ i, f (s.other i) ≤ f s.base

/-- A maximizing vertex of the finite family.  This is a deterministic
mathematical choice, not a hypothesis that the search finds a global maximizer
of the objective on `ℝⁿ`. -/
noncomputable def bestIndex {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) : Fin (n + 1) :=
  Classical.choose (Finite.exists_max (fun i : Fin (n + 1) => f (s.point i)))

theorem le_bestIndex {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) (i : Fin (n + 1)) :
    f (s.point i) ≤ f (s.point (bestIndex f s)) :=
  Classical.choose_spec
    (Finite.exists_max (fun i : Fin (n + 1) => f (s.point i))) i

/-- The maximum objective value among the `n+1` simplex vertices. -/
noncomputable def bestValue {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) : ℝ :=
  f (s.point (bestIndex f s))

theorem point_le_bestValue {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) (i : Fin (n + 1)) :
    f (s.point i) ≤ bestValue f s := by
  exact le_bestIndex f s i

/-- Reorder a simplex by swapping a maximizing vertex into position zero.
The remaining vertices are permuted by the same swap, so no vertex is added or
discarded. -/
noncomputable def reorderBest {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) : MDSSimplex n where
  base := s.point (bestIndex f s)
  other := fun i =>
    s.point ((Equiv.swap (0 : Fin (n + 1)) (bestIndex f s)) i.succ)

theorem reorderBest_orderedFor {n : ℕ} (f : RVec n → ℝ)
    (s : MDSSimplex n) : (reorderBest f s).OrderedFor f := by
  intro i
  exact le_bestIndex f s
    ((Equiv.swap (0 : Fin (n + 1)) (bestIndex f s)) i.succ)

/-- Reflection of every non-base vertex through `v₀`:
`rᵢ = v₀ + (v₀-vᵢ) = 2v₀-vᵢ`. -/
def reflect {n : ℕ} (s : MDSSimplex n) : MDSSimplex n where
  base := s.base
  other := fun i j => s.base j + (s.base j - s.other i j)

/-- Expansion doubles each reflected edge from `v₀`:
`eᵢ = v₀ + 2(v₀-vᵢ)`. -/
def expand {n : ℕ} (s : MDSSimplex n) : MDSSimplex n where
  base := s.base
  other := fun i j => s.base j + 2 * (s.base j - s.other i j)

/-- Contraction halves every edge incident on `v₀`:
`cᵢ = v₀ + (vᵢ-v₀)/2`. -/
noncomputable def contract {n : ℕ} (s : MDSSimplex n) : MDSSimplex n where
  base := s.base
  other := fun i j => s.base j + (s.other i j - s.base j) / 2

@[simp] theorem reflect_base {n : ℕ} (s : MDSSimplex n) :
    s.reflect.base = s.base := rfl

@[simp] theorem reflect_other {n : ℕ} (s : MDSSimplex n)
    (i : Fin n) (j : Fin n) :
    s.reflect.other i j = s.base j + (s.base j - s.other i j) := rfl

@[simp] theorem expand_base {n : ℕ} (s : MDSSimplex n) :
    s.expand.base = s.base := rfl

@[simp] theorem expand_other {n : ℕ} (s : MDSSimplex n)
    (i : Fin n) (j : Fin n) :
    s.expand.other i j = s.base j + 2 * (s.base j - s.other i j) := rfl

@[simp] theorem contract_base {n : ℕ} (s : MDSSimplex n) :
    s.contract.base = s.base := rfl

@[simp] theorem contract_other {n : ℕ} (s : MDSSimplex n)
    (i : Fin n) (j : Fin n) :
    s.contract.other i j = s.base j + (s.other i j - s.base j) / 2 := rfl

private noncomputable def iterationOrdered {n : ℕ} :
    ℕ → (RVec n → ℝ) → MDSSimplex n → Option (MDSSimplex n)
  | 0, _f, _current => none
  | fuel + 1, f, current =>
      let reflected := current.reflect
      if bestValue f reflected > f current.base then
        let expanded := current.expand
        if bestValue f expanded > bestValue f reflected then
          some (reorderBest f expanded)
        else
          some (reorderBest f reflected)
      else
        let contracted := current.contract
        if bestValue f contracted > bestValue f current then
          some (reorderBest f contracted)
        else
          iterationOrdered fuel f contracted

/-- Higham, 2nd ed., Section 26.2, pp. 475-476: one multidirectional-search
iteration with at most `fuel` contraction retries.

The input is first reordered so that `v₀` is a best current vertex.  A
successful reflection is expanded when the expanded simplex has the larger
maximum; otherwise the reflected simplex is accepted.  An unsuccessful
reflection contracts the simplex.  A contraction improving on the current
simplex is accepted, while a non-improving contraction restarts the reflection
test about the same `v₀`, with one less unit of fuel.  `none` records that this
finite observation budget did not witness completion of the iteration; it
makes no termination or optimization-correctness assumption. -/
noncomputable def iteration {n : ℕ} (fuel : ℕ) (f : RVec n → ℝ)
    (input : MDSSimplex n) : Option (MDSSimplex n) :=
  iterationOrdered fuel f (reorderBest f input)

/-- Relational, unbounded specification of a completed MDS iteration: some
finite number of contraction retries reaches one of the source's accepted
reflection, expansion, or contraction branches. -/
def IterationSpec {n : ℕ} (f : RVec n → ℝ)
    (input output : MDSSimplex n) : Prop :=
  ∃ fuel, iteration fuel f input = some output

/-- The source stopping test (26.3), specialized to an MDS simplex. -/
def Converged {n : ℕ} (tol : ℝ) (s : MDSSimplex n) : Prop :=
  mdsConverged tol s.base s.other

/-- General finite execution semantics for the MDS method: stop exactly when
the printed test (26.3) holds; otherwise complete one reflection/expansion/
contraction iteration and continue.  This trace records algorithm control flow
only.  In particular it assumes neither existence of a maximizer nor
stationarity, convergence, or global correctness of the returned simplex. -/
inductive SearchTrace {n : ℕ} (tol : ℝ) (f : RVec n → ℝ) :
    MDSSimplex n → MDSSimplex n → Prop where
  | stop (s : MDSSimplex n) (hconverged : s.Converged tol) :
      SearchTrace tol f s s
  | next {s nextState output : MDSSimplex n}
      (hnotConverged : ¬ s.Converged tol)
      (hiteration : IterationSpec f s nextState)
      (htail : SearchTrace tol f nextState output) :
      SearchTrace tol f s output

end MDSSimplex

/-- Higham, 2nd ed., Section 26.3.2, p. 478, equation (26.4): the normalized
minimum of the left and right inverse residuals, in the repository's exact
maximum-row-sum matrix norm. -/
noncomputable def inverseResidualStabilityMeasure {n : ℕ}
    (A X : Fin n → Fin n → ℝ) : ℝ :=
  let leftResidual := fun i j => matMul n A X i j - idMatrix n i j
  let rightResidual := fun i j => matMul n X A i j - idMatrix n i j
  min (infNorm leftResidual) (infNorm rightResidual) /
    (infNorm A * infNorm X)

/-- The depressed-cubic coefficient `p` from Section 26.3.3. -/
noncomputable def depressedCubicP (a b : ℝ) : ℝ :=
  -(a ^ 2) / 3 + b

/-- The depressed-cubic coefficient `q` from Section 26.3.3. -/
noncomputable def depressedCubicQ (a b c : ℝ) : ℝ :=
  2 * a ^ 3 / 27 - a * b / 3 + c

/-- The change of variable `x = y - a/3` exactly removes the quadratic term. -/
theorem depressedCubic_identity (a b c y : ℝ) :
    (y - a / 3) ^ 3 + a * (y - a / 3) ^ 2 + b * (y - a / 3) + c =
      y ^ 3 + depressedCubicP a b * y + depressedCubicQ a b c := by
  unfold depressedCubicP depressedCubicQ
  ring

/-- The radicand in the quadratic equation for `w^3`. -/
noncomputable def cubicRadicand (p q : ℝ) : ℝ :=
  q ^ 2 / 4 + p ^ 3 / 27

/-- Higham, 2nd ed., Section 26.3.3, p. 479, equation (26.5), plus branch. -/
noncomputable def cubicWCubePlus (p q : ℝ) : ℝ :=
  -q / 2 + Real.sqrt (cubicRadicand p q)

/-- Higham, 2nd ed., Section 26.3.3, p. 479, equation (26.5), minus branch. -/
noncomputable def cubicWCubeMinus (p q : ℝ) : ℝ :=
  -q / 2 - Real.sqrt (cubicRadicand p q)

/-- Each real branch in equation (26.5) solves the quadratic equation for
`w^3`, whenever the printed square root has a nonnegative radicand. -/
theorem cubicWCubePlus_quadratic (p q : ℝ) (h : 0 ≤ cubicRadicand p q) :
    cubicWCubePlus p q ^ 2 + q * cubicWCubePlus p q - p ^ 3 / 27 = 0 := by
  have hsqrt : (Real.sqrt (cubicRadicand p q)) ^ 2 = cubicRadicand p q :=
    Real.sq_sqrt h
  unfold cubicWCubePlus cubicRadicand at *
  nlinarith

/-- The minus branch of equation (26.5) satisfies the same quadratic. -/
theorem cubicWCubeMinus_quadratic (p q : ℝ) (h : 0 ≤ cubicRadicand p q) :
    cubicWCubeMinus p q ^ 2 + q * cubicWCubeMinus p q - p ^ 3 / 27 = 0 := by
  have hsqrt : (Real.sqrt (cubicRadicand p q)) ^ 2 = cubicRadicand p q :=
    Real.sq_sqrt h
  unfold cubicWCubeMinus cubicRadicand at *
  nlinarith

/-- A nonzero-at-zero sign convention, as required by the stable quadratic
choice in equation (26.6): zero is assigned sign `+1`. -/
noncomputable def stableSign (q : ℝ) : ℝ :=
  if 0 ≤ q then 1 else -1

/-- Higham, 2nd ed., Section 26.3.3, p. 480, equation (26.6): the branch that
avoids cancellation in the real subtraction. -/
noncomputable def stableCubicWCube (p q : ℝ) : ℝ :=
  -q / 2 - stableSign q * Real.sqrt (cubicRadicand p q)

/-- Equation (26.6) is one of the two exact branches in (26.5). -/
theorem stableCubicWCube_eq_branch (p q : ℝ) :
    stableCubicWCube p q =
      if 0 ≤ q then cubicWCubeMinus p q else cubicWCubePlus p q := by
  by_cases hq : 0 ≤ q <;>
    simp [stableCubicWCube, stableSign, cubicWCubeMinus, cubicWCubePlus, hq]

/-- Consequently, the stable branch in (26.6) solves the quadratic for `w^3`
when its radicand is nonnegative. -/
theorem stableCubicWCube_quadratic (p q : ℝ) (h : 0 ≤ cubicRadicand p q) :
    stableCubicWCube p q ^ 2 + q * stableCubicWCube p q - p ^ 3 / 27 = 0 := by
  rw [stableCubicWCube_eq_branch]
  split_ifs
  · exact cubicWCubeMinus_quadratic p q h
  · exact cubicWCubePlus_quadratic p q h

/-- The monic cubic used in the residual objective (26.7). -/
def monicCubic (a b c : ℝ) (z : ℂ) : ℂ :=
  z ^ 3 + a * z ^ 2 + b * z + c

/-- Higham, 2nd ed., Section 26.3.3, p. 481, equation (26.7): normalized
backward-residual objective for three computed roots. -/
noncomputable def cubicRootResidualMeasure (a b c : ℝ) (z : Fin 3 → ℂ) : ℝ :=
  ‖fun i =>
    ‖monicCubic a b c (z i)‖ /
      (max (max (max |a| |b|) |c|) 1 *
        (∑ j : Fin 4, ‖z i ^ (j : ℕ)‖))‖

/-! ## Exact interval arithmetic from Section 26.4 -/

/-- A nonempty closed real interval, represented by ordered endpoints. -/
structure RealInterval where
  lower : ℝ
  upper : ℝ
  ordered : lower ≤ upper

namespace RealInterval

/-- Membership in a closed real interval. -/
def Contains (x : RealInterval) (a : ℝ) : Prop :=
  x.lower ≤ a ∧ a ≤ x.upper

/-- Higham, 2nd ed., Section 26.4, p. 481: interval width. -/
def width (x : RealInterval) : ℝ :=
  x.upper - x.lower

theorem width_nonneg (x : RealInterval) : 0 ≤ x.width := by
  exact sub_nonneg.mpr x.ordered

/-- Exact endpoint formula for interval addition. -/
def add (x y : RealInterval) : RealInterval where
  lower := x.lower + y.lower
  upper := x.upper + y.upper
  ordered := add_le_add x.ordered y.ordered

/-- Exact endpoint formula for interval subtraction. -/
def sub (x y : RealInterval) : RealInterval where
  lower := x.lower - y.upper
  upper := x.upper - y.lower
  ordered := sub_le_sub x.ordered y.ordered

/-- Exact endpoint formula for interval multiplication. -/
def mul (x y : RealInterval) : RealInterval where
  lower := min (min (x.lower * y.lower) (x.lower * y.upper))
    (min (x.upper * y.lower) (x.upper * y.upper))
  upper := max (max (x.lower * y.lower) (x.lower * y.upper))
    (max (x.upper * y.lower) (x.upper * y.upper))
  ordered := by
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))

/-- Reciprocal endpoint hull.  Under the source side condition that zero is
not in the interval, this is the printed interval `[1/upper, 1/lower]`. -/
noncomputable def reciprocal (x : RealInterval) : RealInterval where
  lower := min (1 / x.upper) (1 / x.lower)
  upper := max (1 / x.upper) (1 / x.lower)
  ordered := min_le_max

/-- Exact interval-division construction from Section 26.4.  The explicit
side condition rules out the source's division-by-zero breakdown. -/
noncomputable def div (x y : RealInterval) (_hzero : ¬ y.Contains 0) : RealInterval :=
  x.mul y.reciprocal

/-- Addition soundness for the set interpretation of intervals. -/
theorem add_contains {x y : RealInterval} {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.add y).Contains (a + b) := by
  exact ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩

/-- Subtraction soundness for the set interpretation of intervals. -/
theorem sub_contains {x y : RealInterval} {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.sub y).Contains (a - b) := by
  exact ⟨sub_le_sub ha.1 hb.2, sub_le_sub ha.2 hb.1⟩

/-- Multiplication by a fixed real sends an interval to the hull of its two
endpoint products. -/
private theorem fixed_mul_endpoint_bounds (k : ℝ) {y : RealInterval} {b : ℝ}
    (hb : y.Contains b) :
    min (k * y.lower) (k * y.upper) ≤ k * b ∧
      k * b ≤ max (k * y.lower) (k * y.upper) := by
  by_cases hk : 0 ≤ k
  · exact
      ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hb.1 hk),
        le_trans (mul_le_mul_of_nonneg_left hb.2 hk) (le_max_right _ _)⟩
  · have hk' : k ≤ 0 := le_of_not_ge hk
    exact
      ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hb.2 hk'),
        le_trans (mul_le_mul_of_nonpos_left hb.1 hk') (le_max_left _ _)⟩

/-- Multiplication soundness for the set interpretation of the four-corner
endpoint formula in Section 26.4. -/
theorem mul_contains {x y : RealInterval} {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.mul y).Contains (a * b) := by
  have hLower := fixed_mul_endpoint_bounds x.lower hb
  have hUpper := fixed_mul_endpoint_bounds x.upper hb
  by_cases hb0 : 0 ≤ b
  · constructor
    · exact le_trans (min_le_left _ _)
        (le_trans hLower.1 (mul_le_mul_of_nonneg_right ha.1 hb0))
    · exact le_trans (mul_le_mul_of_nonneg_right ha.2 hb0)
        (le_trans hUpper.2 (le_max_right _ _))
  · have hb0' : b ≤ 0 := le_of_not_ge hb0
    constructor
    · exact le_trans (min_le_right _ _)
        (le_trans hUpper.1 (mul_le_mul_of_nonpos_right ha.2 hb0'))
    · exact le_trans (mul_le_mul_of_nonpos_right ha.1 hb0')
        (le_trans hLower.2 (le_max_left _ _))

/-- Reciprocal soundness under the source side condition that zero is not in
the denominator interval. -/
theorem reciprocal_contains {x : RealInterval} {a : ℝ}
    (hzero : ¬ x.Contains 0) (ha : x.Contains a) :
    x.reciprocal.Contains (1 / a) := by
  have hside : x.upper < 0 ∨ 0 < x.lower := by
    by_contra h
    push_neg at h
    exact hzero ⟨h.2, h.1⟩
  rcases hside with hneg | hpos
  · have haNeg : a < 0 := lt_of_le_of_lt ha.2 hneg
    constructor
    · exact le_trans (min_le_left _ _)
        (one_div_le_one_div_of_neg_of_le hneg ha.2)
    · exact le_trans (one_div_le_one_div_of_neg_of_le haNeg ha.1)
        (le_max_right _ _)
  · have haPos : 0 < a := lt_of_lt_of_le hpos ha.1
    constructor
    · exact le_trans (min_le_left _ _)
        (one_div_le_one_div_of_le haPos ha.2)
    · exact le_trans (one_div_le_one_div_of_le hpos ha.1)
        (le_max_right _ _)

/-- Division soundness follows from multiplication and reciprocal soundness. -/
theorem div_contains {x y : RealInterval} {a b : ℝ}
    (hzero : ¬ y.Contains 0) (ha : x.Contains a) (hb : y.Contains b) :
    (x.div y hzero).Contains (a / b) := by
  simpa [div_eq_mul_inv, div] using
    mul_contains ha (reciprocal_contains hzero hb)

/-- The multiplication endpoints are exactly the four-corner formula printed
in Section 26.4. -/
theorem mul_endpoints (x y : RealInterval) :
    (x.mul y).lower =
        min (min (x.lower * y.lower) (x.lower * y.upper))
          (min (x.upper * y.lower) (x.upper * y.upper)) ∧
      (x.mul y).upper =
        max (max (x.lower * y.lower) (x.lower * y.upper))
          (max (x.upper * y.lower) (x.upper * y.upper)) := by
  exact ⟨rfl, rfl⟩

/-- Reusing the same uncertain interval twice can widen a subtraction: for
`[1,2]`, the interval result is exactly `[-1,1]`, as in Section 26.4. -/
theorem dependency_sub_example :
    let x : RealInterval := ⟨1, 2, by norm_num⟩
    (x.sub x).lower = -1 ∧ (x.sub x).upper = 1 := by
  change (1 - 2 : ℝ) = -1 ∧ (2 - 1 : ℝ) = 1
  norm_num

/-- Reusing the same uncertain interval twice also widens division: for
`[1,2]`, the interval result is exactly `[1/2,2]`, rather than the point
interval `[1,1]`, as stated in Section 26.4. -/
theorem dependency_div_example :
    let x : RealInterval := ⟨1, 2, by norm_num⟩
    let hzero : ¬ x.Contains 0 := by
      norm_num [Contains]
    (x.div x hzero).lower = 1 / 2 ∧
      (x.div x hzero).upper = 2 := by
  norm_num [div, mul, reciprocal]
  change
    min (min ((1 : ℝ) / 2) 1) (2 * min ((1 : ℝ) / 2) 1) = (1 : ℝ) / 2 ∧
      max ((1 : ℝ) / 2) 1 = 1
  norm_num [min_def, max_def]
  intro hbad
  exact (not_lt_of_ge (by norm_num : (1 / 2 : ℝ) ≤ 1) hbad).elim

/-! ### Concrete outward-directed floating-point endpoint production -/

/-- The real-valued finite rounding layer can enclose an endpoint whenever it
is in either the gradual-underflow range or the finite normal range.  Values in
the IEEE overflow range require the separate infinity-valued result layer. -/
def EndpointInFiniteRange (fmt : FloatingPointFormat) (a : ℝ) : Prop :=
  fmt.finiteUnderflowRange a ∨ fmt.finiteNormalRange a

theorem finiteRoundTowardNegative_le_of_endpointRange
    (fmt : FloatingPointFormat) {a : ℝ} (ha : EndpointInFiniteRange fmt a) :
    fmt.finiteRoundTowardNegative a ≤ a := by
  rcases ha with ha | ha
  · exact fmt.finiteRoundTowardNegative_le_of_finiteUnderflowRange ha
  · exact fmt.finiteRoundTowardNegative_le_of_finiteNormalRange ha

theorem le_finiteRoundTowardPositive_of_endpointRange
    (fmt : FloatingPointFormat) {a : ℝ} (ha : EndpointInFiniteRange fmt a) :
    a ≤ fmt.finiteRoundTowardPositive a := by
  rcases ha with ha | ha
  · exact fmt.le_finiteRoundTowardPositive_of_finiteUnderflowRange ha
  · exact fmt.le_finiteRoundTowardPositive_of_finiteNormalRange ha

/-- Page 481's computed producer at the finite-real layer: round the exact left
endpoint toward negative infinity and the exact right endpoint toward positive
infinity.  The range evidence is exactly what makes both rounded endpoints
finite reals instead of IEEE infinities. -/
noncomputable def outwardRounded
    (fmt : FloatingPointFormat) (x : RealInterval)
    (hlower : EndpointInFiniteRange fmt x.lower)
    (hupper : EndpointInFiniteRange fmt x.upper) : RealInterval where
  lower := fmt.finiteRoundTowardNegative x.lower
  upper := fmt.finiteRoundTowardPositive x.upper
  ordered :=
    (finiteRoundTowardNegative_le_of_endpointRange fmt hlower).trans
      (x.ordered.trans (le_finiteRoundTowardPositive_of_endpointRange fmt hupper))

/-- The outward-directed computed interval contains every real already
contained by the exact endpoint interval. -/
theorem outwardRounded_contains
    (fmt : FloatingPointFormat) (x : RealInterval)
    (hlower : EndpointInFiniteRange fmt x.lower)
    (hupper : EndpointInFiniteRange fmt x.upper) {a : ℝ}
    (ha : x.Contains a) :
    (outwardRounded fmt x hlower hupper).Contains a := by
  exact
    ⟨(finiteRoundTowardNegative_le_of_endpointRange fmt hlower).trans ha.1,
      ha.2.trans (le_finiteRoundTowardPositive_of_endpointRange fmt hupper)⟩

/-- Concrete computed interval addition from page 481. -/
noncomputable def outwardAdd (fmt : FloatingPointFormat) (x y : RealInterval)
    (hlower : EndpointInFiniteRange fmt (x.add y).lower)
    (hupper : EndpointInFiniteRange fmt (x.add y).upper) : RealInterval :=
  outwardRounded fmt (x.add y) hlower hupper

theorem outwardAdd_contains (fmt : FloatingPointFormat) {x y : RealInterval}
    (hlower : EndpointInFiniteRange fmt (x.add y).lower)
    (hupper : EndpointInFiniteRange fmt (x.add y).upper) {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (outwardAdd fmt x y hlower hupper).Contains (a + b) :=
  outwardRounded_contains fmt (x.add y) hlower hupper (add_contains ha hb)

/-- Concrete computed interval subtraction from page 481. -/
noncomputable def outwardSub (fmt : FloatingPointFormat) (x y : RealInterval)
    (hlower : EndpointInFiniteRange fmt (x.sub y).lower)
    (hupper : EndpointInFiniteRange fmt (x.sub y).upper) : RealInterval :=
  outwardRounded fmt (x.sub y) hlower hupper

theorem outwardSub_contains (fmt : FloatingPointFormat) {x y : RealInterval}
    (hlower : EndpointInFiniteRange fmt (x.sub y).lower)
    (hupper : EndpointInFiniteRange fmt (x.sub y).upper) {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (outwardSub fmt x y hlower hupper).Contains (a - b) :=
  outwardRounded_contains fmt (x.sub y) hlower hupper (sub_contains ha hb)

/-- Concrete computed interval multiplication from page 481. -/
noncomputable def outwardMul (fmt : FloatingPointFormat) (x y : RealInterval)
    (hlower : EndpointInFiniteRange fmt (x.mul y).lower)
    (hupper : EndpointInFiniteRange fmt (x.mul y).upper) : RealInterval :=
  outwardRounded fmt (x.mul y) hlower hupper

theorem outwardMul_contains (fmt : FloatingPointFormat) {x y : RealInterval}
    (hlower : EndpointInFiniteRange fmt (x.mul y).lower)
    (hupper : EndpointInFiniteRange fmt (x.mul y).upper) {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (outwardMul fmt x y hlower hupper).Contains (a * b) :=
  outwardRounded_contains fmt (x.mul y) hlower hupper (mul_contains ha hb)

/-- Concrete computed interval division from page 481. -/
noncomputable def outwardDiv (fmt : FloatingPointFormat) (x y : RealInterval)
    (hzero : ¬ y.Contains 0)
    (hlower : EndpointInFiniteRange fmt (x.div y hzero).lower)
    (hupper : EndpointInFiniteRange fmt (x.div y hzero).upper) : RealInterval :=
  outwardRounded fmt (x.div y hzero) hlower hupper

theorem outwardDiv_contains (fmt : FloatingPointFormat) {x y : RealInterval}
    (hzero : ¬ y.Contains 0)
    (hlower : EndpointInFiniteRange fmt (x.div y hzero).lower)
    (hupper : EndpointInFiniteRange fmt (x.div y hzero).upper) {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (outwardDiv fmt x y hzero hlower hupper).Contains (a / b) :=
  outwardRounded_contains fmt (x.div y hzero) hlower hupper
    (div_contains hzero ha hb)

end RealInterval

end LeanFpAnalysis.FP
