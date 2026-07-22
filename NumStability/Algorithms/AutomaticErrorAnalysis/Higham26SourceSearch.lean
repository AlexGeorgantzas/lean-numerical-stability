/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NumStability.Algorithms.AutomaticErrorAnalysis.Higham26

namespace NumStability

open scoped BigOperators

/-! # Higham Chapter 26: literal direct-search producers

This module supplements the abstract exact-line-search interface in
`Higham26.lean` with the finite crude line search actually described on
p. 475.  It also constructs the right-angled initial MDS simplex from p. 476.
-/

/-- Higham, 2nd ed., p. 475: the first alternating-directions trial step,
`10⁻⁴ xᵢ`, with the printed zero-coordinate fallback
`10⁻⁴ max (‖x‖∞, 1)`.  The norm on a finite real function is its sup norm. -/
noncomputable def higham26ADInitialStep {n : Nat}
    (x : RVec n) (i : Fin n) : Real :=
  if x i = 0 then
    ((1 : Real) / 10000) * max ‖x‖ 1
  else
    ((1 : Real) / 10000) * x i

@[simp] theorem higham26ADInitialStep_of_eq_zero {n : Nat}
    (x : RVec n) (i : Fin n) (hxi : x i = 0) :
    higham26ADInitialStep x i =
      ((1 : Real) / 10000) * max ‖x‖ 1 := by
  simp [higham26ADInitialStep, hxi]

@[simp] theorem higham26ADInitialStep_of_ne_zero {n : Nat}
    (x : RVec n) (i : Fin n) (hxi : x i ≠ 0) :
    higham26ADInitialStep x i = ((1 : Real) / 10000) * x i := by
  simp [higham26ADInitialStep, hxi]

/-- The source's sign-reversal rule: reverse the initial trial precisely when
the first evaluation gives no strict increase over the current point. -/
noncomputable def higham26ADDirectedStep {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) : Real :=
  let h := higham26ADInitialStep x i
  if f (adCoordinateLinePoint x i h) ≤ f x then -h else h

theorem higham26ADDirectedStep_of_noIncrease {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n)
    (h : f (adCoordinateLinePoint x i (higham26ADInitialStep x i)) ≤ f x) :
    higham26ADDirectedStep f x i = -higham26ADInitialStep x i := by
  simp [higham26ADDirectedStep, h]

theorem higham26ADDirectedStep_of_increase {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n)
    (h : f x < f (adCoordinateLinePoint x i (higham26ADInitialStep x i))) :
    higham26ADDirectedStep f x i = higham26ADInitialStep x i := by
  simp [higham26ADDirectedStep, not_le.mpr h]

/-- Starting from a successful signed trial `h`, double it while the newly
doubled trial strictly improves on the previous one.  `fuel` is the exact
upper bound on the number of doublings attempted. -/
noncomputable def higham26ADDoubleSearch {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) : Nat → Real → Real
  | 0, h => h
  | fuel + 1, h =>
      let next := 2 * h
      if f (adCoordinateLinePoint x i h) <
          f (adCoordinateLinePoint x i next) then
        higham26ADDoubleSearch f x i fuel next
      else
        h

/-- The doubling loop never returns a trial with a smaller objective value
than the successful trial with which it started. -/
theorem higham26ADDoubleSearch_value_ge {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n)
    (fuel : Nat) (h : Real) :
    f (adCoordinateLinePoint x i h) ≤
      f (adCoordinateLinePoint x i
        (higham26ADDoubleSearch f x i fuel h)) := by
  induction fuel generalizing h with
  | zero => simp [higham26ADDoubleSearch]
  | succ fuel ih =>
      by_cases hinc : f (adCoordinateLinePoint x i h) <
          f (adCoordinateLinePoint x i (2 * h))
      · simp only [higham26ADDoubleSearch, hinc, if_true]
        exact le_trans (le_of_lt hinc) (ih (2 * h))
      · simp [higham26ADDoubleSearch, hinc]

/-- After at most `fuel` doublings, the returned displacement is exactly
`2^k h` for some `k ≤ fuel`. -/
theorem higham26ADDoubleSearch_eq_pow {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n)
    (fuel : Nat) (h : Real) :
    ∃ k : Nat, k ≤ fuel ∧
      higham26ADDoubleSearch f x i fuel h = (2 : Real) ^ k * h := by
  induction fuel generalizing h with
  | zero =>
      exact ⟨0, le_rfl, by simp [higham26ADDoubleSearch]⟩
  | succ fuel ih =>
      by_cases hinc : f (adCoordinateLinePoint x i h) <
          f (adCoordinateLinePoint x i (2 * h))
      · rcases ih (2 * h) with ⟨k, hk, hout⟩
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
        simp only [higham26ADDoubleSearch, hinc, if_true]
        rw [hout]
        ring
      · exact ⟨0, Nat.zero_le _, by simp [higham26ADDoubleSearch, hinc]⟩

/-- Literal p. 475 crude line-search result.  If the signed trial fails to
improve on `x`, the displacement is zero.  Otherwise it is doubled at most
25 times, stopping at the last strictly improving trial. -/
noncomputable def higham26ADCrudeAlpha {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) : Real :=
  let h := higham26ADDirectedStep f x i
  if f x < f (adCoordinateLinePoint x i h) then
    higham26ADDoubleSearch f x i 25 h
  else
    0

/-- The literal crude line search cannot decrease the objective. -/
theorem higham26ADCrudeAlpha_value_ge {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) :
    f x ≤ f (adCoordinateLinePoint x i (higham26ADCrudeAlpha f x i)) := by
  by_cases hinc : f x <
      f (adCoordinateLinePoint x i (higham26ADDirectedStep f x i))
  · simp only [higham26ADCrudeAlpha, hinc, if_true]
    exact le_trans (le_of_lt hinc)
      (higham26ADDoubleSearch_value_ge f x i 25
        (higham26ADDirectedStep f x i))
  · simp [higham26ADCrudeAlpha, hinc, adCoordinateLinePoint_zero]

/-- The returned displacement is either zero or exactly `2^k` times the
signed trial for some `k ≤ 25`; hence the implementation performs no more
than the 25 doublings printed in the source. -/
theorem higham26ADCrudeAlpha_eq_zero_or_pow {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) :
    ∃ k : Nat, k ≤ 25 ∧
      (higham26ADCrudeAlpha f x i = 0 ∨
        higham26ADCrudeAlpha f x i =
          (2 : Real) ^ k * higham26ADDirectedStep f x i) := by
  by_cases hinc : f x <
      f (adCoordinateLinePoint x i (higham26ADDirectedStep f x i))
  · rcases higham26ADDoubleSearch_eq_pow f x i 25
        (higham26ADDirectedStep f x i) with ⟨k, hk, hout⟩
    exact ⟨k, hk, Or.inr (by simpa [higham26ADCrudeAlpha, hinc] using hout)⟩
  · exact ⟨0, by omega, Or.inl (by simp [higham26ADCrudeAlpha, hinc])⟩

/-- The source's actual finite coordinate-search function, suitable for the
existing `adSweep` and `ADSearchTrace` control-flow definitions. -/
noncomputable def higham26ADCrudeSearch {n : Nat}
    (f : RVec n → Real) : RVec n → Fin n → Real :=
  fun x i => higham26ADCrudeAlpha f x i

theorem higham26ADCrudeCoordinateStep_nondecreasing {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) :
    f x ≤ f (adCoordinateStep (higham26ADCrudeSearch f) x i) := by
  exact higham26ADCrudeAlpha_value_ge f x i

private theorem higham26ADCrudeFold_nondecreasing {n : Nat}
    (f : RVec n → Real) (coordinates : List (Fin n)) (x : RVec n) :
    f x ≤ f (coordinates.foldl
      (adCoordinateStep (higham26ADCrudeSearch f)) x) := by
  induction coordinates generalizing x with
  | nil => simp
  | cons i coordinates ih =>
      exact le_trans (higham26ADCrudeCoordinateStep_nondecreasing f x i)
        (ih (adCoordinateStep (higham26ADCrudeSearch f) x i))

/-- A full literal coordinate-order sweep is objective-nondecreasing. -/
theorem higham26ADCrudeSweep_nondecreasing {n : Nat}
    (f : RVec n → Real) (x : RVec n) :
    f x ≤ f (adSweep (higham26ADCrudeSearch f) x) := by
  exact higham26ADCrudeFold_nondecreasing f
    (List.ofFn (fun i : Fin n => i)) x

/-! ## Right-angled starting simplex from p. 476 -/

/-- Printed initial-simplex scale `max (‖x₀‖∞, 1)`. -/
noncomputable def higham26MDSInitialScale {n : Nat} (x0 : RVec n) : Real :=
  max ‖x0‖ 1

theorem higham26MDSInitialScale_nonneg {n : Nat} (x0 : RVec n) :
    0 ≤ higham26MDSInitialScale x0 := by
  exact le_trans (by norm_num : (0 : Real) ≤ 1)
    (le_max_right ‖x0‖ 1)

/-- Higham p. 476 / Torczon right-angled starting simplex: it contains `x₀`
as its base and adds one scaled coordinate vector for each other vertex. -/
noncomputable def higham26RightAngledSimplex {n : Nat}
    (x0 : RVec n) : MDSSimplex n where
  base := x0
  other := fun i j =>
    x0 j + if j = i then higham26MDSInitialScale x0 else 0

@[simp] theorem higham26RightAngledSimplex_base {n : Nat} (x0 : RVec n) :
    (higham26RightAngledSimplex x0).base = x0 := rfl

/-- Squared Euclidean distance, used to state the source's edge-length
normalization without conflating it with the function-space sup norm. -/
noncomputable def higham26SquaredDistance {n : Nat}
    (x y : RVec n) : Real :=
  ∑ j : Fin n, (x j - y j) ^ 2

/-- Every right-angled edge joined to `x₀` has the printed scale as its
Euclidean length (squared form). -/
theorem higham26RightAngledSimplex_edge_sq {n : Nat}
    (x0 : RVec n) (i : Fin n) :
    higham26SquaredDistance ((higham26RightAngledSimplex x0).other i) x0 =
      higham26MDSInitialScale x0 ^ 2 := by
  unfold higham26SquaredDistance higham26RightAngledSimplex
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Euclidean edge-length form of the same p. 476 scaling statement. -/
theorem higham26RightAngledSimplex_edge_length {n : Nat}
    (x0 : RVec n) (i : Fin n) :
    Real.sqrt
        (higham26SquaredDistance ((higham26RightAngledSimplex x0).other i) x0) =
      higham26MDSInitialScale x0 := by
  rw [higham26RightAngledSimplex_edge_sq]
  exact Real.sqrt_sq (higham26MDSInitialScale_nonneg x0)

/-- Dot product of two edges with a common base. -/
noncomputable def higham26EdgeDot {n : Nat}
    (base x y : RVec n) : Real :=
  ∑ j : Fin n, (x j - base j) * (y j - base j)

/-- Distinct coordinate edges of the constructed simplex are orthogonal,
which justifies the source term “right-angled”. -/
theorem higham26RightAngledSimplex_edges_orthogonal {n : Nat}
    (x0 : RVec n) (i k : Fin n) (hik : i ≠ k) :
    higham26EdgeDot x0
      ((higham26RightAngledSimplex x0).other i)
      ((higham26RightAngledSimplex x0).other k) = 0 := by
  unfold higham26EdgeDot higham26RightAngledSimplex
  apply Finset.sum_eq_zero
  intro j _
  by_cases hji : j = i <;> by_cases hjk : j = k
  · subst j
    exact (hik hjk).elim
  · subst j
    simp [hik]
  · subst j
    simp [Ne.symm hik]
  · simp [hji, hjk]

/-! ## Regular starting simplex from p. 476

The following is the standard coordinate realization used for a regular
simplex with one vertex fixed at `x₀`.  If `s` is the desired side length,
write

`a = s / √2`, `b = s(√(n+1)-1)/(n√2)`

and take the `i`th non-base edge to have coordinate vector `b·1 + a·eᵢ`.
-/

noncomputable def higham26RegularA (s : Real) : Real :=
  s / Real.sqrt 2

noncomputable def higham26RegularB (n : Nat) (s : Real) : Real :=
  s * (Real.sqrt ((n + 1 : Nat) : Real) - 1) /
    ((n : Real) * Real.sqrt 2)

/-- The coefficient identity making every base-to-other edge have squared
length `s²`. -/
theorem higham26Regular_coeff_base_sq (n : Nat) (hn : 0 < n) (s : Real) :
    higham26RegularA s ^ 2 +
        2 * higham26RegularA s * higham26RegularB n s +
        (n : Real) * higham26RegularB n s ^ 2 = s ^ 2 := by
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : Real.sqrt 2 ^ 2 = (2 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hnpos : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hsqrtn : Real.sqrt ((n + 1 : Nat) : Real) ^ 2 =
      ((n + 1 : Nat) : Real) := Real.sq_sqrt (by positivity)
  have hsqrtn' : Real.sqrt ((n + 1 : Nat) : Real) ^ 2 =
      (n : Real) + 1 := by
    simpa using hsqrtn
  have hbracket :
      (n : Real) + 2 * (Real.sqrt ((n + 1 : Nat) : Real) - 1) +
          (Real.sqrt ((n + 1 : Nat) : Real) - 1) ^ 2 = 2 * (n : Real) := by
    nlinarith [hsqrtn']
  unfold higham26RegularA higham26RegularB
  field_simp [ne_of_gt hsqrt2pos, ne_of_gt hnpos]
  rw [hbracket, hsqrt2sq]
  ring

/-- The `a=s/√2` coefficient makes the difference of two distinct edge
vectors have squared length `2a²=s²`. -/
theorem higham26Regular_coeff_pair_sq (s : Real) :
    2 * higham26RegularA s ^ 2 = s ^ 2 := by
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : Real.sqrt 2 ^ 2 = (2 : Real) :=
    Real.sq_sqrt (by norm_num)
  unfold higham26RegularA
  field_simp [ne_of_gt hsqrt2pos]
  nlinarith

/-- Higham p. 476 / Torczon regular starting simplex, with `x₀` as base and
all `n(n+1)/2` edges scaled to `max (‖x₀‖∞,1)`. -/
noncomputable def higham26RegularSimplex {n : Nat}
    (x0 : RVec n) : MDSSimplex n where
  base := x0
  other := fun i j =>
    x0 j + higham26RegularB n (higham26MDSInitialScale x0) +
      if j = i then higham26RegularA (higham26MDSInitialScale x0) else 0

@[simp] theorem higham26RegularSimplex_base {n : Nat} (x0 : RVec n) :
    (higham26RegularSimplex x0).base = x0 := rfl

private theorem higham26Regular_base_sum (n : Nat) (hn : 0 < n)
    (s : Real) (i : Fin n) :
    (∑ j : Fin n,
        (higham26RegularB n s +
          if j = i then higham26RegularA s else 0) ^ 2) = s ^ 2 := by
  let a := higham26RegularA s
  let b := higham26RegularB n s
  change (∑ j : Fin n, (b + if j = i then a else 0) ^ 2) = s ^ 2
  have hpoint : ∀ j : Fin n,
      (b + if j = i then a else 0) ^ 2 =
        b ^ 2 + if j = i then a ^ 2 + 2 * a * b else 0 := by
    intro j
    by_cases hji : j = i <;> simp [hji] <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp
  have hcoeff := higham26Regular_coeff_base_sq n hn s
  dsimp [a, b]
  nlinarith

/-- Every edge from the base of the constructed regular simplex has the
printed squared length. -/
theorem higham26RegularSimplex_base_edge_sq {n : Nat} (hn : 0 < n)
    (x0 : RVec n) (i : Fin n) :
    higham26SquaredDistance ((higham26RegularSimplex x0).other i) x0 =
      higham26MDSInitialScale x0 ^ 2 := by
  unfold higham26SquaredDistance higham26RegularSimplex
  convert higham26Regular_base_sum n hn (higham26MDSInitialScale x0) i using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem higham26Regular_pair_sum (n : Nat) (s : Real)
    (i k : Fin n) (hik : i ≠ k) :
    (∑ j : Fin n,
      ((if j = i then higham26RegularA s else 0) -
        (if j = k then higham26RegularA s else 0)) ^ 2) = s ^ 2 := by
  let a := higham26RegularA s
  have hpoint : ∀ j : Fin n,
      ((if j = i then a else 0) - (if j = k then a else 0)) ^ 2 =
        (if j = i then a ^ 2 else 0) +
          (if j = k then a ^ 2 else 0) := by
    intro j
    by_cases hji : j = i <;> by_cases hjk : j = k
    · subst j
      exact (hik hjk).elim
    · subst j
      simp [hik]
    · subst j
      simp [Ne.symm hik]
    · simp [hji, hjk]
  change (∑ j : Fin n,
      ((if j = i then a else 0) - (if j = k then a else 0)) ^ 2) = s ^ 2
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp
  simpa [a, two_mul] using higham26Regular_coeff_pair_sq s

/-- Every edge between two distinct non-base vertices also has the printed
squared length, so the constructor is genuinely regular. -/
theorem higham26RegularSimplex_other_edge_sq {n : Nat}
    (x0 : RVec n) (i k : Fin n) (hik : i ≠ k) :
    higham26SquaredDistance
        ((higham26RegularSimplex x0).other i)
        ((higham26RegularSimplex x0).other k) =
      higham26MDSInitialScale x0 ^ 2 := by
  unfold higham26SquaredDistance higham26RegularSimplex
  convert higham26Regular_pair_sum n (higham26MDSInitialScale x0) i k hik using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Euclidean length statement for base edges of the regular simplex. -/
theorem higham26RegularSimplex_base_edge_length {n : Nat} (hn : 0 < n)
    (x0 : RVec n) (i : Fin n) :
    Real.sqrt
        (higham26SquaredDistance ((higham26RegularSimplex x0).other i) x0) =
      higham26MDSInitialScale x0 := by
  rw [higham26RegularSimplex_base_edge_sq hn]
  exact Real.sqrt_sq (higham26MDSInitialScale_nonneg x0)

/-- Euclidean length statement for all other regular-simplex edges. -/
theorem higham26RegularSimplex_other_edge_length {n : Nat}
    (x0 : RVec n) (i k : Fin n) (hik : i ≠ k) :
    Real.sqrt
        (higham26SquaredDistance
          ((higham26RegularSimplex x0).other i)
          ((higham26RegularSimplex x0).other k)) =
      higham26MDSInitialScale x0 := by
  rw [higham26RegularSimplex_other_edge_sq x0 i k hik]
  exact Real.sqrt_sq (higham26MDSInitialScale_nonneg x0)

end NumStability
