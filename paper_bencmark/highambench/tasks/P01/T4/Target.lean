import HighamBench.P01Definitions

/-!
# P01-T4: whole-paper statement corpus

This file contains the source-ordered proof-bearing claims for Nicholas J.
Higham, "The Accuracy of Floating Point Summation" (1993). Each declaration
has one enumerated benchmark proof placeholder. The transparent semantic
surface is supplied by `HighamBench.P01Definitions`.
-/

namespace HighamBench

open scoped BigOperators

/-- Recursive, pairwise, insertion, and sign-separated methods are addition-tree methods. -/
theorem p01_t4_four_methods_are_general_addition_schemes
    (flAdd : ℝ → ℝ → ℝ) :
    (∀ inputs : List ℝ, inputs ≠ [] →
      ∃ tree : P01SumTree,
        P01AdditionScheme inputs tree ∧
        P01SumTree.rounded flAdd tree = p01RecursiveList flAdd inputs) ∧
    (∀ inputs result, inputs ≠ [] → P01PairwiseEvaluation flAdd inputs result →
      ∃ tree : P01SumTree,
        P01AdditionScheme inputs tree ∧ P01SumTree.rounded flAdd tree = result) ∧
    (∀ inputs result, inputs ≠ [] → P01InsertionEvaluation flAdd inputs result →
      ∃ tree : P01SumTree,
        P01AdditionScheme inputs tree ∧ P01SumTree.rounded flAdd tree = result) ∧
    (∀ inputs result, inputs ≠ [] → P01PlusMinusEvaluation flAdd inputs result →
      ∃ tree : P01SumTree,
        P01AdditionScheme inputs tree ∧ P01SumTree.rounded flAdd tree = result) := by
  -- PROOF_START P01-D001
  sorry
/-- The permutation symmetry stated immediately after equation (1.1). -/
theorem p01_t4_rosenbrock_pair_swap (a b c d : ℝ) :
    p01ExtendedRosenbrock 2 (p01Four a b c d) =
      p01ExtendedRosenbrock 2 (p01Four c d a b) := by
  -- PROOF_START P01-D005
  sorry
/-- Equation (2.1): all recursive additions admit bounded local factors. -/
theorem p01_t4_eq_2_1
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ) (hn : 0 < n) :
    ∃ δ : Fin n → ℝ, P01RecursiveDeltaWitness fp n v δ := by
  -- PROOF_START P01-D012
  sorry
/-- Equation (2.2), represented as one path product for each input. -/
theorem p01_t4_eq_2_2
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ) (hn : 2 ≤ n) :
    ∃ δ : Fin n → ℝ,
      P01RecursiveDeltaWitness fp n v δ ∧
      p01RecursiveSum fp.fl_add n v = p01RecursiveProductExpansion n v δ := by
  -- PROOF_START P01-D013
  sorry
/-- The finite-product lemma displayed after equation (2.2). -/
theorem p01_t4_finite_product_theta
    (u : ℝ) (m : ℕ) (δ : Fin m → ℝ)
    (hu : 0 ≤ u) (hvalid : P01GammaValid u m)
    (hδ : ∀ i, |δ i| ≤ u) :
    ∃ θ : ℝ,
      (∏ i : Fin m, (1 + δ i)) = 1 + θ ∧ |θ| ≤ p01Gamma u m := by
  -- PROOF_START P01-D014
  sorry
/-- Equation (2.3), with a separate product remainder for every input path. -/
theorem p01_t4_eq_2_3
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ) (hn : 2 ≤ n)
    (hvalid : P01GammaValid fp.u (n - 1)) :
    ∃ θ : Fin n → ℝ, P01RecursiveThetaWitness fp n v θ := by
  -- PROOF_START P01-D015
  sorry
/-- Equation (2.4): the absolute error expressed through the path remainders. -/
theorem p01_t4_eq_2_4
    (fp : P01StandardAddModel) (n : ℕ) (v θ : Fin n → ℝ)
    (hθ : P01RecursiveThetaWitness fp n v θ) :
    |p01RecursiveError fp.fl_add n v| = |∑ i : Fin n, v i * θ i| := by
  -- PROOF_START P01-D016
  sorry
/-- Equation (2.5), in the equivalent path-length indexing of the source formula. -/
theorem p01_t4_eq_2_5
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ) (hn : 2 ≤ n)
    (hvalid : P01GammaValid fp.u (n - 1)) :
    |p01RecursiveError fp.fl_add n v| ≤
      ∑ i : Fin n, |v i| * p01Gamma fp.u (p01RecursivePathLength n i) := by
  -- PROOF_START P01-D017
  sorry
/-- Increasing magnitude minimizes the bound (2.5), but not necessarily actual error. -/
theorem p01_t4_increasing_minimizes_eq25
    (u : ℝ) {n : ℕ} (v : Fin n → ℝ) (p : Equiv.Perm (Fin n))
    (hu : 0 ≤ u) (hvalid : P01GammaValid u (n - 1))
    (hp : P01IncreasingMagnitude v p) :
    ∀ q : Equiv.Perm (Fin n), p01Eq25Budget u v p ≤ p01Eq25Budget u v q := by
  -- PROOF_START P01-D018
  sorry
/-- Example (2.9) witnesses that increasing magnitude need not minimize actual error. -/
theorem p01_t4_increasing_need_not_minimize_actual_error :
    ∃ fp : P01RadixRoundModel, ∃ M : ℝ,
      1 < M ∧
      (p01RadixUnitRoundoff fp)⁻¹ ≤ M ∧
      (∃ e : ℤ, M = (fp.radix : ℝ) ^ e) ∧
      (∀ i, P01BaseRepresentable fp.radix fp.precision (p01Eq29Input M i)) ∧
      fp.round (1 + M) = M ∧
      P01IncreasingMagnitude (p01Eq29Input M) p01Eq29IncreasingPerm ∧
      P01DecreasingMagnitude (p01Eq29Input M) p01Eq29DecreasingPerm ∧
      |p01RecursiveSum (p01RadixRoundAdd fp) 4
          (p01Permuted (p01Eq29Input M) p01Eq29DecreasingPerm) -
          p01ExactSum 4 (p01Eq29Input M)| <
        |p01RecursiveSum (p01RadixRoundAdd fp) 4
          (p01Permuted (p01Eq29Input M) p01Eq29IncreasingPerm) -
          p01ExactSum 4 (p01Eq29Input M)| := by
  -- PROOF_START P01-D018B
  sorry
/-- Equation (2.6), retaining its exact `p01Gamma` bound. -/
theorem p01_t4_eq_2_6
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ)
    (hvalid : P01GammaValid fp.u (n - 1)) :
    |p01RecursiveError fp.fl_add n v| ≤ p01Gamma fp.u (n - 1) * p01AbsoluteSum n v := by
  -- PROOF_START P01-D019
  sorry
/-- Exact remainder identity underlying the `O(u^2)` expansion in equation (2.6). -/
theorem p01_t4_gamma_first_order_remainder
    (u : ℝ) (m : ℕ) (hvalid : P01GammaValid u m) :
    p01Gamma u m = (m : ℝ) * u +
      (((m : ℝ) * u) ^ 2) / (1 - (m : ℝ) * u) := by
  -- PROOF_START P01-D019R
  sorry
/-- The unnumbered relative-error consequence of equation (2.6). -/
theorem p01_t4_recursive_relative_error
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ)
    (hvalid : P01GammaValid fp.u (n - 1)) (hsum : p01ExactSum n v ≠ 0) :
    |p01RecursiveError fp.fl_add n v| / |p01ExactSum n v| ≤
      p01Gamma fp.u (n - 1) * p01SummationCondition n v := by
  -- PROOF_START P01-D021
  sorry
/-- For nonnegative data with nonzero sum, the absolute-sum condition number is one. -/
theorem p01_t4_nonnegative_condition_one
    {n : ℕ} (v : Fin n → ℝ) (hnonnegative : ∀ i, 0 ≤ v i)
    (hsum : p01ExactSum n v ≠ 0) :
    p01SummationCondition n v = 1 := by
  -- PROOF_START P01-D022B
  sorry
/-- `R_n` gives the sharp componentwise relative sensitivity of summation. -/
theorem p01_t4_summation_condition_number
    (n : ℕ) (v : Fin n → ℝ) (hn : 0 < n)
    (hsum : p01ExactSum n v ≠ 0) :
    (∀ ε : ℝ, 0 ≤ ε → ∀ dv : Fin n → ℝ,
      P01ComponentwisePerturbation n v dv ε →
      |p01ExactSum n dv| / |p01ExactSum n v| ≤
        p01SummationCondition n v * ε) ∧
    (∀ κ : ℝ,
      (∀ ε : ℝ, 0 ≤ ε → ∀ dv : Fin n → ℝ,
        P01ComponentwisePerturbation n v dv ε →
        |p01ExactSum n dv| / |p01ExactSum n v| ≤ κ * ε) →
      p01SummationCondition n v ≤ κ) := by
  -- PROOF_START P01-D023
  sorry
/-- Equation (2.7), retaining explicit local rounding witnesses. -/
theorem p01_t4_eq_2_7
    (fp : P01StandardAddModel) (n : ℕ) (v δ : Fin n → ℝ)
    (hδ : P01RecursiveDeltaWitness fp n v δ) (hu : fp.u < 1) :
    p01RecursiveError fp.fl_add n v =
      ∑ k : Fin n,
        if 0 < k.val then
          p01RecursivePrefix fp n v k * δ k / (1 + δ k)
        else 0 := by
  -- PROOF_START P01-D024
  sorry
/-- Equation (2.8), the computed-prefix running-error bound. -/
theorem p01_t4_eq_2_8
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ)
    (hu : fp.u < 1) :
    |p01RecursiveError fp.fl_add n v| ≤
      fp.u / (1 - fp.u) * p01RecursiveRunningMagnitude fp n v := by
  -- PROOF_START P01-D025
  sorry
/-- Bounding the computed prefixes in (2.8) recovers (2.5) up to `O(u²)`. -/
theorem p01_t4_eq_2_8_recovers_eq_2_5
    (family : P01StandardAddFamily) (n : ℕ) (v : Fin n → ℝ) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      ∀ u : NNReal, (u : ℝ) ≤ ε →
        (u : ℝ) / (1 - (u : ℝ)) *
            p01RecursiveRunningMagnitude (family.model u) n v ≤
          (∑ i : Fin n,
            |v i| * p01Gamma (u : ℝ) (p01RecursivePathLength n i)) +
            C * (u : ℝ) ^ 2 := by
  -- PROOF_START P01-D026
  sorry
/-- Psum can change when only the signs change, whereas magnitude ordering cannot. -/
theorem p01_t4_psum_depends_on_signs :
    (∀ {n : ℕ} (v w : Fin n → ℝ) (p : Equiv.Perm (Fin n)),
      (∀ i, |v i| = |w i|) →
        (P01IncreasingMagnitude v p ↔ P01IncreasingMagnitude w p)) ∧
    (∃ v w : Fin 3 → ℝ, ∃ p : Equiv.Perm (Fin 3),
      (∀ i, |v i| = |w i|) ∧
      P01PsumOrder (· + ·) v p ∧ ¬ P01PsumOrder (· + ·) w p) := by
  -- PROOF_START P01-D029S
  sorry
/-- Each actual recursive step loses exactly the low-order block assigned to that input group. -/
theorem p01_t4_near_attainability_local_error
    (flAdd : ℝ → ℝ → ℝ) (r t : ℕ)
    (htrace : P01NearAttainabilityRoundingTrace flAdd r t) :
    ∀ k : Fin (2 ^ r), 0 < k.val →
      let previous :=
        p01RecursiveSum flAdd k.val
          (fun i => p01NearAttainabilityInput r t ⟨i.val, by omega⟩)
      |flAdd previous (p01NearAttainabilityInput r t k) -
          (previous + p01NearAttainabilityInput r t k)| =
        (2 : ℝ) ^ ((Nat.log 2 k.val : ℤ) - (t : ℤ)) := by
  -- PROOF_START P01-D031E
  sorry
/-- Every computed partial sum in the near-attainability example is the corresponding integer. -/
theorem p01_t4_near_attainability_computed_prefixes
    (flAdd : ℝ → ℝ → ℝ) (r t : ℕ)
    (htrace : P01NearAttainabilityRoundingTrace flAdd r t) :
    ∀ k : Fin (2 ^ r),
      p01RecursiveSum flAdd (k.val + 1)
          (fun i => p01NearAttainabilityInput r t ⟨i.val, by omega⟩) =
        ((k.val + 1 : ℕ) : ℝ) := by
  -- PROOF_START P01-D031R
  sorry
/-- The actual computed error of the near-attainability family on printed page 786. -/
theorem p01_t4_near_attainability_total_error
    (flAdd : ℝ → ℝ → ℝ) (r t : ℕ)
    (htrace : P01NearAttainabilityRoundingTrace flAdd r t) :
    |p01RecursiveSum flAdd (2 ^ r) (p01NearAttainabilityInput r t) -
        p01ExactSum (2 ^ r) (p01NearAttainabilityInput r t)| =
      (2 : ℝ) ^ (-(t : ℤ)) * ((4 : ℝ) ^ r - 1) / 3 := by
  -- PROOF_START P01-D032
  sorry
/-- The displayed upper estimate for the equation-(2.6) bound in the
near-attainability family. -/
theorem p01_t4_near_attainability_eq26_upper
    (r t : ℕ)
    (hvalid : P01GammaValid ((2 : ℝ) ^ (-(t : ℤ))) (2 ^ r)) :
    p01NearAttainabilityEq26Bound r t <
      ((2 : ℝ) ^ r * (2 : ℝ) ^ (-(t : ℤ))) /
        (1 - (2 : ℝ) ^ r * (2 : ℝ) ^ (-(t : ℤ))) * (2 : ℝ) ^ r := by
  -- PROOF_START P01-D033U
  sorry
/-- For positive data, decreasing magnitude cannot improve the bound (2.5). -/
theorem p01_t4_decreasing_positive_eq25_no_better
    (u : ℝ) {n : ℕ} (v : Fin n → ℝ)
    (hu : 0 ≤ u) (hv : ∀ i, 0 ≤ v i)
    (hvalid : P01GammaValid u (n - 1))
    (inc dec : Equiv.Perm (Fin n))
    (hinc : P01IncreasingMagnitude v inc)
    (hdec : P01DecreasingMagnitude v dec) :
    p01Eq25Budget u v inc ≤ p01Eq25Budget u v dec := by
  -- PROOF_START P01-D034
  sorry
/-- A fixed-precision recursive harmonic sum eventually stagnates in any machine radix. -/
theorem p01_t4_decreasing_harmonic_stagnates
    (fp : P01RadixRoundModel) :
    ∃ N : ℕ, ∃ s : ℝ, ∀ n : ℕ, N ≤ n →
      (List.range n).foldl
        (fun acc k => fp.round (acc + 1 / ((k + 1 : ℕ) : ℝ))) 0 = s := by
  -- PROOF_START P01-D035
  sorry
/-- The three computed values reported for the machine-radix example (2.9). -/
theorem p01_t4_eq_2_9_results
    (fp : P01RadixRoundModel) (M : ℝ)
    (hM : 1 < M)
    (hlarge : (p01RadixUnitRoundoff fp)⁻¹ ≤ M)
    (hpower : ∃ e : ℤ, M = (fp.radix : ℝ) ^ e)
    (hinputs : ∀ i, P01BaseRepresentable fp.radix fp.precision (p01Eq29Input M i))
    (hlost : fp.round (1 + M) = M) :
    P01IncreasingMagnitude (p01Eq29Input M) p01Eq29IncreasingPerm ∧
    P01PsumOrder (p01RadixRoundAdd fp) (p01Eq29Input M) p01Eq29PsumPerm ∧
    P01DecreasingMagnitude (p01Eq29Input M) p01Eq29DecreasingPerm ∧
    p01RecursiveSum (p01RadixRoundAdd fp) 4
        (p01Permuted (p01Eq29Input M) p01Eq29IncreasingPerm) = 0 ∧
    p01RecursiveSum (p01RadixRoundAdd fp) 4
        (p01Permuted (p01Eq29Input M) p01Eq29PsumPerm) = 0 ∧
    p01RecursiveSum (p01RadixRoundAdd fp) 4
        (p01Permuted (p01Eq29Input M) p01Eq29DecreasingPerm) = 1 ∧
    p01ExactSum 4 (p01Eq29Input M) = 1 ∧
    p01ReportedRelativeError 0 1 = 1 ∧
    |p01RecursiveSum (p01RadixRoundAdd fp) 4
          (p01Permuted (p01Eq29Input M) p01Eq29DecreasingPerm) -
        p01ExactSum 4 (p01Eq29Input M)| <
      |p01RecursiveSum (p01RadixRoundAdd fp) 4
          (p01Permuted (p01Eq29Input M) p01Eq29IncreasingPerm) -
        p01ExactSum 4 (p01Eq29Input M)| ∧
    (∀ k : Fin 4,
      p01RecursiveSum (p01RadixRoundAdd fp) (k.val + 1)
          (fun i => p01Permuted (p01Eq29Input M) p01Eq29DecreasingPerm
            ⟨i.val, by omega⟩) =
        p01ExactSum (k.val + 1)
          (fun i => p01Permuted (p01Eq29Input M) p01Eq29DecreasingPerm
            ⟨i.val, by omega⟩)) := by
  -- PROOF_START P01-D037
  sorry
/-- The three computed-prefix budgets reported for example (2.9). -/
theorem p01_t4_eq_2_9_running_magnitudes
    (fp : P01RadixRoundModel) (M : ℝ)
    (hM : 1 < M)
    (hlarge : (p01RadixUnitRoundoff fp)⁻¹ ≤ M)
    (hpower : ∃ e : ℤ, M = (fp.radix : ℝ) ^ e)
    (hinputs : ∀ i, P01BaseRepresentable fp.radix fp.precision (p01Eq29Input M i))
    (hlost : fp.round (1 + M) = M) :
    P01IncreasingMagnitude (p01Eq29Input M) p01Eq29IncreasingPerm ∧
    P01PsumOrder (p01RadixRoundAdd fp) (p01Eq29Input M) p01Eq29PsumPerm ∧
    P01DecreasingMagnitude (p01Eq29Input M) p01Eq29DecreasingPerm ∧
    p01GenericRunningMagnitude (p01RadixRoundAdd fp) 4
        (p01Permuted (p01Eq29Input M) p01Eq29IncreasingPerm) =
        4 * M ∧
    p01GenericRunningMagnitude (p01RadixRoundAdd fp) 4
        (p01Permuted (p01Eq29Input M) p01Eq29PsumPerm) =
        3 * M ∧
    p01GenericRunningMagnitude (p01RadixRoundAdd fp) 4
        (p01Permuted (p01Eq29Input M) p01Eq29DecreasingPerm) =
        M + 1 := by
  -- PROOF_START P01-D038
  sorry
/-- Every addition in the recursive tree has an original input operand. -/
theorem p01_t4_recursive_tree_every_addition_has_original_operand
    (inputs : List ℝ) (tree : P01SumTree)
    (htree : p01RecursiveTree inputs = some tree) :
    P01EveryAdditionHasOriginalOperand tree := by
  -- PROOF_START P01-D040R
  sorry
/-- Equation (3.2): every rounded addition tree has bounded local factors. -/
theorem p01_t4_eq_3_2 (fp : P01StandardAddModel) (tree : P01SumTree) :
    P01TreeRespectsStandardModel fp tree := by
  -- PROOF_START P01-D041
  sorry
/-- The local-error formula immediately preceding equation (3.3). -/
theorem p01_t4_tree_local_error
    (fp : P01StandardAddModel) (left right : P01SumTree) (hu : fp.u < 1) :
    ∃ δ : ℝ, |δ| ≤ fp.u ∧
      let value := P01SumTree.rounded fp.fl_add (.node left right)
      value - (P01SumTree.rounded fp.fl_add left +
        P01SumTree.rounded fp.fl_add right) = value * δ / (1 + δ) := by
  -- PROOF_START P01-D042
  sorry
/-- Equation (3.3): total error is the sum of the local addition errors. -/
theorem p01_t4_eq_3_3
    (flAdd : ℝ → ℝ → ℝ) (tree : P01SumTree) :
    P01SumTree.rounded flAdd tree - P01SumTree.exact tree =
      (P01SumTree.localErrors flAdd tree).sum := by
  -- PROOF_START P01-D043
  sorry
/-- Equation (3.4): the coefficient is the least uniform local-error coefficient,
and it gives the general-tree running bound. -/
theorem p01_t4_eq_3_4
    (fp : P01StandardAddModel) (tree : P01SumTree) (hu : fp.u < 1) :
    (∀ c : ℝ,
      (∀ δ : ℝ, |δ| ≤ fp.u → |δ / (1 + δ)| ≤ c) →
        fp.u / (1 - fp.u) ≤ c) ∧
    |P01SumTree.rounded fp.fl_add tree - P01SumTree.exact tree| ≤
      fp.u / (1 - fp.u) * p01TreeRunningMagnitude fp.fl_add tree := by
  -- PROOF_START P01-D044
  sorry
/-- Every general-tree internal value has the source's first-order input-sum bound. -/
theorem p01_t4_internal_value_bound
    (family : P01StandardAddFamily) (tree : P01SumTree) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      ∀ u : NNReal, (u : ℝ) ≤ ε →
      ∀ value ∈ P01SumTree.internalValues (family.model u).fl_add tree,
        |value| ≤ (tree.leaves.map abs).sum + C * (u : ℝ) := by
  -- PROOF_START P01-D045
  sorry
/-- Equation (3.5), stated with the exact `p01Gamma` remainder that implies its `O(u^2)` form. -/
theorem p01_t4_eq_3_5
    (fp : P01StandardAddModel) (tree : P01SumTree)
    (hvalid : P01GammaValid fp.u (tree.leaves.length - 1)) :
    |P01SumTree.rounded fp.fl_add tree - P01SumTree.exact tree| ≤
      p01Gamma fp.u (tree.leaves.length - 1) *
        (tree.leaves.map abs).sum := by
  -- PROOF_START P01-D046
  sorry
/-- Recursive summation makes (3.3)--(3.5) specialize to (2.6)--(2.8). -/
theorem p01_t4_recursive_tree_specialization
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ) (hn : 0 < n) :
    ∃ tree : P01SumTree,
      p01RecursiveTree (List.ofFn v) = some tree ∧
      P01AdditionScheme (List.ofFn v) tree ∧
      P01SumTree.rounded fp.fl_add tree = p01RecursiveSum fp.fl_add n v ∧
      (P01SumTree.localErrors fp.fl_add tree).sum = p01RecursiveError fp.fl_add n v ∧
      ((P01SumTree.internalValues fp.fl_add tree).map abs).sum =
        p01RecursiveRunningMagnitude fp n v := by
  -- PROOF_START P01-D047
  sorry
/-- The backward-error statement following equation (3.5), with exact p01Gamma control. -/
theorem p01_t4_general_tree_backward_error
    (fp : P01StandardAddModel) (tree : P01SumTree)
    (hvalid : P01GammaValid fp.u (tree.leaves.length - 1)) :
    ∃ θ : Fin tree.leaves.length → ℝ,
      P01SumTree.rounded fp.fl_add tree =
        ∑ i : Fin tree.leaves.length,
          (tree.leaves.get i) * (1 + θ i) ∧
      ∀ i, |θ i| ≤ p01Gamma fp.u (tree.leaves.length - 1) := by
  -- PROOF_START P01-D048
  sorry
/-- Pairwise summation uses exactly `ceil(log₂ n)` stages. -/
theorem p01_t4_pairwise_stage_count
    (flAdd : ℝ → ℝ → ℝ) (xs : List ℝ) (stages : ℕ) (s : ℝ)
    (h : P01PairwiseEvaluationStages flAdd xs stages s) :
    stages = p01CeilLog2 xs.length := by
  -- PROOF_START P01-D050A
  sorry
/-- The `n=6` symbolic pairwise example on printed page 788. -/
theorem p01_t4_pairwise_six_example
    (flAdd : ℝ → ℝ → ℝ) (x1 x2 x3 x4 x5 x6 : ℝ) :
    P01PairwiseEvaluation flAdd [x1, x2, x3, x4, x5, x6]
      (flAdd (flAdd (flAdd x1 x2) (flAdd x3 x4)) (flAdd x5 x6)) := by
  -- PROOF_START P01-D050B
  sorry
/-- For `n = 2^r`, every pairwise addend participates in exactly `r = log₂ n`
additions. -/
theorem p01_t4_pairwise_every_addend_depth
    (r : ℕ) (v : Fin (2 ^ r) → ℝ) (tree : P01SumTree)
    (htree : P01PairwiseTreeEvaluation (List.ofFn v) tree) :
    tree.leafDepths = List.replicate (2 ^ r) r := by
  -- PROOF_START P01-D051A
  sorry
/-- Pathwise product expansion for balanced pairwise summation. -/
theorem p01_t4_pairwise_product_expansion
    (fp : P01StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ) :
    ∃ δ : Fin (2 ^ r) → Fin r → ℝ,
      (∀ i k, |δ i k| ≤ fp.u) ∧
      pairwiseSum fp.fl_add r v =
        ∑ i : Fin (2 ^ r), v i * ∏ k : Fin r, (1 + δ i k) := by
  -- PROOF_START P01-D052
  sorry
/-- Equation (3.6), specialized exactly as in the paper to `n = 2^r`. -/
theorem p01_t4_eq_3_6
    (fp : P01StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : P01GammaValid fp.u r) :
    |pairwiseSum fp.fl_add r v - p01ExactSum (2 ^ r) v| ≤
      p01Gamma fp.u r * p01AbsoluteSum (2 ^ r) v := by
  -- PROOF_START P01-D053
  sorry
/-- For an inverse-cube example, the recursive equation-(2.5) bound can be
strictly smaller than the pairwise equation-(3.6) bound. -/
theorem p01_t4_recursive_eq25_can_beat_pairwise_bound :
    ∃ (r : ℕ) (u : ℝ),
      0 < u ∧ P01GammaValid u (2 ^ r - 1) ∧
      let v : Fin (2 ^ r) → ℝ :=
        fun i => 1 / ((2 ^ r - i.val : ℕ) : ℝ) ^ 3
      P01IncreasingMagnitude v (Equiv.refl (Fin (2 ^ r))) ∧
      p01Eq25Budget u v (Equiv.refl (Fin (2 ^ r))) <
        p01Gamma u r * p01AbsoluteSum (2 ^ r) v := by
  -- PROOF_START P01-D053B
  sorry
/-- The exact inverse-cube coefficient underlying (3.7), with `O(u²)` made uniform. -/
theorem p01_t4_pairwise_inverse_cube_asymptotic
    (family : P01StandardAddFamily) (r : ℕ) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      ∀ u : NNReal, (u : ℝ) ≤ ε →
        let v : Fin (2 ^ r) → ℝ :=
          fun i => 1 / ((i.val + 1 : ℕ) : ℝ) ^ 3
        |pairwiseSum (family.model u).fl_add r v - p01ExactSum (2 ^ r) v| ≤
            p01InversePowerSeries 3 * (r : ℝ) * (u : ℝ) + C * (u : ℝ) ^ 2 := by
  -- PROOF_START P01-D054A
  sorry
/-- The increasing-order comparison after (3.7), with its finite reciprocal-square coefficient kept exact. -/
theorem p01_t4_increasing_inverse_cube_asymptotic
    (family : P01StandardAddFamily) (n : ℕ) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      ∀ u : NNReal, (u : ℝ) ≤ ε →
        let v : Fin n → ℝ :=
          fun i => 1 / ((n - i.val : ℕ) : ℝ) ^ 3
        |p01RecursiveError (family.model u).fl_add n v| ≤
            p01InversePowerPartial 2 n * (u : ℝ) + C * (u : ℝ) ^ 2 := by
  -- PROOF_START P01-D055A
  sorry
/-- The reciprocal-square series identity used in the parenthesis after (3.7). -/
theorem p01_t4_inverse_square_series_value :
    p01InversePowerSeries 2 = Real.pi ^ 2 / 6 := by
  -- PROOF_START P01-D055S
  sorry
/-- For powers of two, insertion and ordinary recursive summation have a common evaluation. -/
theorem p01_t4_insertion_powers_of_two_are_recursive
    (fp : P01BinaryRoundModel) (n : ℕ) (hn : 0 < n) :
    let inputs := p01PowersOfTwo n
    let recursiveResult := p01RecursiveList (p01RoundAdd fp) inputs
    P01InsertionFrontEvaluation (p01RoundAdd fp) inputs recursiveResult ∧
    ∀ result,
      P01InsertionEvaluation (p01RoundAdd fp) inputs result ↔
        result = recursiveResult := by
  -- PROOF_START P01-D058G
  sorry
/-- The displayed `1,2,4,8 -> 3,4,8 -> 7,8 -> 15` insertion trace. -/
theorem p01_t4_insertion_power_two_example :
    P01InsertionEvaluation (· + ·) [1, 2, 4, 8] 15 := by
  -- PROOF_START P01-D058
  sorry
/-- On `1 < x₁ < ⋯ < xₙ < 2`, insertion is pairwise summation for power-of-two length. -/
theorem p01_t4_insertion_pairwise_interval
    (fp : P01RadixRoundModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hrepresentable : ∀ i, P01BaseRepresentable fp.radix fp.precision (v i))
    (hordered : ∀ i j, i.val < j.val → v i < v j)
    (hlower : ∀ i, 1 < v i) (hupper : ∀ i, v i < 2) :
    P01InsertionBackEvaluation (p01RadixRoundAdd fp) (List.ofFn v)
        (pairwiseSum (p01RadixRoundAdd fp) r v) ∧
    ∀ result,
      P01InsertionEvaluation (p01RadixRoundAdd fp) (List.ofFn v) result ↔
        result = pairwiseSum (p01RadixRoundAdd fp) r v := by
  -- PROOF_START P01-D059
  sorry
/-- The four-term insertion trace printed for `0 < ε < 1/2`. -/
theorem p01_t4_insertion_epsilon_example
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    P01InsertionEvaluation (· + ·)
      [1, 1 + ε, 1 + 2 * ε, 1 + 3 * ε] (4 + 6 * ε) := by
  -- PROOF_START P01-D059E
  sorry
/-- Every sign-separated tree attains a maximal exact magnitude among addition trees. -/
theorem p01_t4_plusminus_maximizes_internal_magnitude
    (inputs : List ℝ) (hnonempty : inputs ≠ []) :
    (∃ witness : P01SumTree, P01PlusMinusTree (· + ·) inputs witness) ∧
    ∀ plusTree : P01SumTree, P01PlusMinusTree (· + ·) inputs plusTree →
      P01AdditionScheme inputs plusTree ∧
      ∀ tree : P01SumTree, P01AdditionScheme inputs tree →
        p01MaxExactValueMagnitude tree ≤ p01MaxExactValueMagnitude plusTree := by
  -- PROOF_START P01-D061
  sorry
/-- The exact subtotal magnitudes in the paper's alternating integer example. -/
theorem p01_t4_plusminus_integer_example (m : ℕ) :
    let xs := p01AlternatingIntegers m
    let positive := xs.filter fun x => 0 ≤ x
    let negative := xs.filter fun x => x < 0
    let TtwoNMinusTwo := negative.sum
    |positive.sum| = (m : ℝ) * (m + 1) / 2 ∧
    |negative.sum| = (m : ℝ) * (m + 1) / 2 ∧
    |TtwoNMinusTwo| = (m : ℝ) * (m + 1) / 2 := by
  -- PROOF_START P01-D062
  sorry
/-- In increasing-magnitude recursive order, every exact prefix has magnitude at most `m`. -/
theorem p01_t4_alternating_increasing_prefix_bound (m : ℕ) :
    ∀ k : Fin (2 * m),
      |p01RecursiveSum (· + ·) (k.val + 1)
          (fun i => p01AlternatingVector m ⟨i.val, by omega⟩)| ≤ (m : ℝ) := by
  -- PROOF_START P01-D062B
  sorry
/-- Equation (3.8), with the source's two ordered sign blocks made explicit. -/
theorem p01_t4_eq_3_8
    (fp : P01StandardAddModel) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (neg : Fin p → ℝ) (nonneg : Fin q → ℝ)
    (hneg : ∀ i, neg i < 0) (hnonneg : ∀ i, 0 ≤ nonneg i)
    (hnegOrder : P01MagnitudeNondecreasing neg)
    (hnonnegOrder : P01MagnitudeNondecreasing nonneg)
    (hvalidNeg : P01GammaValid fp.u p) (hvalidPos : P01GammaValid fp.u q)
    (hu : fp.u < 1) :
    let sNeg := p01RecursiveSum fp.fl_add p neg
    let sPos := p01RecursiveSum fp.fl_add q nonneg
    let computed := fp.fl_add sPos sNeg
    let exact := p01ExactSum q nonneg + p01ExactSum p neg
    |computed - exact| ≤
      (∑ i : Fin p, |neg i| * p01Gamma fp.u (p - i.val)) +
      (∑ i : Fin q, |nonneg i| * p01Gamma fp.u (q - i.val)) +
      fp.u / (1 - fp.u) * |computed| := by
  -- PROOF_START P01-D065
  sorry
/-- Equation (3.9): FastTwoSum recovers the rounding error exactly in radix two. -/
theorem p01_t4_eq_3_9
    (fp : P01BinaryRoundModel) (a b : ℝ)
    (ha : P01BaseTwoRepresentable fp.precision a)
    (hb : P01BaseTwoRepresentable fp.precision b)
    (hmag : |b| ≤ |a|) :
    a + b = p01FastTwoSum fp a b + p01FastTwoSumCorrection fp a b := by
  -- PROOF_START P01-D069
  sorry
/-- The exact-recovery identity (3.9) fails in at least one nonbinary radix. -/
theorem p01_t4_fast_two_sum_not_all_radices :
    ∃ fp : P01RadixRoundModel,
      fp.radix ≠ 2 ∧
      ∃ a b : ℝ,
        P01BaseRepresentable fp.radix fp.precision a ∧
        P01BaseRepresentable fp.radix fp.precision b ∧
        |b| ≤ |a| ∧
        a + b ≠
          p01RadixFastTwoSum fp a b + p01RadixFastTwoSumCorrection fp a b := by
  -- PROOF_START P01-D069N
  sorry
/-- The rounded sum is nearest to `a+b`, and adding then rounding its correction cannot improve it. -/
theorem p01_t4_fast_two_sum_is_best
    (fp : P01BinaryRoundModel) (a b y : ℝ)
    (ha : P01BaseTwoRepresentable fp.precision a)
    (hb : P01BaseTwoRepresentable fp.precision b)
    (hmag : |b| ≤ |a|)
    (hy : P01BaseTwoRepresentable fp.precision y) :
    |a + b - p01FastTwoSum fp a b| ≤ |a + b - y| ∧
    fp.round
        (p01FastTwoSum fp a b + p01FastTwoSumCorrection fp a b) =
      p01FastTwoSum fp a b := by
  -- PROOF_START P01-D070
  sorry
/-- Equation (3.12), including its `nu ≤ 0.1` side condition and explicit coefficient. -/
theorem p01_t4_eq_3_12
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    ∃ μ : Fin n → ℝ,
      p01GlobalCorrectedSum fp.fl_add (List.ofFn v) =
        ∑ i : Fin n, (1 + μ i) * v i ∧
      ∀ i, |μ i| ≤ 2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2 := by
  -- PROOF_START P01-D078
  sorry
/-- The 2.1u bound for the indexed coefficients occurring in (3.12). -/
theorem p01_t4_eq_3_12_corollary
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ)
    (μ : Fin n → ℝ)
    (hrepresentation :
      p01GlobalCorrectedSum fp.fl_add (List.ofFn v) =
        ∑ i : Fin n, (1 + μ i) * v i)
    (hcoefficient :
      ∀ i, |μ i| ≤ 2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2)
    (hsmall : (n : ℝ) ^ 2 * fp.u ≤ 1 / 10) :
    ∀ i, |μ i| ≤ (21 / 10 : ℝ) * fp.u := by
  -- PROOF_START P01-D079
  sorry
/-- In every reported Table 4.1 recursive estimate, the ordering changes
only the coefficient: the full mean-square-error expression has power n^3. -/
theorem p01_t4_table_4_1_recursive_mse_power :
    ∀ (distribution : P01InputDistribution)
      (method : P01StatisticalMethod) (μ σ : ℝ) (n : ℕ),
      (method = .increasing ∨ method = .random ∨ method = .decreasing) →
      p01ReportedMSE distribution method μ σ n =
        p01MSECoefficient distribution method * μ ^ 2 *
          (n : ℝ) ^ 3 * σ ^ 2 := by
  -- PROOF_START P01-D087R
  sorry
/-- For either input distribution, the increasing recursive coefficient is
smallest and the decreasing recursive coefficient is largest. -/
theorem p01_t4_table_4_1_recursive_coefficient_ranking :
    ∀ distribution : P01InputDistribution,
      p01MSECoefficient distribution .increasing <
        p01MSECoefficient distribution .random ∧
      p01MSECoefficient distribution .random <
        p01MSECoefficient distribution .decreasing := by
  -- PROOF_START P01-D087C
  sorry
/-- Insertion and pairwise summation have quadratic rather than the cubic
mean-square-error growth of all three recursive orderings. -/
theorem p01_t4_table_4_1_insertion_pairwise_mse_power :
    p01MSEPower .insertion = 2 ∧
    p01MSEPower .pairwise = 2 ∧
    p01MSEPower .increasing = 3 ∧
    p01MSEPower .random = 3 ∧
    p01MSEPower .decreasing = 3 := by
  -- PROOF_START P01-D087P
  sorry
/-- For either input distribution, insertion has the smaller coefficient of
the two quadratic mean-square estimates. -/
theorem p01_t4_table_4_1_insertion_coefficient_smaller :
    ∀ distribution : P01InputDistribution,
      p01MSECoefficient distribution .insertion <
        p01MSECoefficient distribution .pairwise := by
  -- PROOF_START P01-D087I
  sorry
/-- Under (5.1), equation (2.4) has independent remainders on the first two inputs. -/
theorem p01_t4_no_guard_eq_2_4
    (fp : NoGuardAddModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : 2 ≤ n) (hvalid : P01GammaValid fp.u (n - 1)) :
    ∃ θ : Fin n → ℝ,
      P01NoGuardThetaWitness fp n v θ ∧
      |p01RecursiveSum fp.fl_add n v - p01ExactSum n v| =
        |∑ i : Fin n, v i * θ i| := by
  -- PROOF_START P01-D090A
  sorry
/-- Under (5.1), the equation-(2.5) pathwise error bound is unchanged. -/
theorem p01_t4_no_guard_eq_2_5
    (fp : NoGuardAddModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : 2 ≤ n) (hvalid : P01GammaValid fp.u (n - 1)) :
    |p01RecursiveSum fp.fl_add n v - p01ExactSum n v| ≤
      ∑ i : Fin n, |v i| * p01Gamma fp.u (p01RecursivePathLength n i) := by
  -- PROOF_START P01-D090B
  sorry
/-- Equation (2.6) remains valid under the componentwise no-guard model. -/
theorem p01_t4_no_guard_recursive_gamma_bound
    (fp : NoGuardAddModel) (n : ℕ) (v : Fin n → ℝ)
    (hvalid : P01GammaValid fp.u (n - 1)) :
    |p01RecursiveSum fp.fl_add n v - p01ExactSum n v| ≤
      p01Gamma fp.u (n - 1) * p01AbsoluteSum n v := by
  -- PROOF_START P01-D090
  sorry
/-- Equation (5.2), stated directly with the no-guard recursive algorithm. -/
theorem p01_t4_eq_5_2
    (fp : NoGuardAddModel) (n : ℕ) (v : Fin n → ℝ) :
    ∃ α β : Fin n → ℝ,
      P01NoGuardRecursiveWitness fp n v α β ∧
      p01RecursiveSum fp.fl_add n v - p01ExactSum n v =
        ∑ k : Fin n,
          if 0 < k.val then
            p01RecursiveSum fp.fl_add k.val
              (fun i => v ⟨i.val, by omega⟩) * α k + v k * β k
          else 0 := by
  -- PROOF_START P01-D091
  sorry
/-- Equation (5.3), using the existing transparent running-budget definition. -/
theorem p01_t4_eq_5_3
    (fp : NoGuardAddModel) (n : ℕ) (v : Fin n → ℝ) :
    |p01RecursiveSum fp.fl_add n v - p01ExactSum n v| ≤
      fp.u * noGuardRecursiveRunningBudget fp n v := by
  -- PROOF_START P01-D092
  sorry
/-- The right side of (5.3) is at most `3u * sum |S_hat_k| + O(u²)`. -/
theorem p01_t4_no_guard_eq53_coarse
    (family : P01NoGuardFamily) (n : ℕ) (v : Fin n → ℝ) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      ∀ u : P01PositiveRoundoff, (u : ℝ) ≤ ε →
      (u : ℝ) * noGuardRecursiveRunningBudget (family.model u) n v ≤
        3 * (u : ℝ) *
          (∑ k : Fin n,
            |p01NoGuardRecursivePrefix (family.model u) n v k|) +
        C * (u : ℝ) ^ 2 := by
  -- PROOF_START P01-D093
  sorry
/-- The first computed prefix occurring in (5.3) is `S_hat_1 = x_1`. -/
theorem p01_t4_no_guard_first_prefix_is_first_input
    (fp : NoGuardAddModel) (n : ℕ) (v : Fin n → ℝ) (hn : 0 < n) :
    p01NoGuardRecursivePrefix fp n v ⟨0, by omega⟩ = v ⟨0, by omega⟩ := by
  -- PROOF_START P01-D093A
  sorry
/-- Every no-guard addition tree has the two-perturbation local expansion. -/
theorem p01_t4_no_guard_tree_local_expansion
    (fp : NoGuardAddModel) (tree : P01SumTree) :
    P01NoGuardTreeWitness fp tree := by
  -- PROOF_START P01-D094E
  sorry
/-- The no-guard general-tree bound has `n`, rather than `n-1`, at first order. -/
theorem p01_t4_no_guard_general_tree_bound
    (fp : NoGuardAddModel) (tree : P01SumTree)
    (hvalid : P01GammaValid fp.u tree.leaves.length) :
    |P01SumTree.rounded fp.fl_add tree - P01SumTree.exact tree| ≤
      p01Gamma fp.u tree.leaves.length * (tree.leaves.map abs).sum := by
  -- PROOF_START P01-D094T
  sorry
/-- The pairwise bound (3.6) also remains valid without a guard digit. -/
theorem p01_t4_no_guard_pairwise_bound
    (fp : NoGuardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : P01GammaValid fp.u r) :
    |pairwiseSum fp.fl_add r v - p01ExactSum (2 ^ r) v| ≤
      p01Gamma fp.u r * p01AbsoluteSum (2 ^ r) v := by
  -- PROOF_START P01-D094P
  sorry
/-- In the no-guard version of (3.8), the two sign-block contributions are
unchanged and its final term is replaced by `u * (|Ŝ₊| + |Ŝ₋|)`. -/
theorem p01_t4_no_guard_plusminus_final_bound
    (fp : NoGuardAddModel) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (neg : Fin p → ℝ) (nonneg : Fin q → ℝ)
    (hneg : ∀ i, neg i < 0) (hnonneg : ∀ i, 0 ≤ nonneg i)
    (hnegOrder : P01MagnitudeNondecreasing neg)
    (hnonnegOrder : P01MagnitudeNondecreasing nonneg)
    (hvalidNeg : P01GammaValid fp.u p) (hvalidPos : P01GammaValid fp.u q) :
    let sNeg := p01RecursiveSum fp.fl_add p neg
    let sPos := p01RecursiveSum fp.fl_add q nonneg
    let computed := fp.fl_add sPos sNeg
    let exact := p01ExactSum q nonneg + p01ExactSum p neg
    |computed - exact| ≤
      (∑ i : Fin p, |neg i| * p01Gamma fp.u (p - i.val)) +
      (∑ i : Fin q, |nonneg i| * p01Gamma fp.u (q - i.val)) +
      fp.u * (|sPos| + |sNeg|) := by
  -- PROOF_START P01-D095
  sorry
/-- The replacement sign-block budget is bounded by `u * sum |xᵢ| + O(u²)`. -/
theorem p01_t4_no_guard_plusminus_input_bound
    (family : P01NoGuardFamily) (p q : ℕ)
    (neg : Fin p → ℝ) (nonneg : Fin q → ℝ) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      ∀ u : P01PositiveRoundoff, (u : ℝ) ≤ ε →
        let sNeg := p01RecursiveSum (family.model u).fl_add p neg
        let sPos := p01RecursiveSum (family.model u).fl_add q nonneg
        (u : ℝ) * (|sNeg| + |sPos|) ≤
          (u : ℝ) * (p01AbsoluteSum p neg + p01AbsoluteSum q nonneg) +
            C * (u : ℝ) ^ 2 := by
  -- PROOF_START P01-D095A
  sorry
/-- Error-free correction is not valid for every no-guard arithmetic. -/
theorem p01_t4_no_guard_fast_two_sum_failure :
    ∃ fp : NoGuardAddModel, ∃ a b : ℝ,
      |b| ≤ |a| ∧
      a + b ≠ fp.fl_add a b +
        (-(fp.fl_add (fp.fl_add a b) (-a) |> fun z => fp.fl_add z (-b))) := by
  -- PROOF_START P01-D096A
  sorry
/-- The paper's condition certifying a reference sum to single-precision relative accuracy. -/
theorem p01_t4_reference_sum_accuracy
    (reference : P01MatlabDoubleReferenceArithmetic)
    (n : ℕ) (v : Fin n → ℝ)
    (hn : n ≤ 5000)
    (hsingle : ∀ i, P01BaseTwoRepresentable 23 (v i))
    (hcert : (n : ℝ) * reference.addModel.u * p01AbsoluteSum n v <
      p01SingleUnitRoundoff * |p01ExactSum n v|) :
    |p01RecursiveSum reference.addModel.fl_add n v - p01ExactSum n v| <
      p01SingleUnitRoundoff * |p01ExactSum n v| := by
  -- PROOF_START P01-D101
  sorry
/-- The recursive orderings, insertion, and sign-separated summation have
normalized-error cap `n` to first order. -/
theorem p01_t4_first_order_R_cap_n
    (family : P01StandardAddFamily) (n : ℕ) (hn : 0 < n)
    (method : P01SummationMethod)
    (hmethod : method = .original ∨ method = .increasing ∨
      method = .decreasing ∨ method = .psum ∨ method = .insertion ∨
      method = .plusMinus) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧
      ∀ u : NNReal, (u : ℝ) ≤ η →
      ∀ (v : Fin n → ℝ) (result : ℝ),
        P01InputsRepresentableForAdd (family.model u) n v →
        P01StandardMethodEvaluation (family.model u) method v result →
        |result - p01ExactSum n v| ≤
          ((n : ℝ) * (u : ℝ) + C * (u : ℝ) ^ 2) * p01AbsoluteSum n v := by
  -- PROOF_START P01-D103N
  sorry
/-- For the paper's power-of-two pairwise trees, pairwise summation has
normalized-error cap `log₂ n = r` to first order when `n = 2^r`. -/
theorem p01_t4_first_order_R_cap_pairwise
    (family : P01StandardAddFamily) (r : ℕ) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧
      ∀ u : NNReal, (u : ℝ) ≤ η →
      ∀ (v : Fin (2 ^ r) → ℝ) (result : ℝ),
        P01InputsRepresentableForAdd (family.model u) (2 ^ r) v →
        P01StandardMethodEvaluation (family.model u) .pairwise v result →
        |result - p01ExactSum (2 ^ r) v| ≤
          ((r : ℝ) * (u : ℝ) + C * (u : ℝ) ^ 2) *
            p01AbsoluteSum (2 ^ r) v := by
  -- PROOF_START P01-D103P
  sorry
/-- Decreasing order has the smallest reported relative error in Table 6.1. -/
theorem p01_t4_table_6_1_decreasing_best :
    ∀ method : P01SummationMethod, method ≠ .decreasing →
      (p01Table61 .decreasing).relativeError <
        (p01Table61 method).relativeError := by
  -- PROOF_START P01-D104C
  sorry
/-- Compensated summation gives no reported improvement over original order in Table 6.1. -/
theorem p01_t4_table_6_1_compensated_no_improvement :
    (p01Table61 .compensated).relativeError =
      (p01Table61 .original).relativeError := by
  -- PROOF_START P01-D104N
  sorry
/-- Sign-separated summation has the largest reported relative error in Table 6.1. -/
theorem p01_t4_table_6_1_plusminus_worst :
    ∀ method : P01SummationMethod, method ≠ .plusMinus →
      (p01Table61 method).relativeError <
        (p01Table61 .plusMinus).relativeError := by
  -- PROOF_START P01-D104W
  sorry
/-- Psum has the smallest reported relative error at both Table 6.2 sizes. -/
theorem p01_t4_table_6_2_psum_best :
    (∀ method : P01SummationMethod, method ≠ .psum →
      (p01Table62_2048 .psum).relativeError <
        (p01Table62_2048 method).relativeError) ∧
    (∀ method : P01SummationMethod, method ≠ .psum →
      (p01Table62_4096 .psum).relativeError <
        (p01Table62_4096 method).relativeError) := by
  -- PROOF_START P01-D106C
  sorry
/-- Sign-separated summation has the largest reported relative error at both Table 6.2 sizes. -/
theorem p01_t4_table_6_2_plusminus_worst :
    (∀ method : P01SummationMethod, method ≠ .plusMinus →
      (p01Table62_2048 method).relativeError <
        (p01Table62_2048 .plusMinus).relativeError) ∧
    (∀ method : P01SummationMethod, method ≠ .plusMinus →
      (p01Table62_4096 method).relativeError <
        (p01Table62_4096 .plusMinus).relativeError) := by
  -- PROOF_START P01-D106W
  sorry
/-- Every reported Table 6.3 decreasing-order error exceeds its increasing-order error. -/
theorem p01_t4_table_6_3_comparison :
    ∀ entry ∈ p01Table63, entry.increasingError < entry.decreasingError := by
  -- PROOF_START P01-D108C
  sorry
/-- Pairwise summation outperforms both recursive orders in the two printed Table 6.4 rows. -/
theorem p01_t4_table_6_4_pairwise_outperforms_recursive :
    (p01Table64_2048 .pairwise).map P01ExperimentMetrics.relativeError <
      (p01Table64_2048 .increasing).map P01ExperimentMetrics.relativeError ∧
    (p01Table64_2048 .pairwise).map P01ExperimentMetrics.relativeError <
      (p01Table64_2048 .decreasing).map P01ExperimentMetrics.relativeError ∧
    (p01Table64_4096 .pairwise).map P01ExperimentMetrics.relativeError <
      (p01Table64_4096 .increasing).map P01ExperimentMetrics.relativeError ∧
    (p01Table64_4096 .pairwise).map P01ExperimentMetrics.relativeError <
      (p01Table64_4096 .decreasing).map P01ExperimentMetrics.relativeError := by
  -- PROOF_START P01-D109C
  sorry
/-- Compensated summation has zero reported error in both printed Table 6.4 rows. -/
theorem p01_t4_table_6_4_compensated_rows_zero :
    (p01Table64_2048 .compensated).map P01ExperimentMetrics.relativeError = some 0 ∧
    (p01Table64_4096 .compensated).map P01ExperimentMetrics.relativeError = some 0 := by
  -- PROOF_START P01-D109Z
  sorry
/-- The printed inequality `cond(T,x) ≤ κ∞(T)`. -/
theorem p01_t4_componentwise_condition_le_normwise
    {n : ℕ} (T Tinv : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hinvLeft : ∀ i j, ∑ k : Fin n, Tinv i k * T k j =
      if i = j then 1 else 0)
    (hx : p01VectorInfNorm x ≠ 0) :
    p01ComponentwiseTriangularCondition T Tinv x ≤
      p01NormwiseMatrixCondition T Tinv := by
  -- PROOF_START P01-D117
  sorry
/-- The zero-sum counterexample refutes a uniform bound for this relational method. -/
theorem p01_t4_no_uniform_relative_bound_from_zero_sum
    (fp : P01BinaryRoundModel) (hprecision : fp.precision = 23) :
    ∃ n : ℕ,
      ¬ P01UniformRelativeErrorBound (p01BinaryUnitRoundoff fp)
        (P01DecreasingCompensatedEvaluation fp (n := n)) := by
  -- PROOF_START P01-D121
  sorry
/-- For decreasing-order compensated summation, zero exact sum can have nonzero error. -/
theorem p01_t4_decreasing_compensated_zero_sum_counterexample
    (fp : P01BinaryRoundModel) (hprecision : fp.precision = 23) :
    ∃ n : ℕ, ∃ v : Fin n → ℝ, ∃ result : ℝ,
      (∀ i, P01BaseTwoRepresentable fp.precision (v i)) ∧
      p01ExactSum n v = 0 ∧
      P01DecreasingCompensatedEvaluation fp v result ∧ result ≠ 0 := by
  -- PROOF_START P01-D121A
  sorry
/-- Any permutation-invariant summation method preserves permutations of Rosenbrock pairs. -/
theorem p01_t4_permutation_invariant_preserves_rosenbrock_symmetry
    (method : (n : ℕ) → (Fin n → ℝ) → ℝ)
    (hinvariant : P01PermutationInvariant method)
    (m : ℕ) (x : Fin (2 * m) → ℝ) (p : Equiv.Perm (Fin m)) :
    method m (p01Permuted (p01RosenbrockTerms m x) p) =
      method m (p01RosenbrockTerms m x) := by
  -- PROOF_START P01-D128
  sorry

/-- The concrete tie-broken increasing procedure is independent of the input permutation. -/
theorem p01_t4_increasing_sign_tie_is_permutation_invariant
    (flAdd : ℝ → ℝ → ℝ)
    (inputs₁ inputs₂ ordered₁ ordered₂ : List ℝ)
    (hinputs : inputs₁.Perm inputs₂)
    (hperm₁ : ordered₁.Perm inputs₁) (hperm₂ : ordered₂.Perm inputs₂)
    (hordered₁ : P01IncreasingSignOrdered ordered₁)
    (hordered₂ : P01IncreasingSignOrdered ordered₂) :
    p01RecursiveList flAdd ordered₁ = p01RecursiveList flAdd ordered₂ := by
  -- PROOF_START P01-D128A
  sorry
end HighamBench
