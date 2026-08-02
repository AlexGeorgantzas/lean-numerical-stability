import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Statistics.SampleVariance.Core
import NumStability.Analysis.Statistics.SampleVariance.TwoPass
import NumStability.Analysis.Statistics.SampleVariance.Updating
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Source.Higham.Chapter01.Problem07.SampleVarianceConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter01.Problem10.TwoPassSampleVariance.Bounds
import NumStability.Source.Higham.Chapter01.Section09.SampleVariance.Examples

-- Analysis/SampleVariance.lean
--
-- Exact sample-variance algebra for Higham Chapter 1, Section 1.9.
















namespace NumStability

open scoped BigOperators Topology

/-!
# Sample-Variance Algebra

Higham Chapter 1, Section 1.9 contrasts mathematically equivalent formulae
for the sample variance.  This file records the exact real-arithmetic
identities behind formulas (1.4) and (1.5), plus the shifted one-pass identity.
The floating-point stability bounds for the corresponding algorithms are
separate obligations.
-/
























































































































































































































































































































































































































































































































































































































































































































































































private lemma gamma_le_two_mul_nu_of_mul_u_le_half (fp : FPModel) (n : ℕ)
    (hcap : (n : ℝ) * fp.u ≤ (1 : ℝ) / 2) :
    gamma fp n ≤ 2 * ((n : ℝ) * fp.u) := by
  unfold gamma
  set a : ℝ := (n : ℝ) * fp.u with ha
  have ha_nonneg : 0 ≤ a := by
    rw [ha]
    exact mul_nonneg (by exact_mod_cast n.zero_le) fp.u_nonneg
  have hden_pos : 0 < 1 - a := by linarith
  rw [div_le_iff₀ hden_pos]
  nlinarith





























































/-- Source `O(u^2)` certificate for Problem 1.10: with fixed data and
`(n+3)u <= 1/2`, the named higher-order remainder after the source linear term
`(n+3)u` is bounded by an explicit quadratic expression in the unit roundoff. -/
theorem flSampleVarianceTwoPassProblem110Remainder_le_quadratic_bound {n : ℕ}
    (fp : FPModel) (x : Fin n → ℝ)
    (hn : 1 < n) (hVpos : 0 < sampleVarianceTwoPass x)
    (hγ : gammaValid fp (n + 3))
    (hcap : (((n + 3 : ℕ) : ℝ) * fp.u) ≤ (1 : ℝ) / 2) :
    flSampleVarianceTwoPassProblem110Remainder fp x ≤
      flSampleVarianceTwoPassProblem110RemainderQuadraticBound fp x := by
  set L : ℝ := ((n + 3 : ℕ) : ℝ) * fp.u with hL
  set A : ℝ := (∑ i : Fin n, |x i|) / (n : ℝ) with hA
  set B : ℝ := flSampleVarianceTwoPassProblem110MeanQuadraticBound fp x with hB
  set B2 : ℝ := (((n : ℝ) * (2 * ((n : ℝ) * fp.u) * A) ^ 2 /
      ((n : ℝ) - 1)) / sampleVarianceTwoPass x) with hB2
  have hn_pos_real : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hn)
  have hn_nonneg_real : 0 ≤ (n : ℝ) := le_of_lt hn_pos_real
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact div_nonneg (Finset.sum_nonneg (fun i hi => abs_nonneg (x i)))
      (le_of_lt hn_pos_real)
  have hcap_n : (n : ℝ) * fp.u ≤ (1 : ℝ) / 2 := by
    have hnle : (n : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right n 3)
    exact le_trans (mul_le_mul_of_nonneg_right hnle fp.u_nonneg) hcap
  have hγn : gammaValid fp n := gammaValid_mono fp (Nat.le_add_right n 3) hγ
  have hgamma_n_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hγn
  have hgamma_n_le : gamma fp n ≤ 2 * ((n : ℝ) * fp.u) :=
    gamma_le_two_mul_nu_of_mul_u_le_half fp n hcap_n
  have hleft_nonneg : 0 ≤ gamma fp n * A := mul_nonneg hgamma_n_nonneg hA_nonneg
  have hmul_le :
      gamma fp n * A ≤ 2 * ((n : ℝ) * fp.u) * A :=
    mul_le_mul_of_nonneg_right hgamma_n_le hA_nonneg
  have hsquare_le :
      (gamma fp n * A) ^ 2 ≤ (2 * ((n : ℝ) * fp.u) * A) ^ 2 := by
    nlinarith
  have hB_le_B2 : B ≤ B2 := by
    rw [hB, hB2, hA]
    have hnum_le :
        (n : ℝ) *
            (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 ≤
          (n : ℝ) *
            (2 * ((n : ℝ) * fp.u) * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left (by simpa [hA] using hsquare_le) hn_nonneg_real
    have hdiv1 :
        (n : ℝ) *
            (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
            ((n : ℝ) - 1) ≤
          (n : ℝ) *
            (2 * ((n : ℝ) * fp.u) * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
            ((n : ℝ) - 1) :=
      div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)
    exact div_le_div_of_nonneg_right hdiv1 (le_of_lt hVpos)
  have hB_nonneg : 0 ≤ B := by
    rw [hB]
    exact flSampleVarianceTwoPassProblem110MeanQuadraticBound_nonneg fp x hn hVpos
  have hG_nonneg : 0 ≤ gamma fp (n + 3) := gamma_nonneg fp hγ
  have hG_le_one : gamma fp (n + 3) ≤ 1 := by
    have hle : gamma fp (n + 3) ≤
        2 * ((((n + 3 : ℕ) : ℝ) * fp.u) : ℝ) :=
      gamma_le_two_mul_nu_of_mul_u_le_half fp (n + 3) hcap
    nlinarith
  have hGB_le_B : gamma fp (n + 3) * B ≤ B := by
    nlinarith
  have hL_nonneg : 0 ≤ L := by
    rw [hL]
    exact mul_nonneg (by exact_mod_cast (n + 3).zero_le) fp.u_nonneg
  have hLden_pos : 0 < 1 - L := by linarith
  have hRquad :
      L ^ 2 / (1 - L) ≤ 2 * L ^ 2 := by
    rw [div_le_iff₀ hLden_pos]
    nlinarith
  have htotal :
      L ^ 2 / (1 - L) + B + gamma fp (n + 3) * B ≤ 2 * (L ^ 2 + B2) := by
    nlinarith
  simpa [flSampleVarianceTwoPassProblem110RemainderQuadraticBound,
    flSampleVarianceTwoPassProblem110Remainder,
    flSampleVarianceTwoPassProblem110MeanQuadraticBound, hL, hA, hB, hB2]
    using htotal



























































































































































































































private theorem abs_error_add_perturbed_term_rounding
    (u γ A T θ δ y : ℝ) (hu : 0 ≤ u) (hγ : 0 ≤ γ)
    (hθ : |θ| ≤ γ) (hδ : |δ| ≤ u)
    (hy : y = (A + T * (1 + θ)) * (1 + δ)) :
    |y - (A + T)| ≤ |A + T| * u + |T| * γ * (1 + u) := by
  subst y
  have h1δ : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
      _ = 1 + |δ| := by norm_num
      _ ≤ 1 + u := by linarith
  have hterm1 : |A + T| * |δ| ≤ |A + T| * u :=
    mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
  have hterm2a : |T| * |θ| ≤ |T| * γ :=
    mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
  have hTγnonneg : 0 ≤ |T| * γ :=
    mul_nonneg (abs_nonneg _) hγ
  have hrightnonneg : 0 ≤ 1 + u := by linarith
  have hleftfactor_nonneg : 0 ≤ |1 + δ| := abs_nonneg _
  have hterm2 : |T| * |θ| * |1 + δ| ≤ |T| * γ * (1 + u) :=
    mul_le_mul hterm2a h1δ hleftfactor_nonneg hTγnonneg
  have hdiff :
      (A + T * (1 + θ)) * (1 + δ) - (A + T) =
        (A + T) * δ + T * θ * (1 + δ) := by
    ring
  calc
    |(A + T * (1 + θ)) * (1 + δ) - (A + T)|
        = |(A + T) * δ + T * θ * (1 + δ)| := by rw [hdiff]
    _ ≤ |(A + T) * δ| + |T * θ * (1 + δ)| := abs_add_le _ _
    _ = |A + T| * |δ| + |T| * |θ| * |1 + δ| := by
          rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |A + T| * u + |T| * γ * (1 + u) :=
          add_le_add hterm1 hterm2
































/-- Absolute-error form of the rounded one-step mean update. -/
theorem flPrefixMeanStep_abs_error_le
    (fp : FPModel) (M x : ℝ) (k : ℕ) (hγ : gammaValid fp 2) :
    |flPrefixMeanStep fp M x k - prefixMeanStepExact M x k| ≤
      |prefixMeanStepExact M x k| * fp.u +
        |(x - M) / ((k + 1 : ℕ) : ℝ)| * gamma fp 2 * (1 + fp.u) := by
  obtain ⟨θ, δ, hθ, hδ, hfl⟩ :=
    flPrefixMeanStep_eq_exact_with_local_errors fp M x k hγ
  have hγnonneg : 0 ≤ gamma fp 2 := gamma_nonneg fp hγ
  exact
    (abs_error_add_perturbed_term_rounding fp.u (gamma fp 2) M
      ((x - M) / ((k + 1 : ℕ) : ℝ)) θ δ
      (flPrefixMeanStep fp M x k) fp.u_nonneg hγnonneg hθ hδ
      (by simpa using hfl))

/-- Instantiation of `flPrefixMeanStep_abs_error_le` against the exact prefix
mean recurrence. -/
theorem flPrefixMeanStep_abs_error_le_prefixMean_succ
    (fp : FPModel) (x : ℕ → ℝ) {k : ℕ}
    (hk : (k : ℝ) ≠ 0) (hγ : gammaValid fp 2) :
    |flPrefixMeanStep fp (prefixMean x k) (x k) k - prefixMean x (k + 1)| ≤
      |prefixMean x (k + 1)| * fp.u +
        |(x k - prefixMean x k) / ((k + 1 : ℕ) : ℝ)| *
          gamma fp 2 * (1 + fp.u) := by
  have hbase :=
    flPrefixMeanStep_abs_error_le fp (prefixMean x k) (x k) k hγ
  simpa [prefixMeanStepExact, prefixMean_succ x hk] using hbase







































































/-- Multi-step rounded-prefix-mean theorem for Higham §1.9's update
recurrence.  The bound is explicit and recursive: each previous mean error is
contracted by `k/(k+1)`, then the local rounded correction and final rounded
addition costs are added. -/
theorem flPrefixMeanTrajectory_abs_error_le_budget
    (fp : FPModel) (x : ℕ → ℝ) (hγ : gammaValid fp 2) :
    ∀ k : ℕ,
      |flPrefixMeanTrajectory fp x k - prefixMean x k| ≤
        flPrefixMeanTrajectoryAbsErrorBudget fp x k := by
  intro k
  induction k with
  | zero =>
      simp [flPrefixMeanTrajectory, flPrefixMeanTrajectoryAbsErrorBudget,
        prefixMean]
  | succ k ih =>
      set Mhat : ℝ := flPrefixMeanTrajectory fp x k with hMhat
      set Mexact : ℝ := prefixMean x k with hMexact
      set xk : ℝ := x k with hxk
      set coeff : ℝ := (k : ℝ) / ((k + 1 : ℕ) : ℝ) with hcoeff
      set localErr : ℝ :=
        |prefixMeanStepExact Mhat xk k| * fp.u +
          |(xk - Mhat) / ((k + 1 : ℕ) : ℝ)| *
            gamma fp 2 * (1 + fp.u) with hlocalErr
      have hstepLocal :
          |flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mhat xk k| ≤
            localErr := by
        rw [hlocalErr]
        simpa [hMhat, hxk] using flPrefixMeanStep_abs_error_le fp Mhat xk k hγ
      have hstepExact :
          prefixMeanStepExact Mexact xk k = prefixMean x (k + 1) := by
        rw [hMexact, hxk]
        exact prefixMeanStepExact_prefixMean_eq_succ x k
      have hcoef_nonneg : 0 ≤ coeff := by
        rw [hcoeff]
        exact div_nonneg (by exact_mod_cast Nat.zero_le k)
          (le_of_lt (by exact_mod_cast Nat.succ_pos k))
      have hprev :
          |Mhat - Mexact| ≤ flPrefixMeanTrajectoryAbsErrorBudget fp x k := by
        simpa [hMhat, hMexact] using ih
      have hstepSensitive :
          |prefixMeanStepExact Mhat xk k - prefixMeanStepExact Mexact xk k| ≤
            coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k := by
        have hsub :=
          prefixMeanStepExact_sub_prefixMeanStepExact Mhat Mexact xk k
        calc
          |prefixMeanStepExact Mhat xk k - prefixMeanStepExact Mexact xk k|
              = |coeff * (Mhat - Mexact)| := by rw [hsub, hcoeff]
          _ = coeff * |Mhat - Mexact| := by
              rw [abs_mul, abs_of_nonneg hcoef_nonneg]
          _ ≤ coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k :=
              mul_le_mul_of_nonneg_left hprev hcoef_nonneg
      have htriangle :
          |flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mexact xk k| ≤
            localErr + coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k := by
        have hsplit :
            flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mexact xk k =
              (flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mhat xk k) +
                (prefixMeanStepExact Mhat xk k -
                  prefixMeanStepExact Mexact xk k) := by
          ring
        calc
          |flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mexact xk k|
              = |(flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mhat xk k) +
                  (prefixMeanStepExact Mhat xk k -
                    prefixMeanStepExact Mexact xk k)| := by rw [hsplit]
          _ ≤ |flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mhat xk k| +
              |prefixMeanStepExact Mhat xk k -
                prefixMeanStepExact Mexact xk k| := abs_add_le _ _
          _ ≤ localErr + coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k :=
              add_le_add hstepLocal hstepSensitive
      have hbudget :
          flPrefixMeanTrajectoryAbsErrorBudget fp x (k + 1) =
            coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k + localErr := by
        simp [flPrefixMeanTrajectoryAbsErrorBudget, hcoeff, hlocalErr, hMhat, hxk]
        ring
      calc
        |flPrefixMeanTrajectory fp x (k + 1) - prefixMean x (k + 1)|
            = |flPrefixMeanStep fp Mhat xk k - prefixMean x (k + 1)| := by
              simp [flPrefixMeanTrajectory, hMhat, hxk]
        _ = |flPrefixMeanStep fp Mhat xk k -
                prefixMeanStepExact Mexact xk k| := by
              rw [hstepExact]
        _ ≤ localErr + coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k :=
              htriangle
        _ = flPrefixMeanTrajectoryAbsErrorBudget fp x (k + 1) := by
              rw [hbudget]
              ring































































































































/-- Absolute-error form of the rounded corrected-sum-of-squares update. -/
theorem flPrefixCorrectedSumSquaresStep_abs_error_le
    (fp : FPModel) (Q M x : ℝ) (k : ℕ) (hγ : gammaValid fp 5) :
    |flPrefixCorrectedSumSquaresStep fp Q M x k -
        prefixCorrectedSumSquaresStepExact Q M x k| ≤
      |prefixCorrectedSumSquaresStepExact Q M x k| * fp.u +
        |(k : ℝ) / ((k + 1 : ℕ) : ℝ) * (x - M) ^ 2| *
          gamma fp 5 * (1 + fp.u) := by
  obtain ⟨θ, δ, hθ, hδ, hfl⟩ :=
    flPrefixCorrectedSumSquaresStep_eq_exact_with_local_errors fp Q M x k hγ
  have hγnonneg : 0 ≤ gamma fp 5 := gamma_nonneg fp hγ
  exact
    (abs_error_add_perturbed_term_rounding fp.u (gamma fp 5) Q
      ((k : ℝ) / ((k + 1 : ℕ) : ℝ) * (x - M) ^ 2) θ δ
      (flPrefixCorrectedSumSquaresStep fp Q M x k)
      fp.u_nonneg hγnonneg hθ hδ (by simpa using hfl))

/-- Instantiation of `flPrefixCorrectedSumSquaresStep_abs_error_le` against
the exact prefix corrected-sum-of-squares recurrence. -/
theorem flPrefixCorrectedSumSquaresStep_abs_error_le_prefix_succ
    (fp : FPModel) (x : ℕ → ℝ) {k : ℕ}
    (hk : (k : ℝ) ≠ 0) (hγ : gammaValid fp 5) :
    |flPrefixCorrectedSumSquaresStep fp
        (prefixCorrectedSumSquares x k) (prefixMean x k) (x k) k -
        prefixCorrectedSumSquares x (k + 1)| ≤
      |prefixCorrectedSumSquares x (k + 1)| * fp.u +
        |(k : ℝ) / ((k + 1 : ℕ) : ℝ) *
          (x k - prefixMean x k) ^ 2| * gamma fp 5 * (1 + fp.u) := by
  have hbase :=
    flPrefixCorrectedSumSquaresStep_abs_error_le fp
      (prefixCorrectedSumSquares x k) (prefixMean x k) (x k) k hγ
  simpa [prefixCorrectedSumSquaresStepExact,
    prefixCorrectedSumSquares_succ x hk] using hbase





































































/-- Multi-step rounded corrected-sum-of-squares theorem for Higham §1.9's
update recurrence.  The computed `Q_k` is generated using the rounded prefix
means, and the budget charges previous `Q` error, previous mean error, and the
local five-operation update plus final rounded addition at every step. -/
theorem flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget
    (fp : FPModel) (x : ℕ → ℝ) (hγ : gammaValid fp 5) :
    ∀ k : ℕ,
      |flPrefixCorrectedSumSquaresTrajectory fp x k -
          prefixCorrectedSumSquares x k| ≤
        flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k := by
  intro k
  induction k with
  | zero =>
      simp [flPrefixCorrectedSumSquaresTrajectory,
        flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget,
        prefixCorrectedSumSquares]
  | succ k ih =>
      have hγ2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hγ
      set Qhat : ℝ := flPrefixCorrectedSumSquaresTrajectory fp x k with hQhat
      set Qexact : ℝ := prefixCorrectedSumSquares x k with hQexact
      set Mhat : ℝ := flPrefixMeanTrajectory fp x k with hMhat
      set Mexact : ℝ := prefixMean x k with hMexact
      set xk : ℝ := x k with hxk
      set coeff : ℝ := (k : ℝ) / ((k + 1 : ℕ) : ℝ) with hcoeff
      set localErr : ℝ :=
        |prefixCorrectedSumSquaresStepExact Qhat Mhat xk k| * fp.u +
          |coeff * (xk - Mhat) ^ 2| * gamma fp 5 * (1 + fp.u)
        with hlocalErr
      set meanSens : ℝ :=
        |coeff| * flPrefixMeanTrajectoryAbsErrorBudget fp x k *
          (|xk - Mhat| + |xk - Mexact|)
        with hmeanSens
      have hstepLocal :
          |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
              prefixCorrectedSumSquaresStepExact Qhat Mhat xk k| ≤
            localErr := by
        rw [hlocalErr]
        simpa [hQhat, hMhat, hxk, hcoeff] using
          flPrefixCorrectedSumSquaresStep_abs_error_le fp Qhat Mhat xk k hγ
      have hstepExact :
          prefixCorrectedSumSquaresStepExact Qexact Mexact xk k =
            prefixCorrectedSumSquares x (k + 1) := by
        rw [hQexact, hMexact, hxk]
        exact prefixCorrectedSumSquaresStepExact_prefix_eq_succ x k
      have hQprev :
          |Qhat - Qexact| ≤
            flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k := by
        simpa [hQhat, hQexact] using ih
      have hMprev :
          |Mhat - Mexact| ≤
            flPrefixMeanTrajectoryAbsErrorBudget fp x k := by
        simpa [hMhat, hMexact] using
          flPrefixMeanTrajectory_abs_error_le_budget fp x hγ2 k
      have hdevSum_nonneg :
          0 ≤ |xk - Mhat| + |xk - Mexact| :=
        add_nonneg (abs_nonneg _) (abs_nonneg _)
      have hmeanTerm :
          |coeff| * |Mhat - Mexact| * (|xk - Mhat| + |xk - Mexact|) ≤
            meanSens := by
        have hfirst :
            |coeff| * |Mhat - Mexact| ≤
              |coeff| * flPrefixMeanTrajectoryAbsErrorBudget fp x k :=
          mul_le_mul_of_nonneg_left hMprev (abs_nonneg _)
        have hmul :=
          mul_le_mul_of_nonneg_right hfirst hdevSum_nonneg
        simpa [hmeanSens, mul_assoc] using hmul
      have hsensitive :
          |prefixCorrectedSumSquaresStepExact Qhat Mhat xk k -
              prefixCorrectedSumSquaresStepExact Qexact Mexact xk k| ≤
            flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
              meanSens := by
        have hbase :=
          prefixCorrectedSumSquaresStepExact_abs_sub_le
            Qhat Qexact Mhat Mexact xk k
        calc
          |prefixCorrectedSumSquaresStepExact Qhat Mhat xk k -
              prefixCorrectedSumSquaresStepExact Qexact Mexact xk k|
              ≤ |Qhat - Qexact| +
                  |coeff| * |Mhat - Mexact| *
                    (|xk - Mhat| + |xk - Mexact|) := by
                simpa [hcoeff] using hbase
          _ ≤ flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
              meanSens :=
                add_le_add hQprev hmeanTerm
      have htriangle :
          |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
              prefixCorrectedSumSquaresStepExact Qexact Mexact xk k| ≤
            localErr +
              (flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
                meanSens) := by
        have hsplit :
            flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                prefixCorrectedSumSquaresStepExact Qexact Mexact xk k =
              (flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                prefixCorrectedSumSquaresStepExact Qhat Mhat xk k) +
              (prefixCorrectedSumSquaresStepExact Qhat Mhat xk k -
                prefixCorrectedSumSquaresStepExact Qexact Mexact xk k) := by
          ring
        calc
          |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
              prefixCorrectedSumSquaresStepExact Qexact Mexact xk k|
              =
                |(flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                    prefixCorrectedSumSquaresStepExact Qhat Mhat xk k) +
                  (prefixCorrectedSumSquaresStepExact Qhat Mhat xk k -
                    prefixCorrectedSumSquaresStepExact Qexact Mexact xk k)| := by
                rw [hsplit]
          _ ≤ |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                  prefixCorrectedSumSquaresStepExact Qhat Mhat xk k| +
                |prefixCorrectedSumSquaresStepExact Qhat Mhat xk k -
                  prefixCorrectedSumSquaresStepExact Qexact Mexact xk k| :=
                abs_add_le _ _
          _ ≤ localErr +
              (flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
                meanSens) :=
                add_le_add hstepLocal hsensitive
      have hbudget :
          flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x (k + 1) =
            localErr +
              (flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
                meanSens) := by
        simp [flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget, hlocalErr,
          hmeanSens, hQhat, hMhat, hMexact, hxk, hcoeff]
      calc
        |flPrefixCorrectedSumSquaresTrajectory fp x (k + 1) -
            prefixCorrectedSumSquares x (k + 1)|
            =
              |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                prefixCorrectedSumSquares x (k + 1)| := by
              simp [flPrefixCorrectedSumSquaresTrajectory, hQhat, hMhat, hxk]
        _ =
              |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                prefixCorrectedSumSquaresStepExact Qexact Mexact xk k| := by
              rw [hstepExact]
        _ ≤ localErr +
            (flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
              meanSens) :=
              htriangle
        _ = flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x (k + 1) :=
              hbudget.symm










































/-- End-to-end rounded-update theorem for Higham §1.9's recurrence-based
sample variance.  The rounded mean and `Q` trajectories are charged by the
recursive `Q` budget, and the final division by `n-1` contributes one more
rounded-division term. -/
theorem flSampleVarianceUpdate_abs_error_le_budget
    (fp : FPModel) (x : ℕ → ℝ) {n : ℕ} (hn : 1 < n)
    (hγ : gammaValid fp 5) :
    |flSampleVarianceUpdate fp x n - sampleVariancePrefix x n| ≤
      flSampleVarianceUpdateAbsErrorBudget fp x n := by
  set Qhat : ℝ := flPrefixCorrectedSumSquaresTrajectory fp x n with hQhat
  set Qexact : ℝ := prefixCorrectedSumSquares x n with hQexact
  set d : ℝ := (n : ℝ) - 1 with hd
  have hden : d ≠ 0 := by
    have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
    rw [hd]
    linarith
  have hdenAbs_pos : 0 < |d| := abs_pos.mpr hden
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div Qhat d hden
  have hQprev :
      |Qhat - Qexact| ≤
        flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x n := by
    simpa [hQhat, hQexact] using
      flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget fp x hγ n
  have hquot :
      |Qhat / d - Qexact / d| ≤
        flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x n / |d| := by
    calc
      |Qhat / d - Qexact / d| = |(Qhat - Qexact) / d| := by
        field_simp [hden]
      _ = |Qhat - Qexact| / |d| := by
        rw [abs_div]
      _ ≤ flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x n / |d| :=
        div_le_div_of_nonneg_right hQprev (le_of_lt hdenAbs_pos)
  have hround :
      |Qhat / d * (1 + δ) - Qhat / d| ≤ |Qhat / d| * fp.u := by
    calc
      |Qhat / d * (1 + δ) - Qhat / d|
          = |Qhat / d * δ| := by ring_nf
      _ = |Qhat / d| * |δ| := by rw [abs_mul]
      _ ≤ |Qhat / d| * fp.u :=
        mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
  have hsplit :
      Qhat / d * (1 + δ) - Qexact / d =
        (Qhat / d * (1 + δ) - Qhat / d) +
          (Qhat / d - Qexact / d) := by
    ring
  calc
    |flSampleVarianceUpdate fp x n - sampleVariancePrefix x n|
        = |Qhat / d * (1 + δ) - Qexact / d| := by
          simp [flSampleVarianceUpdate, sampleVariancePrefix, ← hQhat,
            ← hQexact, ← hd, hdiv]
    _ = |(Qhat / d * (1 + δ) - Qhat / d) +
          (Qhat / d - Qexact / d)| := by
          rw [hsplit]
    _ ≤ |Qhat / d * (1 + δ) - Qhat / d| + |Qhat / d - Qexact / d| :=
          abs_add_le _ _
    _ ≤ |Qhat / d| * fp.u +
        flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x n / |d| :=
          add_le_add hround hquot
    _ = flSampleVarianceUpdateAbsErrorBudget fp x n := by
          simp [flSampleVarianceUpdateAbsErrorBudget, hQhat, hd]
          ring_nf



















































































































































-- ============================================================
-- Concrete binary32 one-pass trace for Higham §1.9
-- ============================================================

private abbrev sampleVarianceIeeeSingleFormat : FloatingPointFormat :=
  FloatingPointFormat.ieeeSingleFormat

private theorem ieeeSingleFiniteSystem_of_normalizedExponentRepresentation
    {x : ℝ} {e : ℤ}
    (h : sampleVarianceIeeeSingleFormat.normalizedExponentRepresentation x e) :
    sampleVarianceIeeeSingleFormat.finiteSystem x :=
  Or.inr (Or.inl
    (FloatingPointFormat.normalizedExponentRepresentation_normalizedSystem h))

private theorem ieeeSingle_finiteSystem_zero :
    sampleVarianceIeeeSingleFormat.finiteSystem (0 : ℝ) :=
  Or.inl rfl

private theorem ieeeSingle_finiteSystem_10000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (10000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 14)
  refine ⟨false, 10240000, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_10001 :
    sampleVarianceIeeeSingleFormat.finiteSystem (10001 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 14)
  refine ⟨false, 10241024, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_10002 :
    sampleVarianceIeeeSingleFormat.finiteSystem (10002 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 14)
  refine ⟨false, 10242048, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_20001 :
    sampleVarianceIeeeSingleFormat.finiteSystem (20001 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 15)
  refine ⟨false, 10240512, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_30003 :
    sampleVarianceIeeeSingleFormat.finiteSystem (30003 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 15)
  refine ⟨false, 15361536, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_100000000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (100000000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 27)
  refine ⟨false, 12500000, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_200020000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (200020000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 28)
  refine ⟨false, 12501250, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_300060000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (300060000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 29)
  refine ⟨false, 9376875, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_300059968 :
    sampleVarianceIeeeSingleFormat.finiteSystem (300059968 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 29)
  refine ⟨false, 9376874, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_neg32 :
    sampleVarianceIeeeSingleFormat.finiteSystem (-32 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 6)
  refine ⟨true, 8388608, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_neg16 :
    sampleVarianceIeeeSingleFormat.finiteSystem (-16 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 5)
  refine ⟨true, 8388608, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl













/-- Rounded binary32 square of `10000` in the one-pass sample-variance path. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sq0 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_x0
    sampleVarianceOnePassIeeeSingle_x0

/-- Rounded binary32 square of `10001` in the one-pass sample-variance path. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sq1 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
    sampleVarianceOnePassIeeeSingle_x1

/-- Rounded binary32 square of `10002` in the one-pass sample-variance path. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sq2 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
    sampleVarianceOnePassIeeeSingle_x2

/-- First rounded binary32 sum in the one-pass sum-of-squares accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sumSq01 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_sq0
    sampleVarianceOnePassIeeeSingle_sq1

/-- Final rounded binary32 sum-of-squares accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sumSq : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_sumSq01
    sampleVarianceOnePassIeeeSingle_sq2

/-- First rounded binary32 ordinary sum accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sum01 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_x0
    sampleVarianceOnePassIeeeSingle_x1

/-- Final rounded binary32 ordinary sum accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sum : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_sum01
    sampleVarianceOnePassIeeeSingle_x2

/-- Rounded binary32 square of the rounded ordinary sum. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sumSquare : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_sum
    sampleVarianceOnePassIeeeSingle_sum

/-- Rounded binary32 quotient `(rounded sum)^2 / 3`. -/
noncomputable def sampleVarianceOnePassIeeeSingle_meanSquareTerm : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.div sampleVarianceOnePassIeeeSingle_sumSquare 3

/-- Rounded binary32 cancellation numerator in the one-pass variance formula. -/
noncomputable def sampleVarianceOnePassIeeeSingle_numerator : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.sub sampleVarianceOnePassIeeeSingle_sumSq
    sampleVarianceOnePassIeeeSingle_meanSquareTerm

/-- Rounded binary32 one-pass sample-variance trace for Higham §1.9's data. -/
noncomputable def sampleVarianceOnePassIeeeSingleTrace : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.div sampleVarianceOnePassIeeeSingle_numerator 2

/-- The four nontrivial binary32 nearest/even primitive values in the concrete
one-pass sample-variance trace.  Exact grid-point operations in the same trace
are proved below from `finiteSystem` facts; later theorems prove these four
selector equalities outright and close the full concrete operation trace. -/
def sampleVarianceOnePassIeeeSingleRoundingCertificate : Prop :=
  sampleVarianceOnePassIeeeSingle_sq1 = 100020000 ∧
    sampleVarianceOnePassIeeeSingle_sq2 = 100040000 ∧
      sampleVarianceOnePassIeeeSingle_sumSquare = 900180032 ∧
        sampleVarianceOnePassIeeeSingle_meanSquareTerm = 300060000

/-- Source round-to-even evidence for the non-grid binary32 primitive
`10001^2 -> 100020000` in Higham §1.9's one-pass example. -/
theorem sampleVarianceOnePassIeeeSingle_sq1_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
        sampleVarianceOnePassIeeeSingle_x1) (100020000 : ℝ) := by
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x1]
  change sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
    (100020001 : ℝ) (100020000 : ℝ)
  refine Or.inl ⟨27, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨100020000, 100020008, 12502500, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 12502500, 27, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 27, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_left_closer]
      norm_num

private theorem sampleVarianceOnePassIeeeSingle_sq1_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange (100020001 : ℝ) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change (100020001 : ℝ) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : (100020001 : ℝ) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge

/-- The total binary32 round-to-even selector sends `10001^2 = 100020001` to
`100020000`; the left endpoint of the adjacent binary32 bracket is strictly
nearer than the right endpoint. -/
theorem sampleVarianceOnePassIeeeSingle_sq1_eq :
    sampleVarianceOnePassIeeeSingle_sq1 = 100020000 := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (100020001 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (100020001 : ℝ)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_sq1_finiteNormalRange
  have hround :
      sampleVarianceIeeeSingleFormat.nearestRoundingToUnbounded
        (100020001 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (100020001 : ℝ)) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_nearestRoundingToUnbounded hpolicy
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (100020000 : ℝ) (100020008 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 12502500, 27, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  have hrounded :
      sampleVarianceIeeeSingleFormat.finiteRoundToEven (100020001 : ℝ) =
        (100020000 : ℝ) :=
    FloatingPointFormat.nearestRoundingToUnbounded_eq_left_of_realOrderAdjacent_ordered_between_of_left_closer
      hround hadj (by norm_num) (by norm_num)
  unfold sampleVarianceOnePassIeeeSingle_sq1
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
        sampleVarianceOnePassIeeeSingle_x1) = (100020000 : ℝ)
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x1]
  exact hrounded

/-- Source round-to-even evidence for the halfway binary32 primitive
`10002^2 -> 100040000`: the endpoints are equally near and the left mantissa
is even. -/
theorem sampleVarianceOnePassIeeeSingle_sq2_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
        sampleVarianceOnePassIeeeSingle_x2) (100040000 : ℝ) := by
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]
  change sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
    (100040004 : ℝ) (100040000 : ℝ)
  refine Or.inl ⟨27, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨100040000, 100040008, 12505000, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 12505000, 27, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 27, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_tie_even]
      · norm_num
      · norm_num [FloatingPointFormat.evenMantissa]

private theorem sampleVarianceOnePassIeeeSingle_sq2_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange (100040004 : ℝ) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change (100040004 : ℝ) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : (100040004 : ℝ) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge

/-- The total binary32 round-to-even selector sends the exact halfway square
`10002^2 = 100040004` to the even-left endpoint `100040000`. -/
theorem sampleVarianceOnePassIeeeSingle_sq2_eq :
    sampleVarianceOnePassIeeeSingle_sq2 = 100040000 := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (100040004 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (100040004 : ℝ)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_sq2_finiteNormalRange
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (100040000 : ℝ) (100040008 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 12505000, 27, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  have hleftMantissa :
      sampleVarianceIeeeSingleFormat.normalizedMantissa 12505000 := by
    norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hleft :
      (100040000 : ℝ) =
        sampleVarianceIeeeSingleFormat.normalizedValue false 12505000 27 := by
    norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR]
    try rfl
  have hrounded :
      sampleVarianceIeeeSingleFormat.finiteRoundToEven (100040004 : ℝ) =
        (100040000 : ℝ) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj (by norm_num) hleftMantissa hleft
      (by norm_num) (by norm_num [FloatingPointFormat.evenMantissa])
  unfold sampleVarianceOnePassIeeeSingle_sq2
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
        sampleVarianceOnePassIeeeSingle_x2) = (100040000 : ℝ)
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]
  exact hrounded

/-- Source round-to-even evidence for the exact binary32 primitive value
`30003^2 -> 900180032` in the one-pass trace. -/
theorem sampleVarianceOnePassIeeeSingle_sumSquare_exact_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (900180009 : ℝ) (900180032 : ℝ) := by
  refine Or.inl ⟨30, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨900179968, 900180032, 14065312, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 14065312, 30, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 30, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_right_of_right_closer]
      norm_num

private theorem sampleVarianceOnePassIeeeSingle_sumSquare_exact_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange (900180009 : ℝ) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change (900180009 : ℝ) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : (900180009 : ℝ) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge

private theorem sampleVarianceOnePassIeeeSingle_sumSquare_exact_round_eq :
    sampleVarianceIeeeSingleFormat.finiteRoundToEven (900180009 : ℝ) =
      (900180032 : ℝ) := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (900180009 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (900180009 : ℝ)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_sumSquare_exact_finiteNormalRange
  have hround :
      sampleVarianceIeeeSingleFormat.nearestRoundingToUnbounded
        (900180009 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (900180009 : ℝ)) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_nearestRoundingToUnbounded hpolicy
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (900179968 : ℝ) (900180032 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 14065312, 30, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  exact
    FloatingPointFormat.nearestRoundingToUnbounded_eq_right_of_realOrderAdjacent_ordered_between_of_right_closer
      hround hadj (by norm_num) (by norm_num)

/-- Source round-to-even evidence for the exact binary32 primitive
`900180032 / 3 -> 300060000` in the one-pass trace. -/
theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      ((900180032 : ℝ) / 3) (300060000 : ℝ) := by
  refine Or.inl ⟨29, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨300060000, 300060032, 9376875, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 9376875, 29, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 29, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_left_closer]
      norm_num

private theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange ((900180032 : ℝ) / 3) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · have hpos : 0 ≤ ((900180032 : ℝ) / 3) := by
      norm_num
    rw [abs_of_nonneg hpos]
    simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change ((900180032 : ℝ) / 3) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : ((900180032 : ℝ) / 3) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge

private theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_round_eq :
    sampleVarianceIeeeSingleFormat.finiteRoundToEven ((900180032 : ℝ) / 3) =
      (300060000 : ℝ) := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        ((900180032 : ℝ) / 3)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven ((900180032 : ℝ) / 3)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_finiteNormalRange
  have hround :
      sampleVarianceIeeeSingleFormat.nearestRoundingToUnbounded
        ((900180032 : ℝ) / 3)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven ((900180032 : ℝ) / 3)) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_nearestRoundingToUnbounded hpolicy
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (300060000 : ℝ) (300060032 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 9376875, 29, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  exact
    FloatingPointFormat.nearestRoundingToUnbounded_eq_left_of_realOrderAdjacent_ordered_between_of_left_closer
      hround hadj (by norm_num) (by norm_num)

/-- Source round-to-even evidence for the binary32 division primitive once the
rounded sum square is known to be `900180032`. -/
theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_sourceRoundToEvenEvidence_of_sumSquare
    (hsumSquare : sampleVarianceOnePassIeeeSingle_sumSquare = 900180032) :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.div sampleVarianceOnePassIeeeSingle_sumSquare 3)
      (300060000 : ℝ) := by
  rw [hsumSquare]
  exact sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_sourceRoundToEvenEvidence

/-- The first square in the concrete binary32 one-pass trace is exact. -/
theorem sampleVarianceOnePassIeeeSingle_sq0_eq :
    sampleVarianceOnePassIeeeSingle_sq0 = 100000000 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x0
          sampleVarianceOnePassIeeeSingle_x0) := by
    norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0]
    exact ieeeSingle_finiteSystem_100000000
  unfold sampleVarianceOnePassIeeeSingle_sq0
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0]

/-- The first ordinary sum in the concrete binary32 one-pass trace is exact. -/
theorem sampleVarianceOnePassIeeeSingle_sum01_eq :
    sampleVarianceOnePassIeeeSingle_sum01 = 20001 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_x0
          sampleVarianceOnePassIeeeSingle_x1) := by
    norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0,
      sampleVarianceOnePassIeeeSingle_x1]
    exact ieeeSingle_finiteSystem_20001
  unfold sampleVarianceOnePassIeeeSingle_sum01
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0,
    sampleVarianceOnePassIeeeSingle_x1]

/-- The ordinary sum accumulator in the concrete binary32 one-pass trace is
exact. -/
theorem sampleVarianceOnePassIeeeSingle_sum_eq :
    sampleVarianceOnePassIeeeSingle_sum = 30003 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_sum01
          sampleVarianceOnePassIeeeSingle_x2) := by
    rw [sampleVarianceOnePassIeeeSingle_sum01_eq]
    norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]
    exact ieeeSingle_finiteSystem_30003
  unfold sampleVarianceOnePassIeeeSingle_sum
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    sampleVarianceOnePassIeeeSingle_sum01_eq]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]

/-- Source round-to-even evidence for the binary32 primitive
`sampleVarianceOnePassIeeeSingle_sum^2 -> 900180032`, after the ordinary sum
accumulator has been proved exact. -/
theorem sampleVarianceOnePassIeeeSingle_sumSquare_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_sum
        sampleVarianceOnePassIeeeSingle_sum) (900180032 : ℝ) := by
  rw [sampleVarianceOnePassIeeeSingle_sum_eq]
  have hmul : BasicOp.exact BasicOp.mul (30003 : ℝ) (30003 : ℝ) =
      (900180009 : ℝ) := by
    norm_num [BasicOp.exact]
  simpa [hmul] using
    sampleVarianceOnePassIeeeSingle_sumSquare_exact_sourceRoundToEvenEvidence

/-- The rounded binary32 square of the exact ordinary sum is the displayed
single-precision value `900180032`. -/
theorem sampleVarianceOnePassIeeeSingle_sumSquare_eq :
    sampleVarianceOnePassIeeeSingle_sumSquare = 900180032 := by
  unfold sampleVarianceOnePassIeeeSingle_sumSquare
  rw [sampleVarianceOnePassIeeeSingle_sum_eq]
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.mul (30003 : ℝ) (30003 : ℝ)) = (900180032 : ℝ)
  norm_num [BasicOp.exact]
  exact sampleVarianceOnePassIeeeSingle_sumSquare_exact_round_eq

/-- The rounded binary32 quotient `(rounded sum)^2 / 3` is the displayed
single-precision value `300060000`. -/
theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_eq :
    sampleVarianceOnePassIeeeSingle_meanSquareTerm = 300060000 := by
  unfold sampleVarianceOnePassIeeeSingle_meanSquareTerm
  rw [sampleVarianceOnePassIeeeSingle_sumSquare_eq]
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.div (900180032 : ℝ) 3) = (300060000 : ℝ)
  norm_num [BasicOp.exact]
  exact sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_round_eq

/-- Closed source-level evidence for the four non-grid binary32 primitive
roundings used by the one-pass trace.  This proves the intended grid endpoints
and tie choices.  Later total-selector equalities turn this source evidence into
the closed concrete operation trace. -/
theorem sampleVarianceOnePassIeeeSingle_sourceRoundingEvidenceCertificate :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
          sampleVarianceOnePassIeeeSingle_x1) (100020000 : ℝ) ∧
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
          sampleVarianceOnePassIeeeSingle_x2) (100040000 : ℝ) ∧
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_sum
          sampleVarianceOnePassIeeeSingle_sum) (900180032 : ℝ) ∧
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        ((900180032 : ℝ) / 3) (300060000 : ℝ) := by
  exact ⟨sampleVarianceOnePassIeeeSingle_sq1_sourceRoundToEvenEvidence,
    sampleVarianceOnePassIeeeSingle_sq2_sourceRoundToEvenEvidence,
    sampleVarianceOnePassIeeeSingle_sumSquare_sourceRoundToEvenEvidence,
    sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_sourceRoundToEvenEvidence⟩

/-- The closed square, sum-square, and mean-square primitive equalities imply
the full concrete binary32 rounding certificate. -/
theorem sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingleRoundingCertificate := by
  exact ⟨sampleVarianceOnePassIeeeSingle_sq1_eq, hsq2,
    sampleVarianceOnePassIeeeSingle_sumSquare_eq,
    sampleVarianceOnePassIeeeSingle_meanSquareTerm_eq⟩

/-- The concrete binary32 one-pass operation trace has all four non-grid
nearest/even primitive roundings closed. -/
theorem sampleVarianceOnePassIeeeSingleRoundingCertificate_closed :
    sampleVarianceOnePassIeeeSingleRoundingCertificate :=
  sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq
    sampleVarianceOnePassIeeeSingle_sq2_eq

private theorem sampleVarianceOnePassIeeeSingle_sumSq01_eq_of_sq1
    (hsq1 : sampleVarianceOnePassIeeeSingle_sq1 = 100020000) :
    sampleVarianceOnePassIeeeSingle_sumSq01 = 200020000 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_sq0
          sampleVarianceOnePassIeeeSingle_sq1) := by
    rw [sampleVarianceOnePassIeeeSingle_sq0_eq, hsq1]
    norm_num [BasicOp.exact]
    exact ieeeSingle_finiteSystem_200020000
  unfold sampleVarianceOnePassIeeeSingle_sumSq01
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    sampleVarianceOnePassIeeeSingle_sq0_eq, hsq1]
  norm_num [BasicOp.exact]

/-- Under the two non-grid square-rounding facts, the sum-of-squares accumulator
in the concrete binary32 one-pass trace is exactly `300060000`. -/
theorem sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq1_sq2
    (hsq1 : sampleVarianceOnePassIeeeSingle_sq1 = 100020000)
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingle_sumSq = 300060000 := by
  have hsumSq01 := sampleVarianceOnePassIeeeSingle_sumSq01_eq_of_sq1 hsq1
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_sumSq01
          sampleVarianceOnePassIeeeSingle_sq2) := by
    rw [hsumSq01, hsq2]
    norm_num [BasicOp.exact]
    exact ieeeSingle_finiteSystem_300060000
  unfold sampleVarianceOnePassIeeeSingle_sumSq
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    hsumSq01, hsq2]
  norm_num [BasicOp.exact]

/-- With the first square unconditional, the final sum-of-squares accumulator
can be reduced to the `10002^2` primitive equality. -/
theorem sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq2
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingle_sumSq = 300060000 :=
  sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq1_sq2
    sampleVarianceOnePassIeeeSingle_sq1_eq hsq2

/-- The final sum-of-squares accumulator in the concrete binary32 one-pass trace
is exactly `300060000`. -/
theorem sampleVarianceOnePassIeeeSingle_sumSq_eq :
    sampleVarianceOnePassIeeeSingle_sumSq = 300060000 :=
  sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq2
    sampleVarianceOnePassIeeeSingle_sq2_eq

private theorem sampleVarianceOnePassIeeeSingle_numerator_eq_zero_of_roundingCertificate
    (hcert : sampleVarianceOnePassIeeeSingleRoundingCertificate) :
    sampleVarianceOnePassIeeeSingle_numerator = 0 := by
  rcases hcert with ⟨hsq1, hsq2, _hsumSquare, hmeanSquare⟩
  have hsumSq := sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq1_sq2 hsq1 hsq2
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.sub sampleVarianceOnePassIeeeSingle_sumSq
          sampleVarianceOnePassIeeeSingle_meanSquareTerm) := by
    rw [hsumSq, hmeanSquare]
    simpa [BasicOp.exact] using ieeeSingle_finiteSystem_zero
  unfold sampleVarianceOnePassIeeeSingle_numerator
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    hsumSq, hmeanSquare]
  norm_num [BasicOp.exact]
  rfl

/-- If the four non-grid binary32 primitive roundings in the §1.9 one-pass
trace have the displayed nearest/even values, then the actual rounded operation
trace returns `0.0`. -/
theorem sampleVarianceOnePassIeeeSingleTrace_zero_of_roundingCertificate
    (hcert : sampleVarianceOnePassIeeeSingleRoundingCertificate) :
    sampleVarianceOnePassIeeeSingleTrace = 0 := by
  have hnumer :=
    sampleVarianceOnePassIeeeSingle_numerator_eq_zero_of_roundingCertificate
      hcert
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.div sampleVarianceOnePassIeeeSingle_numerator 2) := by
    rw [hnumer]
    simpa [BasicOp.exact] using ieeeSingle_finiteSystem_zero
  unfold sampleVarianceOnePassIeeeSingleTrace
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    hnumer]
  norm_num [BasicOp.exact]
  rfl

/-- Under the same concrete binary32 rounding certificate, the one-pass trace
has relative error `1` against the exact sample variance, matching Higham
§1.9's displayed single-precision result. -/
theorem sampleVarianceOnePassIeeeSingleTrace_relError_one_of_roundingCertificate
    (hcert : sampleVarianceOnePassIeeeSingleRoundingCertificate) :
    relError sampleVarianceOnePassIeeeSingleTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 1 := by
  rw [sampleVarianceOnePassIeeeSingleTrace_zero_of_roundingCertificate hcert,
    sampleVarianceTwoPass_example_10000_10001_10002]
  norm_num [relError]
  rfl

/-- The concrete binary32 one-pass trace returns `0.0` as soon as the
`10002^2 -> 100040000` primitive equality is supplied. -/
theorem sampleVarianceOnePassIeeeSingleTrace_zero_of_sq2_eq
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingleTrace = 0 :=
  sampleVarianceOnePassIeeeSingleTrace_zero_of_roundingCertificate
    (sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq hsq2)

/-- The concrete binary32 one-pass trace returns `0.0`. -/
theorem sampleVarianceOnePassIeeeSingleTrace_zero :
    sampleVarianceOnePassIeeeSingleTrace = 0 :=
  sampleVarianceOnePassIeeeSingleTrace_zero_of_sq2_eq
    sampleVarianceOnePassIeeeSingle_sq2_eq

/-- The `10002^2 -> 100040000` primitive equality also suffices for the
relative-error-`1` statement against the exact two-pass sample variance. -/
theorem sampleVarianceOnePassIeeeSingleTrace_relError_one_of_sq2_eq
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    relError sampleVarianceOnePassIeeeSingleTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 1 :=
  sampleVarianceOnePassIeeeSingleTrace_relError_one_of_roundingCertificate
    (sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq hsq2)

/-- The concrete binary32 one-pass trace has relative error `1` against the
exact two-pass sample variance. -/
theorem sampleVarianceOnePassIeeeSingleTrace_relError_one :
    relError sampleVarianceOnePassIeeeSingleTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 1 :=
  sampleVarianceOnePassIeeeSingleTrace_relError_one_of_sq2_eq
    sampleVarianceOnePassIeeeSingle_sq2_eq

-- ============================================================
-- Supplied rounded-aggregate negative final-operation trace
-- ============================================================















/-- Rounded binary32 final numerator from the supplied negative aggregate
diagnostic. -/
noncomputable def sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator :
    ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.sub sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq
    sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm

/-- Rounded binary32 final variance quotient from the supplied negative
aggregate diagnostic. -/
noncomputable def sampleVarianceOnePassIeeeSingleNegativeAggregateTrace : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.div sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator 2

/-- The supplied rounded aggregates are binary32 finite-system values. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregate_inputs_finiteSystem :
    sampleVarianceIeeeSingleFormat.finiteSystem
        sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq ∧
      sampleVarianceIeeeSingleFormat.finiteSystem
        sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm := by
  exact ⟨by
      simpa [sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq] using
        ieeeSingle_finiteSystem_300059968,
    by
      simpa [sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm] using
        ieeeSingle_finiteSystem_300060000⟩

/-- The final rounded subtraction in the supplied negative aggregate diagnostic
is exact and gives `-32`. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator_eq :
    sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator = -32 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.sub
          sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq
          sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm) := by
    have hcalc :
        BasicOp.exact BasicOp.sub
            sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq
            sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm =
          (-32 : ℝ) := by
      norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq,
        sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm]
    simpa [hcalc] using ieeeSingle_finiteSystem_neg32
  unfold sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq,
    sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm]

/-- The supplied rounded-aggregate final operation trace returns the concrete
negative binary32 value `-16`. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen :
    sampleVarianceOnePassIeeeSingleNegativeAggregateTrace = -16 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.div
          sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator 2) := by
    have hcalc :
        BasicOp.exact BasicOp.div
            sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator 2 =
          (-16 : ℝ) := by
      rw [sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator_eq]
      norm_num [BasicOp.exact]
    simpa [hcalc] using ieeeSingle_finiteSystem_neg16
  unfold sampleVarianceOnePassIeeeSingleNegativeAggregateTrace
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator_eq]
  norm_num [BasicOp.exact]

/-- The supplied rounded-aggregate final operation trace is strictly negative. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_lt_zero :
    sampleVarianceOnePassIeeeSingleNegativeAggregateTrace < 0 := by
  rw [sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen]
  norm_num

/-- Against the exact sample variance `1` for `[10000,10001,10002]`, the
supplied rounded-aggregate negative final trace has relative error `17`. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_relError :
    relError sampleVarianceOnePassIeeeSingleNegativeAggregateTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 17 := by
  rw [sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen,
    sampleVarianceTwoPass_example_10000_10001_10002]
  norm_num [relError]
  rfl

-- ============================================================
-- Higham Problem 1.7 condition-number closed forms
-- ============================================================







































































































































































































































































































































































end NumStability
