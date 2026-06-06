import LeanFpAnalysis.HDP.Probability.Concentration.Chernoff
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.CentralLimitTheorem

/-!
# Poisson CLT

Poisson-specific moment facts and the HDP Exercise 2.3.8 central-limit
specialization.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace LeanFpAnalysis.HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section PoissonMoments

/-- The real-valued law of a Poisson random variable, obtained by coercing
`ℕ` to `ℝ`. -/
def poissonRealMeasure (lam : ℝ≥0) : Measure ℝ :=
  (ProbabilityTheory.poissonMeasure lam).map fun n : ℕ => (n : ℝ)

instance instIsProbabilityMeasure_poissonRealMeasure (lam : ℝ≥0) :
    IsProbabilityMeasure (poissonRealMeasure lam) :=
  Measure.isProbabilityMeasure_map AEMeasurable.of_discrete

/-- The coercion from `ℕ` to `ℝ` has the real-valued Poisson law under the
native Poisson measure on `ℕ`. -/
lemma hasLaw_coe_nat_poissonRealMeasure (lam : ℝ≥0) :
    HasLaw (fun n : ℕ => (n : ℝ)) (poissonRealMeasure lam)
      (ProbabilityTheory.poissonMeasure lam) where
  aemeasurable := AEMeasurable.of_discrete
  map_eq := rfl

/-- Characteristic function of the real-valued Poisson law. -/
lemma charFun_poissonRealMeasure_eq (lam : ℝ≥0) (theta : ℝ) :
    charFun (poissonRealMeasure lam) theta =
      Complex.exp (((lam : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (theta : ℂ)) - 1)) := by
  rw [poissonRealMeasure, charFun, MeasureTheory.integral_map]
  · rw [ProbabilityTheory.integral_poissonMeasure]
    have hseries :=
      (NormedSpace.expSeries_div_hasSum_exp
        (((lam : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ)))).mul_left
        (((Real.exp (-(lam : ℝ))) : ℝ) : ℂ)
    calc
      (∑' n : ℕ, (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ)) •
          Complex.exp (↑(inner ℝ (n : ℝ) theta) * Complex.I))
          = ∑' n : ℕ, ((Real.exp (-(lam : ℝ)) : ℝ) : ℂ) *
              ((((lam : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ n /
                (n.factorial : ℂ)) := by
            apply tsum_congr
            intro n
            have hnfacR : (n.factorial : ℝ) ≠ 0 := by
              exact_mod_cast Nat.factorial_ne_zero n
            have hnfacC : (n.factorial : ℂ) ≠ 0 := by
              exact_mod_cast Nat.factorial_ne_zero n
            rw [mul_pow]
            rw [← Complex.exp_nat_mul]
            simp [inner, mul_assoc, mul_comm]
            field_simp [hnfacR, hnfacC]
      _ = ((Real.exp (-(lam : ℝ)) : ℝ) : ℂ) *
            Complex.exp (((lam : ℝ) : ℂ) *
              Complex.exp (Complex.I * (theta : ℂ))) := by
            simpa [← Complex.exp_eq_exp_ℂ] using hseries.tsum_eq
      _ = Complex.exp (((lam : ℝ) : ℂ) *
            (Complex.exp (Complex.I * (theta : ℂ)) - 1)) := by
            rw [Complex.ofReal_exp, ← Complex.exp_add]
            congr 1
            norm_num
            ring
  · exact AEMeasurable.of_discrete
  · fun_prop

/-- Poisson exponential moments exist for every real parameter, so the MGF
domain of the real-valued Poisson law is all of `ℝ`. -/
@[simp]
lemma integrableExpSet_coe_nat_poissonMeasure (lam : ℝ≥0) :
    integrableExpSet (fun n : ℕ => (n : ℝ))
      (ProbabilityTheory.poissonMeasure lam) = Set.univ := by
  ext theta
  simp [integrableExpSet, integrable_exp_mul_poissonMeasure lam theta]

/-- First moment of a Poisson random variable. -/
lemma integral_coe_nat_poissonMeasure_eq (lam : ℝ≥0) :
    ∫ n, (n : ℝ) ∂ProbabilityTheory.poissonMeasure lam = (lam : ℝ) := by
  change (ProbabilityTheory.poissonMeasure lam)[fun n : ℕ => (n : ℝ)] = (lam : ℝ)
  rw [← ProbabilityTheory.deriv_mgf_zero
    (X := fun n : ℕ => (n : ℝ)) (μ := ProbabilityTheory.poissonMeasure lam)]
  · rw [show ProbabilityTheory.mgf (fun n : ℕ => (n : ℝ))
          (ProbabilityTheory.poissonMeasure lam) =
          fun theta => Real.exp ((Real.exp theta - 1) * (lam : ℝ)) by
          funext theta
          exact mgf_coe_nat_poissonMeasure_eq lam theta]
    rw [_root_.deriv_exp (by fun_prop)]
    simp
  · simp [integrableExpSet_coe_nat_poissonMeasure lam]

/-- Second raw moment of a Poisson random variable. -/
lemma secondMoment_coe_nat_poissonMeasure_eq (lam : ℝ≥0) :
    ∫ n, ((n : ℝ) ^ 2) ∂ProbabilityTheory.poissonMeasure lam =
      (lam : ℝ) ^ 2 + (lam : ℝ) := by
  change (ProbabilityTheory.poissonMeasure lam)[(fun n : ℕ => (n : ℝ)) ^ 2] =
    (lam : ℝ) ^ 2 + (lam : ℝ)
  rw [← ProbabilityTheory.iteratedDeriv_mgf_zero
    (X := fun n : ℕ => (n : ℝ)) (μ := ProbabilityTheory.poissonMeasure lam) (n := 2)]
  · rw [show ProbabilityTheory.mgf (fun n : ℕ => (n : ℝ))
          (ProbabilityTheory.poissonMeasure lam) =
          fun theta => Real.exp ((Real.exp theta - 1) * (lam : ℝ)) by
          funext theta
          exact mgf_coe_nat_poissonMeasure_eq lam theta]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hderiv :
        deriv (fun theta : ℝ => Real.exp ((Real.exp theta - 1) * (lam : ℝ))) =
          fun theta : ℝ => Real.exp ((Real.exp theta - 1) * (lam : ℝ)) *
            (Real.exp theta * (lam : ℝ)) := by
      funext theta
      rw [_root_.deriv_exp (by fun_prop)]
      congr 1
      rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
      simp
    rw [hderiv]
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    rw [_root_.deriv_exp (by fun_prop)]
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp
    ring
  · simp [integrableExpSet_coe_nat_poissonMeasure lam]

/-- A Poisson random variable has finite second moment. -/
lemma memLp_two_coe_nat_poissonMeasure (lam : ℝ≥0) :
    MemLp (fun n : ℕ => (n : ℝ)) 2 (ProbabilityTheory.poissonMeasure lam) :=
  memLp_of_mem_interior_integrableExpSet
    (by simp [integrableExpSet_coe_nat_poissonMeasure lam]) 2

/-- Variance of a Poisson random variable. -/
lemma variance_coe_nat_poissonMeasure_eq (lam : ℝ≥0) :
    Var[fun n : ℕ => (n : ℝ); ProbabilityTheory.poissonMeasure lam] =
      (lam : ℝ) := by
  rw [ProbabilityTheory.variance_eq_sub (memLp_two_coe_nat_poissonMeasure lam)]
  change
    ∫ n, ((n : ℝ) ^ 2) ∂ProbabilityTheory.poissonMeasure lam -
      (∫ n, (n : ℝ) ∂ProbabilityTheory.poissonMeasure lam) ^ 2 =
        (lam : ℝ)
  rw [integral_coe_nat_poissonMeasure_eq, secondMoment_coe_nat_poissonMeasure_eq]
  ring

/-- Mean of the real-valued Poisson law. -/
lemma integral_id_poissonRealMeasure_eq (lam : ℝ≥0) :
    ∫ x, x ∂poissonRealMeasure lam = (lam : ℝ) := by
  have h := (hasLaw_coe_nat_poissonRealMeasure lam).integral_eq
  rw [← h, integral_coe_nat_poissonMeasure_eq]

/-- The real-valued Poisson law has finite second moment. -/
lemma memLp_two_id_poissonRealMeasure (lam : ℝ≥0) :
    MemLp (fun x : ℝ => x) 2 (poissonRealMeasure lam) := by
  have hident :
      IdentDistrib (fun n : ℕ => (n : ℝ)) (fun x : ℝ => x)
        (ProbabilityTheory.poissonMeasure lam) (poissonRealMeasure lam) :=
    (hasLaw_coe_nat_poissonRealMeasure lam).identDistrib HasLaw.id
  exact hident.memLp_iff.mp (memLp_two_coe_nat_poissonMeasure lam)

/-- Variance of the real-valued Poisson law. -/
lemma variance_id_poissonRealMeasure_eq (lam : ℝ≥0) :
    Var[fun x : ℝ => x; poissonRealMeasure lam] = (lam : ℝ) := by
  have h := (hasLaw_coe_nat_poissonRealMeasure lam).variance_eq
  change Var[id; poissonRealMeasure lam] = (lam : ℝ)
  rw [← h, variance_coe_nat_poissonMeasure_eq]

/-- The centered unit-Poisson variable has mean zero. -/
lemma integral_id_sub_one_poissonRealMeasure_one_eq_zero :
    ∫ x, (x - 1) ∂poissonRealMeasure 1 = 0 := by
  rw [integral_sub (memLp_two_id_poissonRealMeasure 1 |>.integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)) (integrable_const 1)]
  rw [integral_id_poissonRealMeasure_eq]
  norm_num

/-- The centered unit-Poisson variable has second moment one. -/
lemma integral_id_sub_one_sq_poissonRealMeasure_one_eq_one :
    ∫ x, ((fun x : ℝ => x - 1) ^ 2) x ∂poissonRealMeasure 1 = 1 := by
  change ∫ x, (x - 1) ^ 2 ∂poissonRealMeasure 1 = 1
  rw [← ProbabilityTheory.variance_of_integral_eq_zero
    (by fun_prop : AEMeasurable (fun x : ℝ => x - 1) (poissonRealMeasure 1))
    integral_id_sub_one_poissonRealMeasure_one_eq_zero]
  rw [ProbabilityTheory.variance_sub_const
    (memLp_two_id_poissonRealMeasure 1).aestronglyMeasurable 1]
  rw [variance_id_poissonRealMeasure_eq]
  norm_num

end PoissonMoments

section PoissonCLT

/-- The normalized real-valued Poisson law `(X - λ) / sqrt λ`. -/
def poissonNormalizedMeasure (lam : ℝ≥0) : Measure ℝ :=
  (poissonRealMeasure lam).map fun x : ℝ => (x - (lam : ℝ)) / Real.sqrt (lam : ℝ)

/-- The normalized real-valued Poisson law as a probability measure. -/
def poissonNormalizedProbability (N : ℕ) : ProbabilityMeasure ℝ :=
  ⟨poissonNormalizedMeasure (N : ℝ≥0),
    Measure.isProbabilityMeasure_map (by fun_prop :
      AEMeasurable
        (fun x : ℝ => (x - (((N : ℝ≥0) : ℝ))) / Real.sqrt (((N : ℝ≥0) : ℝ)))
        (poissonRealMeasure (N : ℝ≥0)))⟩

/-- Characteristic function of the normalized Poisson law. -/
lemma charFun_poissonNormalizedMeasure_eq (lam : ℝ≥0) (t : ℝ) :
    charFun (poissonNormalizedMeasure lam) t =
      Complex.exp (((lam : ℝ) : ℂ) *
        (Complex.exp (Complex.I * ((t / Real.sqrt (lam : ℝ) : ℝ) : ℂ)) - 1 -
          Complex.I * ((t / Real.sqrt (lam : ℝ) : ℝ) : ℂ))) := by
  let s : ℝ := Real.sqrt (lam : ℝ)
  let a : ℝ := s⁻¹
  let b : ℝ := -((lam : ℝ) / s)
  have hmap :
      poissonNormalizedMeasure lam =
        (poissonRealMeasure lam).map ((fun y : ℝ => y + b) ∘ (fun x : ℝ => a * x)) := by
    unfold poissonNormalizedMeasure
    apply Measure.map_congr
    exact ae_of_all _ fun x => by
      simp [a, b, s, div_eq_inv_mul]
      ring
  rw [hmap]
  rw [← Measure.map_map (by fun_prop : Measurable fun y : ℝ => y + b)
    (by fun_prop : Measurable fun x : ℝ => a * x)]
  rw [charFun_map_add_const, charFun_map_mul, charFun_poissonRealMeasure_eq]
  rw [← Complex.exp_add]
  congr 1
  simp [a, b, s, div_eq_inv_mul, inner, mul_comm]
  ring

/-- The normalized Poisson characteristic function with integer parameter is
the `N`-th power of the centered unit-Poisson characteristic function. -/
lemma charFun_poissonNormalizedProbability_eq_unit_pow (N : ℕ) (t : ℝ) :
    charFun (poissonNormalizedProbability N : Measure ℝ) t =
      (charFun ((poissonRealMeasure 1).map fun x : ℝ => x - 1)
        ((Real.sqrt (N : ℝ))⁻¹ * t)) ^ N := by
  change charFun (poissonNormalizedMeasure (N : ℝ≥0)) t = _
  rw [charFun_poissonNormalizedMeasure_eq]
  have hunit :
      charFun ((poissonRealMeasure 1).map fun x : ℝ => x - 1)
        ((Real.sqrt (N : ℝ))⁻¹ * t) =
        Complex.exp
          (Complex.exp (Complex.I * (((Real.sqrt (N : ℝ))⁻¹ * t : ℝ) : ℂ)) -
            1 - Complex.I * (((Real.sqrt (N : ℝ))⁻¹ * t : ℝ) : ℂ)) := by
    rw [show (fun x : ℝ => x - 1) = (fun y : ℝ => y + (-1)) from by
      funext x
      ring]
    rw [charFun_map_add_const, charFun_poissonRealMeasure_eq]
    rw [← Complex.exp_add]
    congr 1
    simp [inner]
    ring
  rw [hunit]
  rw [← Complex.exp_nat_mul]
  congr 1
  simp [div_eq_inv_mul, mul_comm]

/-- HDP Exercise 2.3.8, Poisson central limit theorem:
the normalized `Poisson(N)` laws converge weakly to the standard normal law. -/
theorem poissonCLT_nat :
    Tendsto poissonNormalizedProbability atTop (𝓝 standardNormalProbability) := by
  refine MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun ?_
  intro t
  have hpow :=
    ProbabilityTheory.tendsto_charFun_inv_sqrt_mul_pow
      (P := poissonRealMeasure 1)
      (X := fun x : ℝ => x - 1)
      (by fun_prop : AEMeasurable (fun x : ℝ => x - 1) (poissonRealMeasure 1))
      integral_id_sub_one_poissonRealMeasure_one_eq_zero
      integral_id_sub_one_sq_poissonRealMeasure_one_eq_one
      t
  have heq :
      (fun N : ℕ => charFun (poissonNormalizedProbability N : Measure ℝ) t)
        = fun N : ℕ =>
          (charFun ((poissonRealMeasure 1).map fun x : ℝ => x - 1)
            ((Real.sqrt (N : ℝ))⁻¹ * t)) ^ N := by
    funext N
    exact charFun_poissonNormalizedProbability_eq_unit_pow N t
  simpa [heq, standardNormalProbability, standardNormal_charFun t] using hpow

/-- Tail form of HDP Exercise 2.3.8. -/
theorem poissonCLT_nat_tail_tendsto_integral (t : ℝ) :
    Tendsto
      (fun N : ℕ =>
        (((poissonNormalizedProbability N) (Set.Ici t) : ℝ≥0) : ℝ))
      atTop
      (𝓝 (∫ x in Set.Ici t, standardNormalDensity x)) := by
  have h_cont :
      standardNormalProbability (frontier (Set.Ici t)) = 0 := by
    have hfront : frontier (Set.Ici t) = ({t} : Set ℝ) := by
      simp [frontier, closure_Ici]
    rw [hfront]
    haveI : NoAtoms standardNormalMeasure :=
      ProbabilityTheory.noAtoms_gaussianReal (μ := 0) (v := (1 : ℝ≥0)) (by norm_num)
    ext
    simp [standardNormalProbability]
  have h_nn :
      Tendsto
        (fun N : ℕ => (poissonNormalizedProbability N) (Set.Ici t))
        atTop
        (𝓝 (standardNormalProbability (Set.Ici t))) :=
    MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      poissonCLT_nat h_cont
  have htarget :
      ((((standardNormalProbability : ProbabilityMeasure ℝ)
        (Set.Ici t) : ℝ≥0) : ℝ)) =
        ∫ x in Set.Ici t, standardNormalDensity x := by
    have h_nonneg :
        0 ≤ ∫ x in Set.Ici t, standardNormalDensity x := by
      exact integral_nonneg fun x =>
        ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x
    change (standardNormalMeasure (Set.Ici t)).toReal =
      ∫ x in Set.Ici t, standardNormalDensity x
    rw [standardNormal_tail_eq_integral t]
    exact ENNReal.toReal_ofReal h_nonneg
  rw [← htarget]
  exact (NNReal.continuous_coe.tendsto _).comp h_nn

end PoissonCLT

section UnitPoissonCLT

/-- Book-style hypotheses for HDP Exercise 2.3.8 in the unit-Poisson
representation: the summands are independent and all have Poisson(1) law. -/
structure UnitPoissonCLTHypotheses [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) : Prop where
  independent : iIndepFun X μ
  hasLaw : ∀ i, HasLaw (X i) (poissonRealMeasure 1) μ

/-- HDP Exercise 2.3.8, Poisson CLT in the standard representation of a
Poisson variable with integer parameter as a sum of i.i.d. Poisson(1)
variables. -/
theorem poissonCLT_iid_unit
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h : UnitPoissonCLTHypotheses (μ := μ) X) :
    centralLimitConclusion
      (μ := μ) X 1 1
      (normalizedSum_aemeasurable (μ := μ) fun i => (h.hasLaw i).aemeasurable) := by
  refine
    lindebergLevyCentralLimitTheorem
      (μ := μ) (X := X) (m := 1) (σ := 1) ?_
  refine
    { aemeasurable := fun i => (h.hasLaw i).aemeasurable
      integrable_zero := ?_
      square_integrable_zero := ?_
      independent := h.independent
      identDistrib := fun i => (h.hasLaw i).identDistrib (h.hasLaw 0)
      mean_eq := ?_
      variance_eq := ?_
      sigma_pos := by norm_num }
  · have hident :
        IdentDistrib (X 0) (fun x : ℝ => x) μ (poissonRealMeasure 1) :=
      (h.hasLaw 0).identDistrib HasLaw.id
    exact
      (hident.memLp_iff.mpr (memLp_two_id_poissonRealMeasure 1)).integrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  · have hident :
        IdentDistrib (X 0) (fun x : ℝ => x) μ (poissonRealMeasure 1) :=
      (h.hasLaw 0).identDistrib HasLaw.id
    exact hident.memLp_iff.mpr (memLp_two_id_poissonRealMeasure 1)
  · calc
      μ[X 0] = ∫ x, x ∂poissonRealMeasure 1 := (h.hasLaw 0).integral_eq
      _ = 1 := by
        rw [integral_id_poissonRealMeasure_eq]
        norm_num
  · calc
      Var[X 0; μ] = Var[fun x : ℝ => x; poissonRealMeasure 1] :=
        (h.hasLaw 0).variance_eq
      _ = 1 ^ 2 := by
        rw [variance_id_poissonRealMeasure_eq]
        norm_num

/-- Tail form of HDP Exercise 2.3.8. -/
theorem poissonCLT_iid_unit_tail_tendsto_integral
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h : UnitPoissonCLTHypotheses (μ := μ) X)
    (t : ℝ) :
    Tendsto
      (fun N : ℕ =>
        (((lawOf (μ := μ) (normalizedSum X 1 1 N)
          (normalizedSum_aemeasurable (μ := μ) (fun i => (h.hasLaw i).aemeasurable) N) :
            ProbabilityMeasure ℝ)
          (Set.Ici t) : ℝ≥0) : ℝ))
      atTop
      (𝓝 (∫ x in Set.Ici t, standardNormalDensity x)) :=
  centralLimit_tail_tendsto_integral
    (μ := μ)
    (X := X)
    (m := 1)
    (σ := 1)
    (hCLT := poissonCLT_iid_unit (μ := μ) h)
    t

end UnitPoissonCLT

end LeanFpAnalysis.HDP
