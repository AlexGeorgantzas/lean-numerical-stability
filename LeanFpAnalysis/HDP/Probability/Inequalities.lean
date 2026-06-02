import LeanFpAnalysis.HDP.Probability.RandomVariables
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-!
# Classical Probability Inequalities

HDP Chapter 1, Section 1.2: Jensen, monotonicity of `L^p` norms,
Minkowski, Holder/Cauchy-Schwarz, layer-cake identities, Markov, and
Chebyshev.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace LeanFpAnalysis.HDP

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Jensen

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {s : Set E} {φ : E → ℝ} {X : Ω → E}

/-- HDP Jensen inequality: `φ(E X) ≤ E φ(X)` for a convex continuous function
on a closed convex set containing the random variable almost surely. -/
theorem jensen_integral [IsProbabilityMeasure μ]
    (hφ : ConvexOn ℝ s φ) (hφc : ContinuousOn φ s) (hs : IsClosed s)
    (hXs : ∀ᵐ ω ∂μ, X ω ∈ s) (hX : Integrable X μ) (hφX : Integrable (φ ∘ X) μ) :
    φ (μ[X]) ≤ μ[fun ω => φ (X ω)] :=
  hφ.map_integral_le hφc hs hXs hX hφX

end Jensen

section Lp

variable [NormedAddCommGroup E] {X Y : Ω → E} {p q : ℝ≥0∞}

/-- HDP (1.3): on a probability space, `‖X‖_p ≤ ‖X‖_q` for `p ≤ q`. -/
theorem lpNorm_mono_exponent [IsProbabilityMeasure μ]
    (hpq : p ≤ q) (hX : AEStronglyMeasurable X μ) :
    eLpNorm X p μ ≤ eLpNorm X q μ :=
  eLpNorm_le_eLpNorm_of_exponent_le hpq hX

/-- HDP (1.4), Minkowski's inequality for the extended `L^p` seminorm. -/
theorem minkowski_eLpNorm (hp : 1 ≤ p)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    eLpNorm (X + Y) p μ ≤ eLpNorm X p μ + eLpNorm Y p μ :=
  eLpNorm_add_le hX hY hp

end Lp

section Holder

variable {X Y : Ω → ℝ} {p q : ℝ}

/-- Holder's inequality for real random variables, in the form displayed in
HDP Section 1.2. -/
theorem holder_integral_mul_abs
    (hpq : p.HolderConjugate q)
    (hX : MemLp X (ENNReal.ofReal p) μ)
    (hY : MemLp Y (ENNReal.ofReal q) μ) :
    |μ[fun ω => X ω * Y ω]|
      ≤ (μ[fun ω => ‖X ω‖ ^ p]) ^ (1 / p) *
        (μ[fun ω => ‖Y ω‖ ^ q]) ^ (1 / q) := by
  have habs :
      |μ[fun ω => X ω * Y ω]| ≤ μ[fun ω => |X ω * Y ω|] :=
    abs_integral_le_integral_abs
  have hholder :
      μ[fun ω => ‖X ω‖ * ‖Y ω‖]
        ≤ (μ[fun ω => ‖X ω‖ ^ p]) ^ (1 / p) *
          (μ[fun ω => ‖Y ω‖ ^ q]) ^ (1 / q) :=
    integral_mul_norm_le_Lp_mul_Lq hpq hX hY
  exact habs.trans (by simpa [abs_mul] using hholder)

/-- Cauchy-Schwarz, the `p = q = 2` case of Holder. -/
theorem cauchy_schwarz_integral_mul
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |μ[fun ω => X ω * Y ω]|
      ≤ (μ[fun ω => ‖X ω‖ ^ (2 : ℝ)]) ^ (1 / (2 : ℝ)) *
        (μ[fun ω => ‖Y ω‖ ^ (2 : ℝ)]) ^ (1 / (2 : ℝ)) :=
  holder_integral_mul_abs (μ := μ) (X := X) (Y := Y)
    (p := 2) (q := 2) Real.HolderConjugate.two_two
    (by simpa : MemLp X (ENNReal.ofReal (2 : ℝ)) μ)
    (by simpa : MemLp Y (ENNReal.ofReal (2 : ℝ)) μ)

end Holder

section TailIdentities

variable {X : Ω → ℝ}

/-- HDP Lemma 1.2.1: for a nonnegative integrable random variable,
`E X = ∫_0^∞ P{X > t} dt`. -/
theorem integral_identity_nonnegative
    (hX : Integrable X μ) (hX_nonneg : 0 ≤ᵐ[μ] X) :
    μ[X] = ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < X ω} :=
  hX.integral_eq_integral_meas_lt hX_nonneg

/-- A two-sided tail identity equivalent to HDP Exercise 1.2.2:
`E X = ∫_0^∞ P{X > t} dt - ∫_0^∞ P{X < -t} dt`. -/
theorem integral_identity_real (hX : Integrable X μ) :
    μ[X] =
      (∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < X ω})
        - ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | X ω < -t} := by
  let Xpos : Ω → ℝ := fun ω => (Real.toNNReal (X ω) : ℝ)
  let Xneg : Ω → ℝ := fun ω => (Real.toNNReal (-X ω) : ℝ)
  have hpos_int : Integrable Xpos μ := hX.real_toNNReal
  have hneg_int : Integrable Xneg μ := hX.neg.real_toNNReal
  have hpos_nonneg : 0 ≤ᵐ[μ] Xpos := .of_forall fun _ => by positivity
  have hneg_nonneg : 0 ≤ᵐ[μ] Xneg := .of_forall fun _ => by positivity
  have hpos_tail :
      μ[Xpos] = ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < X ω} := by
    rw [hpos_int.integral_eq_integral_meas_lt hpos_nonneg]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have hset : {ω : Ω | t < Xpos ω} = {ω : Ω | t < X ω} := by
      ext ω
      change t < (Real.toNNReal (X ω) : ℝ) ↔ t < X ω
      rw [Real.coe_toNNReal']
      constructor
      · intro h
        rcases lt_max_iff.mp h with h | h
        · exact h
        · exact (not_lt_of_ge ht.le h).elim
      · intro h
        exact lt_max_of_lt_left h
    simpa using congrArg μ.real hset
  have hneg_tail :
      μ[Xneg] = ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | X ω < -t} := by
    rw [hneg_int.integral_eq_integral_meas_lt hneg_nonneg]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have hset : {ω : Ω | t < Xneg ω} = {ω : Ω | X ω < -t} := by
      ext ω
      change t < (Real.toNNReal (-X ω) : ℝ) ↔ X ω < -t
      rw [Real.coe_toNNReal']
      constructor
      · intro h
        rcases lt_max_iff.mp h with h | h
        · linarith
        · exact (not_lt_of_ge ht.le h).elim
      · intro h
        apply lt_max_of_lt_left
        linarith
    simpa using congrArg μ.real hset
  calc
    μ[X] = μ[Xpos] - μ[Xneg] := by
      simpa [Xpos, Xneg] using
        (integral_eq_integral_pos_part_sub_integral_neg_part (μ := μ) hX)
    _ = (∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < X ω})
        - ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | X ω < -t} := by
      rw [hpos_tail, hneg_tail]

/-- HDP Exercise 1.2.3: absolute moments via tails, in the extended
nonnegative form where both sides may be infinite. -/
theorem eAbsoluteMoment_eq_lintegral_tail
    (hX : AEMeasurable X μ) {p : ℝ} (hp : 0 < p) :
    eAbsoluteMoment X μ p =
      ENNReal.ofReal p *
        ∫⁻ t in Set.Ioi (0 : ℝ),
          μ {ω | t < |X ω|} * ENNReal.ofReal (t ^ (p - 1)) := by
  simpa [eAbsoluteMoment] using
    MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
      (μ := μ) (f := fun ω => |X ω|)
      (.of_forall fun _ => abs_nonneg _) hX.abs hp

end TailIdentities

section MarkovChebyshev

variable {X : Ω → ℝ}

/-- HDP Proposition 1.2.4, Markov's inequality:
`P{X ≥ t} ≤ E X / t` for nonnegative `X` and `t > 0`. -/
theorem markov_inequality
    (hX_nonneg : 0 ≤ᵐ[μ] X) (hX : Integrable X μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ X ω} ≤ μ[X] / t := by
  rw [le_div_iff₀ ht]
  simpa [mul_comm] using
    (mul_meas_ge_le_integral_of_nonneg (μ := μ) hX_nonneg hX t)

/-- HDP Corollary 1.2.5, Chebyshev's inequality:
`P{|X - E X| ≥ t} ≤ Var(X)/t^2`. -/
theorem chebyshev_inequality
    [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω - μ[X]|} ≤ Var[X; μ] / t ^ 2 := by
  have h := ProbabilityTheory.meas_ge_le_variance_div_sq (μ := μ) hX (c := t) ht
  have hnonneg : 0 ≤ Var[X; μ] / t ^ 2 :=
    div_nonneg (ProbabilityTheory.variance_nonneg X μ) (sq_nonneg t)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa [MeasureTheory.measureReal_def, ENNReal.toReal_ofReal hnonneg] using hreal

end MarkovChebyshev

end LeanFpAnalysis.HDP
