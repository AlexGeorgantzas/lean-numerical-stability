import LeanFpAnalysis.HDP.Probability.RandomVariables
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
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

/-- Cauchy-Schwarz with the constant `1`: on a probability space,
`E |X| ≤ (E X^2)^{1/2}`. This is the inequality used in HDP
Exercise 1.3.3. -/
theorem integral_abs_le_sqrt_integral_sq
    [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) :
    μ[fun ω => |X ω|] ≤ Real.sqrt (μ[fun ω => X ω ^ 2]) := by
  have h_abs_lp : MemLp (fun ω => |X ω|) 2 μ := by
    simpa [Real.norm_eq_abs] using hX.norm
  have h_one_lp : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ := memLp_const (1 : ℝ)
  have hcs :=
    cauchy_schwarz_integral_mul (μ := μ)
      (X := fun ω => |X ω|) (Y := fun _ : Ω => (1 : ℝ))
      h_abs_lp h_one_lp
  have h_nonneg : 0 ≤ μ[fun ω => |X ω|] :=
    integral_nonneg fun _ => abs_nonneg _
  simpa [abs_of_nonneg h_nonneg, Real.norm_eq_abs, Real.sqrt_eq_rpow, sq_abs] using hcs

/-- Hölder endpoint from HDP Section 1.2 in extended-norm form:
the case `p = 1`, `q = ∞`. -/
theorem holder_eLpNorm_one_top
    (hX : MemLp X 1 μ)
    (hY : MemLp Y ∞ μ) :
    ENNReal.ofReal |μ[fun ω => X ω * Y ω]|
      ≤ eLpNorm X 1 μ * eLpNorm Y ∞ μ := by
  have h_smul :
      eLpNorm (fun ω => Y ω * X ω) 1 μ
        ≤ eLpNorm Y ∞ μ * eLpNorm X 1 μ := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.eLpNorm_smul_le_mul_eLpNorm
        (μ := μ) (f := X) (φ := Y) (p := ∞) (q := 1) (r := 1)
        hX.aestronglyMeasurable hY.aestronglyMeasurable)
  have h_comm :
    eLpNorm (fun ω => X ω * Y ω) 1 μ =
        eLpNorm (fun ω => Y ω * X ω) 1 μ :=
    eLpNorm_congr_ae <| ae_of_all μ fun ω => by simp [mul_comm]
  calc
    ENNReal.ofReal |μ[fun ω => X ω * Y ω]|
        = ‖μ[fun ω => X ω * Y ω]‖ₑ := by
          rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    _ ≤ ∫⁻ ω, ‖X ω * Y ω‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun ω => X ω * Y ω) 1 μ := by
          rw [eLpNorm_one_eq_lintegral_enorm]
    _ ≤ eLpNorm Y ∞ μ * eLpNorm X 1 μ := by
          rw [h_comm]
          exact h_smul
    _ = eLpNorm X 1 μ * eLpNorm Y ∞ μ := by
          rw [mul_comm]

/-- Hölder endpoint from HDP Section 1.2: the displayed real-valued case
`p = 1`, `q = ∞`. -/
theorem holder_integral_mul_abs_one_top
    (hX : MemLp X 1 μ)
    (hY : MemLp Y ∞ μ) :
    |μ[fun ω => X ω * Y ω]|
      ≤ μ[fun ω => |X ω|] * (eLpNorm Y ∞ μ).toReal := by
  have h := holder_eLpNorm_one_top (μ := μ) (X := X) (Y := Y) hX hY
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hX.eLpNorm_ne_top hY.eLpNorm_ne_top) h
  simpa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
    MeasureTheory.toReal_eLpNorm hX.aestronglyMeasurable,
    MeasureTheory.lpNorm_one_eq_integral_norm hX.aestronglyMeasurable,
    Real.norm_eq_abs] using hreal

end Holder

section TailIdentities

variable {X : Ω → ℝ}

/-- HDP Lemma 1.2.1 for extended nonnegative random variables, with real
thresholds. This is the natural `ℝ≥0∞` formulation in the current mathlib
setup, where there is no canonical Lebesgue `volume` measure on `ℝ≥0∞`.

The finite-a.e. hypothesis is automatic for ordinary real-valued nonnegative
random variables; the fully infinite-valued case is handled by the more general
lintegral API rather than a `volume : Measure ℝ≥0∞` identity. -/
theorem lintegral_identity_nonnegative_ennreal
    {X : Ω → ℝ≥0∞}
    (hX : AEMeasurable X μ)
    (hX_finite : ∀ᵐ ω ∂μ, X ω < ∞) :
    ∫⁻ ω, X ω ∂μ =
      ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | ENNReal.ofReal t < X ω} := by
  have hreal :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt
      μ
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      hX.ennreal_toReal
  have hfinite_ne : ∀ᵐ ω ∂μ, X ω ≠ ∞ :=
    hX_finite.mono fun _ hω => ne_of_lt hω
  calc
    ∫⁻ ω, X ω ∂μ
        = ∫⁻ ω, ENNReal.ofReal ((X ω).toReal) ∂μ := by
          exact (lintegral_congr_ae (ofReal_toReal_ae_eq hX_finite)).symm
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | t < (X ω).toReal} := hreal
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | ENNReal.ofReal t < X ω} := by
      apply lintegral_congr_ae
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with t ht
      apply measure_congr
      filter_upwards [hfinite_ne] with ω hω
      exact propext ((ENNReal.ofReal_lt_iff_lt_toReal ht.le hω).symm)

/-- HDP Lemma 1.2.1 for `ℝ≥0∞` variables that are finite a.e.

This wrapper makes the finite-a.e. hypothesis explicit. In the current
mathlib layer-cake API, the chapter-facing fully infinite identity is available
for real-valued nonnegative random variables; this `ℝ≥0∞` real-threshold form
uses `toReal`, and therefore needs `X < ∞` a.e. -/
theorem lintegral_identity_nonnegative_ennreal_of_ae_lt_top
    {X : Ω → ℝ≥0∞}
    (hX : AEMeasurable X μ)
    (hX_finite : ∀ᵐ ω ∂μ, X ω < ∞) :
    ∫⁻ ω, X ω ∂μ =
      ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | ENNReal.ofReal t < X ω} :=
  lintegral_identity_nonnegative_ennreal (μ := μ) hX hX_finite

/-- HDP Lemma 1.2.1 in extended form for real nonnegative random variables:
both sides may be infinite. -/
theorem lintegral_identity_nonnegative_real
    (hX : AEMeasurable X μ) (hX_nonneg : 0 ≤ᵐ[μ] X) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ =
      ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | t < X ω} :=
  MeasureTheory.lintegral_eq_lintegral_meas_lt μ hX_nonneg hX

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

/-- HDP Exercise 1.2.2 in the exact displayed form from the book:
`E X = ∫_0^∞ P{X > t} dt - ∫_{-∞}^0 P{X < t} dt`. -/
theorem integral_identity_real_book_form (hX : Integrable X μ) :
    μ[X] =
      (∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < X ω})
        - ∫ t in Set.Iio (0 : ℝ), μ.real {ω | X ω < t} := by
  rw [integral_identity_real (μ := μ) hX]
  congr 1
  calc
    (∫ t in Set.Ioi (0 : ℝ), μ.real {ω | X ω < -t})
        = ∫ t in Set.Iic (0 : ℝ), μ.real {ω | X ω < t} := by
          simpa using
            (integral_comp_neg_Ioi
              (0 : ℝ) (fun t : ℝ => μ.real {ω | X ω < t}))
    _ = ∫ t in Set.Iio (0 : ℝ), μ.real {ω | X ω < t} :=
          MeasureTheory.integral_Iic_eq_integral_Iio

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

/-- HDP Exercise 1.2.3 in the finite real-valued form displayed in the book:
`E |X|^p = ∫_0^∞ p t^(p-1) P{|X| > t} dt`. -/
theorem absoluteMoment_eq_integral_tail
    [IsProbabilityMeasure μ]
    (hX : AEMeasurable X μ)
    {p : ℝ} (hp : 0 < p)
    (hMoment : Integrable (fun ω => |X ω| ^ p) μ)
    (hTail :
      Integrable
        (fun t : ℝ => p * t ^ (p - 1) * μ.real {ω | t < |X ω|})
        (volume.restrict (Set.Ioi (0 : ℝ)))) :
    absoluteMoment X μ p =
      ∫ t in Set.Ioi (0 : ℝ),
        p * t ^ (p - 1) * μ.real {ω | t < |X ω|} := by
  let tail : ℝ → ℝ :=
    fun t => p * t ^ (p - 1) * μ.real {ω | t < |X ω|}
  have htail_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] tail := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    exact mul_nonneg
      (mul_nonneg hp.le (Real.rpow_nonneg ht.le (p - 1)))
      (measureReal_nonneg)
  have h_abs_nonneg : 0 ≤ absoluteMoment X μ p := by
    exact integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) p
  have h_tail_integral_nonneg :
      0 ≤ ∫ t in Set.Ioi (0 : ℝ),
        p * t ^ (p - 1) * μ.real {ω | t < |X ω|} := by
    exact integral_nonneg_of_ae htail_nonneg
  have hleft :
      ENNReal.ofReal (absoluteMoment X μ p) = eAbsoluteMoment X μ p := by
    simpa [absoluteMoment, eAbsoluteMoment] using
      (ofReal_integral_eq_lintegral_ofReal
        (μ := μ) (f := fun ω => |X ω| ^ p) hMoment
        (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) p))
  have hright :
      ENNReal.ofReal
        (∫ t in Set.Ioi (0 : ℝ),
          p * t ^ (p - 1) * μ.real {ω | t < |X ω|})
        =
      ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (tail t) := by
    simpa [tail] using
      (ofReal_integral_eq_lintegral_ofReal
        (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := tail)
        hTail htail_nonneg)
  have hlin_tail :
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (tail t)
        =
      ENNReal.ofReal p *
        ∫⁻ t in Set.Ioi (0 : ℝ),
          μ {ω | t < |X ω|} * ENNReal.ofReal (t ^ (p - 1)) := by
    rw [← lintegral_const_mul'
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (ENNReal.ofReal p)
      (fun t : ℝ => μ {ω | t < |X ω|} * ENNReal.ofReal (t ^ (p - 1)))
      ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht_pow_nonneg : 0 ≤ t ^ (p - 1) :=
      Real.rpow_nonneg ht.le (p - 1)
    have hμ_nonneg : 0 ≤ μ.real {ω | t < |X ω|} :=
      measureReal_nonneg
    change ENNReal.ofReal
        (p * t ^ (p - 1) * μ.real {ω | t < |X ω|}) =
      ENNReal.ofReal p *
        (μ {ω | t < |X ω|} * ENNReal.ofReal (t ^ (p - 1)))
    rw [ENNReal.ofReal_mul (mul_nonneg hp.le ht_pow_nonneg),
      ENNReal.ofReal_mul hp.le, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ _)]
    ac_rfl
  have hofReal_eq :
      ENNReal.ofReal (absoluteMoment X μ p) =
      ENNReal.ofReal
        (∫ t in Set.Ioi (0 : ℝ),
          p * t ^ (p - 1) * μ.real {ω | t < |X ω|}) := by
    rw [hleft, eAbsoluteMoment_eq_lintegral_tail (μ := μ) (X := X) hX hp,
      ← hlin_tail, ← hright]
  exact (ENNReal.ofReal_eq_ofReal_iff h_abs_nonneg h_tail_integral_nonneg).mp hofReal_eq

/-- HDP Exercise 1.2.3 in the exact finite-tail form: if the extended
right-hand tail integral is finite, then the real-valued absolute-moment
identity follows. -/
theorem absoluteMoment_eq_integral_tail_of_lintegral_tail_lt_top
    [IsProbabilityMeasure μ]
    (hX : AEMeasurable X μ)
    {p : ℝ} (hp : 0 < p)
    (hfinite :
      (∫⁻ t in Set.Ioi (0 : ℝ),
        μ {ω | t < |X ω|} *
          ENNReal.ofReal (p * t ^ (p - 1))) < ∞) :
    absoluteMoment X μ p =
      ∫ t in Set.Ioi (0 : ℝ),
        p * t ^ (p - 1) * μ.real {ω | t < |X ω|} := by
  classical
  let tail : ℝ → ℝ :=
    fun t => p * t ^ (p - 1) * μ.real {ω | t < |X ω|}
  have htail_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] tail := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    exact mul_nonneg
      (mul_nonneg hp.le (Real.rpow_nonneg ht.le (p - 1)))
      measureReal_nonneg
  have htail_prob_meas :
      Measurable (fun t : ℝ => μ.real {ω | t < |X ω|}) := by
    refine Antitone.measurable ?_
    intro s t hst
    exact measureReal_mono fun _ hω => lt_of_le_of_lt hst hω
  have htail_meas : Measurable tail := by
    have hfactor : Measurable (fun t : ℝ => p * t ^ (p - 1)) := by
      fun_prop
    simpa [tail, mul_assoc] using hfactor.mul htail_prob_meas
  have htail_lintegral :
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (tail t)) =
        ∫⁻ t in Set.Ioi (0 : ℝ),
          μ {ω | t < |X ω|} *
            ENNReal.ofReal (p * t ^ (p - 1)) := by
    apply lintegral_congr_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have hpt_nonneg : 0 ≤ p * t ^ (p - 1) :=
      mul_nonneg hp.le (Real.rpow_nonneg ht.le (p - 1))
    change ENNReal.ofReal
        (p * t ^ (p - 1) * μ.real {ω | t < |X ω|}) =
      μ {ω | t < |X ω|} *
        ENNReal.ofReal (p * t ^ (p - 1))
    rw [ENNReal.ofReal_mul hpt_nonneg, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ _)]
    ac_rfl
  have hTail :
      Integrable tail (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine ⟨htail_meas.aemeasurable.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal htail_nonneg).mpr
      (by rw [htail_lintegral]; exact hfinite)
  have hlin_tail :
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (tail t)
        =
      ENNReal.ofReal p *
        ∫⁻ t in Set.Ioi (0 : ℝ),
          μ {ω | t < |X ω|} * ENNReal.ofReal (t ^ (p - 1)) := by
    rw [← lintegral_const_mul'
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (ENNReal.ofReal p)
      (fun t : ℝ => μ {ω | t < |X ω|} * ENNReal.ofReal (t ^ (p - 1)))
      ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht_pow_nonneg : 0 ≤ t ^ (p - 1) :=
      Real.rpow_nonneg ht.le (p - 1)
    change ENNReal.ofReal
        (p * t ^ (p - 1) * μ.real {ω | t < |X ω|}) =
      ENNReal.ofReal p *
        (μ {ω | t < |X ω|} * ENNReal.ofReal (t ^ (p - 1)))
    rw [ENNReal.ofReal_mul (mul_nonneg hp.le ht_pow_nonneg),
      ENNReal.ofReal_mul hp.le, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ _)]
    ac_rfl
  have hMoment_lintegral :
      eAbsoluteMoment X μ p < ∞ := by
    rw [eAbsoluteMoment_eq_lintegral_tail (μ := μ) (X := X) hX hp,
      ← hlin_tail, htail_lintegral]
    exact hfinite
  have hMoment :
      Integrable (fun ω => |X ω| ^ p) μ := by
    refine ⟨(hX.abs.pow_const p).aestronglyMeasurable, ?_⟩
    exact
      (hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun ω =>
          Real.rpow_nonneg (abs_nonneg (X ω)) p)).mpr
        (by simpa [eAbsoluteMoment] using hMoment_lintegral)
  exact
    absoluteMoment_eq_integral_tail
      (μ := μ) hX hp hMoment hTail

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
