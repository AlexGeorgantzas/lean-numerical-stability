import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# Random Variables: Basic Quantities

Definitions and elementary identities from HDP Chapter 1, Section 1.1.
Most objects are thin wrappers around mathlib's probability API, with names
chosen to match the book's terminology.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace LeanFpAnalysis.HDP

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Expectations

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Expectation of an `E`-valued random variable, written as an explicit
definition for HDP lookup. Mathlib notation is `μ[X]`. -/
def expectation (X : Ω → E) (μ : Measure Ω) : E :=
  ∫ ω, X ω ∂μ

@[simp]
lemma expectation_def (X : Ω → E) (μ : Measure Ω) :
    expectation X μ = μ[X] := rfl

end Expectations

section RealRandomVariables

variable (X Y : Ω → ℝ) (μ : Measure Ω)

/-- Moment-generating function `M_X(t) = E exp(tX)`. -/
def momentGeneratingFunction : ℝ → ℝ :=
  ProbabilityTheory.mgf X μ

@[simp]
lemma momentGeneratingFunction_apply (t : ℝ) :
    momentGeneratingFunction X μ t = μ[fun ω => Real.exp (t * X ω)] := rfl

/-- The `p`-th raw real moment `E X^p`, for real exponents where this expression
is meaningful. For natural moments, mathlib also provides `ProbabilityTheory.moment`. -/
def rawMoment (p : ℝ) : ℝ :=
  μ[fun ω => X ω ^ p]

/-- The `p`-th absolute moment `E |X|^p`. -/
def absoluteMoment (p : ℝ) : ℝ :=
  μ[fun ω => |X ω| ^ p]

/-- Extended nonnegative version of the absolute moment. This is the natural
form for layer-cake/tail identities, where both sides may be infinite. -/
def eAbsoluteMoment (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ

/-- The extended `L^p` seminorm used by mathlib. For probability measures and
`p ≤ q`, this is monotone in `p`; see `lpNorm_mono_exponent` in
`Inequalities.lean`. -/
def lpNorm (p : ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm X p μ

/-- The book's `L^∞` seminorm definition:
`‖X‖_{L∞} = ess sup ‖X‖`, written in extended nonnegative form. -/
theorem lpNorm_top_eq_essSup_enorm :
    lpNorm X μ ∞ = essSup (fun ω => ‖X ω‖ₑ) μ := by
  simp [lpNorm, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]

/-- Real-valued version of the book's `L^∞` seminorm definition:
`‖X‖_{L∞} = ess sup |X|`. -/
theorem lpNorm_top_eq_essSup_abs :
    lpNorm X μ ∞ = essSup (fun ω => ENNReal.ofReal |X ω|) μ := by
  rw [lpNorm_top_eq_essSup_enorm]
  congr with ω
  rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]

/-- The `L^2` inner product of real random variables: `E[XY]`. -/
def l2Inner : ℝ :=
  μ[fun ω => X ω * Y ω]

/-- The `L^2` norm written in the elementary square-root form from (1.1). -/
def l2Norm : ℝ :=
  Real.sqrt (μ[fun ω => X ω ^ 2])

/-- Standard deviation `sqrt(Var(X))`. -/
def standardDeviation : ℝ :=
  Real.sqrt (Var[X; μ])

@[simp]
lemma momentGeneratingFunction_eq_mgf :
    momentGeneratingFunction X μ = ProbabilityTheory.mgf X μ := rfl

@[simp]
lemma rawMoment_def (p : ℝ) :
    rawMoment X μ p = μ[fun ω => X ω ^ p] := rfl

@[simp]
lemma absoluteMoment_def (p : ℝ) :
    absoluteMoment X μ p = μ[fun ω => |X ω| ^ p] := rfl

@[simp]
lemma eAbsoluteMoment_def (p : ℝ) :
    eAbsoluteMoment X μ p = ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ := rfl

@[simp]
lemma lpNorm_def (p : ℝ≥0∞) :
    lpNorm X μ p = eLpNorm X p μ := rfl

@[simp]
lemma l2Inner_def :
    l2Inner X Y μ = μ[fun ω => X ω * Y ω] := rfl

@[simp]
lemma l2Norm_def :
    l2Norm X μ = Real.sqrt (μ[fun ω => X ω ^ 2]) := rfl

@[simp]
lemma standardDeviation_def :
    standardDeviation X μ = Real.sqrt (Var[X; μ]) := rfl

/-- HDP (1.1): the `L^2` inner product is expectation of the product. -/
theorem l2Inner_eq_expectation_mul :
    l2Inner X Y μ = expectation (fun ω => X ω * Y ω) μ := rfl

/-- HDP (1.1): `‖X‖_2 = (E |X|^2)^{1/2}`. -/
theorem l2Norm_eq_sqrt_absMoment :
    l2Norm X μ = Real.sqrt (absoluteMoment X μ 2) := by
  simp [l2Norm, absoluteMoment, sq_abs]

/-- Variance as `E (X - EX)^2`, matching the definition displayed in Section 1.1. -/
theorem variance_eq_expectation_sq_sub_mean (hX : AEMeasurable X μ) :
    Var[X; μ] = μ[fun ω => (X ω - μ[X]) ^ 2] :=
  ProbabilityTheory.variance_eq_integral hX

/-- Standard deviation squared is the variance. -/
theorem standardDeviation_sq :
    standardDeviation X μ ^ 2 = Var[X; μ] := by
  simp [standardDeviation, Real.sq_sqrt (ProbabilityTheory.variance_nonneg X μ)]

/-- The standard deviation is the `L^2` norm of the centered variable. -/
theorem standardDeviation_eq_l2Norm_centered (hX : AEMeasurable X μ) :
    standardDeviation X μ = l2Norm (fun ω => X ω - μ[X]) μ := by
  simp [standardDeviation, l2Norm, ProbabilityTheory.variance_eq_integral hX]

/-- HDP (1.2): covariance is the `L^2` inner product of centered variables. -/
theorem covariance_eq_l2Inner_centered :
    cov[X, Y; μ] =
      l2Inner (fun ω => X ω - μ[X]) (fun ω => Y ω - μ[Y]) μ := rfl

/-- The second central moment is the variance. -/
theorem centralMoment_two_eq_variance (hX : AEMeasurable X μ) :
    ProbabilityTheory.centralMoment X 2 μ = Var[X; μ] :=
  ProbabilityTheory.centralMoment_two_eq_variance hX

end RealRandomVariables

section LpSpace

variable [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- Book-facing membership predicate for `L^p`: random variables with finite
`L^p` seminorm, together with mathlib's a.e. strong measurability condition. -/
def hdpMemLp (X : Ω → E) (p : ℝ≥0∞) (μ : Measure Ω) : Prop :=
  MemLp X p μ

/-- The actual `L^p` space, using mathlib's quotient space of a.e.-equal functions. -/
abbrev hdpLp (F : Type*) [NormedAddCommGroup F] (p : ℝ≥0∞) (μ : Measure Ω) :=
  Lp F p μ

/-- HDP set-builder notation for `L^p` agrees with mathlib's `MemLp`. -/
theorem hdpMemLp_iff_memLp (X : Ω → E) :
    hdpMemLp X p μ ↔ MemLp X p μ := Iff.rfl

/-- Expanded HDP description of `L^p`: a.e. strong measurability plus finite
extended `L^p` seminorm. -/
theorem hdpMemLp_iff_aestronglyMeasurable_and_eLpNorm_lt_top (X : Ω → E) :
    hdpMemLp X p μ ↔ AEStronglyMeasurable X μ ∧ eLpNorm X p μ < ∞ := Iff.rfl

end LpSpace

section LpGeometry

variable [NormedAddCommGroup E]

/-- HDP Section 1.1: for `1 ≤ p`, mathlib's `Lp E p μ` is complete. -/
theorem hdpLp_completeSpace [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    CompleteSpace (hdpLp (Ω := Ω) E p μ) := by
  infer_instance

/-- HDP Section 1.1: `L^2` of real random variables is a Hilbert space. -/
def hdpL2_real_innerProductSpace :
    InnerProductSpace ℝ (hdpLp (Ω := Ω) ℝ 2 μ) := by
  infer_instance

/-- HDP Section 1.1: `L^2` of real random variables is complete. -/
theorem hdpL2_real_completeSpace :
    CompleteSpace (hdpLp (Ω := Ω) ℝ 2 μ) := by
  infer_instance

end LpGeometry

section DistributionFunctions

variable (X : Ω → ℝ) (μ : Measure Ω)

/-- The law/distribution of a real random variable. -/
def distribution : Measure ℝ :=
  μ.map X

/-- Cumulative distribution function `F_X(t) = P{X ≤ t}`. -/
def cumulativeDistribution (t : ℝ) : ℝ :=
  μ.real {ω | X ω ≤ t}

/-- Upper tail `P{X > t}`. -/
def upperTail (t : ℝ) : ℝ :=
  μ.real {ω | t < X ω}

/-- Closed upper tail `P{X ≥ t}`. -/
def closedUpperTail (t : ℝ) : ℝ :=
  μ.real {ω | t ≤ X ω}

/-- Lower strict tail `P{X < t}`. -/
def lowerTail (t : ℝ) : ℝ :=
  μ.real {ω | X ω < t}

@[simp]
lemma distribution_def :
    distribution X μ = μ.map X := rfl

@[simp]
lemma cumulativeDistribution_def (t : ℝ) :
    cumulativeDistribution X μ t = μ.real {ω | X ω ≤ t} := rfl

@[simp]
lemma upperTail_def (t : ℝ) :
    upperTail X μ t = μ.real {ω | t < X ω} := rfl

@[simp]
lemma closedUpperTail_def (t : ℝ) :
    closedUpperTail X μ t = μ.real {ω | t ≤ X ω} := rfl

@[simp]
lemma lowerTail_def (t : ℝ) :
    lowerTail X μ t = μ.real {ω | X ω < t} := rfl

/-- The HDP CDF agrees with the real measure of the `Iic` set under the law of `X`. -/
theorem cumulativeDistribution_eq_distribution_Iic (hX : Measurable X) (t : ℝ) :
    cumulativeDistribution X μ t = (distribution X μ).real (Set.Iic t) := by
  rw [cumulativeDistribution, distribution, MeasureTheory.map_measureReal_apply hX measurableSet_Iic]
  rfl

/-- The closed upper tail agrees with the real measure of the `Ici` set under the law of `X`. -/
theorem closedUpperTail_eq_distribution_Ici (hX : Measurable X) (t : ℝ) :
    closedUpperTail X μ t = (distribution X μ).real (Set.Ici t) := by
  rw [closedUpperTail, distribution, MeasureTheory.map_measureReal_apply hX measurableSet_Ici]
  rfl

/-- Tail/CDF relation `P{X > t} = 1 - F_X(t)` for probability measures. -/
theorem upperTail_eq_one_sub_cdf [IsProbabilityMeasure μ] (hX : Measurable X) (t : ℝ) :
    upperTail X μ t = 1 - cumulativeDistribution X μ t := by
  have hset : {ω : Ω | t < X ω} = {ω : Ω | X ω ≤ t}ᶜ := by
    ext ω
    simp [not_le]
  have hmeas : MeasurableSet {ω : Ω | X ω ≤ t} :=
    measurableSet_le hX measurable_const
  simp [upperTail, cumulativeDistribution, hset, MeasureTheory.measureReal_compl hmeas]

/-- Closed-tail/open-lower-tail relation `P{X ≥ t} = 1 - P{X < t}`. -/
theorem closedUpperTail_eq_one_sub_lowerTail [IsProbabilityMeasure μ]
    (hX : Measurable X) (t : ℝ) :
    closedUpperTail X μ t = 1 - lowerTail X μ t := by
  have hset : {ω : Ω | t ≤ X ω} = {ω : Ω | X ω < t}ᶜ := by
    ext ω
    simp [not_lt]
  have hmeas : MeasurableSet {ω : Ω | X ω < t} :=
    measurableSet_lt hX measurable_const
  simp [closedUpperTail, lowerTail, hset, MeasureTheory.measureReal_compl hmeas]

end DistributionFunctions

section CDFDeterminesLaw

variable {Ω' : Type*} [MeasurableSpace Ω']
variable {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
variable {X : Ω → ℝ} {Y : Ω' → ℝ}

/-- HDP Section 1.1: a real-valued random variable's CDF determines its law. -/
theorem distribution_eq_of_cdf_eq
    (hX : Measurable X) (hY : Measurable Y)
    (hCDF : ∀ t : ℝ,
      cumulativeDistribution X μ t = cumulativeDistribution Y ν t) :
    distribution X μ = distribution Y ν := by
  haveI : IsFiniteMeasure (distribution X μ) := by
    simpa [distribution] using Measure.isFiniteMeasure_map μ X
  haveI : IsFiniteMeasure (distribution Y ν) := by
    simpa [distribution] using Measure.isFiniteMeasure_map ν Y
  refine Measure.ext_of_Iic (distribution X μ) (distribution Y ν) fun t => ?_
  have hreal :
      (distribution X μ).real (Set.Iic t) = (distribution Y ν).real (Set.Iic t) := by
    exact
      (cumulativeDistribution_eq_distribution_Iic (X := X) (μ := μ) hX t).symm.trans
        ((hCDF t).trans
          (cumulativeDistribution_eq_distribution_Iic (X := Y) (μ := ν) hY t))
  exact (MeasureTheory.measureReal_eq_measureReal_iff
    (μ := distribution X μ) (ν := distribution Y ν)
    (s := Set.Iic t) (t := Set.Iic t)).mp hreal

end CDFDeterminesLaw

section NamedDistributions

/-- The standard normal density from HDP (1.6). -/
def standardNormalDensity (x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 1 x

/-- The standard normal probability measure `N(0,1)`. -/
def standardNormalMeasure : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 1

instance : IsProbabilityMeasure standardNormalMeasure :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 1

/-- The standard normal density in the elementary form `1 / sqrt(2π) * exp(-x^2/2)`. -/
theorem standardNormalDensity_eq (x : ℝ) :
    standardNormalDensity x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  simp [standardNormalDensity, ProbabilityTheory.gaussianPDFReal, div_eq_mul_inv,
    mul_comm, mul_left_comm]

end NamedDistributions

end LeanFpAnalysis.HDP
