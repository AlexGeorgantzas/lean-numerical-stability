import LeanFpAnalysis.HDP.Probability.Concentration.Normal
import LeanFpAnalysis.HDP.Probability.RandomVariables
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Berry-Esseen Interface

Book-facing definitions for HDP Theorem 2.1.3, the Berry-Esseen central limit
theorem.  This file contains the measure/CDF/tail vocabulary and consequences
that the Fourier smoothing proof must discharge.  It intentionally does not
pretend that a proposition-valued theorem target is a proof of Berry-Esseen.
The current genuine proof lives in `BerryEsseenSmoothing.lean` and proves the
public theorem with constant `C = 3`; exact-constant `C = 1` promotion lemmas are
kept there as conditional bridge API for later completion.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace LeanFpAnalysis.HDP

section CDFError

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The CDF of the standard normal distribution. -/
def standardNormalCDF (t : ℝ) : ℝ :=
  standardNormalMeasure.real (Set.Iic t)

@[simp]
lemma standardNormalCDF_def (t : ℝ) :
    standardNormalCDF t = standardNormalMeasure.real (Set.Iic t) := rfl

/-- Pointwise Kolmogorov/CDF error against the standard normal law. -/
def cdfErrorAt (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  |cumulativeDistribution X μ t - standardNormalCDF t|

@[simp]
lemma cdfErrorAt_nonneg (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) :
    0 ≤ cdfErrorAt X μ t := by
  simp [cdfErrorAt]

/-- Uniform CDF-error bound against the standard normal law. -/
def cdfErrorBound (X : Ω → ℝ) (μ : Measure Ω) (ε : ℝ) : Prop :=
  ∀ t : ℝ, cdfErrorAt X μ t ≤ ε

lemma cdfErrorBound_mono {X : Ω → ℝ} {ε δ : ℝ}
    (h : cdfErrorBound X μ ε) (hεδ : ε ≤ δ) :
    cdfErrorBound X μ δ := by
  intro t
  exact (h t).trans hεδ

lemma cdfErrorBound_of_standardNormalCDF_eq
    {X : Ω → ℝ} {ε : ℝ}
    (hCDF : ∀ t : ℝ, cumulativeDistribution X μ t = standardNormalCDF t)
    (hε : 0 ≤ ε) :
    cdfErrorBound X μ ε := by
  intro t
  rw [cdfErrorAt, hCDF t]
  simpa using hε

lemma cdfErrorBound_of_map_eq_standardNormal
    {X : Ω → ℝ} {ε : ℝ}
    (hX : Measurable X)
    (hLaw : μ.map X = standardNormalMeasure)
    (hε : 0 ≤ ε) :
    cdfErrorBound X μ ε := by
  refine cdfErrorBound_of_standardNormalCDF_eq (μ := μ) ?_ hε
  intro t
  rw [cumulativeDistribution_eq_distribution_Iic (X := X) (μ := μ) hX t]
  simp [distribution, standardNormalCDF, hLaw]

end CDFError

section UpperTailError

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Strict upper tail of the standard normal law, `P{g > t}`. -/
def standardNormalUpperTail (t : ℝ) : ℝ :=
  standardNormalMeasure.real (Set.Ioi t)

/-- Closed upper tail of the standard normal law, `P{g ≥ t}`. -/
def standardNormalClosedUpperTail (t : ℝ) : ℝ :=
  standardNormalMeasure.real (Set.Ici t)

@[simp]
lemma standardNormalUpperTail_def (t : ℝ) :
    standardNormalUpperTail t = standardNormalMeasure.real (Set.Ioi t) := rfl

@[simp]
lemma standardNormalClosedUpperTail_def (t : ℝ) :
    standardNormalClosedUpperTail t = standardNormalMeasure.real (Set.Ici t) := rfl

lemma standardNormalUpperTail_eq_one_sub_cdf (t : ℝ) :
    standardNormalUpperTail t = 1 - standardNormalCDF t := by
  have hcompl : (Set.Iic t : Set ℝ)ᶜ = Set.Ioi t := by
    ext x
    simp
  have hIic : MeasurableSet (Set.Iic t : Set ℝ) := measurableSet_Iic
  rw [standardNormalUpperTail, standardNormalCDF, ← hcompl]
  simpa using MeasureTheory.measureReal_compl (μ := standardNormalMeasure) hIic

/-- Closed-tail/open-left-tail relation for the standard normal law. -/
lemma standardNormalClosedUpperTail_eq_one_sub_Iio (t : ℝ) :
    standardNormalClosedUpperTail t = 1 - standardNormalMeasure.real (Set.Iio t) := by
  have hcompl : (Set.Iio t : Set ℝ)ᶜ = Set.Ici t := by
    ext x
    simp
  have hIio : MeasurableSet (Set.Iio t : Set ℝ) := measurableSet_Iio
  rw [standardNormalClosedUpperTail, ← hcompl]
  simpa using MeasureTheory.measureReal_compl (μ := standardNormalMeasure) hIio

/-- Pointwise strict-upper-tail error against the standard normal law. -/
def upperTailErrorAt (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  |upperTail X μ t - standardNormalUpperTail t|

/-- Pointwise closed-upper-tail error against the standard normal law. -/
def closedUpperTailErrorAt (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  |closedUpperTail X μ t - standardNormalClosedUpperTail t|

@[simp]
lemma upperTailErrorAt_nonneg (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) :
    0 ≤ upperTailErrorAt X μ t := by
  simp [upperTailErrorAt]

@[simp]
lemma closedUpperTailErrorAt_nonneg (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) :
    0 ≤ closedUpperTailErrorAt X μ t := by
  simp [closedUpperTailErrorAt]

/-- Uniform strict-upper-tail error bound against the standard normal law. -/
def upperTailErrorBound (X : Ω → ℝ) (μ : Measure Ω) (ε : ℝ) : Prop :=
  ∀ t : ℝ, upperTailErrorAt X μ t ≤ ε

/-- Uniform closed-upper-tail error bound against the standard normal law. -/
def closedUpperTailErrorBound (X : Ω → ℝ) (μ : Measure Ω) (ε : ℝ) : Prop :=
  ∀ t : ℝ, closedUpperTailErrorAt X μ t ≤ ε

lemma upperTailErrorBound_mono {X : Ω → ℝ} {ε δ : ℝ}
    (h : upperTailErrorBound X μ ε) (hεδ : ε ≤ δ) :
    upperTailErrorBound X μ δ := by
  intro t
  exact (h t).trans hεδ

lemma closedUpperTailErrorBound_mono {X : Ω → ℝ} {ε δ : ℝ}
    (h : closedUpperTailErrorBound X μ ε) (hεδ : ε ≤ δ) :
    closedUpperTailErrorBound X μ δ := by
  intro t
  exact (h t).trans hεδ

lemma upperTailErrorBound_of_cdfErrorBound
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {ε : ℝ}
    (hX : Measurable X) (h : cdfErrorBound X μ ε) :
    upperTailErrorBound X μ ε := by
  intro t
  rw [upperTailErrorAt, upperTail_eq_one_sub_cdf (X := X) (μ := μ) hX t,
    standardNormalUpperTail_eq_one_sub_cdf t]
  simpa [cdfErrorAt, sub_sub_sub_cancel_right, abs_sub_comm] using h t

end UpperTailError

section MeasureCDFError

/-- Measure-level uniform CDF-error bound.  This is the Kolmogorov-distance
inequality written as a predicate, avoiding a supremum until it is needed. -/
def measureCDFErrorLE (ν η : Measure ℝ) (ε : ℝ) : Prop :=
  ∀ t : ℝ, |ν.real (Set.Iic t) - η.real (Set.Iic t)| ≤ ε

/-- Measure-level strict-upper-tail bound. -/
def measureUpperTailErrorLE (ν η : Measure ℝ) (ε : ℝ) : Prop :=
  ∀ t : ℝ, |ν.real (Set.Ioi t) - η.real (Set.Ioi t)| ≤ ε

lemma measureCDFErrorLE_refl (ν : Measure ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    measureCDFErrorLE ν ν ε := by
  intro t
  simpa [measureCDFErrorLE] using hε

lemma measureCDFErrorLE_symm {ν η : Measure ℝ} {ε : ℝ}
    (h : measureCDFErrorLE ν η ε) :
    measureCDFErrorLE η ν ε := by
  intro t
  simpa [measureCDFErrorLE, abs_sub_comm] using h t

lemma measureCDFErrorLE_mono {ν η : Measure ℝ} {ε δ : ℝ}
    (h : measureCDFErrorLE ν η ε) (hεδ : ε ≤ δ) :
    measureCDFErrorLE ν η δ := by
  intro t
  exact (h t).trans hεδ

lemma measureCDFErrorLE_one
    (ν η : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
    measureCDFErrorLE ν η 1 := by
  intro t
  have hνnonneg : 0 ≤ ν.real (Set.Iic t) := measureReal_nonneg
  have hηnonneg : 0 ≤ η.real (Set.Iic t) := measureReal_nonneg
  have hνle : ν.real (Set.Iic t) ≤ 1 := by
    simpa using measureReal_mono (μ := ν) (s₁ := Set.Iic t)
      (s₂ := Set.univ) (Set.subset_univ _)
  have hηle : η.real (Set.Iic t) ≤ 1 := by
    simpa using measureReal_mono (μ := η) (s₁ := Set.Iic t)
      (s₂ := Set.univ) (Set.subset_univ _)
  rw [abs_sub_le_iff]
  constructor <;> linarith

lemma cdfErrorBound_of_measureCDFErrorLE
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {ε : ℝ}
    (hX : AEMeasurable X μ)
    (h : measureCDFErrorLE (μ.map X) standardNormalMeasure ε) :
    cdfErrorBound X μ ε := by
  intro t
  have hmap :
      (μ.map X).real (Set.Iic t) = μ.real {ω | X ω ≤ t} := by
    rw [measureReal_def,
      Measure.map_apply_of_aemeasurable hX measurableSet_Iic]
    rfl
  simpa [cdfErrorAt, cumulativeDistribution, standardNormalCDF, hmap] using h t

lemma measureCDFErrorLE_triangle {ν η κ : Measure ℝ} {ε δ : ℝ}
    (hνη : measureCDFErrorLE ν η ε)
    (hηκ : measureCDFErrorLE η κ δ) :
    measureCDFErrorLE ν κ (ε + δ) := by
  intro t
  calc
    |ν.real (Set.Iic t) - κ.real (Set.Iic t)|
        = |(ν.real (Set.Iic t) - η.real (Set.Iic t)) +
            (η.real (Set.Iic t) - κ.real (Set.Iic t))| := by
          congr 1
          ring
    _ ≤ |ν.real (Set.Iic t) - η.real (Set.Iic t)| +
        |η.real (Set.Iic t) - κ.real (Set.Iic t)| := abs_add_le _ _
    _ ≤ ε + δ := add_le_add (hνη t) (hηκ t)

lemma measureUpperTailErrorLE_of_measureCDFErrorLE
    {ν η : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure η] {ε : ℝ}
    (h : measureCDFErrorLE ν η ε) :
    measureUpperTailErrorLE ν η ε := by
  intro t
  have hcompl : (Set.Iic t : Set ℝ)ᶜ = Set.Ioi t := by
    ext x
    simp
  have hIic : MeasurableSet (Set.Iic t : Set ℝ) := measurableSet_Iic
  rw [← hcompl, MeasureTheory.measureReal_compl (μ := ν) hIic,
    MeasureTheory.measureReal_compl (μ := η) hIic]
  simpa [measureCDFErrorLE, sub_sub_sub_cancel_right, abs_sub_comm] using h t

lemma upperTailErrorBound_of_measureUpperTailErrorLE
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {ε : ℝ}
    (hX : AEMeasurable X μ)
    (h : measureUpperTailErrorLE (μ.map X) standardNormalMeasure ε) :
    upperTailErrorBound X μ ε := by
  intro t
  have hmap :
      (μ.map X).real (Set.Ioi t) = μ.real {ω | t < X ω} := by
    rw [measureReal_def,
      Measure.map_apply_of_aemeasurable hX measurableSet_Ioi]
    rfl
  simpa [upperTailErrorAt, upperTail, standardNormalUpperTail, hmap] using h t

/-- Measure-level closed-upper-tail bound. -/
def measureClosedUpperTailErrorLE (ν η : Measure ℝ) (ε : ℝ) : Prop :=
  ∀ t : ℝ, |ν.real (Set.Ici t) - η.real (Set.Ici t)| ≤ ε

lemma tendsto_measureReal_iUnion_atTop
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
    {s : ι → Set α} (hs : Monotone s) :
    Tendsto (fun i => μ.real (s i)) atTop (𝓝 (μ.real (⋃ i, s i))) := by
  change Tendsto (fun i => (μ (s i)).toReal) atTop
    (𝓝 ((μ (⋃ i, s i)).toReal))
  exact (ENNReal.tendsto_toReal (by finiteness)).comp
    (tendsto_measure_iUnion_atTop (μ := μ) hs)

lemma tendsto_measureReal_Iic_approach_Iio
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Tendsto
      (fun n : ℕ => μ.real (Set.Iic (t - ((n + 1 : ℕ) : ℝ)⁻¹)))
      atTop (𝓝 (μ.real (Set.Iio t))) := by
  let a : ℕ → ℝ := fun n => t - ((n + 1 : ℕ) : ℝ)⁻¹
  have ha_mono : Monotone a := by
    intro m n hmn
    dsimp [a]
    gcongr
  have ha_lt : ∀ n, a n < t := by
    intro n
    dsimp [a]
    exact sub_lt_self t (inv_pos.mpr (by positivity))
  have ha_tendsto : Tendsto a atTop (𝓝 t) := by
    have hsucc :
        Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hinv :
        Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hsucc
    simpa [a, sub_eq_add_neg] using
      (tendsto_const_nhds (x := t)).sub hinv
  have hUnion : (⋃ n : ℕ, Set.Iic (a n)) = Set.Iio t :=
    iUnion_Iic_eq_Iio_of_lt_of_tendsto ha_lt ha_tendsto
  have hT :
      Tendsto (fun n : ℕ => μ.real (Set.Iic (a n))) atTop
        (𝓝 (μ.real (⋃ n : ℕ, Set.Iic (a n)))) :=
    tendsto_measureReal_iUnion_atTop (μ := μ)
      (s := fun n : ℕ => Set.Iic (a n)) (fun m n hmn =>
        Set.Iic_subset_Iic.mpr (ha_mono hmn))
  rw [hUnion] at hT
  simpa [a] using hT

lemma measureIioErrorLE_of_measureCDFErrorLE
    {ν η : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure η] {ε : ℝ}
    (h : measureCDFErrorLE ν η ε) :
    ∀ t : ℝ, |ν.real (Set.Iio t) - η.real (Set.Iio t)| ≤ ε := by
  intro t
  let a : ℕ → ℝ := fun n => t - ((n + 1 : ℕ) : ℝ)⁻¹
  have hν :
      Tendsto (fun n : ℕ => ν.real (Set.Iic (a n))) atTop
        (𝓝 (ν.real (Set.Iio t))) := by
    simpa [a] using tendsto_measureReal_Iic_approach_Iio ν t
  have hη :
      Tendsto (fun n : ℕ => η.real (Set.Iic (a n))) atTop
        (𝓝 (η.real (Set.Iio t))) := by
    simpa [a] using tendsto_measureReal_Iic_approach_Iio η t
  have hlim :
      Tendsto (fun n : ℕ => |ν.real (Set.Iic (a n)) - η.real (Set.Iic (a n))|)
        atTop (𝓝 |ν.real (Set.Iio t) - η.real (Set.Iio t)|) :=
    (hν.sub hη).abs
  exact le_of_tendsto hlim (Eventually.of_forall fun n => h (a n))

lemma measureClosedUpperTailErrorLE_of_measureCDFErrorLE
    {ν η : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure η] {ε : ℝ}
    (h : measureCDFErrorLE ν η ε) :
    measureClosedUpperTailErrorLE ν η ε := by
  intro t
  have hcompl : (Set.Iio t : Set ℝ)ᶜ = Set.Ici t := by
    ext x
    simp
  have hIio : MeasurableSet (Set.Iio t : Set ℝ) := measurableSet_Iio
  rw [← hcompl, MeasureTheory.measureReal_compl (μ := ν) hIio,
    MeasureTheory.measureReal_compl (μ := η) hIio]
  simpa [measureCDFErrorLE, sub_sub_sub_cancel_right, abs_sub_comm] using
    measureIioErrorLE_of_measureCDFErrorLE (ν := ν) (η := η) h t

lemma closedUpperTailErrorBound_of_measureClosedUpperTailErrorLE
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {ε : ℝ}
    (hX : AEMeasurable X μ)
    (h : measureClosedUpperTailErrorLE (μ.map X) standardNormalMeasure ε) :
    closedUpperTailErrorBound X μ ε := by
  intro t
  have hmap :
      (μ.map X).real (Set.Ici t) = μ.real {ω | t ≤ X ω} := by
    rw [measureReal_def,
      Measure.map_apply_of_aemeasurable hX measurableSet_Ici]
    rfl
  simpa [closedUpperTailErrorAt, closedUpperTail, standardNormalClosedUpperTail, hmap] using h t

end MeasureCDFError

section ClosedUpperTailTransfer

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma closedUpperTailErrorBound_of_cdfErrorBound
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {ε : ℝ}
    (hX : Measurable X) (h : cdfErrorBound X μ ε) :
    closedUpperTailErrorBound X μ ε := by
  haveI : IsProbabilityMeasure (distribution X μ) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have hmeasure : measureCDFErrorLE (distribution X μ) standardNormalMeasure ε := by
    intro t
    rw [← cumulativeDistribution_eq_distribution_Iic (X := X) (μ := μ) hX t]
    simpa [measureCDFErrorLE, cdfErrorAt, standardNormalCDF] using h t
  have hclosed :
      measureClosedUpperTailErrorLE (distribution X μ) standardNormalMeasure ε :=
    measureClosedUpperTailErrorLE_of_measureCDFErrorLE hmeasure
  intro t
  rw [closedUpperTailErrorAt,
    closedUpperTail_eq_distribution_Ici (X := X) (μ := μ) hX t,
    standardNormalClosedUpperTail]
  exact hclosed t

end ClosedUpperTailTransfer

section BerryEsseenStatement

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The absolute third centered moment appearing in Berry-Esseen. -/
def centeredThirdAbsoluteMoment (X : Ω → ℝ) (μ : Measure Ω) (m : ℝ) : ℝ :=
  μ[fun ω => |X ω - m| ^ 3]

lemma centeredThirdAbsoluteMoment_nonneg (X : Ω → ℝ) (μ : Measure Ω) (m : ℝ) :
    0 ≤ centeredThirdAbsoluteMoment X μ m := by
  exact integral_nonneg fun _ => by positivity

/-- Dimensionless Berry-Esseen third-moment parameter
`E |X - m|^3 / σ^3`. -/
def standardizedThirdAbsoluteMoment
    (X : Ω → ℝ) (μ : Measure Ω) (m σ : ℝ) : ℝ :=
  centeredThirdAbsoluteMoment X μ m / σ ^ 3

lemma standardizedThirdAbsoluteMoment_nonneg
    (X : Ω → ℝ) (μ : Measure Ω) (m : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    0 ≤ standardizedThirdAbsoluteMoment X μ m σ := by
  exact div_nonneg
    (centeredThirdAbsoluteMoment_nonneg X μ m)
    (pow_nonneg hσ 3)

/-- Explicit Berry-Esseen rate `C * ρ / sqrt N`. -/
def berryEsseenRate (C ρ : ℝ) (N : ℕ) : ℝ :=
  C * ρ / Real.sqrt (N : ℝ)

lemma tendsto_berryEsseenRate_atTop (C ρ : ℝ) :
    Tendsto (fun N : ℕ => berryEsseenRate C ρ N) atTop (𝓝 0) := by
  have hsqrt :
      Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hinv :
      Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  simpa [berryEsseenRate, div_eq_mul_inv, mul_assoc] using
    (tendsto_const_nhds (x := C * ρ)).mul hinv

lemma berryEsseenRate_nonneg {C ρ : ℝ} (hCρ : 0 ≤ C * ρ) (N : ℕ) :
    0 ≤ berryEsseenRate C ρ N := by
  exact div_nonneg hCρ (Real.sqrt_nonneg _)

lemma berryEsseenRate_mono_constant {C D ρ : ℝ} (hCD : C ≤ D) (hρ : 0 ≤ ρ)
    (N : ℕ) :
    berryEsseenRate C ρ N ≤ berryEsseenRate D ρ N := by
  calc
    berryEsseenRate C ρ N = C * (ρ / Real.sqrt (N : ℝ)) := by
      rw [berryEsseenRate]
      ring
    _ ≤ D * (ρ / Real.sqrt (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hCD (div_nonneg hρ (Real.sqrt_nonneg _))
    _ = berryEsseenRate D ρ N := by
      rw [berryEsseenRate]
      ring

/-- HDP Theorem 2.1.3 as a reusable proposition: all normalized sums satisfy a
uniform CDF-error bound with rate `C * ρ / sqrt N`. -/
def berryEsseenCDFBound
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (m σ C ρ : ℝ) : Prop :=
  ∀ N : ℕ, 0 < N →
    cdfErrorBound (normalizedSum X m σ N) μ (berryEsseenRate C ρ N)

/-- HDP Theorem 2.1.3 in strict-upper-tail form:
`|P{Z_N > t} - P{g > t}| ≤ C * ρ / sqrt N`. -/
def berryEsseenUpperTailBound
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (m σ C ρ : ℝ) : Prop :=
  ∀ N : ℕ, 0 < N →
    upperTailErrorBound (normalizedSum X m σ N) μ (berryEsseenRate C ρ N)

/-- HDP Theorem 2.1.3 in the displayed closed-upper-tail form:
`|P{Z_N ≥ t} - P{g ≥ t}| ≤ C * ρ / sqrt N`. -/
def berryEsseenClosedUpperTailBound
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (m σ C ρ : ℝ) : Prop :=
  ∀ N : ℕ, 0 < N →
    closedUpperTailErrorBound (normalizedSum X m σ N) μ (berryEsseenRate C ρ N)

/-- The Berry-Esseen parameter for an i.i.d. sequence, computed from `X 0`. -/
def berryEsseenRho
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (m σ : ℝ) : ℝ :=
  standardizedThirdAbsoluteMoment (X 0) μ m σ

/-- A book-style bundle of the hypotheses used to state Berry-Esseen for the
i.i.d. CLT normalization. -/
structure BerryEsseenHypotheses [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (m σ : ℝ) : Prop where
  aemeasurable : ∀ i, AEMeasurable (X i) μ
  independent : iIndepFun X μ
  identDistrib : ∀ i, IdentDistrib (X i) (X 0) μ μ
  mean_eq : ∀ i, μ[X i] = m
  variance_eq : ∀ i, Var[X i; μ] = σ ^ 2
  sigma_pos : 0 < σ
  third_abs_integrable : Integrable (fun ω => |X 0 ω - m| ^ 3) μ

/-- The HDP Berry-Esseen conclusion with an explicit absolute constant `C`. -/
def BerryEsseenConclusion
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (m σ C : ℝ) : Prop :=
  berryEsseenCDFBound X μ m σ C (berryEsseenRho X μ m σ)

/-- The corresponding strict-upper-tail conclusion.  The displayed HDP theorem
uses constant `1`; Durrett's proof supplies a larger absolute constant unless
the sharper estimates are formalized. -/
def BerryEsseenTailConclusion
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (m σ C : ℝ) : Prop :=
  berryEsseenUpperTailBound X μ m σ C (berryEsseenRho X μ m σ)

/-- The corresponding closed-upper-tail conclusion, matching the event
`{Z_N ≥ t}` displayed in HDP Theorem 2.1.3. -/
def BerryEsseenClosedTailConclusion
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (m σ C : ℝ) : Prop :=
  berryEsseenClosedUpperTailBound X μ m σ C (berryEsseenRho X μ m σ)

lemma BerryEsseenConclusion.mono_constant
    {X : ℕ → Ω → ℝ} {m σ C D : ℝ}
    (h : BerryEsseenConclusion X μ m σ C)
    (hCD : C ≤ D)
    (hρ : 0 ≤ berryEsseenRho X μ m σ) :
    BerryEsseenConclusion X μ m σ D := by
  intro N hN t
  exact (h N hN t).trans (berryEsseenRate_mono_constant hCD hρ N)

lemma BerryEsseenTailConclusion.mono_constant
    {X : ℕ → Ω → ℝ} {m σ C D : ℝ}
    (h : BerryEsseenTailConclusion X μ m σ C)
    (hCD : C ≤ D)
    (hρ : 0 ≤ berryEsseenRho X μ m σ) :
    BerryEsseenTailConclusion X μ m σ D := by
  intro N hN t
  exact (h N hN t).trans (berryEsseenRate_mono_constant hCD hρ N)

lemma BerryEsseenClosedTailConclusion.mono_constant
    {X : ℕ → Ω → ℝ} {m σ C D : ℝ}
    (h : BerryEsseenClosedTailConclusion X μ m σ C)
    (hCD : C ≤ D)
    (hρ : 0 ≤ berryEsseenRho X μ m σ) :
    BerryEsseenClosedTailConclusion X μ m σ D := by
  intro N hN t
  exact (h N hN t).trans (berryEsseenRate_mono_constant hCD hρ N)

lemma berryEsseenUpperTailBound_of_cdfBound
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {m σ C ρ : ℝ}
    (hZ : ∀ N, 0 < N → Measurable (normalizedSum X m σ N))
    (hBE : berryEsseenCDFBound X μ m σ C ρ) :
    berryEsseenUpperTailBound X μ m σ C ρ := by
  intro N hN
  exact upperTailErrorBound_of_cdfErrorBound (μ := μ)
    (X := normalizedSum X m σ N) (hZ N hN) (hBE N hN)

lemma berryEsseenClosedUpperTailBound_of_cdfBound
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {m σ C ρ : ℝ}
    (hZ : ∀ N, 0 < N → Measurable (normalizedSum X m σ N))
    (hBE : berryEsseenCDFBound X μ m σ C ρ) :
    berryEsseenClosedUpperTailBound X μ m σ C ρ := by
  intro N hN
  exact closedUpperTailErrorBound_of_cdfErrorBound (μ := μ)
    (X := normalizedSum X m σ N) (hZ N hN) (hBE N hN)

lemma BerryEsseenTailConclusion_of_cdfConclusion
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {m σ C : ℝ}
    (hZ : ∀ N, 0 < N → Measurable (normalizedSum X m σ N))
    (hBE : BerryEsseenConclusion X μ m σ C) :
    BerryEsseenTailConclusion X μ m σ C :=
  berryEsseenUpperTailBound_of_cdfBound (μ := μ) hZ hBE

lemma BerryEsseenClosedTailConclusion_of_cdfConclusion
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {m σ C : ℝ}
    (hZ : ∀ N, 0 < N → Measurable (normalizedSum X m σ N))
    (hBE : BerryEsseenConclusion X μ m σ C) :
    BerryEsseenClosedTailConclusion X μ m σ C :=
  berryEsseenClosedUpperTailBound_of_cdfBound (μ := μ) hZ hBE

lemma berryEsseenCDFBound_of_exact_normal_laws
    {X : ℕ → Ω → ℝ} {m σ C ρ : ℝ}
    (hZ : ∀ N, 0 < N → Measurable (normalizedSum X m σ N))
    (hLaw : ∀ N, 0 < N → μ.map (normalizedSum X m σ N) = standardNormalMeasure)
    (hCρ : 0 ≤ C * ρ) :
    berryEsseenCDFBound X μ m σ C ρ := by
  intro N hN
  exact cdfErrorBound_of_map_eq_standardNormal
    (μ := μ) (X := normalizedSum X m σ N)
    (ε := berryEsseenRate C ρ N)
    (hZ N hN) (hLaw N hN) (berryEsseenRate_nonneg hCρ N)

lemma tendsto_cdfErrorAt_zero_of_berryEsseenCDFBound
    {X : ℕ → Ω → ℝ} {m σ C ρ : ℝ}
    (hBE : berryEsseenCDFBound X μ m σ C ρ)
    (t : ℝ) :
    Tendsto
      (fun N : ℕ => cdfErrorAt (normalizedSum X m σ N) μ t)
      atTop (𝓝 0) := by
  refine squeeze_zero'
    (Eventually.of_forall fun N => cdfErrorAt_nonneg (normalizedSum X m σ N) μ t)
    ?_
    (tendsto_berryEsseenRate_atTop C ρ)
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact hBE N hN t

end BerryEsseenStatement

end LeanFpAnalysis.HDP
