import Mathlib.Data.Sym.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.TestMatrices.Higham28GinibreMeasure
import NumStability.Analysis.TestMatrices.RealGinibre.GinibreRoots
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.RootMeasurability.GinibreRoots

/-!
# Higham28GinibreRoots (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreRoots`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

noncomputable section

namespace NumStability

open MeasureTheory Polynomial

local instance (n : ℕ) : MeasurableSpace (GinibreRawMatrix n) := MeasurableSpace.pi

local instance (n : ℕ) : OpensMeasurableSpace (GinibreRawMatrix n) := Pi.opensMeasurableSpace

local instance (n : ℕ) : BorelSpace (GinibreRawMatrix n) := Pi.borelSpace

local instance (n : ℕ) : StandardBorelSpace (GinibreRawMatrix n) :=
  StandardBorelSpace.pi_countable

local instance (n : ℕ) : MeasurableSpace (Fin n → ℂ) := MeasurableSpace.pi

local instance (n : ℕ) : OpensMeasurableSpace (Fin n → ℂ) := Pi.opensMeasurableSpace

local instance (n : ℕ) : BorelSpace (Fin n → ℂ) := Pi.borelSpace

local instance (n : ℕ) : StandardBorelSpace (Fin n → ℂ) :=
  StandardBorelSpace.pi_countable

theorem measurable_complexTupleRealCount (n : ℕ) :
    Measurable (@complexTupleRealCount n) := by
  classical
  unfold complexTupleRealCount
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite
  · exact measurableSet_eq_fun
      (Complex.measurable_im.comp (measurable_pi_apply i)) measurable_const
  · exact measurable_const
  · exact measurable_const

theorem measurableSet_complexRootTupleCountSet (n k : ℕ) :
    MeasurableSet (complexRootTupleCountSet n k) := by
  apply (isClosed_complexRootTupleSet n).measurableSet.inter
  exact measurableSet_eq_fun
    ((measurable_complexTupleRealCount n).comp measurable_snd) measurable_const

theorem analyticSet_complexRootTupleCountProjection (n k : ℕ) :
    AnalyticSet (complexRootTupleCountProjection n k) := by
  exact (measurableSet_complexRootTupleCountSet n k).analyticSet.image_of_continuous
    continuous_fst

theorem measurableSet_realEigenvalueCount_level (n k : ℕ) :
    MeasurableSet {A : GinibreRawMatrix n | realEigenvalueCount n A = k} := by
  have hset : {A : GinibreRawMatrix n | realEigenvalueCount n A = k} =
      complexRootTupleCountProjection n k := by
    ext A
    exact (mem_complexRootTupleCountProjection_iff n k A).symm
  rw [hset]
  apply (analyticSet_complexRootTupleCountProjection n k).measurableSet_of_compl
  rw [compl_complexRootTupleCountProjection]
  apply AnalyticSet.iUnion
  intro j
  split
  · exact analyticSet_empty
  · exact analyticSet_complexRootTupleCountProjection n j

theorem measurable_realEigenvalueCount (n : ℕ) :
    Measurable (fun A : GinibreRawMatrix n => realEigenvalueCount n A) := by
  apply measurable_to_countable'
  intro k
  simpa only [Set.preimage, Set.mem_singleton_iff] using
    measurableSet_realEigenvalueCount_level n k

/-- The real-valued root count used in the Ginibre expectation is Borel
measurable; this is the source-facing form needed by Bochner integration. -/
theorem measurable_realEigenvalueCount_real (n : ℕ) :
    Measurable (fun A : GinibreRawMatrix n => (realEigenvalueCount n A : ℝ)) :=
  (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (measurable_realEigenvalueCount n)

theorem aestronglyMeasurable_realEigenvalueCount (n : ℕ) :
    AEStronglyMeasurable
      (fun A : GinibreRawMatrix n => (realEigenvalueCount n A : ℝ))
      (realGinibreMeasure n) :=
  (measurable_realEigenvalueCount_real n).aestronglyMeasurable

/-- The real-eigenvalue count is integrable under the normalized real
Ginibre law, unconditionally. -/
theorem integrable_realEigenvalueCount (n : ℕ) :
    Integrable
      (fun A : GinibreRawMatrix n => (realEigenvalueCount n A : ℝ))
      (realGinibreMeasure n) :=
  integrable_realEigenvalueCount_of_aestronglyMeasurable n
    (aestronglyMeasurable_realEigenvalueCount n)

theorem measurable_complexTupleRealBelowCount (n : ℕ) :
    Measurable (@complexTupleRealBelowCount n) := by
  classical
  unfold complexTupleRealBelowCount
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite
  · apply MeasurableSet.inter
    · exact measurableSet_eq_fun
        (Complex.measurable_im.comp (measurable_pi_apply i |>.comp measurable_fst))
        measurable_const
    · exact measurableSet_lt
        (Complex.measurable_re.comp (measurable_pi_apply i |>.comp measurable_fst))
        measurable_snd
  · exact measurable_const
  · exact measurable_const

theorem measurableSet_complexRootTupleBelowCountSet (n k : ℕ) :
    MeasurableSet (complexRootTupleBelowCountSet n k) := by
  apply MeasurableSet.inter
  · exact (isClosed_complexRootTupleSet n).measurableSet.preimage
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  · exact measurableSet_eq_fun
      ((measurable_complexTupleRealBelowCount n).comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
      measurable_const

theorem analyticSet_complexRootTupleBelowCountProjection (n k : ℕ) :
    AnalyticSet (complexRootTupleBelowCountProjection n k) := by
  exact (measurableSet_complexRootTupleBelowCountSet n k).analyticSet.image_of_continuous
    continuous_fst

theorem measurableSet_realEigenvalueBelowCount_level (n k : ℕ) :
    MeasurableSet {p : GinibreRawMatrix n × ℝ | realEigenvalueBelowCount p = k} := by
  have hset : {p : GinibreRawMatrix n × ℝ | realEigenvalueBelowCount p = k} =
      complexRootTupleBelowCountProjection n k := by
    ext p
    exact (mem_complexRootTupleBelowCountProjection_iff n k p).symm
  rw [hset]
  apply (analyticSet_complexRootTupleBelowCountProjection n k).measurableSet_of_compl
  rw [compl_complexRootTupleBelowCountProjection]
  apply AnalyticSet.iUnion
  intro j
  split
  · exact analyticSet_empty
  · exact analyticSet_complexRootTupleBelowCountProjection n j

theorem measurable_realEigenvalueBelowCount (n : ℕ) :
    Measurable (@realEigenvalueBelowCount n) := by
  apply measurable_to_countable'
  intro k
  simpa only [Set.preimage, Set.mem_singleton_iff] using
    measurableSet_realEigenvalueBelowCount_level n k

private theorem card_filter_le_card_filter_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x → q x) :
    (s.filter p).card ≤ (s.filter q).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
      by_cases hpx : p x
      · have hqx : q x := hpq x hpx
        simpa [hpx, hqx] using ih
      · by_cases hqx : q x
        · simpa [hpx, hqx] using ih.trans (Nat.le_succ _)
        · simpa [hpx, hqx] using ih

/-- A root lying strictly between two thresholds forces a strict increase
of the number of roots below the threshold. -/
theorem card_filter_lt_card_filter_of_mem
    (s : Multiset ℝ) {a b : ℝ} (ha : a ∈ s) (hab : a < b) :
    (s.filter fun x => x < a).card < (s.filter fun x => x < b).card := by
  classical
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  have hmono :
      (t.filter fun x => x < a).card ≤ (t.filter fun x => x < b).card :=
    card_filter_le_card_filter_of_imp t (fun x => x < a) (fun x => x < b)
      (fun _ hx => hx.trans hab)
  simpa [hab, lt_irrefl] using Nat.lt_succ_of_le hmono

end NumStability

end
