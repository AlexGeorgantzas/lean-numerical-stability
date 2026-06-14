import LeanFpAnalysis.HDP.Probability.Concentration.Basic
import LeanFpAnalysis.HDP.Probability.Concentration.Chernoff
import LeanFpAnalysis.HDP.Combinatorics.Binomial
import Mathlib.Data.Finset.Union
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Random Graph Degree Bounds

Book-facing event and union-bound statements for HDP Chapter 2, Section 2.4.
The degree tail input is kept explicit, so these lemmas can be used both with
the Bernoulli/Chernoff API already formalized in this library and with future
edge-coordinate facts about `SimpleGraph.binomialRandom`.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Asymptotics
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace LeanFpAnalysis.HDP

/-- The expected degree `d = (n - 1) p` in the Erdős-Rényi graph `G(n,p)` on
`n` vertices. -/
def erdosRenyiExpectedDegree (n : ℕ) (p : unitInterval) : ℝ :=
  ((n - 1 : ℕ) : ℝ) * (unitInterval.toNNReal p : ℝ)

lemma erdosRenyiExpectedDegree_nonneg (n : ℕ) (p : unitInterval) :
    0 ≤ erdosRenyiExpectedDegree n p := by
  dsimp [erdosRenyiExpectedDegree]
  exact mul_nonneg (by positivity) (unitInterval.nonneg p)

section Events

variable {V : Type*}

/-- The degree of a vertex, stated using `Set.ncard` so it is available without
choosing decidability data for graph adjacency. -/
def graphDegree (G : SimpleGraph V) (v : V) : ℕ :=
  (G.neighborSet v).ncard

/-- The event that one vertex has degree deviating from `d` by at least
`ε d`. -/
def graphDegreeDeviationEvent (d ε : ℝ) (v : V) : Set (SimpleGraph V) :=
  {G | ε * d ≤ |(graphDegree G v : ℝ) - d|}

/-- The event that some vertex has degree deviating from `d` by at least
`ε d`. This is the bad event in Proposition 2.4.1. -/
def graphSomeDegreeDeviationEvent (d ε : ℝ) : Set (SimpleGraph V) :=
  {G | ∃ v, G ∈ graphDegreeDeviationEvent (V := V) d ε v}

/-- The event that one vertex has degree at least a prescribed level. -/
def graphDegreeAtLeastEvent (L : ℝ) (v : V) : Set (SimpleGraph V) :=
  {G | L ≤ (graphDegree G v : ℝ)}

/-- The event that some vertex has degree at least a prescribed level. -/
def graphSomeDegreeAtLeastEvent (L : ℝ) : Set (SimpleGraph V) :=
  {G | ∃ v, G ∈ graphDegreeAtLeastEvent (V := V) L v}

/-- The good event for maximum-degree upper bounds: every vertex has degree
strictly below a prescribed level. -/
def graphAllDegreesBelowEvent (L : ℝ) : Set (SimpleGraph V) :=
  {G | ∀ v, (graphDegree G v : ℝ) < L}

/-- The event that all vertices have degrees strictly within `ε d` of `d`. -/
def graphAllDegreesWithinEvent (d ε : ℝ) : Set (SimpleGraph V) :=
  {G | ∀ v, |(graphDegree G v : ℝ) - d| < ε * d}

lemma mem_graphAllDegreesWithinEvent_iff_not_mem_bad
    (G : SimpleGraph V) (d ε : ℝ) :
    G ∈ graphAllDegreesWithinEvent (V := V) d ε ↔
      G ∉ graphSomeDegreeDeviationEvent (V := V) d ε := by
  classical
  simp [graphAllDegreesWithinEvent, graphSomeDegreeDeviationEvent,
    graphDegreeDeviationEvent, not_le]

/-- The good all-degrees event is the complement of the bad some-degree
deviation event. -/
lemma graphAllDegreesWithinEvent_eq_compl_someDeviation (d ε : ℝ) :
    graphAllDegreesWithinEvent (V := V) d ε =
      (graphSomeDegreeDeviationEvent (V := V) d ε)ᶜ := by
  ext G
  exact mem_graphAllDegreesWithinEvent_iff_not_mem_bad G d ε

lemma mem_graphAllDegreesBelowEvent_iff_not_mem_high
    (G : SimpleGraph V) (L : ℝ) :
    G ∈ graphAllDegreesBelowEvent (V := V) L ↔
      G ∉ graphSomeDegreeAtLeastEvent (V := V) L := by
  classical
  simp [graphAllDegreesBelowEvent, graphSomeDegreeAtLeastEvent,
    graphDegreeAtLeastEvent, not_le]

/-- The good maximum-degree event is the complement of the bad event that some
vertex has degree at least the prescribed threshold. -/
lemma graphAllDegreesBelowEvent_eq_compl_someAtLeast (L : ℝ) :
    graphAllDegreesBelowEvent (V := V) L =
      (graphSomeDegreeAtLeastEvent (V := V) L)ᶜ := by
  ext G
  exact mem_graphAllDegreesBelowEvent_iff_not_mem_high G L

end Events

section EdgeCylinders

variable {ι V J : Type*}

/-- Finite cylinder event for a `setBernoulli` random set: all elements of the
finite set `E` are present. -/
def setBernoulliFinsetPresentEvent (E : Finset ι) : Set (Set ι) :=
  {s | ∀ e ∈ E, e ∈ s}

/-- Graph event that all edges in the finite set `E` are present. -/
def graphEdgesPresentFinsetEvent (E : Finset (Sym2 V)) :
    Set (SimpleGraph V) :=
  {G | ∀ e ∈ E, e ∈ G.edgeSet}

lemma measurableSet_graphEdgesPresentFinsetEvent
    (E : Finset (Sym2 V)) :
    MeasurableSet (graphEdgesPresentFinsetEvent (V := V) E) := by
  classical
  rw [show graphEdgesPresentFinsetEvent (V := V) E =
      ⋂ e ∈ E, {G : SimpleGraph V | e ∈ G.edgeSet} by
    ext G
    simp [graphEdgesPresentFinsetEvent]]
  exact E.measurableSet_biInter fun e _he =>
    (measurableSet_mem e).preimage SimpleGraph.measurable_edgeSet

/-- Exact finite-cylinder probability under `setBernoulli`: if all required
coordinates lie in the active set `u`, the probability that they are all present
is `p ^ |E|`. -/
lemma setBernoulliFinsetPresentEvent_probability
    (u : Set ι) (p : unitInterval) (E : Finset ι)
    (hE : ↑E ⊆ u) :
    setBer(u, p) (setBernoulliFinsetPresentEvent E) =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ E.card := by
  classical
  rw [ProbabilityTheory.setBernoulli_apply']
  have hpre :
      ((fun p : ι → Prop => {i | p i}) ⁻¹'
          setBernoulliFinsetPresentEvent E)
        =
      Set.pi (E : Set ι) (fun _ => ({True} : Set Prop)) := by
    ext f
    simp [setBernoulliFinsetPresentEvent, Set.mem_pi]
  rw [hpre]
  rw [Measure.infinitePi_pi]
  · calc
      (∏ e ∈ E,
          (unitInterval.toNNReal p • Measure.dirac (e ∈ u) +
              unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False)
            ({True} : Set Prop))
          =
        ∏ _e ∈ E, (unitInterval.toNNReal p : ℝ≥0∞) := by
          refine Finset.prod_congr rfl ?_
          intro e he
          have heu : e ∈ u := hE (by simpa using he)
          simp only [heu, Measure.coe_add, Pi.add_apply, Measure.smul_apply,
            Measure.dirac_apply, ENNReal.smul_def, smul_eq_mul]
          simp
      _ = (unitInterval.toNNReal p : ℝ≥0∞) ^ E.card := by
          simp
  · intro e _he
    exact measurableSet_singleton True

/-- Finite cylinder event for a `setBernoulli` random set: among the
coordinates in `E`, exactly the coordinates in `T` are present. Coordinates
outside `E` are unrestricted. -/
def setBernoulliFinsetExactEvent (E T : Finset ι) : Set (Set ι) :=
  {s | ∀ e ∈ E, (e ∈ s ↔ e ∈ T)}

lemma finset_prod_ite_mem_eq_pow_mul_pow {α M : Type*}
    [DecidableEq α] [CommMonoid M] (E T : Finset α) (hT : T ⊆ E)
    (a b : M) :
    (∏ e ∈ E, if e ∈ T then a else b) =
      a ^ T.card * b ^ (E.card - T.card) := by
  classical
  have hfilter : E.filter (fun e => e ∈ T) = T := by
    ext e
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro heT
      exact Finset.mem_filter.mpr ⟨hT heT, heT⟩
  have hfilterNot : E.filter (fun e => e ∉ T) = E \ T := by
    ext e
    simp
  calc
    (∏ e ∈ E, if e ∈ T then a else b)
        = (∏ e ∈ E.filter (fun e => e ∈ T),
              if e ∈ T then a else b) *
            (∏ e ∈ E.filter (fun e => e ∉ T),
              if e ∈ T then a else b) := by
          rw [← Finset.prod_filter_mul_prod_filter_not
            (s := E) (p := fun e => e ∈ T)
            (f := fun e => if e ∈ T then a else b)]
    _ = (∏ _e ∈ T, a) * (∏ _e ∈ E \ T, b) := by
          rw [hfilter, hfilterNot]
          congr 1
          · exact Finset.prod_congr rfl fun e he => by simp [he]
          · refine Finset.prod_congr rfl fun e he => ?_
            have hnot : e ∉ T := (Finset.mem_sdiff.mp he).2
            simp [hnot]
    _ = a ^ T.card * b ^ (E.card - T.card) := by
          simp [Finset.card_sdiff_of_subset hT]

/-- Exact finite-cylinder probability under `setBernoulli`: if `T ⊆ E` and
all coordinates in `E` lie in the active set `u`, then the probability that
exactly `T` is present among `E` is
`p ^ |T| (1-p) ^ (|E|-|T|)`. -/
lemma setBernoulliFinsetExactEvent_probability
    [DecidableEq ι] (u : Set ι) (p : unitInterval) (E T : Finset ι)
    (hE : ↑E ⊆ u) (hT : T ⊆ E) :
    setBer(u, p) (setBernoulliFinsetExactEvent E T) =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ T.card *
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^
          (E.card - T.card) := by
  classical
  rw [ProbabilityTheory.setBernoulli_apply']
  have hpre :
      ((fun p : ι → Prop => {i | p i}) ⁻¹'
          setBernoulliFinsetExactEvent E T)
        =
      Set.pi (E : Set ι)
        (fun e =>
          if e ∈ T then ({True} : Set Prop) else ({False} : Set Prop)) := by
    ext f
    simp only [Set.mem_preimage, setBernoulliFinsetExactEvent,
      Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe]
    constructor
    · intro h e heE
      by_cases heT : e ∈ T
      · simp [heT, (h e heE).2 heT]
      · have hnot : ¬ f e := fun hf => heT ((h e heE).1 hf)
        simp [heT, hnot]
    · intro h e heE
      have he := h e heE
      by_cases heT : e ∈ T
      · simp [heT] at he
        exact ⟨fun _ => heT, fun _ => he⟩
      · simp [heT] at he
        exact ⟨fun hf => (he hf).elim, fun hmem => False.elim (heT hmem)⟩
  rw [hpre]
  rw [Measure.infinitePi_pi]
  · calc
      (∏ e ∈ E,
          (unitInterval.toNNReal p • Measure.dirac (e ∈ u) +
              unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False)
            (if e ∈ T then ({True} : Set Prop) else ({False} : Set Prop)))
          =
        ∏ e ∈ E,
          if e ∈ T then
            (unitInterval.toNNReal p : ℝ≥0∞)
          else
            (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) := by
          refine Finset.prod_congr rfl ?_
          intro e heE
          have heu : e ∈ u := hE (by simpa using heE)
          by_cases heT : e ∈ T
          · simp only [heT, if_true, heu, Measure.coe_add, Pi.add_apply,
              Measure.smul_apply, Measure.dirac_apply, ENNReal.smul_def,
              smul_eq_mul]
            simp
          · simp only [heT, if_false, heu, Measure.coe_add, Pi.add_apply,
              Measure.smul_apply, Measure.dirac_apply, ENNReal.smul_def,
              smul_eq_mul]
            simp
      _ =
        (unitInterval.toNNReal p : ℝ≥0∞) ^ T.card *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^
            (E.card - T.card) := by
          exact finset_prod_ite_mem_eq_pow_mul_pow E T hT _ _
  · intro e _he
    by_cases heT : e ∈ T <;> simp [heT]

/-- The finite-cylinder probability transported to the binomial random graph
model. Requiring a finite set of non-diagonal edges to be present has
probability `p ^ |E|`. -/
lemma binomialRandom_graphEdgesPresentFinsetEvent_probability
    [Countable V] (p : unitInterval) (E : Finset (Sym2 V))
    (hE : (E : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ) :
    SimpleGraph.binomialRandom V p
        (graphEdgesPresentFinsetEvent (V := V) E)
      =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ E.card := by
  classical
  rw [SimpleGraph.binomialRandom_eq_map]
  rw [Measure.map_apply SimpleGraph.measurable_fromEdgeSet
    (measurableSet_graphEdgesPresentFinsetEvent (V := V) E)]
  have hpre :
      SimpleGraph.fromEdgeSet ⁻¹'
          graphEdgesPresentFinsetEvent (V := V) E
        =
      setBernoulliFinsetPresentEvent E := by
    ext s
    simp only [Set.mem_preimage, graphEdgesPresentFinsetEvent,
      setBernoulliFinsetPresentEvent]
    constructor
    · intro hs e he
      have hesdiff : e ∈ (SimpleGraph.fromEdgeSet s).edgeSet := hs e he
      rw [SimpleGraph.edgeSet_fromEdgeSet] at hesdiff
      exact hesdiff.1
    · intro hs e he
      have hnotdiag : e ∈ Sym2.diagSetᶜ := hE (by simpa using he)
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨hs e he, hnotdiag⟩
  rw [hpre]
  exact
    setBernoulliFinsetPresentEvent_probability
      (u := Sym2.diagSetᶜ) (p := p) (E := E) hE

/-- Graph event that, among the finite edge set `E`, exactly the edges in `T`
are present. Edges outside `E` are unrestricted. -/
def graphEdgesExactFinsetEvent (E T : Finset (Sym2 V)) :
    Set (SimpleGraph V) :=
  {G | ∀ e ∈ E, (e ∈ G.edgeSet ↔ e ∈ T)}

lemma measurableSet_graphEdgesExactFinsetEvent
    [DecidableEq (Sym2 V)] (E T : Finset (Sym2 V)) :
    MeasurableSet (graphEdgesExactFinsetEvent (V := V) E T) := by
  classical
  rw [show graphEdgesExactFinsetEvent (V := V) E T =
      ⋂ e ∈ E,
        if e ∈ T then {G : SimpleGraph V | e ∈ G.edgeSet}
        else {G : SimpleGraph V | e ∉ G.edgeSet} by
    ext G
    simp only [Set.mem_iInter, graphEdgesExactFinsetEvent, Set.mem_setOf_eq]
    constructor
    · intro h e heE
      by_cases heT : e ∈ T
      · simp [heT, (h e heE).2 heT]
      · have hnot : e ∉ G.edgeSet := fun hmem => heT ((h e heE).1 hmem)
        simp [heT, hnot]
    · intro h e heE
      have he := h e heE
      by_cases heT : e ∈ T
      · simp [heT] at he
        exact ⟨fun _ => heT, fun _ => he⟩
      · simp [heT] at he
        exact ⟨fun hmem => (he hmem).elim,
          fun hmemT => False.elim (heT hmemT)⟩]
  exact E.measurableSet_biInter fun e _he => by
    by_cases heT : e ∈ T
    · simpa only [heT, if_true] using
        (measurableSet_mem e).preimage SimpleGraph.measurable_edgeSet
    · simpa only [heT, if_false] using
        ((measurableSet_mem e).preimage SimpleGraph.measurable_edgeSet).compl

/-- Exact finite-cylinder probability transported to `G(n,p)`: requiring exactly
`T` among a finite set `E` of non-diagonal edges has probability
`p ^ |T| (1-p) ^ (|E|-|T|)`. -/
lemma binomialRandom_graphEdgesExactFinsetEvent_probability
    [Countable V] [DecidableEq (Sym2 V)] (p : unitInterval)
    (E T : Finset (Sym2 V))
    (hE : (E : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ) (hT : T ⊆ E) :
    SimpleGraph.binomialRandom V p
        (graphEdgesExactFinsetEvent (V := V) E T) =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ T.card *
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^
          (E.card - T.card) := by
  classical
  rw [SimpleGraph.binomialRandom_eq_map]
  rw [Measure.map_apply SimpleGraph.measurable_fromEdgeSet
    (measurableSet_graphEdgesExactFinsetEvent (V := V) E T)]
  have hpre :
      SimpleGraph.fromEdgeSet ⁻¹'
          graphEdgesExactFinsetEvent (V := V) E T =
        setBernoulliFinsetExactEvent E T := by
    ext s
    simp only [Set.mem_preimage, graphEdgesExactFinsetEvent,
      setBernoulliFinsetExactEvent, Set.mem_setOf_eq]
    constructor
    · intro hs e heE
      have hnotdiag : e ∈ Sym2.diagSetᶜ := hE (by simpa using heE)
      rw [Set.mem_compl_iff, Sym2.mem_diagSet] at hnotdiag
      have hiff := hs e heE
      rw [SimpleGraph.edgeSet_fromEdgeSet] at hiff
      simp [hnotdiag] at hiff
      exact hiff
    · intro hs e heE
      have hnotdiag : e ∈ Sym2.diagSetᶜ := hE (by simpa using heE)
      rw [Set.mem_compl_iff, Sym2.mem_diagSet] at hnotdiag
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      simp [hnotdiag, hs e heE]
  rw [hpre]
  exact setBernoulliFinsetExactEvent_probability
    (u := Sym2.diagSetᶜ) (p := p) (E := E) (T := T) hE hT

lemma graphEdgesPresentFinsetEvent_iInter_eq_biUnion
    [DecidableEq (Sym2 V)] (E : J → Finset (Sym2 V))
    (s : Finset J) :
    (⋂ j ∈ s, graphEdgesPresentFinsetEvent (V := V) (E j))
      =
    graphEdgesPresentFinsetEvent (V := V) (s.biUnion E) := by
  ext G
  simp only [Set.mem_iInter, graphEdgesPresentFinsetEvent, Set.mem_setOf_eq,
    Finset.mem_biUnion]
  constructor
  · intro h e he
    rcases he with ⟨j, hjs, heE⟩
    exact h j hjs e heE
  · intro h j hjs e heE
    exact h e ⟨j, hjs, heE⟩

lemma coe_finset_biUnion_subset {α β : Type*} [DecidableEq β]
    {s : Finset α} {E : α → Finset β} {u : Set β}
    (hE : ∀ a ∈ s, ↑(E a) ⊆ u) :
    ↑(s.biUnion E) ⊆ u := by
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_biUnion] at hx
  rcases hx with ⟨a, has, hxE⟩
  exact hE a has hxE

lemma card_biUnion_of_pairwiseDisjoint
    {α β : Type*} [DecidableEq β]
    {s : Finset α} {E : α → Finset β}
    (hdisj : (s : Set α).PairwiseDisjoint E) :
    (s.biUnion E).card = ∑ a ∈ s, (E a).card := by
  simpa using Finset.card_biUnion hdisj

lemma pairwiseDisjoint_finset_of_subset
    {α β : Type*} [DecidableEq β]
    {s : Finset α} {E T : α → Finset β}
    (hdisj : (s : Set α).PairwiseDisjoint E)
    (hT : ∀ a ∈ s, T a ⊆ E a) :
    (s : Set α).PairwiseDisjoint T := by
  intro i his j hjs hij
  change Disjoint (T i) (T j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  exact (Finset.disjoint_left.mp (hdisj his hjs hij))
    (hT i his hxi) (hT j hjs hxj)

lemma finset_biUnion_subset_biUnion
    {α β : Type*} [DecidableEq β]
    {s : Finset α} {E T : α → Finset β}
    (hT : ∀ a ∈ s, T a ⊆ E a) :
    s.biUnion T ⊆ s.biUnion E := by
  intro x hx
  rw [Finset.mem_biUnion] at hx ⊢
  rcases hx with ⟨a, has, hxT⟩
  exact ⟨a, has, hT a has hxT⟩

lemma graphEdgesExactFinsetEvent_iInter_eq_biUnion
    [DecidableEq (Sym2 V)] (E T : J → Finset (Sym2 V))
    (hT : ∀ j, T j ⊆ E j)
    {s : Finset J} (hdisj : (s : Set J).PairwiseDisjoint E) :
    (⋂ j ∈ s, graphEdgesExactFinsetEvent (V := V) (E j) (T j))
      =
    graphEdgesExactFinsetEvent (V := V) (s.biUnion E) (s.biUnion T) := by
  classical
  ext G
  simp only [Set.mem_iInter, graphEdgesExactFinsetEvent, Set.mem_setOf_eq,
    Finset.mem_biUnion]
  constructor
  · intro h e he
    constructor
    · intro heG
      rcases he with ⟨j, hjs, heE⟩
      exact ⟨j, hjs, (h j hjs e heE).1 heG⟩
    · rintro ⟨j, hjs, heT⟩
      exact (h j hjs e (hT j heT)).2 heT
  · intro h j hjs e heE
    constructor
    · intro heG
      have heUnionT :
          ∃ k, k ∈ s ∧ e ∈ T k :=
        (h e ⟨j, hjs, heE⟩).1 heG
      rcases heUnionT with ⟨k, hks, heTk⟩
      by_cases hkj : k = j
      · simpa [hkj] using heTk
      · have hdis : Disjoint (E k) (E j) :=
          hdisj hks hjs hkj
        exact False.elim
          ((Finset.disjoint_left.mp hdis) (hT k heTk) heE)
    · intro heT
      exact (h e ⟨j, hjs, heE⟩).2 ⟨j, hjs, heT⟩

/-- The exact edge-pattern events on a fixed finite edge block. -/
def graphEdgesExactPatternFamily (E : Finset (Sym2 V)) :
    Set (Set (SimpleGraph V)) :=
  {A | ∃ T, T ⊆ E ∧ A = graphEdgesExactFinsetEvent (V := V) E T}

lemma graphEdgesExactPatternFamily_isPiSystem
    [DecidableEq (Sym2 V)] (E : Finset (Sym2 V)) :
    IsPiSystem (graphEdgesExactPatternFamily (V := V) E) := by
  classical
  rintro A ⟨T, hT, rfl⟩ B ⟨U, hU, rfl⟩ hnonempty
  have hTU : T = U := by
    rcases hnonempty with ⟨G, hGT, hGU⟩
    ext e
    constructor
    · intro heT
      exact (hGU e (hT heT)).1 ((hGT e (hT heT)).2 heT)
    · intro heU
      exact (hGT e (hU heU)).1 ((hGU e (hU heU)).2 heU)
  rw [hTU, Set.inter_self]
  exact ⟨U, hU, rfl⟩

/-- Exact edge-pattern pi-systems on disjoint edge blocks are independent under
`G(n,p)`. This upgrades coordinate independence from single present-edge
cylinders to all finite present/absent patterns on each block. -/
theorem binomialRandom_graphEdgesExactPatternFamily_iIndepSets
    [Countable V] [DecidableEq (Sym2 V)]
    (p : unitInterval) (E : J → Finset (Sym2 V))
    (hdiag : ∀ j, (E j : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ)
    (hdisj : (Set.univ : Set J).PairwiseDisjoint E) :
    iIndepSets
      (fun j => graphEdgesExactPatternFamily (V := V) (E j))
      (SimpleGraph.binomialRandom V p) := by
  classical
  refine (iIndepSets_iff
    (fun j => graphEdgesExactPatternFamily (V := V) (E j))
    (SimpleGraph.binomialRandom V p)).2 ?_
  intro s f hf
  let T : J → Finset (Sym2 V) := fun j =>
    if hj : j ∈ s then Classical.choose (hf j hj) else ∅
  have hTsub : ∀ j, T j ⊆ E j := by
    intro j
    by_cases hj : j ∈ s
    · dsimp [T]
      simpa [hj] using (Classical.choose_spec (hf j hj)).1
    · dsimp [T]
      simp [hj]
  have hf_eq : ∀ j ∈ s,
      f j = graphEdgesExactFinsetEvent (V := V) (E j) (T j) := by
    intro j hj
    dsimp [T]
    simpa [hj] using (Classical.choose_spec (hf j hj)).2
  have hrestrict : (s : Set J).PairwiseDisjoint E :=
    hdisj.subset (by simp)
  have hrestrictT : (s : Set J).PairwiseDisjoint T :=
    pairwiseDisjoint_finset_of_subset hrestrict (fun j _hj => hTsub j)
  have hcardE :
      (s.biUnion E).card = ∑ j ∈ s, (E j).card :=
    card_biUnion_of_pairwiseDisjoint hrestrict
  have hcardT :
      (s.biUnion T).card = ∑ j ∈ s, (T j).card :=
    card_biUnion_of_pairwiseDisjoint hrestrictT
  have hsumdiff :
      ∑ j ∈ s, ((E j).card - (T j).card) =
        ∑ j ∈ s, (E j).card - ∑ j ∈ s, (T j).card := by
    exact Finset.sum_tsub_distrib s
      (fun j _hj => Finset.card_le_card (hTsub j))
  have hiInter_eq :
      (⋂ j ∈ s, f j) =
        (⋂ j ∈ s,
          graphEdgesExactFinsetEvent (V := V) (E j) (T j)) := by
    ext G
    simp only [Set.mem_iInter]
    constructor
    · intro h j hj
      simpa [hf_eq j hj] using h j hj
    · intro h j hj
      simpa [hf_eq j hj] using h j hj
  calc
    SimpleGraph.binomialRandom V p (⋂ j ∈ s, f j)
        =
      SimpleGraph.binomialRandom V p
        (⋂ j ∈ s,
          graphEdgesExactFinsetEvent (V := V) (E j) (T j)) := by
          rw [hiInter_eq]
    _ =
      SimpleGraph.binomialRandom V p
        (graphEdgesExactFinsetEvent (V := V) (s.biUnion E) (s.biUnion T)) := by
          rw [graphEdgesExactFinsetEvent_iInter_eq_biUnion
            (V := V) (E := E) (T := T) hTsub hrestrict]
    _ =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ (s.biUnion T).card *
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^
          ((s.biUnion E).card - (s.biUnion T).card) := by
          exact binomialRandom_graphEdgesExactFinsetEvent_probability
            (V := V) (p := p) (E := s.biUnion E) (T := s.biUnion T)
            (coe_finset_biUnion_subset (fun j _hj => hdiag j))
            (finset_biUnion_subset_biUnion (s := s)
              (E := E) (T := T) (fun j _hj => hTsub j))
    _ =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ (∑ j ∈ s, (T j).card) *
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^
          (∑ j ∈ s, ((E j).card - (T j).card)) := by
          rw [hcardT, hcardE, ← hsumdiff]
    _ =
      ∏ j ∈ s,
        ((unitInterval.toNNReal p : ℝ≥0∞) ^ (T j).card *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^
            ((E j).card - (T j).card)) := by
          rw [Finset.prod_mul_distrib]
          rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
    _ =
      ∏ j ∈ s, SimpleGraph.binomialRandom V p (f j) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          rw [hf_eq j hj]
          rw [binomialRandom_graphEdgesExactFinsetEvent_probability
            (V := V) (p := p) (E := E j) (T := T j)
            (hdiag j) (hTsub j)]

/-- Disjoint finite edge cylinders are independent under the binomial random
graph measure. -/
theorem binomialRandom_graphEdgesPresentFinsetEvent_iIndepSet
    [Countable V] [DecidableEq (Sym2 V)]
    (p : unitInterval) (E : J → Finset (Sym2 V))
    (hdiag : ∀ j, (E j : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ)
    (hdisj : (Set.univ : Set J).PairwiseDisjoint E) :
    iIndepSet
      (fun j => graphEdgesPresentFinsetEvent (V := V) (E j))
      (SimpleGraph.binomialRandom V p) := by
  classical
  refine (iIndepSet_iff_meas_biInter
    (μ := SimpleGraph.binomialRandom V p)
    (f := fun j => graphEdgesPresentFinsetEvent (V := V) (E j))
    (fun j => measurableSet_graphEdgesPresentFinsetEvent (V := V) (E j))).2 ?_
  intro s
  rw [graphEdgesPresentFinsetEvent_iInter_eq_biUnion (V := V) E s]
  rw [binomialRandom_graphEdgesPresentFinsetEvent_probability
    (V := V) (p := p) (E := s.biUnion E)]
  · rw [card_biUnion_of_pairwiseDisjoint]
    · symm
      calc
        (∏ j ∈ s,
            SimpleGraph.binomialRandom V p
              (graphEdgesPresentFinsetEvent (V := V) (E j)))
            =
          ∏ j ∈ s,
            (unitInterval.toNNReal p : ℝ≥0∞) ^ (E j).card := by
            refine Finset.prod_congr rfl ?_
            intro j _hj
            exact binomialRandom_graphEdgesPresentFinsetEvent_probability
              (V := V) (p := p) (E := E j) (hdiag j)
        _ = (unitInterval.toNNReal p : ℝ≥0∞) ^
              (∑ j ∈ s, (E j).card) := by
            exact Finset.prod_pow_eq_pow_sum s (fun j => (E j).card)
              (unitInterval.toNNReal p : ℝ≥0∞)
    · exact hdisj.subset (by simp)
  · exact coe_finset_biUnion_subset (fun j _hj => hdiag j)

end EdgeCylinders

section StarWitnesses

variable {V J : Type*}

/-- The finite set of unordered edges from a center `v` to a finite leaf set
`S`. The embedding form records that the number of edges is exactly `|S|`. -/
def graphStarEdgeFinset (v : V) (S : Finset V) : Finset (Sym2 V) :=
  S.map (Sym2.mkEmbedding v)

@[simp]
lemma graphStarEdgeFinset_card (v : V) (S : Finset V) :
    (graphStarEdgeFinset v S).card = S.card := by
  simp [graphStarEdgeFinset]

/-- The event that all edges from `v` to vertices in `S` are present. -/
def graphStarPresentEvent (v : V) (S : Finset V) : Set (SimpleGraph V) :=
  {G | ∀ w ∈ S, G.Adj v w}

lemma graphStarPresentEvent_eq_graphEdgesPresentFinsetEvent
    (v : V) (S : Finset V) :
    graphStarPresentEvent (V := V) v S =
      graphEdgesPresentFinsetEvent (V := V) (graphStarEdgeFinset v S) := by
  ext G
  simp [graphStarPresentEvent, graphEdgesPresentFinsetEvent,
    graphStarEdgeFinset, SimpleGraph.mem_edgeSet]

lemma measurableSet_graphStarPresentEvent (v : V) (S : Finset V) :
    MeasurableSet (graphStarPresentEvent (V := V) v S) := by
  rw [graphStarPresentEvent_eq_graphEdgesPresentFinsetEvent]
  exact measurableSet_graphEdgesPresentFinsetEvent _

lemma graphStarEdgeFinset_subset_diag_compl {v : V} {S : Finset V}
    (hvS : v ∉ S) :
    (graphStarEdgeFinset v S : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ := by
  intro e he
  rcases Finset.mem_map.mp he with ⟨w, hw, rfl⟩
  change s(v, w) ∈ Sym2.diagSetᶜ
  rw [Set.mem_compl_iff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
  intro hvw
  exact hvS (by simpa [hvw] using hw)

/-- Exact probability of a concrete star witness in `G(n,p)`: all `|S|` star
edges are present. -/
lemma binomialRandom_graphStarPresentEvent_probability
    [Countable V] [DecidableEq (Sym2 V)] (p : unitInterval)
    {v : V} {S : Finset V} (hvS : v ∉ S) :
    SimpleGraph.binomialRandom V p
        (graphStarPresentEvent (V := V) v S) =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ S.card := by
  rw [graphStarPresentEvent_eq_graphEdgesPresentFinsetEvent]
  rw [binomialRandom_graphEdgesPresentFinsetEvent_probability
    (V := V) (p := p) (E := graphStarEdgeFinset v S)]
  · simp
  · exact graphStarEdgeFinset_subset_diag_compl hvS

/-- Real-probability form of
`binomialRandom_graphStarPresentEvent_probability`. -/
lemma binomialRandom_graphStarPresentEvent_probability_real
    [Countable V] [DecidableEq (Sym2 V)] (p : unitInterval)
    {v : V} {S : Finset V} (hvS : v ∉ S) :
    (SimpleGraph.binomialRandom V p).real
        (graphStarPresentEvent (V := V) v S) =
      (unitInterval.toNNReal p : ℝ) ^ S.card := by
  rw [measureReal_def,
    binomialRandom_graphStarPresentEvent_probability (V := V) p hvS]
  simp

/-- Disjoint star edge blocks give independent star-present witness events. -/
theorem binomialRandom_graphStarPresentEvent_iIndepSet
    [Countable V] [DecidableEq (Sym2 V)]
    (p : unitInterval) (v : J → V) (S : J → Finset V)
    (hvS : ∀ j, v j ∉ S j)
    (hdisj : (Set.univ : Set J).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v j) (S j))) :
    iIndepSet
      (fun j => graphStarPresentEvent (V := V) (v j) (S j))
      (SimpleGraph.binomialRandom V p) := by
  simpa [graphStarPresentEvent_eq_graphEdgesPresentFinsetEvent] using
    (binomialRandom_graphEdgesPresentFinsetEvent_iIndepSet
      (V := V) (J := J) (p := p)
      (E := fun j => graphStarEdgeFinset (v j) (S j))
      (hdiag := fun j => graphStarEdgeFinset_subset_diag_compl (hvS j))
      (hdisj := hdisj))

lemma graphStarPresentEvent_subset_degreeAtLeast [Fintype V]
    {v : V} {S : Finset V} {L : ℝ}
    (hL : L ≤ (S.card : ℝ)) :
    graphStarPresentEvent (V := V) v S ⊆
      graphDegreeAtLeastEvent (V := V) L v := by
  intro G hG
  have hsubset : (S : Set V) ⊆ G.neighborSet v := by
    intro w hw
    exact (SimpleGraph.mem_neighborSet G v w).2 (hG w (by simpa using hw))
  have hleNat : S.card ≤ graphDegree G v := by
    have hle := Set.ncard_le_ncard hsubset (Set.toFinite (G.neighborSet v))
    simpa [graphDegree] using hle
  exact hL.trans (by exact_mod_cast hleNat)

lemma graphStarPresentEvent_subset_someDegreeAtLeast [Fintype V]
    {v : V} {S : Finset V} {L : ℝ}
    (hL : L ≤ (S.card : ℝ)) :
    graphStarPresentEvent (V := V) v S ⊆
      graphSomeDegreeAtLeastEvent (V := V) L := by
  intro G hG
  exact ⟨v, graphStarPresentEvent_subset_degreeAtLeast (V := V) hL hG⟩

/-- The event that, among the finite leaf set `S`, exactly the vertices in `T`
are adjacent to the center `v`. -/
def graphStarExactEvent (v : V) (S T : Finset V) : Set (SimpleGraph V) :=
  {G | ∀ w ∈ S, (G.Adj v w ↔ w ∈ T)}

lemma graphStarExactEvent_eq_graphEdgesExactFinsetEvent
    {v : V} {S T : Finset V} (hvS : v ∉ S) :
    graphStarExactEvent (V := V) v S T =
      graphEdgesExactFinsetEvent (V := V)
        (graphStarEdgeFinset v S) (graphStarEdgeFinset v T) := by
  ext G
  simp [graphStarExactEvent, graphEdgesExactFinsetEvent,
    graphStarEdgeFinset, SimpleGraph.mem_edgeSet]
  constructor
  · intro h a haS
    have hmem : (∃ b ∈ T, b = a ∨ v = a ∧ b = v) ↔ a ∈ T := by
      constructor
      · rintro ⟨b, hbT, hba | ⟨hva, _hbv⟩⟩
        · simpa [hba] using hbT
        · exact False.elim (hvS (by simpa [hva] using haS))
      · intro haT
        exact ⟨a, haT, Or.inl rfl⟩
    exact (h a haS).trans hmem.symm
  · intro h a haS
    have hmem : (∃ b ∈ T, b = a ∨ v = a ∧ b = v) ↔ a ∈ T := by
      constructor
      · rintro ⟨b, hbT, hba | ⟨hva, _hbv⟩⟩
        · simpa [hba] using hbT
        · exact False.elim (hvS (by simpa [hva] using haS))
      · intro haT
        exact ⟨a, haT, Or.inl rfl⟩
    exact (h a haS).trans hmem

lemma graphStarEdgeFinset_subset {v : V} {S T : Finset V} (hT : T ⊆ S) :
    graphStarEdgeFinset v T ⊆ graphStarEdgeFinset v S := by
  intro e he
  rcases Finset.mem_map.mp he with ⟨w, hw, rfl⟩
  exact Finset.mem_map.mpr ⟨w, hT hw, rfl⟩

lemma measurableSet_graphStarExactEvent
    [DecidableEq (Sym2 V)] {v : V} {S T : Finset V} (hvS : v ∉ S) :
    MeasurableSet (graphStarExactEvent (V := V) v S T) := by
  rw [graphStarExactEvent_eq_graphEdgesExactFinsetEvent hvS]
  exact measurableSet_graphEdgesExactFinsetEvent _ _

/-- Exact probability of a star pattern in `G(n,p)`: among `S`, exactly `T`
is adjacent to the center. -/
lemma binomialRandom_graphStarExactEvent_probability
    [Countable V] [DecidableEq (Sym2 V)] (p : unitInterval)
    {v : V} {S T : Finset V} (hvS : v ∉ S) (hT : T ⊆ S) :
    SimpleGraph.binomialRandom V p
        (graphStarExactEvent (V := V) v S T) =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ T.card *
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^
          (S.card - T.card) := by
  rw [graphStarExactEvent_eq_graphEdgesExactFinsetEvent hvS]
  rw [binomialRandom_graphEdgesExactFinsetEvent_probability
    (V := V) (p := p) (E := graphStarEdgeFinset v S)
    (T := graphStarEdgeFinset v T)]
  · simp
  · exact graphStarEdgeFinset_subset_diag_compl hvS
  · exact graphStarEdgeFinset_subset hT

/-- Real-probability form of
`binomialRandom_graphStarExactEvent_probability`. -/
lemma binomialRandom_graphStarExactEvent_probability_real
    [Countable V] [DecidableEq (Sym2 V)] (p : unitInterval)
    {v : V} {S T : Finset V} (hvS : v ∉ S) (hT : T ⊆ S) :
    (SimpleGraph.binomialRandom V p).real
        (graphStarExactEvent (V := V) v S T) =
      (unitInterval.toNNReal p : ℝ) ^ T.card *
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
          (S.card - T.card) := by
  rw [measureReal_def,
    binomialRandom_graphStarExactEvent_probability (V := V) p hvS hT]
  simp

lemma graphStarExactEvent_subset_degreeAtLeast [Fintype V]
    {v : V} {S T : Finset V} {L : ℝ} (hT : T ⊆ S)
    (hL : L ≤ (T.card : ℝ)) :
    graphStarExactEvent (V := V) v S T ⊆
      graphDegreeAtLeastEvent (V := V) L v := by
  intro G hG
  refine graphStarPresentEvent_subset_degreeAtLeast
    (V := V) (v := v) (S := T) hL ?_
  intro w hwT
  exact (hG w (hT hwT)).2 hwT

lemma graphStarExactEvent_subset_someDegreeAtLeast [Fintype V]
    {v : V} {S T : Finset V} {L : ℝ} (hT : T ⊆ S)
    (hL : L ≤ (T.card : ℝ)) :
    graphStarExactEvent (V := V) v S T ⊆
      graphSomeDegreeAtLeastEvent (V := V) L := by
  intro G hG
  exact ⟨v, graphStarExactEvent_subset_degreeAtLeast (V := V) hT hL hG⟩

lemma graphStarExactEvent_disjoint_of_ne
    {v : V} {S T U : Finset V}
    (hT : T ⊆ S) (hU : U ⊆ S) (hne : T ≠ U) :
    Disjoint (graphStarExactEvent (V := V) v S T)
      (graphStarExactEvent (V := V) v S U) := by
  rw [Set.disjoint_left]
  intro G hGT hGU
  exact hne (by
    ext w
    by_cases hwS : w ∈ S
    · constructor
      · intro hwT
        exact (hGU w hwS).1 ((hGT w hwS).2 hwT)
      · intro hwU
        exact (hGT w hwS).1 ((hGU w hwS).2 hwU)
    · constructor
      · intro hwT
        exact False.elim (hwS (hT hwT))
      · intro hwU
        exact False.elim (hwS (hU hwU)))

/-- A binomial lower-mass bound for one star in `G(n,p)`: for any fixed center
`v` and candidate neighbor set `S`, the probability that `v` has degree at
least `k` is at least the single binomial mass
`choose(|S|, k) p^k (1-p)^(|S|-k)`. -/
theorem binomialRandom_graphDegreeAtLeast_probability_ge_star_binomial_mass
    [Fintype V] [Countable V] [DecidableEq (Sym2 V)]
    (p : unitInterval) {v : V} {S : Finset V} (hvS : v ∉ S) (k : ℕ) :
    (Nat.choose S.card k : ℝ) *
        (unitInterval.toNNReal p : ℝ) ^ k *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^ (S.card - k)
      ≤ (SimpleGraph.binomialRandom V p).real
          (graphDegreeAtLeastEvent (V := V) (k : ℝ) v) := by
  classical
  let C : Finset (Finset V) := S.powersetCard k
  let A : Finset V → Set (SimpleGraph V) :=
    fun T => graphStarExactEvent (V := V) v S T
  have hpd : (↑C : Set (Finset V)).PairwiseDisjoint A := by
    intro T hTC U hUC hne
    have hTsub : T ⊆ S := (Finset.mem_powersetCard.mp hTC).1
    have hUsub : U ⊆ S := (Finset.mem_powersetCard.mp hUC).1
    exact graphStarExactEvent_disjoint_of_ne
      (V := V) (v := v) (S := S) hTsub hUsub hne
  have hmeas : ∀ T ∈ C, MeasurableSet (A T) := by
    intro T _hT
    exact measurableSet_graphStarExactEvent
      (V := V) (v := v) (S := S) (T := T) hvS
  have hUnionReal :
      (SimpleGraph.binomialRandom V p).real (⋃ T ∈ C, A T) =
        ∑ T ∈ C, (SimpleGraph.binomialRandom V p).real (A T) := by
    exact MeasureTheory.measureReal_biUnion_finset
      (μ := SimpleGraph.binomialRandom V p) hpd hmeas
  have hterm : ∀ T ∈ C,
      (SimpleGraph.binomialRandom V p).real (A T) =
        (unitInterval.toNNReal p : ℝ) ^ k *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
            (S.card - k) := by
    intro T hTC
    have hTsub : T ⊆ S := (Finset.mem_powersetCard.mp hTC).1
    have hTcard : T.card = k := (Finset.mem_powersetCard.mp hTC).2
    rw [binomialRandom_graphStarExactEvent_probability_real
      (V := V) (p := p) (v := v) (S := S) (T := T) hvS hTsub]
    rw [hTcard]
  have hUnionEval :
      (SimpleGraph.binomialRandom V p).real (⋃ T ∈ C, A T) =
        (Nat.choose S.card k : ℝ) *
          ((unitInterval.toNNReal p : ℝ) ^ k *
            (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
              (S.card - k)) := by
    rw [hUnionReal]
    calc
      (∑ T ∈ C, (SimpleGraph.binomialRandom V p).real (A T))
          =
        ∑ _T ∈ C,
          ((unitInterval.toNNReal p : ℝ) ^ k *
            (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
              (S.card - k)) := by
            exact Finset.sum_congr rfl fun T hTC => hterm T hTC
      _ =
        (C.card : ℝ) *
          ((unitInterval.toNNReal p : ℝ) ^ k *
            (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
              (S.card - k)) := by
            simp
      _ =
        (Nat.choose S.card k : ℝ) *
          ((unitInterval.toNNReal p : ℝ) ^ k *
            (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
              (S.card - k)) := by
            simp [C, Finset.card_powersetCard]
  have hsubset :
      (⋃ T ∈ C, A T) ⊆
        graphDegreeAtLeastEvent (V := V) (k : ℝ) v := by
    intro G hG
    simp only [Set.mem_iUnion] at hG
    rcases hG with ⟨T, hTC, hGA⟩
    have hTsub : T ⊆ S := (Finset.mem_powersetCard.mp hTC).1
    have hTcard : T.card = k := (Finset.mem_powersetCard.mp hTC).2
    exact graphStarExactEvent_subset_degreeAtLeast
      (V := V) (v := v) (S := S) (T := T) hTsub (by rw [hTcard]) hGA
  calc
    (Nat.choose S.card k : ℝ) *
        (unitInterval.toNNReal p : ℝ) ^ k *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^ (S.card - k)
        =
      (Nat.choose S.card k : ℝ) *
        ((unitInterval.toNNReal p : ℝ) ^ k *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
            (S.card - k)) := by
        ring
    _ = (SimpleGraph.binomialRandom V p).real (⋃ T ∈ C, A T) :=
      hUnionEval.symm
    _ ≤
      (SimpleGraph.binomialRandom V p).real
        (graphDegreeAtLeastEvent (V := V) (k : ℝ) v) :=
      MeasureTheory.measureReal_mono hsubset

/-- The event that exactly `k` vertices in the finite leaf block `S` are
adjacent to the center `v`. Edges outside the star block are unrestricted. -/
def graphStarExactCardEvent (v : V) (S : Finset V) (k : ℕ) :
    Set (SimpleGraph V) :=
  ⋃ T ∈ S.powersetCard k, graphStarExactEvent (V := V) v S T

lemma measurableSet_graphStarExactCardEvent
    [DecidableEq (Sym2 V)] {v : V} {S : Finset V} (hvS : v ∉ S) (k : ℕ) :
    MeasurableSet (graphStarExactCardEvent (V := V) v S k) := by
  classical
  dsimp [graphStarExactCardEvent]
  exact (S.powersetCard k).measurableSet_biUnion fun T _hT =>
    measurableSet_graphStarExactEvent (V := V) (v := v) (S := S) (T := T) hvS

lemma measurableSet_graphStarExactCardEvent_generateFrom_edgePatterns
    [DecidableEq (Sym2 V)] {v : V} {S : Finset V} (hvS : v ∉ S) (k : ℕ) :
    @MeasurableSet (SimpleGraph V)
      (MeasurableSpace.generateFrom
        (graphEdgesExactPatternFamily (V := V) (graphStarEdgeFinset v S)))
      (graphStarExactCardEvent (V := V) v S k) := by
  classical
  dsimp [graphStarExactCardEvent]
  refine @Finset.measurableSet_biUnion (SimpleGraph V) (Finset V)
    (MeasurableSpace.generateFrom
      (graphEdgesExactPatternFamily (V := V) (graphStarEdgeFinset v S)))
    (fun T => graphStarExactEvent (V := V) v S T)
    (S.powersetCard k) ?_
  intro T hT
  dsimp
  show @MeasurableSet (SimpleGraph V)
    (MeasurableSpace.generateFrom
      (graphEdgesExactPatternFamily (V := V) (graphStarEdgeFinset v S)))
    (graphStarExactEvent (V := V) v S T)
  rw [graphStarExactEvent_eq_graphEdgesExactFinsetEvent (V := V) hvS]
  exact MeasurableSpace.measurableSet_generateFrom
    (show
      graphEdgesExactFinsetEvent (V := V)
          (graphStarEdgeFinset v S) (graphStarEdgeFinset v T) ∈
        graphEdgesExactPatternFamily (V := V) (graphStarEdgeFinset v S) from by
    have hTsub : T ⊆ S := (Finset.mem_powersetCard.mp hT).1
    exact ⟨graphStarEdgeFinset v T, graphStarEdgeFinset_subset hTsub, rfl⟩)

lemma graphStarExactCardEvent_subset_degreeAtLeast [Fintype V]
    {v : V} {S : Finset V} {k : ℕ} :
    graphStarExactCardEvent (V := V) v S k ⊆
      graphDegreeAtLeastEvent (V := V) (k : ℝ) v := by
  classical
  intro G hG
  simp only [graphStarExactCardEvent, Set.mem_iUnion] at hG
  rcases hG with ⟨T, hTC, hGT⟩
  have hTsub : T ⊆ S := (Finset.mem_powersetCard.mp hTC).1
  have hTcard : T.card = k := (Finset.mem_powersetCard.mp hTC).2
  exact graphStarExactEvent_subset_degreeAtLeast
    (V := V) (v := v) (S := S) (T := T) hTsub (by rw [hTcard]) hGT

lemma graphStarExactCardEvent_subset_someDegreeAtLeast [Fintype V]
    {v : V} {S : Finset V} {k : ℕ} :
    graphStarExactCardEvent (V := V) v S k ⊆
      graphSomeDegreeAtLeastEvent (V := V) (k : ℝ) := by
  intro G hG
  exact ⟨v, graphStarExactCardEvent_subset_degreeAtLeast (V := V) hG⟩

/-- The exact binomial mass for a star block: in `G(n,p)`, the probability
that exactly `k` leaves in `S` are adjacent to `v` is
`choose(|S|, k) p^k (1-p)^(|S|-k)`. -/
lemma binomialRandom_graphStarExactCardEvent_probability_real
    [Countable V] [DecidableEq (Sym2 V)] (p : unitInterval)
    {v : V} {S : Finset V} (hvS : v ∉ S) (k : ℕ) :
    (SimpleGraph.binomialRandom V p).real
        (graphStarExactCardEvent (V := V) v S k) =
      (Nat.choose S.card k : ℝ) *
        (unitInterval.toNNReal p : ℝ) ^ k *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^ (S.card - k) := by
  classical
  let C : Finset (Finset V) := S.powersetCard k
  let A : Finset V → Set (SimpleGraph V) :=
    fun T => graphStarExactEvent (V := V) v S T
  have hpd : (↑C : Set (Finset V)).PairwiseDisjoint A := by
    intro T hTC U hUC hne
    have hTsub : T ⊆ S := (Finset.mem_powersetCard.mp hTC).1
    have hUsub : U ⊆ S := (Finset.mem_powersetCard.mp hUC).1
    exact graphStarExactEvent_disjoint_of_ne
      (V := V) (v := v) (S := S) hTsub hUsub hne
  have hmeas : ∀ T ∈ C, MeasurableSet (A T) := by
    intro T _hT
    exact measurableSet_graphStarExactEvent
      (V := V) (v := v) (S := S) (T := T) hvS
  have hUnionReal :
      (SimpleGraph.binomialRandom V p).real (⋃ T ∈ C, A T) =
        ∑ T ∈ C, (SimpleGraph.binomialRandom V p).real (A T) := by
    exact MeasureTheory.measureReal_biUnion_finset
      (μ := SimpleGraph.binomialRandom V p) hpd hmeas
  have hterm : ∀ T ∈ C,
      (SimpleGraph.binomialRandom V p).real (A T) =
        (unitInterval.toNNReal p : ℝ) ^ k *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
            (S.card - k) := by
    intro T hTC
    have hTsub : T ⊆ S := (Finset.mem_powersetCard.mp hTC).1
    have hTcard : T.card = k := (Finset.mem_powersetCard.mp hTC).2
    rw [binomialRandom_graphStarExactEvent_probability_real
      (V := V) (p := p) (v := v) (S := S) (T := T) hvS hTsub]
    rw [hTcard]
  calc
    (SimpleGraph.binomialRandom V p).real
        (graphStarExactCardEvent (V := V) v S k)
        =
      (SimpleGraph.binomialRandom V p).real (⋃ T ∈ C, A T) := by
        rfl
    _ =
      ∑ T ∈ C, (SimpleGraph.binomialRandom V p).real (A T) :=
        hUnionReal
    _ =
      ∑ _T ∈ C,
        ((unitInterval.toNNReal p : ℝ) ^ k *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
            (S.card - k)) := by
        exact Finset.sum_congr rfl fun T hTC => hterm T hTC
    _ =
      (C.card : ℝ) *
        ((unitInterval.toNNReal p : ℝ) ^ k *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
            (S.card - k)) := by
        simp
    _ =
      (Nat.choose S.card k : ℝ) *
        ((unitInterval.toNNReal p : ℝ) ^ k *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
            (S.card - k)) := by
        simp [C, Finset.card_powersetCard]
    _ =
      (Nat.choose S.card k : ℝ) *
        (unitInterval.toNNReal p : ℝ) ^ k *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
            (S.card - k) := by
        ring

/-- Elementary lower bound used in the exact-count random-graph lower tails:
for `0 ≤ x ≤ 1/2`, `exp (-2x) ≤ 1 - x`. -/
lemma exp_neg_two_mul_le_one_sub_of_le_half {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have hpos : 0 < 1 - x := by linarith
  rw [← Real.le_log_iff_exp_le hpos]
  have hlog_lower : 1 - (1 - x)⁻¹ ≤ Real.log (1 - x) :=
    Real.one_sub_inv_le_log_of_pos hpos
  have haux : -(2 * x) ≤ 1 - (1 - x)⁻¹ := by
    field_simp [hpos.ne']
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxhalf)]
  exact haux.trans hlog_lower

/-- Product form of `exp (-2p) ≤ 1 - p`. -/
lemma one_sub_pow_ge_exp_neg_two_mul {p : ℝ} {m : ℕ}
    (hp0 : 0 ≤ p) (hphalf : p ≤ 1 / 2) :
    Real.exp (-(2 * (m : ℝ) * p)) ≤ (1 - p) ^ m := by
  have hbase : Real.exp (-(2 * p)) ≤ 1 - p :=
    exp_neg_two_mul_le_one_sub_of_le_half hp0 hphalf
  have hpow : (Real.exp (-(2 * p))) ^ m ≤ (1 - p) ^ m := by
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hbase m
  calc
    Real.exp (-(2 * (m : ℝ) * p)) = (Real.exp (-(2 * p))) ^ m := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ (1 - p) ^ m := hpow

/-- Lower bound on one exact binomial mass.  If the block mean `m p` lies
between `η` and `D`, then the exact `k`-success mass is bounded below by the
single displayed term. -/
lemma binomial_exact_mass_lower_exp_of_mean_bounds
    {m k : ℕ} {p η D : ℝ}
    (hk0 : 0 < k) (hkm : k ≤ m)
    (hp0 : 0 ≤ p) (hphalf : p ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη : η ≤ (m : ℝ) * p)
    (hD : (m : ℝ) * p ≤ D) :
    Real.exp (-(2 * D)) * (η / (k : ℝ)) ^ k ≤
      (Nat.choose m k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by
  have hkposR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hchoose : ((m : ℝ) / (k : ℝ)) ^ k ≤ (Nat.choose m k : ℝ) :=
    choose_lower_bound m k hk0 hkm
  have hηdiv_nonneg : 0 ≤ η / (k : ℝ) := by positivity
  have hratio : (η / (k : ℝ)) ^ k ≤ (((m : ℝ) * p) / (k : ℝ)) ^ k := by
    exact pow_le_pow_left₀ hηdiv_nonneg
      (div_le_div_of_nonneg_right hη hkposR.le) k
  have hmp_eq :
      (((m : ℝ) * p) / (k : ℝ)) ^ k =
        ((m : ℝ) / (k : ℝ)) ^ k * p ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp [hkposR.ne']
  have hchoose_p :
      (η / (k : ℝ)) ^ k ≤ (Nat.choose m k : ℝ) * p ^ k := by
    calc
      (η / (k : ℝ)) ^ k ≤ (((m : ℝ) * p) / (k : ℝ)) ^ k := hratio
      _ = ((m : ℝ) / (k : ℝ)) ^ k * p ^ k := hmp_eq
      _ ≤ (Nat.choose m k : ℝ) * p ^ k := by
        exact mul_le_mul_of_nonneg_right hchoose (pow_nonneg hp0 k)
  have habs_m : Real.exp (-(2 * D)) ≤ (1 - p) ^ m := by
    calc
      Real.exp (-(2 * D)) ≤ Real.exp (-(2 * ((m : ℝ) * p))) := by
        rw [Real.exp_le_exp]
        nlinarith
      _ = Real.exp (-(2 * (m : ℝ) * p)) := by ring_nf
      _ ≤ (1 - p) ^ m := one_sub_pow_ge_exp_neg_two_mul hp0 hphalf
  have hbase0 : 0 ≤ 1 - p := by linarith
  have hbase1 : 1 - p ≤ 1 := by linarith
  have hpow_m_le : (1 - p) ^ m ≤ (1 - p) ^ (m - k) := by
    exact pow_le_pow_of_le_one hbase0 hbase1 (Nat.sub_le m k)
  have habs : Real.exp (-(2 * D)) ≤ (1 - p) ^ (m - k) :=
    habs_m.trans hpow_m_le
  have hnonneg_abs : 0 ≤ (1 - p) ^ (m - k) := pow_nonneg hbase0 _
  calc
    Real.exp (-(2 * D)) * (η / (k : ℝ)) ^ k
        ≤ (1 - p) ^ (m - k) * ((Nat.choose m k : ℝ) * p ^ k) := by
          exact mul_le_mul habs hchoose_p
            (pow_nonneg hηdiv_nonneg k) hnonneg_abs
    _ = (Nat.choose m k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by ring

/-- The algebraic constant from the corrected Exercise 2.4.4 proof:
when `k = 10d`, the lower-tail term
`exp(-2d) * ((d/3) / k)^k` is exactly the advertised exponential lower
bound with constant `10 log 30 + 2`. -/
lemma sparse_exact_mass_pdf_exponential_lower
    {d : ℝ} {k : ℕ} (hk0 : 0 < k) (hk : (k : ℝ) = 10 * d) :
    Real.exp (-((10 * Real.log 30 + 2) * d)) ≤
      Real.exp (-(2 * d)) * ((d / 3) / (k : ℝ)) ^ k := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hdpos : 0 < d := by nlinarith
  have hbase : (d / 3) / (k : ℝ) = (1 / 30 : ℝ) := by
    rw [hk]
    field_simp [hdpos.ne']
    ring
  have hpow :
      (1 / 30 : ℝ) ^ k =
        Real.exp (-(Real.log 30) * (k : ℝ)) := by
    calc
      (1 / 30 : ℝ) ^ k =
          (Real.exp (Real.log (1 / 30 : ℝ))) ^ k := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 30)]
      _ = Real.exp ((k : ℝ) * Real.log (1 / 30 : ℝ)) := by
            rw [← Real.exp_nat_mul]
      _ = Real.exp (-(Real.log 30) * (k : ℝ)) := by
            congr 1
            rw [show (1 / 30 : ℝ) = (30 : ℝ)⁻¹ by norm_num,
              Real.log_inv]
            ring
  rw [hbase, hpow, ← Real.exp_add]
  rw [Real.exp_le_exp]
  rw [hk]
  ring_nf
  exact le_rfl

/-- Power-form lower bound used in the corrected Exercise 2.4.5 proof. -/
lemma exp_neg_le_div_pow_of_mul_log_le
    {a t : ℝ} {r : ℕ} (ha : 0 < a) (hr : 0 < r)
    (hscale : (r : ℝ) * Real.log ((r : ℝ) / a) ≤ t) :
    Real.exp (-t) ≤ (a / (r : ℝ)) ^ r := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hpow :
      (a / (r : ℝ)) ^ r =
        Real.exp (-((r : ℝ) * Real.log ((r : ℝ) / a))) := by
    have hbase_pos : 0 < a / (r : ℝ) := div_pos ha hrpos
    calc
      (a / (r : ℝ)) ^ r =
          (Real.exp (Real.log (a / (r : ℝ)))) ^ r := by
            rw [Real.exp_log hbase_pos]
      _ = Real.exp ((r : ℝ) * Real.log (a / (r : ℝ))) := by
            rw [← Real.exp_nat_mul]
      _ = Real.exp (-((r : ℝ) * Real.log ((r : ℝ) / a))) := by
            congr 1
            rw [Real.log_div ha.ne' hrpos.ne',
              Real.log_div hrpos.ne' ha.ne']
            ring
  rw [hpow, Real.exp_le_exp]
  linarith

/-- Exact-star probability lower bound in `G(n,p)`, derived from
`binomial_exact_mass_lower_exp_of_mean_bounds`. -/
lemma binomialRandom_graphStarExactCardEvent_probability_real_ge_exp_of_mean_bounds
    [Countable V] [DecidableEq (Sym2 V)] (p : unitInterval)
    {v : V} {S : Finset V} (hvS : v ∉ S) {k : ℕ} {η D : ℝ}
    (hk0 : 0 < k) (hkm : k ≤ S.card)
    (hphalf : (unitInterval.toNNReal p : ℝ) ≤ 1 / 2)
    (hη0 : 0 ≤ η)
    (hη : η ≤ (S.card : ℝ) * (unitInterval.toNNReal p : ℝ))
    (hD : (S.card : ℝ) * (unitInterval.toNNReal p : ℝ) ≤ D) :
    Real.exp (-(2 * D)) * (η / (k : ℝ)) ^ k ≤
      (SimpleGraph.binomialRandom V p).real
        (graphStarExactCardEvent (V := V) v S k) := by
  rw [binomialRandom_graphStarExactCardEvent_probability_real
    (V := V) (p := p) (v := v) (S := S) hvS k]
  exact binomial_exact_mass_lower_exp_of_mean_bounds
    (m := S.card) (k := k)
    (p := (unitInterval.toNNReal p : ℝ)) (η := η) (D := D)
    hk0 hkm (by positivity) hphalf hη0 hη hD

/-- A logarithmic corollary of the exact binomial-mass lower bound: if the
block mean is bounded above by `D` and below by a positive `η`, then the
exact-count mass at level `k` is at least
`exp (-B (k log k + k))` with `B = 2D + |log η| + 1`. -/
lemma exp_neg_const_mul_k_log_k_add_k_le_exp_mul_pow
    {D η : ℝ} {k : ℕ} (hD0 : 0 ≤ D) (hηpos : 0 < η) (hk0 : 0 < k) :
    Real.exp (-((2 * D + |Real.log η| + 1) *
        ((k : ℝ) * Real.log (k : ℝ) + (k : ℝ))))
      ≤ Real.exp (-(2 * D)) * (η / (k : ℝ)) ^ k := by
  let B : ℝ := 2 * D + |Real.log η| + 1
  have hkposR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hkge1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
  have hlogk_nonneg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hkge1R
  have hB_ge_one : 1 ≤ B := by
    dsimp [B]
    nlinarith [abs_nonneg (Real.log η)]
  have hB_ge_2D_abs : 2 * D + |Real.log η| ≤ B := by
    dsimp [B]
    linarith
  have hpow_eq :
      (η / (k : ℝ)) ^ k =
        Real.exp ((k : ℝ) * (Real.log η - Real.log (k : ℝ))) := by
    have hbase_pos : 0 < η / (k : ℝ) := div_pos hηpos hkposR
    calc
      (η / (k : ℝ)) ^ k =
          (Real.exp (Real.log (η / (k : ℝ)))) ^ k := by
            rw [Real.exp_log hbase_pos]
      _ = Real.exp ((k : ℝ) * Real.log (η / (k : ℝ))) := by
            rw [← Real.exp_nat_mul]
      _ = Real.exp ((k : ℝ) * (Real.log η - Real.log (k : ℝ))) := by
            rw [Real.log_div hηpos.ne' hkposR.ne']
  have hrhs_eq :
      Real.exp (-(2 * D)) * (η / (k : ℝ)) ^ k =
        Real.exp (-(2 * D) +
          (k : ℝ) * (Real.log η - Real.log (k : ℝ))) := by
    rw [hpow_eq, ← Real.exp_add]
  rw [hrhs_eq]
  rw [Real.exp_le_exp]
  have hneg_log_eta_le_abs : -Real.log η ≤ |Real.log η| := neg_le_abs _
  have hmain :
      2 * D + (k : ℝ) * Real.log (k : ℝ) -
          (k : ℝ) * Real.log η ≤
        B * ((k : ℝ) * Real.log (k : ℝ) + (k : ℝ)) := by
    have h1 :
        (k : ℝ) * Real.log (k : ℝ) ≤
          B * ((k : ℝ) * Real.log (k : ℝ)) := by
      simpa using (mul_le_mul_of_nonneg_right hB_ge_one
        (mul_nonneg hkposR.le hlogk_nonneg))
    have h2D_le : 2 * D ≤ (2 * D) * (k : ℝ) := by
      calc
        2 * D = (2 * D) * 1 := by ring
        _ ≤ (2 * D) * (k : ℝ) := by
          exact mul_le_mul_of_nonneg_left hkge1R (by nlinarith)
    have hneglog_le :
        -((k : ℝ) * Real.log η) ≤ (k : ℝ) * |Real.log η| := by
      have := mul_le_mul_of_nonneg_left hneg_log_eta_le_abs hkposR.le
      nlinarith
    have h2 :
        2 * D - (k : ℝ) * Real.log η ≤ B * (k : ℝ) := by
      have hA :
          2 * D - (k : ℝ) * Real.log η ≤
            (2 * D) * (k : ℝ) + (k : ℝ) * |Real.log η| := by
        nlinarith
      have hBmul :
          (2 * D) * (k : ℝ) + (k : ℝ) * |Real.log η| ≤
            B * (k : ℝ) := by
        have := mul_le_mul_of_nonneg_right hB_ge_2D_abs hkposR.le
        nlinarith
      exact hA.trans hBmul
    have hsum :
        (k : ℝ) * Real.log (k : ℝ) +
            (2 * D - (k : ℝ) * Real.log η) ≤
          B * ((k : ℝ) * Real.log (k : ℝ)) + B * (k : ℝ) := by
      nlinarith
    calc
      2 * D + (k : ℝ) * Real.log (k : ℝ) -
          (k : ℝ) * Real.log η
          =
        (k : ℝ) * Real.log (k : ℝ) +
          (2 * D - (k : ℝ) * Real.log η) := by ring
      _ ≤ B * ((k : ℝ) * Real.log (k : ℝ)) + B * (k : ℝ) := hsum
      _ = B * ((k : ℝ) * Real.log (k : ℝ) + (k : ℝ)) := by ring
  nlinarith

/-- Exact binomial mass lower bound in `exp (-B(k log k + k))` form. -/
lemma binomial_exact_mass_lower_exp_log_of_mean_bounds
    {m k : ℕ} {p η D : ℝ}
    (hk0 : 0 < k) (hkm : k ≤ m)
    (hp0 : 0 ≤ p) (hphalf : p ≤ 1 / 2)
    (hD0 : 0 ≤ D) (hηpos : 0 < η)
    (hη : η ≤ (m : ℝ) * p)
    (hD : (m : ℝ) * p ≤ D) :
    Real.exp (-((2 * D + |Real.log η| + 1) *
        ((k : ℝ) * Real.log (k : ℝ) + (k : ℝ)))) ≤
      (Nat.choose m k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by
  exact (exp_neg_const_mul_k_log_k_add_k_le_exp_mul_pow
    (D := D) (η := η) (k := k) hD0 hηpos hk0).trans
    (binomial_exact_mass_lower_exp_of_mean_bounds
      (m := m) (k := k) (p := p) (η := η) (D := D)
      hk0 hkm hp0 hphalf hηpos.le hη hD)

/-- Exact-star probability lower bound in logarithmic `k log k` form. -/
lemma binomialRandom_graphStarExactCardEvent_probability_real_ge_exp_log_of_mean_bounds
    [Countable V] [DecidableEq (Sym2 V)] (p : unitInterval)
    {v : V} {S : Finset V} (hvS : v ∉ S) {k : ℕ} {η D : ℝ}
    (hk0 : 0 < k) (hkm : k ≤ S.card)
    (hphalf : (unitInterval.toNNReal p : ℝ) ≤ 1 / 2)
    (hD0 : 0 ≤ D) (hηpos : 0 < η)
    (hη : η ≤ (S.card : ℝ) * (unitInterval.toNNReal p : ℝ))
    (hD : (S.card : ℝ) * (unitInterval.toNNReal p : ℝ) ≤ D) :
    Real.exp (-((2 * D + |Real.log η| + 1) *
        ((k : ℝ) * Real.log (k : ℝ) + (k : ℝ)))) ≤
      (SimpleGraph.binomialRandom V p).real
        (graphStarExactCardEvent (V := V) v S k) := by
  rw [binomialRandom_graphStarExactCardEvent_probability_real
    (V := V) (p := p) (v := v) (S := S) hvS k]
  exact binomial_exact_mass_lower_exp_log_of_mean_bounds
    (m := S.card) (k := k)
    (p := (unitInterval.toNNReal p : ℝ)) (η := η) (D := D)
    hk0 hkm (by positivity) hphalf hD0 hηpos hη hD

/-- Disjoint star edge blocks give independent exact-count star events. -/
theorem binomialRandom_graphStarExactCardEvent_iIndepSet
    [Countable V] [DecidableEq (Sym2 V)]
    (p : unitInterval) (v : J → V) (S : J → Finset V) (k : J → ℕ)
    (hvS : ∀ j, v j ∉ S j)
    (hdisj : (Set.univ : Set J).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v j) (S j))) :
    iIndepSet
      (fun j => graphStarExactCardEvent (V := V) (v j) (S j) (k j))
      (SimpleGraph.binomialRandom V p) := by
  classical
  let π : J → Set (Set (SimpleGraph V)) := fun j =>
    graphEdgesExactPatternFamily (V := V) (graphStarEdgeFinset (v j) (S j))
  let m : J → MeasurableSpace (SimpleGraph V) := fun j =>
    MeasurableSpace.generateFrom (π j)
  have hπindep : iIndepSets π (SimpleGraph.binomialRandom V p) := by
    simpa [π] using
      (binomialRandom_graphEdgesExactPatternFamily_iIndepSets
        (V := V) (J := J) (p := p)
        (E := fun j => graphStarEdgeFinset (v j) (S j))
        (hdiag := fun j => graphStarEdgeFinset_subset_diag_compl (hvS j))
        (hdisj := hdisj))
  have hm_le :
      ∀ j, m j ≤ (by infer_instance : MeasurableSpace (SimpleGraph V)) := by
    intro j
    dsimp [m, π]
    exact MeasurableSpace.generateFrom_le fun A hA => by
      rcases hA with ⟨T, _hT, rfl⟩
      exact measurableSet_graphEdgesExactFinsetEvent (V := V)
        (graphStarEdgeFinset (v j) (S j)) T
  have hm_indep : iIndep m (SimpleGraph.binomialRandom V p) :=
    iIndepSets.iIndep
      (m := m)
      (h_le := hm_le)
      (π := π)
      (h_pi := fun j => by
        dsimp [π]
        exact graphEdgesExactPatternFamily_isPiSystem (V := V)
          (graphStarEdgeFinset (v j) (S j)))
      (h_generate := fun j => by rfl)
      hπindep
  exact iIndepSets.iIndepSet_of_mem
    (π := fun j => {A : Set (SimpleGraph V) | MeasurableSet[m j] A})
    (f := fun j => graphStarExactCardEvent (V := V) (v j) (S j) (k j))
    (hfπ := fun j => by
      dsimp [m, π]
      exact measurableSet_graphStarExactCardEvent_generateFrom_edgePatterns
        (V := V) (v := v j) (S := S j) (hvS j) (k j))
    (hf := fun j =>
      measurableSet_graphStarExactCardEvent
        (V := V) (v := v j) (S := S j) (hvS j) (k j))
    hm_indep.iIndepSets'

end StarWitnesses

section DegreeComplements

variable {V : Type*} [MeasurableSpace (SimpleGraph V)]
variable {μ : Measure (SimpleGraph V)}

/-- Complement form of the random-graph union bound: if the bad event has
probability at most `δ`, then the good all-degrees event has probability at
least `1 - δ`. -/
theorem graphAllDegreesWithin_probability_ge_one_sub
    [IsProbabilityMeasure μ] {d ε δ : ℝ}
    (hmeas :
      MeasurableSet (graphSomeDegreeDeviationEvent (V := V) d ε))
    (hbad :
      μ.real (graphSomeDegreeDeviationEvent (V := V) d ε) ≤ δ) :
    1 - δ ≤ μ.real (graphAllDegreesWithinEvent (V := V) d ε) := by
  rw [graphAllDegreesWithinEvent_eq_compl_someDeviation,
    MeasureTheory.measureReal_compl hmeas]
  rw [MeasureTheory.probReal_univ]
  linarith

/-- Complement form of the maximum-degree union bound: if the event that some
vertex has degree at least `L` has probability at most `δ`, then with
probability at least `1 - δ` all degrees are below `L`. -/
theorem graphAllDegreesBelow_probability_ge_one_sub
    [IsProbabilityMeasure μ] {L δ : ℝ}
    (hmeas :
      MeasurableSet (graphSomeDegreeAtLeastEvent (V := V) L))
    (hbad :
      μ.real (graphSomeDegreeAtLeastEvent (V := V) L) ≤ δ) :
    1 - δ ≤ μ.real (graphAllDegreesBelowEvent (V := V) L) := by
  rw [graphAllDegreesBelowEvent_eq_compl_someAtLeast,
    MeasureTheory.measureReal_compl hmeas]
  rw [MeasureTheory.probReal_univ]
  linarith

end DegreeComplements

section DegreeUnionBounds

variable {V : Type*} [Fintype V] [MeasurableSpace (SimpleGraph V)]
variable {μ : Measure (SimpleGraph V)}

/-- Union-bound amplification of per-vertex degree deviation probabilities. -/
theorem graphSomeDegreeDeviation_probability_le_sum (d ε : ℝ) :
    μ.real (graphSomeDegreeDeviationEvent (V := V) d ε)
      ≤ ∑ v, μ.real (graphDegreeDeviationEvent (V := V) d ε v) := by
  classical
  simpa [graphSomeDegreeDeviationEvent] using
    (measureReal_exists_le_sum
      (μ := μ)
      (A := fun v : V => graphDegreeDeviationEvent (V := V) d ε v))

/-- Uniform per-vertex degree deviation tail implies a graph-wide bad-event
bound. -/
theorem graphSomeDegreeDeviation_probability_le_of_forall
    {d ε q : ℝ}
    (htail : ∀ v, μ.real (graphDegreeDeviationEvent (V := V) d ε v) ≤ q) :
    μ.real (graphSomeDegreeDeviationEvent (V := V) d ε)
      ≤ (Fintype.card V : ℝ) * q := by
  classical
  calc
    μ.real (graphSomeDegreeDeviationEvent (V := V) d ε)
        ≤ ∑ v, μ.real (graphDegreeDeviationEvent (V := V) d ε v) :=
      graphSomeDegreeDeviation_probability_le_sum (μ := μ) d ε
    _ ≤ ∑ _v : V, q := by
      exact Finset.sum_le_sum fun v _hv => htail v
    _ = (Fintype.card V : ℝ) * q := by
      simp

/-- Union-bound amplification of per-vertex high-degree probabilities. This is
the reusable proof pattern behind Exercises 2.4.2 and 2.4.3. -/
theorem graphSomeDegreeAtLeast_probability_le_sum (L : ℝ) :
    μ.real (graphSomeDegreeAtLeastEvent (V := V) L)
      ≤ ∑ v, μ.real (graphDegreeAtLeastEvent (V := V) L v) := by
  classical
  simpa [graphSomeDegreeAtLeastEvent] using
    (measureReal_exists_le_sum
      (μ := μ)
      (A := fun v : V => graphDegreeAtLeastEvent (V := V) L v))

/-- Uniform per-vertex high-degree tail implies a graph-wide maximum-degree
bound. -/
theorem graphSomeDegreeAtLeast_probability_le_of_forall
    {L q : ℝ}
    (htail : ∀ v, μ.real (graphDegreeAtLeastEvent (V := V) L v) ≤ q) :
    μ.real (graphSomeDegreeAtLeastEvent (V := V) L)
      ≤ (Fintype.card V : ℝ) * q := by
  classical
  calc
    μ.real (graphSomeDegreeAtLeastEvent (V := V) L)
        ≤ ∑ v, μ.real (graphDegreeAtLeastEvent (V := V) L v) :=
      graphSomeDegreeAtLeast_probability_le_sum (μ := μ) L
    _ ≤ ∑ _v : V, q := by
      exact Finset.sum_le_sum fun v _hv => htail v
    _ = (Fintype.card V : ℝ) * q := by
      simp

/-- High-probability maximum-degree upper bound obtained from uniform
per-vertex tails and a union-budget of `0.1`. -/
theorem graphAllDegreesBelow_probability_ge_nine_tenths_of_forall
    [IsProbabilityMeasure μ] {L q : ℝ}
    (hmeas :
      MeasurableSet (graphSomeDegreeAtLeastEvent (V := V) L))
    (htail : ∀ v, μ.real (graphDegreeAtLeastEvent (V := V) L v) ≤ q)
    (hcard : (Fintype.card V : ℝ) * q ≤ 1 / 10) :
    9 / 10 ≤ μ.real (graphAllDegreesBelowEvent (V := V) L) := by
  have hbad :
      μ.real (graphSomeDegreeAtLeastEvent (V := V) L) ≤ 1 / 10 := by
    exact (graphSomeDegreeAtLeast_probability_le_of_forall
      (μ := μ) (V := V) (L := L) (q := q) htail).trans hcard
  have hgood :=
    graphAllDegreesBelow_probability_ge_one_sub
      (μ := μ) (V := V) (L := L) (δ := 1 / 10) hmeas hbad
  norm_num at hgood ⊢
  exact hgood

end DegreeUnionBounds

section SparseUpperBounds

variable {V : Type*} [Fintype V] [MeasurableSpace (SimpleGraph V)]
variable {μ : Measure (SimpleGraph V)}

/-- Quantitative form of HDP Exercise 2.4.2: if the per-vertex probability
of degree at least `A log n` has union-budget at most `0.1`, then with
probability at least `0.9` all degrees are `O(log n)` with constant `A`. -/
theorem sparse_graphs_degree_upper_bound_probability_ge_nine_tenths
    [IsProbabilityMeasure μ] {A q : ℝ}
    (hmeas :
      MeasurableSet
        (graphSomeDegreeAtLeastEvent (V := V)
          (A * Real.log (Fintype.card V : ℝ))))
    (htail : ∀ v,
      μ.real
        (graphDegreeAtLeastEvent (V := V)
          (A * Real.log (Fintype.card V : ℝ)) v) ≤ q)
    (hcard : (Fintype.card V : ℝ) * q ≤ 1 / 10) :
    9 / 10 ≤
      μ.real
        (graphAllDegreesBelowEvent (V := V)
          (A * Real.log (Fintype.card V : ℝ))) :=
  graphAllDegreesBelow_probability_ge_nine_tenths_of_forall
    (μ := μ) (V := V)
    (L := A * Real.log (Fintype.card V : ℝ)) (q := q)
    hmeas htail hcard

/-- Quantitative form of HDP Exercise 2.4.3: if the per-vertex probability
of degree at least `A log n / log log n` has union-budget at most `0.1`, then
with probability at least `0.9` all degrees have that order. -/
theorem very_sparse_graphs_degree_upper_bound_probability_ge_nine_tenths
    [IsProbabilityMeasure μ] {A q : ℝ}
    (hmeas :
      MeasurableSet
        (graphSomeDegreeAtLeastEvent (V := V)
          (A * Real.log (Fintype.card V : ℝ) /
            Real.log (Real.log (Fintype.card V : ℝ)))))
    (htail : ∀ v,
      μ.real
        (graphDegreeAtLeastEvent (V := V)
          (A * Real.log (Fintype.card V : ℝ) /
            Real.log (Real.log (Fintype.card V : ℝ))) v) ≤ q)
    (hcard : (Fintype.card V : ℝ) * q ≤ 1 / 10) :
    9 / 10 ≤
      μ.real
        (graphAllDegreesBelowEvent (V := V)
          (A * Real.log (Fintype.card V : ℝ) /
            Real.log (Real.log (Fintype.card V : ℝ)))) :=
  graphAllDegreesBelow_probability_ge_nine_tenths_of_forall
    (μ := μ) (V := V)
    (L := A * Real.log (Fintype.card V : ℝ) /
      Real.log (Real.log (Fintype.card V : ℝ))) (q := q)
    hmeas htail hcard

end SparseUpperBounds

section DegreeLowerWitnesses

variable {V J : Type*} [Fintype J] [MeasurableSpace (SimpleGraph V)]
variable {μ : Measure (SimpleGraph V)}

/-- Independent witness events for high-degree vertices amplify to a graph-level
lower bound. This is the reusable probability step behind the hints for
Exercises 2.4.4 and 2.4.5: construct independent events, each forcing the
existence of a high-degree vertex, then take the complementary product. -/
theorem graphSomeDegreeAtLeast_probability_ge_one_sub_pow_one_sub_of_independent_witnesses
    [IsProbabilityMeasure μ] {L q : ℝ} {B : J → Set (SimpleGraph V)}
    (hBmeas : ∀ j, MeasurableSet (B j))
    (hindep : iIndepSet B μ)
    (hprob : ∀ j, q ≤ μ.real (B j))
    (hforces : ∀ j, B j ⊆ graphSomeDegreeAtLeastEvent (V := V) L) :
    1 - (1 - q) ^ Fintype.card J
      ≤ μ.real (graphSomeDegreeAtLeastEvent (V := V) L) := by
  have hwitness :
      1 - (1 - q) ^ Fintype.card J
        ≤ μ.real {G | ∃ j, G ∈ B j} :=
    measureReal_exists_ge_one_sub_pow_one_sub_of_iIndepSet
      (μ := μ) (A := B) (q := q) hBmeas hindep hprob
  have hsubset :
      {G | ∃ j, G ∈ B j} ⊆ graphSomeDegreeAtLeastEvent (V := V) L := by
    rintro G ⟨j, hGj⟩
    exact hforces j hGj
  exact hwitness.trans (MeasureTheory.measureReal_mono hsubset)

/-- `0.9` form of the independent-witness lower bound for random-graph maximum
degrees. -/
theorem graphSomeDegreeAtLeast_probability_ge_nine_tenths_of_independent_witnesses
    [IsProbabilityMeasure μ] {L q : ℝ} {B : J → Set (SimpleGraph V)}
    (hBmeas : ∀ j, MeasurableSet (B j))
    (hindep : iIndepSet B μ)
    (hprob : ∀ j, q ≤ μ.real (B j))
    (hbudget : (1 - q) ^ Fintype.card J ≤ 1 / 10)
    (hforces : ∀ j, B j ⊆ graphSomeDegreeAtLeastEvent (V := V) L) :
    9 / 10 ≤ μ.real (graphSomeDegreeAtLeastEvent (V := V) L) := by
  have hlower :=
    graphSomeDegreeAtLeast_probability_ge_one_sub_pow_one_sub_of_independent_witnesses
      (μ := μ) (V := V) (J := J) (L := L) (q := q)
      hBmeas hindep hprob hforces
  nlinarith

/-- HDP Exercise 2.4.4, finite witness form: if one has independent witness
events, each with probability at least `q`, each forcing some vertex to have
degree at least `10d`, and the complementary product is at most `0.1`, then
with probability at least `0.9` the sparse graph is not almost regular in the
book's displayed sense. -/
theorem sparse_graphs_not_almost_regular_probability_ge_nine_tenths_of_independent_witnesses
    [IsProbabilityMeasure μ] {d q : ℝ} {B : J → Set (SimpleGraph V)}
    (hBmeas : ∀ j, MeasurableSet (B j))
    (hindep : iIndepSet B μ)
    (hprob : ∀ j, q ≤ μ.real (B j))
    (hbudget : (1 - q) ^ Fintype.card J ≤ 1 / 10)
    (hforces : ∀ j,
      B j ⊆ graphSomeDegreeAtLeastEvent (V := V) (10 * d)) :
    9 / 10 ≤
      μ.real (graphSomeDegreeAtLeastEvent (V := V) (10 * d)) :=
  graphSomeDegreeAtLeast_probability_ge_nine_tenths_of_independent_witnesses
    (μ := μ) (V := V) (J := J) (L := 10 * d) (q := q)
    hBmeas hindep hprob hbudget hforces

/-- HDP Exercise 2.4.5, finite witness form: independent witnesses that each
force a vertex of degree at least `A log n / log log n` amplify to the
book's `0.9` high-probability lower bound. -/
theorem very_sparse_graphs_far_from_regular_probability_ge_nine_tenths_of_independent_witnesses
    [Fintype V] [IsProbabilityMeasure μ] {A q : ℝ}
    {B : J → Set (SimpleGraph V)}
    (hBmeas : ∀ j, MeasurableSet (B j))
    (hindep : iIndepSet B μ)
    (hprob : ∀ j, q ≤ μ.real (B j))
    (hbudget : (1 - q) ^ Fintype.card J ≤ 1 / 10)
    (hforces : ∀ j,
      B j ⊆ graphSomeDegreeAtLeastEvent (V := V)
        (A * Real.log (Fintype.card V : ℝ) /
          Real.log (Real.log (Fintype.card V : ℝ)))) :
    9 / 10 ≤
      μ.real (graphSomeDegreeAtLeastEvent (V := V)
        (A * Real.log (Fintype.card V : ℝ) /
          Real.log (Real.log (Fintype.card V : ℝ)))) :=
  graphSomeDegreeAtLeast_probability_ge_nine_tenths_of_independent_witnesses
    (μ := μ) (V := V) (J := J)
    (L := A * Real.log (Fintype.card V : ℝ) /
      Real.log (Real.log (Fintype.card V : ℝ)))
    (q := q) hBmeas hindep hprob hbudget hforces

end DegreeLowerWitnesses

section StarLowerWitnesses

variable {V J : Type*}
variable [Fintype V] [Countable V] [DecidableEq (Sym2 V)] [Fintype J]

/-- Concrete `G(n,p)` lower-bound amplifier from disjoint star witnesses. Each
block is a finite star whose center is outside the leaf set; the disjointness
hypothesis is on the underlying unordered edge blocks. -/
theorem graphSomeDegreeAtLeast_probability_ge_one_sub_pow_one_sub_of_disjoint_star_witnesses
    (p : unitInterval) {L q : ℝ} (v : J → V) (S : J → Finset V)
    (hvS : ∀ j, v j ∉ S j)
    (hprob : ∀ j, q ≤ (unitInterval.toNNReal p : ℝ) ^ (S j).card)
    (hcard : ∀ j, L ≤ ((S j).card : ℝ))
    (hdisj : (Set.univ : Set J).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v j) (S j))) :
    1 - (1 - q) ^ Fintype.card J
      ≤ (SimpleGraph.binomialRandom V p).real
          (graphSomeDegreeAtLeastEvent (V := V) L) := by
  refine
    graphSomeDegreeAtLeast_probability_ge_one_sub_pow_one_sub_of_independent_witnesses
      (μ := SimpleGraph.binomialRandom V p) (V := V) (J := J)
      (L := L) (q := q)
      (B := fun j => graphStarPresentEvent (V := V) (v j) (S j))
      ?_ ?_ ?_ ?_
  · intro j
    exact measurableSet_graphStarPresentEvent (V := V) (v j) (S j)
  · exact binomialRandom_graphStarPresentEvent_iIndepSet
      (V := V) (J := J) p v S hvS hdisj
  · intro j
    rw [binomialRandom_graphStarPresentEvent_probability_real
      (V := V) p (hvS j)]
    exact hprob j
  · intro j
    exact graphStarPresentEvent_subset_someDegreeAtLeast (V := V) (hcard j)

/-- `0.9` form of the concrete `G(n,p)` star-witness lower-bound amplifier. -/
theorem graphSomeDegreeAtLeast_probability_ge_nine_tenths_of_disjoint_star_witnesses
    (p : unitInterval) {L q : ℝ} (v : J → V) (S : J → Finset V)
    (hvS : ∀ j, v j ∉ S j)
    (hprob : ∀ j, q ≤ (unitInterval.toNNReal p : ℝ) ^ (S j).card)
    (hcard : ∀ j, L ≤ ((S j).card : ℝ))
    (hbudget : (1 - q) ^ Fintype.card J ≤ 1 / 10)
    (hdisj : (Set.univ : Set J).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v j) (S j))) :
    9 / 10 ≤
      (SimpleGraph.binomialRandom V p).real
        (graphSomeDegreeAtLeastEvent (V := V) L) := by
  have hlower :=
    graphSomeDegreeAtLeast_probability_ge_one_sub_pow_one_sub_of_disjoint_star_witnesses
      (V := V) (J := J) p (L := L) (q := q) v S
      hvS hprob hcard hdisj
  nlinarith

/-- Concrete `G(n,p)` finite star-witness form for HDP Exercise 2.4.4:
disjoint star witnesses that each force degree at least `10d` amplify to the
book's displayed high-probability lower bound. -/
theorem sparse_graphs_not_almost_regular_probability_ge_nine_tenths_of_disjoint_star_witnesses
    (p : unitInterval) {d q : ℝ} (v : J → V) (S : J → Finset V)
    (hvS : ∀ j, v j ∉ S j)
    (hprob : ∀ j, q ≤ (unitInterval.toNNReal p : ℝ) ^ (S j).card)
    (hcard : ∀ j, 10 * d ≤ ((S j).card : ℝ))
    (hbudget : (1 - q) ^ Fintype.card J ≤ 1 / 10)
    (hdisj : (Set.univ : Set J).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v j) (S j))) :
    9 / 10 ≤
      (SimpleGraph.binomialRandom V p).real
        (graphSomeDegreeAtLeastEvent (V := V) (10 * d)) :=
  graphSomeDegreeAtLeast_probability_ge_nine_tenths_of_disjoint_star_witnesses
    (V := V) (J := J) p (L := 10 * d) (q := q) v S
    hvS hprob hcard hbudget hdisj

/-- Concrete `G(n,p)` finite star-witness form for HDP Exercise 2.4.5 at the
very-sparse lower scale `log n / log log n`. -/
theorem very_sparse_graphs_far_from_regular_probability_ge_nine_tenths_of_disjoint_star_witnesses
    (p : unitInterval) {A q : ℝ} (v : J → V) (S : J → Finset V)
    (hvS : ∀ j, v j ∉ S j)
    (hprob : ∀ j, q ≤ (unitInterval.toNNReal p : ℝ) ^ (S j).card)
    (hcard : ∀ j,
      A * Real.log (Fintype.card V : ℝ) /
          Real.log (Real.log (Fintype.card V : ℝ))
        ≤ ((S j).card : ℝ))
    (hbudget : (1 - q) ^ Fintype.card J ≤ 1 / 10)
    (hdisj : (Set.univ : Set J).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v j) (S j))) :
    9 / 10 ≤
      (SimpleGraph.binomialRandom V p).real
        (graphSomeDegreeAtLeastEvent (V := V)
          (A * Real.log (Fintype.card V : ℝ) /
            Real.log (Real.log (Fintype.card V : ℝ)))) :=
  graphSomeDegreeAtLeast_probability_ge_nine_tenths_of_disjoint_star_witnesses
    (V := V) (J := J) p
    (L := A * Real.log (Fintype.card V : ℝ) /
      Real.log (Real.log (Fintype.card V : ℝ)))
    (q := q) v S hvS hprob hcard hbudget hdisj

/-- Concrete `G(n,p)` lower-bound amplifier from disjoint exact-count star
blocks. Each witness says that exactly `k j` leaves in the block `S j` are
adjacent to the center `v j`, so the witness probability is the corresponding
binomial mass. -/
theorem graphSomeDegreeAtLeast_probability_ge_one_sub_pow_one_sub_of_disjoint_star_exact_count_witnesses
    (p : unitInterval) {L q : ℝ} (v : J → V) (S : J → Finset V) (k : J → ℕ)
    (hvS : ∀ j, v j ∉ S j)
    (hprob : ∀ j,
      q ≤ (Nat.choose (S j).card (k j) : ℝ) *
        (unitInterval.toNNReal p : ℝ) ^ (k j) *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
            ((S j).card - k j))
    (hcard : ∀ j, L ≤ (k j : ℝ))
    (hdisj : (Set.univ : Set J).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v j) (S j))) :
    1 - (1 - q) ^ Fintype.card J
      ≤ (SimpleGraph.binomialRandom V p).real
          (graphSomeDegreeAtLeastEvent (V := V) L) := by
  refine
    graphSomeDegreeAtLeast_probability_ge_one_sub_pow_one_sub_of_independent_witnesses
      (μ := SimpleGraph.binomialRandom V p) (V := V) (J := J)
      (L := L) (q := q)
      (B := fun j => graphStarExactCardEvent (V := V) (v j) (S j) (k j))
      ?_ ?_ ?_ ?_
  · intro j
    exact measurableSet_graphStarExactCardEvent
      (V := V) (v := v j) (S := S j) (hvS j) (k j)
  · exact binomialRandom_graphStarExactCardEvent_iIndepSet
      (V := V) (J := J) p v S k hvS hdisj
  · intro j
    rw [binomialRandom_graphStarExactCardEvent_probability_real
      (V := V) (p := p) (v := v j) (S := S j) (hvS j) (k j)]
    exact hprob j
  · intro j G hG
    exact ⟨v j,
      (hcard j).trans
        (graphStarExactCardEvent_subset_degreeAtLeast (V := V) hG)⟩

/-- `0.9` form of the concrete exact-count star-block amplifier. -/
theorem graphSomeDegreeAtLeast_probability_ge_nine_tenths_of_disjoint_star_exact_count_witnesses
    (p : unitInterval) {L q : ℝ} (v : J → V) (S : J → Finset V) (k : J → ℕ)
    (hvS : ∀ j, v j ∉ S j)
    (hprob : ∀ j,
      q ≤ (Nat.choose (S j).card (k j) : ℝ) *
        (unitInterval.toNNReal p : ℝ) ^ (k j) *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
            ((S j).card - k j))
    (hcard : ∀ j, L ≤ (k j : ℝ))
    (hbudget : (1 - q) ^ Fintype.card J ≤ 1 / 10)
    (hdisj : (Set.univ : Set J).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v j) (S j))) :
    9 / 10 ≤
      (SimpleGraph.binomialRandom V p).real
        (graphSomeDegreeAtLeastEvent (V := V) L) := by
  have hlower :=
    graphSomeDegreeAtLeast_probability_ge_one_sub_pow_one_sub_of_disjoint_star_exact_count_witnesses
      (V := V) (J := J) p (L := L) (q := q) v S k
      hvS hprob hcard hdisj
  nlinarith

/-- Concrete `G(n,p)` exact-count star-block form for HDP Exercise 2.4.4:
disjoint blocks whose exact-count witnesses force degree at least `10d` amplify
to the book's displayed high-probability lower bound. -/
theorem sparse_graphs_not_almost_regular_probability_ge_nine_tenths_of_disjoint_star_exact_count_witnesses
    (p : unitInterval) {d q : ℝ} (v : J → V) (S : J → Finset V) (k : J → ℕ)
    (hvS : ∀ j, v j ∉ S j)
    (hprob : ∀ j,
      q ≤ (Nat.choose (S j).card (k j) : ℝ) *
        (unitInterval.toNNReal p : ℝ) ^ (k j) *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
            ((S j).card - k j))
    (hcard : ∀ j, 10 * d ≤ (k j : ℝ))
    (hbudget : (1 - q) ^ Fintype.card J ≤ 1 / 10)
    (hdisj : (Set.univ : Set J).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v j) (S j))) :
    9 / 10 ≤
      (SimpleGraph.binomialRandom V p).real
        (graphSomeDegreeAtLeastEvent (V := V) (10 * d)) :=
  graphSomeDegreeAtLeast_probability_ge_nine_tenths_of_disjoint_star_exact_count_witnesses
    (V := V) (J := J) p (L := 10 * d) (q := q) v S k
    hvS hprob hcard hbudget hdisj

/-- Concrete `G(n,p)` exact-count star-block form for HDP Exercise 2.4.5 at
the very-sparse lower scale `log n / log log n`. -/
theorem very_sparse_graphs_far_from_regular_probability_ge_nine_tenths_of_disjoint_star_exact_count_witnesses
    (p : unitInterval) {A q : ℝ} (v : J → V) (S : J → Finset V) (k : J → ℕ)
    (hvS : ∀ j, v j ∉ S j)
    (hprob : ∀ j,
      q ≤ (Nat.choose (S j).card (k j) : ℝ) *
        (unitInterval.toNNReal p : ℝ) ^ (k j) *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ) ^
            ((S j).card - k j))
    (hcard : ∀ j,
      A * Real.log (Fintype.card V : ℝ) /
          Real.log (Real.log (Fintype.card V : ℝ))
        ≤ (k j : ℝ))
    (hbudget : (1 - q) ^ Fintype.card J ≤ 1 / 10)
    (hdisj : (Set.univ : Set J).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v j) (S j))) :
    9 / 10 ≤
      (SimpleGraph.binomialRandom V p).real
        (graphSomeDegreeAtLeastEvent (V := V)
          (A * Real.log (Fintype.card V : ℝ) /
            Real.log (Real.log (Fintype.card V : ℝ)))) :=
  graphSomeDegreeAtLeast_probability_ge_nine_tenths_of_disjoint_star_exact_count_witnesses
    (V := V) (J := J) p
    (L := A * Real.log (Fintype.card V : ℝ) /
      Real.log (Real.log (Fintype.card V : ℝ)))
    (q := q) v S k hvS hprob hcard hbudget hdisj

end StarLowerWitnesses

section FinThirdStarBlocks

/-- Embedding of the first third of `Fin n` into `Fin n`. These vertices serve
as independent star centers in the corrected proofs of Exercises 2.4.4 and
2.4.5. -/
def finFirstThirdEmbedding (n : ℕ) : Fin (n / 3) ↪ Fin n where
  toFun j :=
    ⟨j.1, lt_of_lt_of_le j.2 (Nat.div_le_self n 3)⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) h

/-- The center vertex attached to a first-third index. -/
def finFirstThirdCenter (n : ℕ) (j : Fin (n / 3)) : Fin n :=
  finFirstThirdEmbedding n j

/-- Embedding of another block of `n / 3` vertices near the end of `Fin n`.
This block is disjoint from the first-third centers. -/
def finLastThirdEmbedding (n : ℕ) : Fin (n / 3) ↪ Fin n where
  toFun j :=
    ⟨n - n / 3 + j.1, by
      have hj : j.1 < n / 3 := j.2
      omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hval := congrArg Fin.val h
    simp only at hval
    omega

/-- The common leaf block used by the corrected lower-bound proofs. -/
def finLastThirdVertexSet (n : ℕ) : Finset (Fin n) :=
  Finset.univ.map (finLastThirdEmbedding n)

@[simp]
lemma finLastThirdVertexSet_card (n : ℕ) :
    (finLastThirdVertexSet n).card = n / 3 := by
  simp [finLastThirdVertexSet]

lemma finFirstThirdCenter_not_mem_finLastThirdVertexSet
    (n : ℕ) (j : Fin (n / 3)) :
    finFirstThirdCenter n j ∉ finLastThirdVertexSet n := by
  classical
  intro hjmem
  rcases Finset.mem_map.mp hjmem with ⟨b, _hb, hb_eq⟩
  have hval := congrArg Fin.val hb_eq
  have hthree : (n / 3) * 3 ≤ n := Nat.div_mul_le_self n 3
  simp [finFirstThirdCenter, finFirstThirdEmbedding,
    finLastThirdEmbedding] at hval
  omega

/-- The first-third centers with the common last-third leaf block give
pairwise disjoint unordered-edge star blocks. -/
lemma finThirdStarEdgeFinset_pairwiseDisjoint (n : ℕ) :
    (Set.univ : Set (Fin (n / 3))).PairwiseDisjoint
      (fun j =>
        graphStarEdgeFinset
          (finFirstThirdCenter n j) (finLastThirdVertexSet n)) := by
  classical
  intro i _hi j _hj hij
  change Disjoint
    (graphStarEdgeFinset (finFirstThirdCenter n i) (finLastThirdVertexSet n))
    (graphStarEdgeFinset (finFirstThirdCenter n j) (finLastThirdVertexSet n))
  rw [Finset.disjoint_left]
  intro e hei hej
  rcases Finset.mem_map.mp hei with ⟨x, hx, rfl⟩
  rcases Finset.mem_map.mp hej with ⟨y, hy, hxy⟩
  change s(finFirstThirdCenter n j, y) =
    s(finFirstThirdCenter n i, x) at hxy
  rcases (Sym2.eq_iff.mp hxy) with hsame | hswap
  · exact hij (((finFirstThirdEmbedding n).injective hsame.1).symm)
  · exact finFirstThirdCenter_not_mem_finLastThirdVertexSet n j
      (by simpa [hswap.1] using hx)

/-- Embedding of the vertices after the first third of `Fin n`. This is the
`B` block in the corrected proofs of Exercises 2.4.4 and 2.4.5. -/
def finAfterFirstThirdEmbedding (n : ℕ) : Fin (n - n / 3) ↪ Fin n where
  toFun j :=
    ⟨n / 3 + j.1, by
      have hj : j.1 < n - n / 3 := j.2
      omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hval := congrArg Fin.val h
    simp only at hval
    omega

/-- The leaf block `B` obtained by deleting the first-third centers. -/
def finAfterFirstThirdVertexSet (n : ℕ) : Finset (Fin n) :=
  Finset.univ.map (finAfterFirstThirdEmbedding n)

@[simp]
lemma finAfterFirstThirdVertexSet_card (n : ℕ) :
    (finAfterFirstThirdVertexSet n).card = n - n / 3 := by
  simp [finAfterFirstThirdVertexSet]

lemma finFirstThirdCenter_not_mem_finAfterFirstThirdVertexSet
    (n : ℕ) (j : Fin (n / 3)) :
    finFirstThirdCenter n j ∉ finAfterFirstThirdVertexSet n := by
  classical
  intro hjmem
  rcases Finset.mem_map.mp hjmem with ⟨b, _hb, hb_eq⟩
  have hval := congrArg Fin.val hb_eq
  simp [finFirstThirdCenter, finFirstThirdEmbedding,
    finAfterFirstThirdEmbedding] at hval
  omega

/-- The first-third centers and after-first-third leaves give disjoint star
edge blocks. -/
lemma finAfterFirstThirdStarEdgeFinset_pairwiseDisjoint (n : ℕ) :
    (Set.univ : Set (Fin (n / 3))).PairwiseDisjoint
      (fun j =>
        graphStarEdgeFinset
          (finFirstThirdCenter n j) (finAfterFirstThirdVertexSet n)) := by
  classical
  intro i _hi j _hj hij
  change Disjoint
    (graphStarEdgeFinset
      (finFirstThirdCenter n i) (finAfterFirstThirdVertexSet n))
    (graphStarEdgeFinset
      (finFirstThirdCenter n j) (finAfterFirstThirdVertexSet n))
  rw [Finset.disjoint_left]
  intro e hei hej
  rcases Finset.mem_map.mp hei with ⟨x, hx, rfl⟩
  rcases Finset.mem_map.mp hej with ⟨y, hy, hxy⟩
  change s(finFirstThirdCenter n j, y) =
    s(finFirstThirdCenter n i, x) at hxy
  rcases (Sym2.eq_iff.mp hxy) with hsame | hswap
  · exact hij (((finFirstThirdEmbedding n).injective hsame.1).symm)
  · exact finFirstThirdCenter_not_mem_finAfterFirstThirdVertexSet n j
      (by simpa [hswap.1] using hx)

lemma fin_third_card_linear_eventually
    {α : Type*} {l : Filter α} {n : α → ℕ}
    (hn : Tendsto (fun a => (n a : ℝ)) l atTop) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ a in l, c * (Fintype.card (Fin (n a)) : ℝ) ≤
        (Fintype.card (Fin (n a / 3)) : ℝ) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  filter_upwards [hn.eventually_ge_atTop (6 : ℝ)] with a ha
  have hnat : 6 ≤ n a := by exact_mod_cast ha
  have hle_nat : n a ≤ 4 * (n a / 3) := by omega
  have hle : (n a : ℝ) ≤ 4 * ((n a / 3 : ℕ) : ℝ) := by
    exact_mod_cast hle_nat
  simp only [Fintype.card_fin]
  nlinarith

end FinThirdStarBlocks

section DenseGraphs

variable {V : Type*} [Fintype V] [MeasurableSpace (SimpleGraph V)]
variable {μ : Measure (SimpleGraph V)}

/-- The book's displayed per-vertex bound in the proof of Proposition 2.4.1:
`2 exp(-c d)`. -/
def denseGraphBookVertexTailBound (c d : ℝ) : ℝ :=
  2 * Real.exp (-c * d)

/-- The explicit bound supplied by this library's Chernoff small-deviation
constant: `2 exp(-(1/4) d ε²)`. -/
def chernoffSmallDeviationVertexTailBound (d ε : ℝ) : ℝ :=
  2 * Real.exp (-(1 / 4 : ℝ) * d * ε ^ 2)

/-- HDP Proposition 2.4.1, finite quantitative form: if every vertex satisfies
the displayed Chernoff tail `2 exp(-c d)` and the union-bound expression is at
most `0.1`, then the probability of a vertex outside `[0.9d, 1.1d]` is at most
`0.1`. -/
theorem dense_graphs_are_almost_regular_book_bound
    {c d : ℝ}
    (htail : ∀ v,
      μ.real (graphDegreeDeviationEvent (V := V) d (1 / 10) v)
        ≤ denseGraphBookVertexTailBound c d)
    (hcard :
      (Fintype.card V : ℝ) * denseGraphBookVertexTailBound c d ≤ 1 / 10) :
    μ.real (graphSomeDegreeDeviationEvent (V := V) d (1 / 10))
      ≤ 1 / 10 := by
  calc
    μ.real (graphSomeDegreeDeviationEvent (V := V) d (1 / 10))
        ≤ (Fintype.card V : ℝ) * denseGraphBookVertexTailBound c d :=
      graphSomeDegreeDeviation_probability_le_of_forall
        (μ := μ) (d := d) (ε := 1 / 10)
        (q := denseGraphBookVertexTailBound c d) htail
    _ ≤ 1 / 10 := hcard

/-- Proposition 2.4.1 with the book's logarithmic growth condition made
quantitative: if `d ≥ log(20n)/c`, then the union-bound term
`n · 2 exp(-cd)` is at most `0.1`. -/
theorem dense_graphs_are_almost_regular_book_bound_of_log_card
    {c d : ℝ}
    (hc : 0 < c)
    (hcard_pos : 0 < Fintype.card V)
    (hd : Real.log (20 * (Fintype.card V : ℝ)) / c ≤ d)
    (htail : ∀ v,
      μ.real (graphDegreeDeviationEvent (V := V) d (1 / 10) v)
        ≤ denseGraphBookVertexTailBound c d) :
    μ.real (graphSomeDegreeDeviationEvent (V := V) d (1 / 10))
      ≤ 1 / 10 := by
  classical
  let n : ℝ := Fintype.card V
  have hn_pos : 0 < n := by
    dsimp [n]
    exact_mod_cast hcard_pos
  have htwenty_n_pos : 0 < 20 * n := by positivity
  have hlog_le : Real.log (20 * n) ≤ c * d := by
    rw [div_le_iff₀ hc] at hd
    simpa [n, mul_comm] using hd
  have hexp_le :
      Real.exp (-c * d) ≤ 1 / (20 * n) := by
    calc
      Real.exp (-c * d)
          ≤ Real.exp (-Real.log (20 * n)) := by
        rw [Real.exp_le_exp]
        linarith
      _ = 1 / (20 * n) := by
        rw [Real.exp_neg, Real.exp_log htwenty_n_pos]
        ring
  refine dense_graphs_are_almost_regular_book_bound
    (μ := μ) (V := V) (c := c) (d := d) htail ?_
  calc
    (Fintype.card V : ℝ) * denseGraphBookVertexTailBound c d
        = n * (2 * Real.exp (-c * d)) := by
      simp [n, denseGraphBookVertexTailBound]
    _ ≤ n * (2 * (1 / (20 * n))) := by
      gcongr
    _ = 1 / 10 := by
      field_simp [ne_of_gt hn_pos]
      norm_num

/-- Proposition 2.4.1 with the explicit small-deviation Chernoff constant used
elsewhere in this library. -/
theorem dense_graphs_are_almost_regular_chernoff_bound
    {d : ℝ}
    (htail : ∀ v,
      μ.real (graphDegreeDeviationEvent (V := V) d (1 / 10) v)
        ≤ chernoffSmallDeviationVertexTailBound d (1 / 10))
    (hcard :
      (Fintype.card V : ℝ) * chernoffSmallDeviationVertexTailBound d (1 / 10)
        ≤ 1 / 10) :
    μ.real (graphSomeDegreeDeviationEvent (V := V) d (1 / 10))
      ≤ 1 / 10 := by
  calc
    μ.real (graphSomeDegreeDeviationEvent (V := V) d (1 / 10))
        ≤ (Fintype.card V : ℝ)
            * chernoffSmallDeviationVertexTailBound d (1 / 10) :=
      graphSomeDegreeDeviation_probability_le_of_forall
        (μ := μ) (d := d) (ε := 1 / 10)
        (q := chernoffSmallDeviationVertexTailBound d (1 / 10)) htail
    _ ≤ 1 / 10 := hcard

/-- HDP Proposition 2.4.1 in the displayed probability form: under the
book-tail and logarithmic union-budget hypotheses, the all-degrees-good event
has probability at least `0.9`. -/
theorem dense_graphs_are_almost_regular_probability_ge_nine_tenths
    [IsProbabilityMeasure μ] {c d : ℝ}
    (hmeas :
      MeasurableSet
        (graphSomeDegreeDeviationEvent (V := V) d (1 / 10)))
    (htail : ∀ v,
      μ.real (graphDegreeDeviationEvent (V := V) d (1 / 10) v)
        ≤ denseGraphBookVertexTailBound c d)
    (hcard :
      (Fintype.card V : ℝ) * denseGraphBookVertexTailBound c d ≤ 1 / 10) :
    9 / 10 ≤ μ.real (graphAllDegreesWithinEvent (V := V) d (1 / 10)) := by
  have hbad :
      μ.real (graphSomeDegreeDeviationEvent (V := V) d (1 / 10))
        ≤ 1 / 10 :=
    dense_graphs_are_almost_regular_book_bound
      (μ := μ) (V := V) (c := c) (d := d) htail hcard
  have hgood :=
    graphAllDegreesWithin_probability_ge_one_sub
      (μ := μ) (V := V) (d := d) (ε := 1 / 10)
      (δ := 1 / 10) hmeas hbad
  norm_num at hgood ⊢
  exact hgood

/-- Proposition 2.4.1 in probability form with the logarithmic condition
`d ≥ log(20n)/c` made explicit. -/
theorem dense_graphs_are_almost_regular_probability_ge_nine_tenths_of_log_card
    [IsProbabilityMeasure μ] {c d : ℝ}
    (hmeas :
      MeasurableSet
        (graphSomeDegreeDeviationEvent (V := V) d (1 / 10)))
    (hc : 0 < c)
    (hcard_pos : 0 < Fintype.card V)
    (hd : Real.log (20 * (Fintype.card V : ℝ)) / c ≤ d)
    (htail : ∀ v,
      μ.real (graphDegreeDeviationEvent (V := V) d (1 / 10) v)
        ≤ denseGraphBookVertexTailBound c d) :
    9 / 10 ≤ μ.real (graphAllDegreesWithinEvent (V := V) d (1 / 10)) := by
  have hbad :
      μ.real (graphSomeDegreeDeviationEvent (V := V) d (1 / 10))
        ≤ 1 / 10 :=
    dense_graphs_are_almost_regular_book_bound_of_log_card
      (μ := μ) (V := V) (c := c) (d := d)
      hc hcard_pos hd htail
  have hgood :=
    graphAllDegreesWithin_probability_ge_one_sub
      (μ := μ) (V := V) (d := d) (ε := 1 / 10)
      (δ := 1 / 10) hmeas hbad
  norm_num at hgood ⊢
  exact hgood

end DenseGraphs

section Asymptotic

variable {α : Type*} {l : Filter α}
variable {V : α → Type*}
variable {J : α → Type*}
variable [∀ n, Fintype (V n)]
variable [∀ n, Fintype (J n)]
variable [∀ n, MeasurableSpace (SimpleGraph (V n))]

/-- Asymptotic form of Proposition 2.4.1: once the union-bound expression tends
to zero, the bad-degree probability tends to zero. The hypothesis `htail` is
the per-vertex Chernoff line in the book proof. -/
theorem graphSomeDegreeDeviation_probability_tendsto_zero
    (μ : ∀ n, Measure (SimpleGraph (V n))) (d ε q : α → ℝ)
    (htail : ∀ n v,
      (μ n).real (graphDegreeDeviationEvent (V := V n) (d n) (ε n) v) ≤ q n)
    (hq :
      Tendsto (fun n => (Fintype.card (V n) : ℝ) * q n) l (𝓝 0)) :
    Tendsto
      (fun n =>
        (μ n).real
          (graphSomeDegreeDeviationEvent (V := V n) (d n) (ε n)))
      l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _n => (0 : ℝ))
    (h := fun n => (Fintype.card (V n) : ℝ) * q n)
    tendsto_const_nhds hq ?_ ?_
  · intro n
    exact MeasureTheory.measureReal_nonneg
  · intro n
    exact graphSomeDegreeDeviation_probability_le_of_forall
      (μ := μ n) (d := d n) (ε := ε n) (q := q n) (htail n)

/-- Asymptotic union-bound form for maximum-degree upper bounds, the common
core of Exercises 2.4.2 and 2.4.3. -/
theorem graphSomeDegreeAtLeast_probability_tendsto_zero
    (μ : ∀ n, Measure (SimpleGraph (V n))) (L q : α → ℝ)
    (htail : ∀ n v,
      (μ n).real (graphDegreeAtLeastEvent (V := V n) (L n) v) ≤ q n)
    (hq :
      Tendsto (fun n => (Fintype.card (V n) : ℝ) * q n) l (𝓝 0)) :
    Tendsto
      (fun n =>
        (μ n).real (graphSomeDegreeAtLeastEvent (V := V n) (L n)))
      l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _n => (0 : ℝ))
    (h := fun n => (Fintype.card (V n) : ℝ) * q n)
    tendsto_const_nhds hq ?_ ?_
  · intro n
    exact MeasureTheory.measureReal_nonneg
  · intro n
    exact graphSomeDegreeAtLeast_probability_le_of_forall
      (μ := μ n) (L := L n) (q := q n) (htail n)

omit [∀ n, Fintype (V n)] [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- Product-budget discharge for independent witness lower bounds: if the
number of witnesses times a uniform witness probability tends to infinity, then
the probability that all witnesses fail tends to zero. -/
theorem one_sub_pow_card_tendsto_zero_of_card_mul_tendsto_atTop
    (q : α → ℝ)
    (hq0 : ∀ᶠ n in l, 0 ≤ q n)
    (hq1 : ∀ᶠ n in l, q n ≤ 1)
    (hmass :
      Tendsto (fun n => (Fintype.card (J n) : ℝ) * q n) l atTop) :
    Tendsto (fun n => (1 - q n) ^ Fintype.card (J n)) l (𝓝 0) := by
  have hone_sub_le_exp_neg : ∀ u : ℝ, 1 - u ≤ Real.exp (-u) := by
    intro u
    have h := Real.add_one_le_exp (-u)
    linarith
  have hexp_tendsto :
      Tendsto
        (fun n => Real.exp (-((Fintype.card (J n) : ℝ) * q n)))
        l (𝓝 0) := by
    have hneg :
        Tendsto
          (fun n => -((Fintype.card (J n) : ℝ) * q n)) l atBot := by
      simpa only [neg_mul, one_mul] using
        hmass.const_mul_atTop_of_neg (show (-1 : ℝ) < 0 by norm_num)
    exact Real.tendsto_exp_atBot.comp hneg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hexp_tendsto ?_ ?_
  · filter_upwards [hq1] with n hn1
    exact pow_nonneg (by linarith) _
  · filter_upwards [hq0, hq1] with n hn0 hn1
    have hbase_nonneg : 0 ≤ 1 - q n := by linarith
    have hbase_le : 1 - q n ≤ Real.exp (-(q n)) :=
      hone_sub_le_exp_neg (q n)
    calc
      (1 - q n) ^ Fintype.card (J n)
          ≤ (Real.exp (-(q n))) ^ Fintype.card (J n) :=
            pow_le_pow_left₀ hbase_nonneg hbase_le _
      _ = Real.exp (-((Fintype.card (J n) : ℝ) * q n)) := by
            rw [← Real.exp_nat_mul]
            ring_nf

omit [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- If the number of independent witnesses is linear in the graph size, then
a per-witness lower bound of order `exp (-(1/2) log |V_n|)` has divergent
total mass. This is the reusable product-budget discharge for the lower-bound
exercises. -/
theorem card_mul_exp_neg_half_log_card_tendsto_atTop_of_linear_card
    (hcard_tendsto :
      Tendsto (fun n => (Fintype.card (V n) : ℝ)) l atTop)
    (hlinear : ∃ a : ℝ, 0 < a ∧
      ∀ᶠ n in l,
        a * (Fintype.card (V n) : ℝ) ≤ (Fintype.card (J n) : ℝ)) :
    Tendsto
      (fun n =>
        (Fintype.card (J n) : ℝ) *
          Real.exp (-((1 / 2 : ℝ) *
            Real.log (Fintype.card (V n) : ℝ)))) l atTop := by
  rcases hlinear with ⟨a, ha, hlinear⟩
  let N : α → ℝ := fun n => (Fintype.card (V n) : ℝ)
  let M : α → ℝ := fun n => (Fintype.card (J n) : ℝ)
  have hNge1 : ∀ᶠ n in l, (1 : ℝ) ≤ N n :=
    hcard_tendsto.eventually_ge_atTop 1
  have hlower : ∀ᶠ n in l,
      a * Real.exp ((1 / 2 : ℝ) * Real.log (N n)) ≤
        M n * Real.exp (-((1 / 2 : ℝ) * Real.log (N n))) := by
    filter_upwards [hNge1, hlinear] with n hN1 hM
    have hNpos : 0 < N n := by linarith
    have hNexp :
        N n * Real.exp (-((1 / 2 : ℝ) * Real.log (N n))) =
          Real.exp ((1 / 2 : ℝ) * Real.log (N n)) := by
      calc
        N n * Real.exp (-((1 / 2 : ℝ) * Real.log (N n)))
            =
          Real.exp (Real.log (N n)) *
            Real.exp (-((1 / 2 : ℝ) * Real.log (N n))) := by
              rw [Real.exp_log hNpos]
        _ = Real.exp ((1 / 2 : ℝ) * Real.log (N n)) := by
              rw [← Real.exp_add]
              congr 1
              ring
    calc
      a * Real.exp ((1 / 2 : ℝ) * Real.log (N n))
          =
        a * (N n *
          Real.exp (-((1 / 2 : ℝ) * Real.log (N n)))) := by
            rw [hNexp]
      _ = (a * N n) *
            Real.exp (-((1 / 2 : ℝ) * Real.log (N n))) := by ring
      _ ≤ M n * Real.exp (-((1 / 2 : ℝ) * Real.log (N n))) := by
            exact mul_le_mul_of_nonneg_right hM (Real.exp_nonneg _)
  have hlogtop : Tendsto (fun n => Real.log (N n)) l atTop :=
    Real.tendsto_log_atTop.comp hcard_tendsto
  have hhalf_top :
      Tendsto (fun n => (1 / 2 : ℝ) * Real.log (N n)) l atTop :=
    hlogtop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hexp_top :
      Tendsto (fun n => Real.exp ((1 / 2 : ℝ) * Real.log (N n)))
        l atTop :=
    Real.tendsto_exp_atTop.comp hhalf_top
  have hleft_top :
      Tendsto (fun n => a *
        Real.exp ((1 / 2 : ℝ) * Real.log (N n))) l atTop :=
    hexp_top.const_mul_atTop ha
  simpa [N, M] using tendsto_atTop_mono' l hlower hleft_top

omit [∀ n, Fintype (V n)] in
/-- Asymptotic independent-witness lower bound for maximum degrees: if the
probability that all independent witnesses fail tends to zero, then the
probability of seeing some vertex above the threshold tends to one. -/
theorem graphSomeDegreeAtLeast_probability_tendsto_one_of_independent_witnesses
    (μ : ∀ n, Measure (SimpleGraph (V n)))
    [∀ n, IsProbabilityMeasure (μ n)]
    (L q : α → ℝ)
    (B : ∀ n, J n → Set (SimpleGraph (V n)))
    (hBmeas : ∀ n j, MeasurableSet (B n j))
    (hindep : ∀ n, iIndepSet (B n) (μ n))
    (hprob : ∀ n j, q n ≤ (μ n).real (B n j))
    (hbudget :
      Tendsto
        (fun n => (1 - q n) ^ Fintype.card (J n)) l (𝓝 0))
    (hforces : ∀ n j,
      B n j ⊆ graphSomeDegreeAtLeastEvent (V := V n) (L n)) :
    Tendsto
      (fun n =>
        (μ n).real (graphSomeDegreeAtLeastEvent (V := V n) (L n)))
      l (𝓝 1) := by
  have hlower_tendsto :
      Tendsto
        (fun n => 1 - (1 - q n) ^ Fintype.card (J n)) l (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hbudget)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => 1 - (1 - q n) ^ Fintype.card (J n))
    (h := fun _n => (1 : ℝ))
    hlower_tendsto tendsto_const_nhds ?_ ?_
  · intro n
    exact
      graphSomeDegreeAtLeast_probability_ge_one_sub_pow_one_sub_of_independent_witnesses
        (μ := μ n) (V := V n) (J := J n) (L := L n) (q := q n)
        (hBmeas n) (hindep n) (hprob n) (hforces n)
  · intro n
    exact measureReal_le_one

omit [∀ n, Fintype (V n)] in
/-- HDP Exercise 2.4.4, asymptotic independent-witness form: once the modified
independent degree witnesses from the hint have a vanishing all-fail
probability, the event that some vertex has degree at least `10d` holds with
probability tending to one. -/
theorem sparse_graphs_not_almost_regular_probability_tendsto_one_of_independent_witnesses
    (μ : ∀ n, Measure (SimpleGraph (V n)))
    [∀ n, IsProbabilityMeasure (μ n)]
    (d q : α → ℝ)
    (B : ∀ n, J n → Set (SimpleGraph (V n)))
    (hBmeas : ∀ n j, MeasurableSet (B n j))
    (hindep : ∀ n, iIndepSet (B n) (μ n))
    (hprob : ∀ n j, q n ≤ (μ n).real (B n j))
    (hbudget :
      Tendsto
        (fun n => (1 - q n) ^ Fintype.card (J n)) l (𝓝 0))
    (hforces : ∀ n j,
      B n j ⊆ graphSomeDegreeAtLeastEvent (V := V n) (10 * d n)) :
    Tendsto
      (fun n =>
        (μ n).real
          (graphSomeDegreeAtLeastEvent (V := V n) (10 * d n)))
      l (𝓝 1) :=
  graphSomeDegreeAtLeast_probability_tendsto_one_of_independent_witnesses
    (V := V) (J := J) (l := l) (μ := μ)
    (L := fun n => 10 * d n) (q := q) (B := B)
    hBmeas hindep hprob hbudget hforces

/-- HDP Exercise 2.4.5, asymptotic independent-witness form for the matching
very-sparse lower scale `log n / log log n`. -/
theorem very_sparse_graphs_far_from_regular_probability_tendsto_one_of_independent_witnesses
    (μ : ∀ n, Measure (SimpleGraph (V n)))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A q : α → ℝ)
    (B : ∀ n, J n → Set (SimpleGraph (V n)))
    (hBmeas : ∀ n j, MeasurableSet (B n j))
    (hindep : ∀ n, iIndepSet (B n) (μ n))
    (hprob : ∀ n j, q n ≤ (μ n).real (B n j))
    (hbudget :
      Tendsto
        (fun n => (1 - q n) ^ Fintype.card (J n)) l (𝓝 0))
    (hforces : ∀ n j,
      B n j ⊆ graphSomeDegreeAtLeastEvent (V := V n)
        (A n * Real.log (Fintype.card (V n) : ℝ) /
          Real.log (Real.log (Fintype.card (V n) : ℝ)))) :
    Tendsto
      (fun n =>
        (μ n).real
          (graphSomeDegreeAtLeastEvent (V := V n)
            (A n * Real.log (Fintype.card (V n) : ℝ) /
              Real.log (Real.log (Fintype.card (V n) : ℝ)))))
      l (𝓝 1) :=
  graphSomeDegreeAtLeast_probability_tendsto_one_of_independent_witnesses
    (V := V) (J := J) (l := l) (μ := μ)
    (L := fun n =>
      A n * Real.log (Fintype.card (V n) : ℝ) /
        Real.log (Real.log (Fintype.card (V n) : ℝ)))
    (q := q) (B := B) hBmeas hindep hprob hbudget hforces

section ExactCountStarAsymptotic

variable [∀ n, Countable (V n)]
variable [∀ n, DecidableEq (Sym2 (V n))]

omit [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- Eventual-probability variant of the exact-count star-block amplifier. This
is useful for asymptotic lower-tail estimates that only hold for all sufficiently
large graph sizes. -/
theorem graphSomeDegreeAtLeast_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_eventually
    (p : α → unitInterval) (L q : α → ℝ)
    (v : ∀ n, J n → V n) (S : ∀ n, J n → Finset (V n))
    (k : ∀ n, J n → ℕ)
    (hvS : ∀ n j, v n j ∉ S n j)
    (hprob : ∀ᶠ n in l, ∀ j,
      q n ≤ (Nat.choose (S n j).card (k n j) : ℝ) *
        (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
          (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
            ((S n j).card - k n j))
    (hbudget :
      Tendsto
        (fun n => (1 - q n) ^ Fintype.card (J n)) l (𝓝 0))
    (hcard : ∀ᶠ n in l, ∀ j, L n ≤ (k n j : ℝ))
    (hdisj : ∀ n, (Set.univ : Set (J n)).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v n j) (S n j))) :
    Tendsto
      (fun n =>
        (SimpleGraph.binomialRandom (V n) (p n)).real
          (graphSomeDegreeAtLeastEvent (V := V n) (L n)))
      l (𝓝 1) := by
  have hlower_tendsto :
      Tendsto
        (fun n => 1 - (1 - q n) ^ Fintype.card (J n)) l (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hbudget)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower_tendsto tendsto_const_nhds ?_ ?_
  · filter_upwards [hprob, hcard] with n hnprob hncard
    exact
      graphSomeDegreeAtLeast_probability_ge_one_sub_pow_one_sub_of_disjoint_star_exact_count_witnesses
        (V := V n) (J := J n) (p := p n) (L := L n) (q := q n)
        (v := v n) (S := S n) (k := k n)
        (hvS n) hnprob hncard (hdisj n)
  · exact Eventually.of_forall fun _n => measureReal_le_one

omit [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- Exact-count star-block lower bound with the product budget discharged from
a half-log lower bound on each witness probability and linearly many disjoint
witnesses. -/
theorem graphSomeDegreeAtLeast_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_half_log
    (p : α → unitInterval) (L : α → ℝ)
    (v : ∀ n, J n → V n) (S : ∀ n, J n → Finset (V n))
    (k : ∀ n, J n → ℕ)
    (hvS : ∀ n j, v n j ∉ S n j)
    (hcard_tendsto :
      Tendsto (fun n => (Fintype.card (V n) : ℝ)) l atTop)
    (hlinear : ∃ a : ℝ, 0 < a ∧
      ∀ᶠ n in l,
        a * (Fintype.card (V n) : ℝ) ≤ (Fintype.card (J n) : ℝ))
    (hprob : ∀ᶠ n in l, ∀ j,
      Real.exp (-((1 / 2 : ℝ) *
          Real.log (Fintype.card (V n) : ℝ))) ≤
        (Nat.choose (S n j).card (k n j) : ℝ) *
          (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
            (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
              ((S n j).card - k n j))
    (hcard : ∀ᶠ n in l, ∀ j, L n ≤ (k n j : ℝ))
    (hdisj : ∀ n, (Set.univ : Set (J n)).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v n j) (S n j))) :
    Tendsto
      (fun n =>
        (SimpleGraph.binomialRandom (V n) (p n)).real
          (graphSomeDegreeAtLeastEvent (V := V n) (L n)))
      l (𝓝 1) := by
  let q : α → ℝ := fun n =>
    Real.exp (-((1 / 2 : ℝ) *
      Real.log (Fintype.card (V n) : ℝ)))
  have hmass : Tendsto (fun n => (Fintype.card (J n) : ℝ) * q n) l atTop := by
    simpa [q] using
      card_mul_exp_neg_half_log_card_tendsto_atTop_of_linear_card
        (V := V) (J := J) (l := l) hcard_tendsto hlinear
  have hq0 : ∀ᶠ n in l, 0 ≤ q n :=
    Eventually.of_forall fun _n => Real.exp_nonneg _
  have hq1 : ∀ᶠ n in l, q n ≤ 1 := by
    have hNge1 :
        ∀ᶠ n in l, (1 : ℝ) ≤ (Fintype.card (V n) : ℝ) :=
      hcard_tendsto.eventually_ge_atTop 1
    filter_upwards [hNge1] with n hN1
    have hlog_nonneg :
        0 ≤ Real.log (Fintype.card (V n) : ℝ) :=
      Real.log_nonneg hN1
    dsimp [q]
    calc
      Real.exp (-((1 / 2 : ℝ) *
          Real.log (Fintype.card (V n) : ℝ))) ≤ Real.exp 0 := by
        rw [Real.exp_le_exp]
        nlinarith
      _ = 1 := Real.exp_zero
  have hbudget :
      Tendsto (fun n => (1 - q n) ^ Fintype.card (J n)) l (𝓝 0) :=
    one_sub_pow_card_tendsto_zero_of_card_mul_tendsto_atTop
      (J := J) (l := l) (q := q) hq0 hq1 hmass
  exact
    graphSomeDegreeAtLeast_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_eventually
      (V := V) (J := J) (l := l) (p := p) (L := L) (q := q)
      (v := v) (S := S) (k := k) hvS
      (by simpa [q] using hprob) hbudget hcard hdisj

omit [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- Constant-factor variant of the half-log exact-count amplifier. A fixed
positive constant times `exp (-(1/2) log |V_n|)` still gives divergent total
witness mass when the number of disjoint witnesses is linear in `|V_n|`. -/
theorem graphSomeDegreeAtLeast_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_const_half_log
    (p : α → unitInterval) (L : α → ℝ) {c : ℝ}
    (v : ∀ n, J n → V n) (S : ∀ n, J n → Finset (V n))
    (k : ∀ n, J n → ℕ)
    (hvS : ∀ n j, v n j ∉ S n j)
    (hc : 0 < c)
    (hcard_tendsto :
      Tendsto (fun n => (Fintype.card (V n) : ℝ)) l atTop)
    (hlinear : ∃ a : ℝ, 0 < a ∧
      ∀ᶠ n in l,
        a * (Fintype.card (V n) : ℝ) ≤ (Fintype.card (J n) : ℝ))
    (hprob : ∀ᶠ n in l, ∀ j,
      c * Real.exp (-((1 / 2 : ℝ) *
          Real.log (Fintype.card (V n) : ℝ))) ≤
        (Nat.choose (S n j).card (k n j) : ℝ) *
          (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
            (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
              ((S n j).card - k n j))
    (hcard : ∀ᶠ n in l, ∀ j, L n ≤ (k n j : ℝ))
    (hdisj : ∀ n, (Set.univ : Set (J n)).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v n j) (S n j))) :
    Tendsto
      (fun n =>
        (SimpleGraph.binomialRandom (V n) (p n)).real
          (graphSomeDegreeAtLeastEvent (V := V n) (L n)))
      l (𝓝 1) := by
  let q : α → ℝ := fun n =>
    c * Real.exp (-((1 / 2 : ℝ) *
      Real.log (Fintype.card (V n) : ℝ)))
  have hbase_mass :
      Tendsto
        (fun n =>
          (Fintype.card (J n) : ℝ) *
            Real.exp (-((1 / 2 : ℝ) *
              Real.log (Fintype.card (V n) : ℝ)))) l atTop :=
    card_mul_exp_neg_half_log_card_tendsto_atTop_of_linear_card
      (V := V) (J := J) (l := l) hcard_tendsto hlinear
  have hmass : Tendsto
      (fun n => (Fintype.card (J n) : ℝ) * q n) l atTop := by
    simpa [q, mul_assoc, mul_left_comm, mul_comm] using
      hbase_mass.const_mul_atTop hc
  have hq0 : ∀ᶠ n in l, 0 ≤ q n :=
    Eventually.of_forall fun _n => mul_nonneg hc.le (Real.exp_nonneg _)
  have hlogtop :
      Tendsto (fun n => Real.log (Fintype.card (V n) : ℝ)) l atTop :=
    Real.tendsto_log_atTop.comp hcard_tendsto
  have hhalf_top :
      Tendsto (fun n => (1 / 2 : ℝ) *
        Real.log (Fintype.card (V n) : ℝ)) l atTop :=
    hlogtop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hneg_bot :
      Tendsto (fun n => -((1 / 2 : ℝ) *
        Real.log (Fintype.card (V n) : ℝ))) l atBot := by
    simpa only [neg_mul, one_mul] using
      hhalf_top.const_mul_atTop_of_neg (show (-1 : ℝ) < 0 by norm_num)
  have hbase_zero :
      Tendsto (fun n =>
        Real.exp (-((1 / 2 : ℝ) *
          Real.log (Fintype.card (V n) : ℝ)))) l (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg_bot
  have hq_zero : Tendsto q l (𝓝 0) := by
    simpa [q] using (tendsto_const_nhds.mul hbase_zero)
  have hq1 : ∀ᶠ n in l, q n ≤ 1 := by
    exact (hq_zero.eventually_lt_const zero_lt_one).mono fun _ hn => hn.le
  have hbudget :
      Tendsto (fun n => (1 - q n) ^ Fintype.card (J n)) l (𝓝 0) :=
    one_sub_pow_card_tendsto_zero_of_card_mul_tendsto_atTop
      (J := J) (l := l) (q := q) hq0 hq1 hmass
  exact
    graphSomeDegreeAtLeast_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_eventually
      (V := V) (J := J) (l := l) (p := p) (L := L) (q := q)
      (v := v) (S := S) (k := k) hvS
      (by simpa [q] using hprob) hbudget hcard hdisj

omit [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- Asymptotic `G(n,p)` lower-bound amplifier from disjoint exact-count star
blocks. It is the direct random-graph form of the independent-witness theorem:
the witness probability is the exact binomial mass of each star block, and the
only remaining budget is the all-witnesses-fail product. -/
theorem graphSomeDegreeAtLeast_probability_tendsto_one_of_disjoint_star_exact_count_witnesses
    (p : α → unitInterval) (L q : α → ℝ)
    (v : ∀ n, J n → V n) (S : ∀ n, J n → Finset (V n))
    (k : ∀ n, J n → ℕ)
    (hvS : ∀ n j, v n j ∉ S n j)
    (hprob : ∀ n j,
      q n ≤ (Nat.choose (S n j).card (k n j) : ℝ) *
        (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
          (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
            ((S n j).card - k n j))
    (hbudget :
      Tendsto
        (fun n => (1 - q n) ^ Fintype.card (J n)) l (𝓝 0))
    (hcard : ∀ n j, L n ≤ (k n j : ℝ))
    (hdisj : ∀ n, (Set.univ : Set (J n)).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v n j) (S n j))) :
    Tendsto
      (fun n =>
        (SimpleGraph.binomialRandom (V n) (p n)).real
          (graphSomeDegreeAtLeastEvent (V := V n) (L n)))
      l (𝓝 1) := by
  have hlower_tendsto :
      Tendsto
        (fun n => 1 - (1 - q n) ^ Fintype.card (J n)) l (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hbudget)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => 1 - (1 - q n) ^ Fintype.card (J n))
    (h := fun _n => (1 : ℝ))
    hlower_tendsto tendsto_const_nhds ?_ ?_
  · intro n
    exact
      graphSomeDegreeAtLeast_probability_ge_one_sub_pow_one_sub_of_disjoint_star_exact_count_witnesses
        (V := V n) (J := J n) (p := p n) (L := L n) (q := q n)
        (v := v n) (S := S n) (k := k n)
        (hvS n) (hprob n) (hcard n) (hdisj n)
  · intro n
    exact measureReal_le_one

omit [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- HDP Exercise 2.4.4 in asymptotic exact-count star-block form: once the
explicit binomial star-block mass makes the all-fail product tend to zero, the
probability of a vertex with degree at least `10d` tends to one in `G(n,p)`. -/
theorem sparse_graphs_not_almost_regular_probability_tendsto_one_of_disjoint_star_exact_count_witnesses
    (p : α → unitInterval) (d q : α → ℝ)
    (v : ∀ n, J n → V n) (S : ∀ n, J n → Finset (V n))
    (k : ∀ n, J n → ℕ)
    (hvS : ∀ n j, v n j ∉ S n j)
    (hprob : ∀ n j,
      q n ≤ (Nat.choose (S n j).card (k n j) : ℝ) *
        (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
          (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
            ((S n j).card - k n j))
    (hbudget :
      Tendsto
        (fun n => (1 - q n) ^ Fintype.card (J n)) l (𝓝 0))
    (hcard : ∀ n j, 10 * d n ≤ (k n j : ℝ))
    (hdisj : ∀ n, (Set.univ : Set (J n)).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v n j) (S n j))) :
    Tendsto
      (fun n =>
        (SimpleGraph.binomialRandom (V n) (p n)).real
          (graphSomeDegreeAtLeastEvent (V := V n) (10 * d n)))
      l (𝓝 1) :=
  graphSomeDegreeAtLeast_probability_tendsto_one_of_disjoint_star_exact_count_witnesses
    (V := V) (J := J) (l := l) (p := p)
    (L := fun n => 10 * d n) (q := q)
    (v := v) (S := S) (k := k)
    hvS hprob hbudget hcard hdisj

omit [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- HDP Exercise 2.4.4 with the product budget discharged: if linearly many
disjoint exact-count star witnesses each have probability at least
`exp (-(1/2) log |V_n|)` and force degree at least `10d_n`, then the sparse
lower-bound event occurs with probability tending to one. -/
theorem sparse_graphs_not_almost_regular_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_half_log
    (p : α → unitInterval) (d : α → ℝ)
    (v : ∀ n, J n → V n) (S : ∀ n, J n → Finset (V n))
    (k : ∀ n, J n → ℕ)
    (hvS : ∀ n j, v n j ∉ S n j)
    (hcard_tendsto :
      Tendsto (fun n => (Fintype.card (V n) : ℝ)) l atTop)
    (hlinear : ∃ a : ℝ, 0 < a ∧
      ∀ᶠ n in l,
        a * (Fintype.card (V n) : ℝ) ≤ (Fintype.card (J n) : ℝ))
    (hprob : ∀ᶠ n in l, ∀ j,
      Real.exp (-((1 / 2 : ℝ) *
          Real.log (Fintype.card (V n) : ℝ))) ≤
        (Nat.choose (S n j).card (k n j) : ℝ) *
          (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
            (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
              ((S n j).card - k n j))
    (hcard : ∀ᶠ n in l, ∀ j, 10 * d n ≤ (k n j : ℝ))
    (hdisj : ∀ n, (Set.univ : Set (J n)).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v n j) (S n j))) :
    Tendsto
      (fun n =>
        (SimpleGraph.binomialRandom (V n) (p n)).real
          (graphSomeDegreeAtLeastEvent (V := V n) (10 * d n)))
      l (𝓝 1) :=
  graphSomeDegreeAtLeast_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_half_log
    (V := V) (J := J) (l := l) (p := p)
    (L := fun n => 10 * d n) (v := v) (S := S) (k := k)
    hvS hcard_tendsto hlinear hprob hcard hdisj

omit [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- Sparse lower-bound form with the `d = o(log n)` budget discharged from an
exponential exact-count lower mass. This isolates the analytic budget needed by
Exercise 2.4.4: an eventual lower bound `exp(-C d_n)` for each independent
star block is enough when `d_n = o(log |V_n|)`. -/
theorem sparse_graphs_not_almost_regular_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_of_exp_lower
    (p : α → unitInterval) (d : α → ℝ) {C : ℝ}
    (v : ∀ n, J n → V n) (S : ∀ n, J n → Finset (V n))
    (k : ∀ n, J n → ℕ)
    (hvS : ∀ n j, v n j ∉ S n j)
    (hC : 0 < C)
    (hcard_tendsto :
      Tendsto (fun n => (Fintype.card (V n) : ℝ)) l atTop)
    (hlinear : ∃ a : ℝ, 0 < a ∧
      ∀ᶠ n in l,
        a * (Fintype.card (V n) : ℝ) ≤ (Fintype.card (J n) : ℝ))
    (hd_nonneg : ∀ᶠ n in l, 0 ≤ d n)
    (hd_small :
      d =o[l] fun n => Real.log (Fintype.card (V n) : ℝ))
    (hprob_exp : ∀ᶠ n in l, ∀ j,
      Real.exp (-(C * d n)) ≤
        (Nat.choose (S n j).card (k n j) : ℝ) *
          (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
            (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
              ((S n j).card - k n j))
    (hcard : ∀ᶠ n in l, ∀ j, 10 * d n ≤ (k n j : ℝ))
    (hdisj : ∀ n, (Set.univ : Set (J n)).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v n j) (S n j))) :
    Tendsto
      (fun n =>
        (SimpleGraph.binomialRandom (V n) (p n)).real
          (graphSomeDegreeAtLeastEvent (V := V n) (10 * d n)))
      l (𝓝 1) := by
  have hNge1 :
      ∀ᶠ n in l, (1 : ℝ) ≤ (Fintype.card (V n) : ℝ) :=
    hcard_tendsto.eventually_ge_atTop 1
  have hsmall :
      ∀ᶠ n in l,
        ‖d n‖ ≤ (1 / (2 * C)) *
          ‖Real.log (Fintype.card (V n) : ℝ)‖ :=
    hd_small.def (by positivity : 0 < 1 / (2 * C))
  have hprob_half : ∀ᶠ n in l, ∀ j,
      Real.exp (-((1 / 2 : ℝ) *
          Real.log (Fintype.card (V n) : ℝ))) ≤
        (Nat.choose (S n j).card (k n j) : ℝ) *
          (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
            (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
              ((S n j).card - k n j) := by
    filter_upwards [hNge1, hd_nonneg, hsmall, hprob_exp] with
      n hN1 hd0 hs hnprob j
    have hlog_nonneg :
        0 ≤ Real.log (Fintype.card (V n) : ℝ) :=
      Real.log_nonneg hN1
    have hd_le :
        d n ≤ (1 / (2 * C)) *
          Real.log (Fintype.card (V n) : ℝ) := by
      have hdnorm : ‖d n‖ = d n := by
        rw [Real.norm_eq_abs, abs_of_nonneg hd0]
      have hlognorm :
          ‖Real.log (Fintype.card (V n) : ℝ)‖ =
            Real.log (Fintype.card (V n) : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]
      simpa [hdnorm, hlognorm] using hs
    have hCd :
        C * d n ≤ (1 / 2 : ℝ) *
          Real.log (Fintype.card (V n) : ℝ) := by
      calc
        C * d n ≤
            C * ((1 / (2 * C)) *
              Real.log (Fintype.card (V n) : ℝ)) :=
          mul_le_mul_of_nonneg_left hd_le hC.le
        _ = (1 / 2 : ℝ) *
            Real.log (Fintype.card (V n) : ℝ) := by field_simp [hC.ne']
    calc
      Real.exp (-((1 / 2 : ℝ) *
          Real.log (Fintype.card (V n) : ℝ))) ≤
          Real.exp (-(C * d n)) := by
            rw [Real.exp_le_exp]
            linarith
      _ ≤ (Nat.choose (S n j).card (k n j) : ℝ) *
          (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
            (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
              ((S n j).card - k n j) := hnprob j
  exact
    sparse_graphs_not_almost_regular_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_half_log
      (V := V) (J := J) (l := l) (p := p) (d := d)
      (v := v) (S := S) (k := k) hvS hcard_tendsto hlinear
      hprob_half hcard hdisj

omit [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- HDP Exercise 2.4.5 in asymptotic exact-count star-block form at the
matching `log n / log log n` lower scale. The remaining budget is explicitly
the product of exact binomial star-block failure probabilities. -/
theorem very_sparse_graphs_far_from_regular_probability_tendsto_one_of_disjoint_star_exact_count_witnesses
    (p : α → unitInterval) (A q : α → ℝ)
    (v : ∀ n, J n → V n) (S : ∀ n, J n → Finset (V n))
    (k : ∀ n, J n → ℕ)
    (hvS : ∀ n j, v n j ∉ S n j)
    (hprob : ∀ n j,
      q n ≤ (Nat.choose (S n j).card (k n j) : ℝ) *
        (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
          (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
            ((S n j).card - k n j))
    (hbudget :
      Tendsto
        (fun n => (1 - q n) ^ Fintype.card (J n)) l (𝓝 0))
    (hcard : ∀ n j,
      A n * Real.log (Fintype.card (V n) : ℝ) /
          Real.log (Real.log (Fintype.card (V n) : ℝ))
        ≤ (k n j : ℝ))
    (hdisj : ∀ n, (Set.univ : Set (J n)).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v n j) (S n j))) :
    Tendsto
      (fun n =>
        (SimpleGraph.binomialRandom (V n) (p n)).real
          (graphSomeDegreeAtLeastEvent (V := V n)
            (A n * Real.log (Fintype.card (V n) : ℝ) /
              Real.log (Real.log (Fintype.card (V n) : ℝ)))))
      l (𝓝 1) :=
  graphSomeDegreeAtLeast_probability_tendsto_one_of_disjoint_star_exact_count_witnesses
    (V := V) (J := J) (l := l) (p := p)
    (L := fun n =>
      A n * Real.log (Fintype.card (V n) : ℝ) /
        Real.log (Real.log (Fintype.card (V n) : ℝ)))
    (q := q) (v := v) (S := S) (k := k)
    hvS hprob hbudget hcard hdisj

omit [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- HDP Exercise 2.4.5 with the product budget discharged from a half-log
per-witness exact-count mass lower bound and linearly many disjoint star
blocks. -/
theorem very_sparse_graphs_far_from_regular_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_half_log
    (p : α → unitInterval) (A : α → ℝ)
    (v : ∀ n, J n → V n) (S : ∀ n, J n → Finset (V n))
    (k : ∀ n, J n → ℕ)
    (hvS : ∀ n j, v n j ∉ S n j)
    (hcard_tendsto :
      Tendsto (fun n => (Fintype.card (V n) : ℝ)) l atTop)
    (hlinear : ∃ a : ℝ, 0 < a ∧
      ∀ᶠ n in l,
        a * (Fintype.card (V n) : ℝ) ≤ (Fintype.card (J n) : ℝ))
    (hprob : ∀ᶠ n in l, ∀ j,
      Real.exp (-((1 / 2 : ℝ) *
          Real.log (Fintype.card (V n) : ℝ))) ≤
        (Nat.choose (S n j).card (k n j) : ℝ) *
          (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
            (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
              ((S n j).card - k n j))
    (hcard : ∀ᶠ n in l, ∀ j,
      A n * Real.log (Fintype.card (V n) : ℝ) /
          Real.log (Real.log (Fintype.card (V n) : ℝ))
        ≤ (k n j : ℝ))
    (hdisj : ∀ n, (Set.univ : Set (J n)).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v n j) (S n j))) :
    Tendsto
      (fun n =>
        (SimpleGraph.binomialRandom (V n) (p n)).real
          (graphSomeDegreeAtLeastEvent (V := V n)
            (A n * Real.log (Fintype.card (V n) : ℝ) /
              Real.log (Real.log (Fintype.card (V n) : ℝ)))))
      l (𝓝 1) :=
  graphSomeDegreeAtLeast_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_half_log
    (V := V) (J := J) (l := l) (p := p)
    (L := fun n =>
      A n * Real.log (Fintype.card (V n) : ℝ) /
        Real.log (Real.log (Fintype.card (V n) : ℝ)))
    (v := v) (S := S) (k := k) hvS hcard_tendsto hlinear
    hprob hcard hdisj

omit [∀ n, MeasurableSpace (SimpleGraph (V n))] in
/-- Very-sparse exact-count lower-bound form with the product budget discharged
from a Poisson-scale mass lower bound. If each star-block mass is at least
`exp (-B (k log k + k))` and that exponent is eventually below
`(1/2) log |V_n|`, then the Exercise 2.4.5 lower-bound event holds with
probability tending to one. -/
theorem very_sparse_graphs_far_from_regular_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_of_exp_log_lower
    (p : α → unitInterval) (A : α → ℝ) {B : ℝ}
    (v : ∀ n, J n → V n) (S : ∀ n, J n → Finset (V n))
    (k : ∀ n, J n → ℕ)
    (hvS : ∀ n j, v n j ∉ S n j)
    (hcard_tendsto :
      Tendsto (fun n => (Fintype.card (V n) : ℝ)) l atTop)
    (hlinear : ∃ a : ℝ, 0 < a ∧
      ∀ᶠ n in l,
        a * (Fintype.card (V n) : ℝ) ≤ (Fintype.card (J n) : ℝ))
    (hprob_exp : ∀ᶠ n in l, ∀ j,
      Real.exp (-(B *
          ((k n j : ℝ) * Real.log (k n j : ℝ) + (k n j : ℝ)))) ≤
        (Nat.choose (S n j).card (k n j) : ℝ) *
          (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
            (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
              ((S n j).card - k n j))
    (hscale : ∀ᶠ n in l, ∀ j,
      B * ((k n j : ℝ) * Real.log (k n j : ℝ) + (k n j : ℝ)) ≤
        (1 / 2 : ℝ) * Real.log (Fintype.card (V n) : ℝ))
    (hcard : ∀ᶠ n in l, ∀ j,
      A n * Real.log (Fintype.card (V n) : ℝ) /
          Real.log (Real.log (Fintype.card (V n) : ℝ))
        ≤ (k n j : ℝ))
    (hdisj : ∀ n, (Set.univ : Set (J n)).PairwiseDisjoint
      (fun j => graphStarEdgeFinset (v n j) (S n j))) :
    Tendsto
      (fun n =>
        (SimpleGraph.binomialRandom (V n) (p n)).real
          (graphSomeDegreeAtLeastEvent (V := V n)
            (A n * Real.log (Fintype.card (V n) : ℝ) /
              Real.log (Real.log (Fintype.card (V n) : ℝ)))))
      l (𝓝 1) := by
  have hprob_half : ∀ᶠ n in l, ∀ j,
      Real.exp (-((1 / 2 : ℝ) *
          Real.log (Fintype.card (V n) : ℝ))) ≤
        (Nat.choose (S n j).card (k n j) : ℝ) *
          (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
            (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
              ((S n j).card - k n j) := by
    filter_upwards [hprob_exp, hscale] with n hnprob hnscale j
    calc
      Real.exp (-((1 / 2 : ℝ) *
          Real.log (Fintype.card (V n) : ℝ))) ≤
          Real.exp (-(B *
            ((k n j : ℝ) * Real.log (k n j : ℝ) +
              (k n j : ℝ)))) := by
            rw [Real.exp_le_exp]
            linarith [hnscale j]
      _ ≤ (Nat.choose (S n j).card (k n j) : ℝ) *
          (unitInterval.toNNReal (p n) : ℝ) ^ (k n j) *
            (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ) ^
              ((S n j).card - k n j) := hnprob j
  exact
    very_sparse_graphs_far_from_regular_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_half_log
      (V := V) (J := J) (l := l) (p := p) (A := A)
      (v := v) (S := S) (k := k) hvS hcard_tendsto hlinear
      hprob_half hcard hdisj

end ExactCountStarAsymptotic

section CorrectedExercises

/-- The real scale used to choose the exact-count witnesses in the corrected
Exercise 2.4.5 proof. -/
def verySparseCorrectedWitnessScale (n : ℕ) : ℝ :=
  (1 / 4 : ℝ) * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))

/-- The integer witness count `⌊(1/4) log n / log log n⌋` from the corrected
Exercise 2.4.5 proof. -/
def verySparseCorrectedWitnessCount (n : ℕ) : ℕ :=
  ⌊verySparseCorrectedWitnessScale n⌋₊

/-- The displayed lower-degree scale produced by corrected Exercise 2.4.5. -/
def verySparseCorrectedLowerScale (n : ℕ) : ℝ :=
  (1 / 8 : ℝ) * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))

/-- If the requested degree threshold is eventually nonpositive and the graph
has at least one vertex, the maximum-degree lower event has probability one
eventually. This is the formal trivial branch used in the Exercise 2.4.4
footnote when `10d = 0`. -/
theorem graphSomeDegreeAtLeast_probability_tendsto_one_of_eventually_nonpos_fin
    (n : α → ℕ) (p : α → unitInterval) (L : α → ℝ)
    (hn : Tendsto (fun a => (n a : ℝ)) l atTop)
    (hL : ∀ᶠ a in l, L a ≤ 0) :
    Tendsto
      (fun a =>
        (SimpleGraph.binomialRandom (Fin (n a)) (p a)).real
          (graphSomeDegreeAtLeastEvent (V := Fin (n a)) (L a)))
      l (𝓝 1) := by
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [hL, hn.eventually_ge_atTop (1 : ℝ)] with a hLa hn_ge1
  have hn1 : 1 ≤ n a := by exact_mod_cast hn_ge1
  have hnonempty : Nonempty (Fin (n a)) := Fin.pos_iff_nonempty.mp (by omega)
  classical
  have hevent :
      graphSomeDegreeAtLeastEvent (V := Fin (n a)) (L a) = Set.univ := by
    ext G
    constructor
    · intro _h
      trivial
    · intro _h
      rcases hnonempty with ⟨v⟩
      exact ⟨v, hLa.trans (by positivity : 0 ≤ (graphDegree G v : ℝ))⟩
  rw [hevent, probReal_univ]

/-- Corrected Exercise 2.4.4, trivial integer case: if `k_n = 10d_n` is
eventually zero, then `Δ(G) ≥ 10d_n` is automatic. -/
theorem sparse_graphs_not_almost_regular_probability_tendsto_one_corrected_of_eventually_zero
    (n : α → ℕ) (p : α → unitInterval) (k : α → ℕ)
    (hn : Tendsto (fun a => (n a : ℝ)) l atTop)
    (hk : ∀ᶠ a in l,
      (k a : ℝ) = 10 * erdosRenyiExpectedDegree (n a) (p a))
    (hkzero : ∀ᶠ a in l, k a = 0) :
    Tendsto
      (fun a =>
        (SimpleGraph.binomialRandom (Fin (n a)) (p a)).real
          (graphSomeDegreeAtLeastEvent (V := Fin (n a))
            (10 * erdosRenyiExpectedDegree (n a) (p a))))
      l (𝓝 1) := by
  refine
    graphSomeDegreeAtLeast_probability_tendsto_one_of_eventually_nonpos_fin
      (l := l) (n := n) (p := p)
      (L := fun a => 10 * erdosRenyiExpectedDegree (n a) (p a))
      hn ?_
  filter_upwards [hk, hkzero] with a hk_eq hk_zero
  rw [← hk_eq, hk_zero]
  norm_num

/-- Corrected Exercise 2.4.4, nontrivial integer case.  Let
`d_n = (n - 1)p_n` and suppose the integer witness count `k_n = 10 d_n` is
eventually positive. If `d_n = o(log n)`, then in `G(n,p_n)` the event
`Δ(G) ≥ 10 d_n` has probability tending to one. The proof uses the corrected
PDF's first-third/remaining-vertices star blocks and the exact binomial
point-mass lower bound. -/
theorem sparse_graphs_not_almost_regular_probability_tendsto_one_corrected_of_eventually_pos
    (n : α → ℕ) (p : α → unitInterval) (k : α → ℕ)
    (hn : Tendsto (fun a => (n a : ℝ)) l atTop)
    (hk : ∀ᶠ a in l,
      (k a : ℝ) = 10 * erdosRenyiExpectedDegree (n a) (p a))
    (hkpos : ∀ᶠ a in l, 0 < k a)
    (hd_small :
      (fun a => erdosRenyiExpectedDegree (n a) (p a))
        =o[l] fun a => Real.log (n a : ℝ)) :
    Tendsto
      (fun a =>
        (SimpleGraph.binomialRandom (Fin (n a)) (p a)).real
          (graphSomeDegreeAtLeastEvent (V := Fin (n a))
            (10 * erdosRenyiExpectedDegree (n a) (p a))))
      l (𝓝 1) := by
  let d : α → ℝ := fun a => erdosRenyiExpectedDegree (n a) (p a)
  have hcard_tendsto :
      Tendsto (fun a => (Fintype.card (Fin (n a)) : ℝ)) l atTop := by
    simpa only [Fintype.card_fin] using hn
  have hlinear :
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ a in l,
          c * (Fintype.card (Fin (n a)) : ℝ) ≤
            (Fintype.card (Fin (n a / 3)) : ℝ) :=
    fin_third_card_linear_eventually (l := l) hn
  have hlog_o_nat :
      (fun a => Real.log (n a : ℝ)) =o[l] fun a => (n a : ℝ) := by
    have h :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp_tendsto hn
    simpa [Real.rpow_one] using h
  have hd_o_nat : d =o[l] fun a => (n a : ℝ) := by
    have hd_small_d : d =o[l] fun a => Real.log (n a : ℝ) := by
      simpa [d] using hd_small
    exact hd_small_d.trans hlog_o_nat
  have hd_le_nat_div40 : ∀ᶠ a in l, d a ≤ (1 / 40 : ℝ) * (n a : ℝ) := by
    have hsmall := hd_o_nat.def (by norm_num : (0 : ℝ) < 1 / 40)
    filter_upwards [hsmall] with a ha
    have hd0 : 0 ≤ d a := erdosRenyiExpectedDegree_nonneg (n a) (p a)
    have hdnorm : ‖d a‖ = d a := by
      rw [Real.norm_eq_abs, abs_of_nonneg hd0]
    have hnnorm : ‖(n a : ℝ)‖ = (n a : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa [hdnorm, hnnorm] using ha
  have hC : 0 < 10 * Real.log 30 + 2 := by
    have hlog30 : 0 < Real.log 30 := Real.log_pos (by norm_num : (1 : ℝ) < 30)
    nlinarith
  have hprob_exp : ∀ᶠ a in l, ∀ j : Fin (n a / 3),
      Real.exp (-((10 * Real.log 30 + 2) * d a)) ≤
        (Nat.choose (finAfterFirstThirdVertexSet (n a)).card (k a) : ℝ) *
          (unitInterval.toNNReal (p a) : ℝ) ^ (k a) *
            (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ) ^
              ((finAfterFirstThirdVertexSet (n a)).card - k a) := by
    filter_upwards [hk, hkpos, hd_le_nat_div40,
      hn.eventually_ge_atTop (3 : ℝ)] with a hk_eq hk_pos hd_le hn_ge3 j
    let ρ : ℝ := (unitInterval.toNNReal (p a) : ℝ)
    have hρ0 : 0 ≤ ρ := by
      dsimp [ρ]
      exact unitInterval.nonneg (p a)
    have hn3 : 3 ≤ n a := by exact_mod_cast hn_ge3
    have hn1 : 1 ≤ n a := by omega
    have hpred_pos_nat : 0 < n a - 1 := by omega
    have hpred_pos : 0 < ((n a - 1 : ℕ) : ℝ) := by exact_mod_cast hpred_pos_nat
    have hkm_real :
        (k a : ℝ) ≤ ((finAfterFirstThirdVertexSet (n a)).card : ℝ) := by
      have hk_le_quarter : (k a : ℝ) ≤ (1 / 4 : ℝ) * (n a : ℝ) := by
        rw [hk_eq]
        nlinarith
      have hleaf_quarter :
          (1 / 4 : ℝ) * (n a : ℝ) ≤
            ((finAfterFirstThirdVertexSet (n a)).card : ℝ) := by
        have hnat : n a ≤ 4 * (n a - n a / 3) := by omega
        have hreal : (n a : ℝ) ≤
            4 * ((n a - n a / 3 : ℕ) : ℝ) := by
          exact_mod_cast hnat
        simp only [finAfterFirstThirdVertexSet_card]
        nlinarith
      exact hk_le_quarter.trans hleaf_quarter
    have hkm : k a ≤ (finAfterFirstThirdVertexSet (n a)).card := by
      exact_mod_cast hkm_real
    have hpred_cast :
        ((n a - 1 : ℕ) : ℝ) = (n a : ℝ) - 1 := by
      rw [Nat.cast_sub hn1]
      norm_num
    have hd_le_pred_half :
        d a ≤ (1 / 2 : ℝ) * ((n a - 1 : ℕ) : ℝ) := by
      rw [hpred_cast]
      nlinarith
    have hphalf : ρ ≤ 1 / 2 := by
      have hprod :
          ((n a - 1 : ℕ) : ℝ) * ρ ≤
            ((n a - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) := by
        simpa [d, erdosRenyiExpectedDegree, ρ, mul_comm, mul_left_comm,
          mul_assoc] using hd_le_pred_half
      exact (mul_le_mul_iff_right₀ hpred_pos).mp hprod
    have hmean_lower :
        d a / 3 ≤
          ((finAfterFirstThirdVertexSet (n a)).card : ℝ) * ρ := by
      have hnat : n a - 1 ≤ 3 * (n a - n a / 3) := by omega
      have hreal :
          ((n a - 1 : ℕ) : ℝ) ≤
            3 * ((n a - n a / 3 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hmul :=
        mul_le_mul_of_nonneg_right hreal hρ0
      have hdiv :
          ((n a - 1 : ℕ) : ℝ) * ρ / 3 ≤
            ((n a - n a / 3 : ℕ) : ℝ) * ρ := by
        nlinarith
      simpa [d, erdosRenyiExpectedDegree, ρ,
        finAfterFirstThirdVertexSet_card, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc] using hdiv
    have hmean_upper :
        ((finAfterFirstThirdVertexSet (n a)).card : ℝ) * ρ ≤ d a := by
      have hnat : n a - n a / 3 ≤ n a - 1 := by omega
      have hreal :
          ((n a - n a / 3 : ℕ) : ℝ) ≤
            ((n a - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hmul :=
        mul_le_mul_of_nonneg_right hreal hρ0
      simp only [finAfterFirstThirdVertexSet_card]
      dsimp [d, erdosRenyiExpectedDegree, ρ]
      exact hmul
    have hmass :=
      binomial_exact_mass_lower_exp_of_mean_bounds
        (m := (finAfterFirstThirdVertexSet (n a)).card)
        (k := k a) (p := ρ) (η := d a / 3) (D := d a)
        hk_pos hkm hρ0 hphalf
        (div_nonneg (erdosRenyiExpectedDegree_nonneg (n a) (p a))
          (by norm_num : (0 : ℝ) ≤ 3))
        hmean_lower hmean_upper
    exact
      (sparse_exact_mass_pdf_exponential_lower
        (d := d a) (k := k a) hk_pos hk_eq).trans (by
          simpa [ρ] using hmass)
  have hcard : ∀ᶠ a in l, ∀ j : Fin (n a / 3),
      10 * d a ≤ (k a : ℝ) := by
    filter_upwards [hk] with a hk_eq j
    rw [hk_eq]
  have hd_nonneg : ∀ᶠ a in l, 0 ≤ d a :=
    Eventually.of_forall fun a => erdosRenyiExpectedDegree_nonneg (n a) (p a)
  simpa [d] using
    sparse_graphs_not_almost_regular_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_of_exp_lower
      (V := fun a => Fin (n a)) (J := fun a => Fin (n a / 3))
      (l := l) (p := p) (d := d) (C := 10 * Real.log 30 + 2)
      (v := fun a j => finFirstThirdCenter (n a) j)
      (S := fun a _j => finAfterFirstThirdVertexSet (n a))
      (k := fun a _j => k a)
      (fun a j => finFirstThirdCenter_not_mem_finAfterFirstThirdVertexSet (n a) j)
      hC hcard_tendsto hlinear hd_nonneg
      (by simpa [d] using hd_small) hprob_exp hcard
      (fun a => finAfterFirstThirdStarEdgeFinset_pairwiseDisjoint (n a))

/-- Corrected Exercise 2.4.5. If the expected degrees
`d_n = (n - 1)p_n` stay between two fixed constants `0 < d0 ≤ D`, then
`G(n,p_n)` has maximum degree at least
`(1/8) log n / log log n` with probability tending to one. This is the
corrected `d = Θ(1)` statement from the supplied solutions PDF; the proof uses
the integer witness count `⌊(1/4) log n / log log n⌋`. -/
theorem very_sparse_graphs_far_from_regular_probability_tendsto_one_corrected
    (n : α → ℕ) (p : α → unitInterval) {d0 D : ℝ}
    (hn : Tendsto (fun a => (n a : ℝ)) l atTop)
    (hd0 : 0 < d0) (hD : d0 ≤ D)
    (hdeg_lower : ∀ᶠ a in l,
      d0 ≤ erdosRenyiExpectedDegree (n a) (p a))
    (hdeg_upper : ∀ᶠ a in l,
      erdosRenyiExpectedDegree (n a) (p a) ≤ D) :
    Tendsto
      (fun a =>
        (SimpleGraph.binomialRandom (Fin (n a)) (p a)).real
          (graphSomeDegreeAtLeastEvent (V := Fin (n a))
            (verySparseCorrectedLowerScale (n a))))
      l (𝓝 1) := by
  let η : ℝ := d0 / 3
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  have hDpos : 0 < D := lt_of_lt_of_le hd0 hD
  have hcard_tendsto :
      Tendsto (fun a => (Fintype.card (Fin (n a)) : ℝ)) l atTop := by
    simpa only [Fintype.card_fin] using hn
  have hlinear :
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ a in l,
          c * (Fintype.card (Fin (n a)) : ℝ) ≤
            (Fintype.card (Fin (n a / 3)) : ℝ) :=
    fin_third_card_linear_eventually (l := l) hn
  have hlog_top :
      Tendsto (fun a => Real.log (n a : ℝ)) l atTop :=
    Real.tendsto_log_atTop.comp hn
  have hloglog_top :
      Tendsto (fun a => Real.log (Real.log (n a : ℝ))) l atTop :=
    Real.tendsto_log_atTop.comp hlog_top
  have hloglog_o_log :
      (fun a => Real.log (Real.log (n a : ℝ))) =o[l]
        fun a => Real.log (n a : ℝ) := by
    have h :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp_tendsto
        hlog_top
    simpa [Real.rpow_one] using h
  have hloglog_le_sixteenth_log : ∀ᶠ a in l,
      Real.log (Real.log (n a : ℝ)) ≤
        (1 / 16 : ℝ) * Real.log (n a : ℝ) := by
    have hsmall := hloglog_o_log.def (by norm_num : (0 : ℝ) < 1 / 16)
    filter_upwards [hsmall, hlog_top.eventually_ge_atTop (1 : ℝ),
      hloglog_top.eventually_ge_atTop (0 : ℝ)] with a hsmall_a hg_ge1 hll_ge0
    have hg_nonneg : 0 ≤ Real.log (n a : ℝ) := by linarith
    have hll_nonneg : 0 ≤ Real.log (Real.log (n a : ℝ)) := hll_ge0
    have hllnorm :
        ‖Real.log (Real.log (n a : ℝ))‖ =
          Real.log (Real.log (n a : ℝ)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hll_nonneg]
    have hgnorm :
        ‖Real.log (n a : ℝ)‖ = Real.log (n a : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hg_nonneg]
    simpa [hllnorm, hgnorm] using hsmall_a
  have hconst_le_loglog : ∀ᶠ a in l,
      -Real.log η ≤ Real.log (Real.log (n a : ℝ)) :=
    hloglog_top.eventually_ge_atTop (-Real.log η)
  have hprob : ∀ᶠ a in l, ∀ j : Fin (n a / 3),
      Real.exp (-(2 * D)) *
          Real.exp (-((1 / 2 : ℝ) *
            Real.log (Fintype.card (Fin (n a)) : ℝ))) ≤
        (Nat.choose (finAfterFirstThirdVertexSet (n a)).card
            (verySparseCorrectedWitnessCount (n a)) : ℝ) *
          (unitInterval.toNNReal (p a) : ℝ) ^
            verySparseCorrectedWitnessCount (n a) *
            (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ) ^
              ((finAfterFirstThirdVertexSet (n a)).card -
                verySparseCorrectedWitnessCount (n a)) := by
    filter_upwards [hdeg_lower, hdeg_upper,
      hn.eventually_ge_atTop (3 : ℝ),
      hn.eventually_ge_atTop (2 * D + 3),
      hlog_top.eventually_ge_atTop (1 : ℝ),
      hloglog_top.eventually_ge_atTop (1 : ℝ),
      hloglog_le_sixteenth_log, hconst_le_loglog] with
      a hd_lower hd_upper hn_ge3 hn_geD hg_ge1 hll_ge1 hll_le hconst_le j
    let r : ℕ := verySparseCorrectedWitnessCount (n a)
    let x : ℝ := verySparseCorrectedWitnessScale (n a)
    let g : ℝ := Real.log (n a : ℝ)
    let ll : ℝ := Real.log (Real.log (n a : ℝ))
    let ρ : ℝ := (unitInterval.toNNReal (p a) : ℝ)
    have hρ0 : 0 ≤ ρ := by
      dsimp [ρ]
      exact unitInterval.nonneg (p a)
    have hn3 : 3 ≤ n a := by exact_mod_cast hn_ge3
    have hn1 : 1 ≤ n a := by omega
    have hpred_pos_nat : 0 < n a - 1 := by omega
    have hpred_pos : 0 < ((n a - 1 : ℕ) : ℝ) := by exact_mod_cast hpred_pos_nat
    have hpred_cast :
        ((n a - 1 : ℕ) : ℝ) = (n a : ℝ) - 1 := by
      rw [Nat.cast_sub hn1]
      norm_num
    have hg_nonneg : 0 ≤ g := by
      dsimp [g]
      linarith
    have hll_pos : 0 < ll := by
      dsimp [ll]
      linarith
    have hx_eq : x = (1 / 4 : ℝ) * g / ll := by
      rfl
    have hx_ge_four : 4 ≤ x := by
      rw [hx_eq]
      rw [le_div_iff₀ hll_pos]
      have hll_le' : ll ≤ (1 / 16 : ℝ) * g := by
        simpa [ll, g] using hll_le
      nlinarith
    have hx_nonneg : 0 ≤ x := by nlinarith
    have hr_ge_four : 4 ≤ r := by
      dsimp [r]
      exact Nat.le_floor hx_ge_four
    have hr_pos : 0 < r := by omega
    have hrposR : 0 < (r : ℝ) := by exact_mod_cast hr_pos
    have hr_le_x : (r : ℝ) ≤ x := by
      dsimp [r]
      exact Nat.floor_le hx_nonneg
    have hx_le_quarter_n : x ≤ (1 / 4 : ℝ) * (n a : ℝ) := by
      have hg_le_n : g ≤ (n a : ℝ) := by
        dsimp [g]
        exact Real.log_le_self (by positivity : 0 ≤ (n a : ℝ))
      have hdiv_le : g / ll ≤ (n a : ℝ) := by
        rw [div_le_iff₀ hll_pos]
        have hn_nonneg : 0 ≤ (n a : ℝ) := by positivity
        nlinarith
      calc
        x = (1 / 4 : ℝ) * (g / ll) := by
          rw [hx_eq]
          ring
        _ ≤ (1 / 4 : ℝ) * (n a : ℝ) :=
          mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
    have hkm_real :
        (r : ℝ) ≤ ((finAfterFirstThirdVertexSet (n a)).card : ℝ) := by
      have hleaf_quarter :
          (1 / 4 : ℝ) * (n a : ℝ) ≤
            ((finAfterFirstThirdVertexSet (n a)).card : ℝ) := by
        have hnat : n a ≤ 4 * (n a - n a / 3) := by omega
        have hreal : (n a : ℝ) ≤
            4 * ((n a - n a / 3 : ℕ) : ℝ) := by
          exact_mod_cast hnat
        simp only [finAfterFirstThirdVertexSet_card]
        nlinarith
      exact hr_le_x.trans (hx_le_quarter_n.trans hleaf_quarter)
    have hkm : r ≤ (finAfterFirstThirdVertexSet (n a)).card := by
      exact_mod_cast hkm_real
    have hd_le_pred_half :
        erdosRenyiExpectedDegree (n a) (p a) ≤
          (1 / 2 : ℝ) * ((n a - 1 : ℕ) : ℝ) := by
      have hD_le_pred :
          D ≤ (1 / 2 : ℝ) * ((n a - 1 : ℕ) : ℝ) := by
        rw [hpred_cast]
        nlinarith
      exact hd_upper.trans hD_le_pred
    have hphalf : ρ ≤ 1 / 2 := by
      have hprod :
          ((n a - 1 : ℕ) : ℝ) * ρ ≤
            ((n a - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) := by
        simpa [erdosRenyiExpectedDegree, ρ, mul_comm, mul_left_comm,
          mul_assoc] using hd_le_pred_half
      exact (mul_le_mul_iff_right₀ hpred_pos).mp hprod
    have hmean_lower :
        η ≤ ((finAfterFirstThirdVertexSet (n a)).card : ℝ) * ρ := by
      have hnat : n a - 1 ≤ 3 * (n a - n a / 3) := by omega
      have hreal :
          ((n a - 1 : ℕ) : ℝ) ≤
            3 * ((n a - n a / 3 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hmul := mul_le_mul_of_nonneg_right hreal hρ0
      have hdiv :
          erdosRenyiExpectedDegree (n a) (p a) / 3 ≤
            ((n a - n a / 3 : ℕ) : ℝ) * ρ := by
        have hdiv' :
            ((n a - 1 : ℕ) : ℝ) * ρ / 3 ≤
              ((n a - n a / 3 : ℕ) : ℝ) * ρ := by
          nlinarith
        simpa [erdosRenyiExpectedDegree, ρ] using hdiv'
      have hd0_div :
          η ≤ erdosRenyiExpectedDegree (n a) (p a) / 3 := by
        dsimp [η]
        nlinarith
      exact hd0_div.trans (by
        simpa [finAfterFirstThirdVertexSet_card] using hdiv)
    have hmean_upper :
        ((finAfterFirstThirdVertexSet (n a)).card : ℝ) * ρ ≤ D := by
      have hnat : n a - n a / 3 ≤ n a - 1 := by omega
      have hreal :
          ((n a - n a / 3 : ℕ) : ℝ) ≤
            ((n a - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hmul := mul_le_mul_of_nonneg_right hreal hρ0
      have hleaf_le_d :
          ((finAfterFirstThirdVertexSet (n a)).card : ℝ) * ρ ≤
            erdosRenyiExpectedDegree (n a) (p a) := by
        simp only [finAfterFirstThirdVertexSet_card]
        dsimp [erdosRenyiExpectedDegree, ρ]
        exact hmul
      exact hleaf_le_d.trans hd_upper
    have hx_le_g : x ≤ g := by
      have hdiv_le_g : g / ll ≤ g := by
        rw [div_le_iff₀ hll_pos]
        nlinarith
      calc
        x = (1 / 4 : ℝ) * (g / ll) := by
          rw [hx_eq]
          ring
        _ ≤ (1 / 4 : ℝ) * g :=
          mul_le_mul_of_nonneg_left hdiv_le_g (by norm_num)
        _ ≤ g := by nlinarith
    have hr_le_g : (r : ℝ) ≤ g := hr_le_x.trans hx_le_g
    have hg_pos : 0 < g := lt_of_lt_of_le hrposR hr_le_g
    have hlog_ratio :
        Real.log ((r : ℝ) / η) ≤ 2 * ll := by
      have hdiv_le : (r : ℝ) / η ≤ g / η := by
        exact div_le_div_of_nonneg_right hr_le_g hηpos.le
      have hlog_le :
          Real.log ((r : ℝ) / η) ≤ Real.log (g / η) :=
        Real.log_le_log (div_pos hrposR hηpos) hdiv_le
      have hlog_eq : Real.log (g / η) = ll - Real.log η := by
        dsimp [ll, g]
        rw [Real.log_div hg_pos.ne' hηpos.ne']
      calc
        Real.log ((r : ℝ) / η) ≤ Real.log (g / η) := hlog_le
        _ = ll - Real.log η := hlog_eq
        _ ≤ 2 * ll := by
          have hconst_le' : -Real.log η ≤ ll := by
            simpa [ll] using hconst_le
          calc
            ll - Real.log η = ll + (-Real.log η) := by ring
            _ ≤ ll + ll := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right hconst_le' ll
            _ = 2 * ll := by ring
    have hscale :
        (r : ℝ) * Real.log ((r : ℝ) / η) ≤
          (1 / 2 : ℝ) * g := by
      have hstep1 :
          (r : ℝ) * Real.log ((r : ℝ) / η) ≤ (r : ℝ) * (2 * ll) :=
        mul_le_mul_of_nonneg_left hlog_ratio (by exact_mod_cast Nat.zero_le r)
      have htwo_ll_nonneg : 0 ≤ 2 * ll :=
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hll_pos.le
      have hstep2 : (r : ℝ) * (2 * ll) ≤ x * (2 * ll) :=
        mul_le_mul_of_nonneg_right hr_le_x htwo_ll_nonneg
      have hx_mul : x * (2 * ll) = (1 / 2 : ℝ) * g := by
        rw [hx_eq]
        field_simp [hll_pos.ne']
        ring
      calc
        (r : ℝ) * Real.log ((r : ℝ) / η) ≤
            (r : ℝ) * (2 * ll) := hstep1
        _ ≤ x * (2 * ll) := hstep2
        _ = (1 / 2 : ℝ) * g := hx_mul
    have hpow_lower_g :
        Real.exp (-((1 / 2 : ℝ) * g)) ≤
          (η / (r : ℝ)) ^ r :=
      exp_neg_le_div_pow_of_mul_log_le
        (a := η) (t := (1 / 2 : ℝ) * g)
        (r := r) hηpos hr_pos hscale
    have hpow_lower :
        Real.exp (-((1 / 2 : ℝ) * Real.log (n a : ℝ))) ≤
          (η / (r : ℝ)) ^ r := by
      simpa [g] using hpow_lower_g
    have hmass :
        Real.exp (-(2 * D)) * (η / (r : ℝ)) ^ r ≤
          (Nat.choose (finAfterFirstThirdVertexSet (n a)).card r : ℝ) *
            ρ ^ r * (1 - ρ) ^
              ((finAfterFirstThirdVertexSet (n a)).card - r) :=
      binomial_exact_mass_lower_exp_of_mean_bounds
        (m := (finAfterFirstThirdVertexSet (n a)).card)
        (k := r) (p := ρ) (η := η) (D := D)
        hr_pos hkm hρ0 hphalf hηpos.le hmean_lower hmean_upper
    have hleft :
        Real.exp (-(2 * D)) *
            Real.exp (-((1 / 2 : ℝ) * Real.log (n a : ℝ))) ≤
          Real.exp (-(2 * D)) * (η / (r : ℝ)) ^ r :=
      mul_le_mul_of_nonneg_left hpow_lower (Real.exp_nonneg _)
    exact (by
      simpa [r, ρ, Fintype.card_fin, finAfterFirstThirdVertexSet_card]
        using hleft.trans hmass)
  have hcard : ∀ᶠ a in l, ∀ j : Fin (n a / 3),
      verySparseCorrectedLowerScale (n a) ≤
        (verySparseCorrectedWitnessCount (n a) : ℝ) := by
    filter_upwards [hloglog_top.eventually_ge_atTop (1 : ℝ),
      hloglog_le_sixteenth_log] with a hll_ge1 hll_le j
    let x : ℝ := verySparseCorrectedWitnessScale (n a)
    let g : ℝ := Real.log (n a : ℝ)
    let ll : ℝ := Real.log (Real.log (n a : ℝ))
    have hll_pos : 0 < ll := by
      dsimp [ll]
      linarith
    have hx_eq : x = (1 / 4 : ℝ) * g / ll := rfl
    have hx_ge_four : 4 ≤ x := by
      rw [hx_eq]
      rw [le_div_iff₀ hll_pos]
      have hll_le' : ll ≤ (1 / 16 : ℝ) * g := by
        simpa [ll, g] using hll_le
      nlinarith
    have hx_nonneg : 0 ≤ x := by nlinarith
    have hfloor_gt : x - 1 < (verySparseCorrectedWitnessCount (n a) : ℝ) := by
      dsimp [verySparseCorrectedWitnessCount]
      rw [natCast_floor_eq_intCast_floor hx_nonneg]
      exact Int.sub_one_lt_floor x
    have hlower_eq :
        verySparseCorrectedLowerScale (n a) = x / 2 := by
      dsimp [x, verySparseCorrectedWitnessScale, verySparseCorrectedLowerScale]
      ring
    rw [hlower_eq]
    exact le_of_lt (lt_of_le_of_lt (by nlinarith) hfloor_gt)
  simpa [verySparseCorrectedLowerScale] using
    graphSomeDegreeAtLeast_probability_tendsto_one_of_disjoint_star_exact_count_witnesses_const_half_log
      (V := fun a => Fin (n a)) (J := fun a => Fin (n a / 3))
      (l := l) (p := p)
      (L := fun a => verySparseCorrectedLowerScale (n a))
      (c := Real.exp (-(2 * D)))
      (v := fun a j => finFirstThirdCenter (n a) j)
      (S := fun a _j => finAfterFirstThirdVertexSet (n a))
      (k := fun a _j => verySparseCorrectedWitnessCount (n a))
      (fun a j => finFirstThirdCenter_not_mem_finAfterFirstThirdVertexSet (n a) j)
      (Real.exp_pos _) hcard_tendsto hlinear hprob hcard
      (fun a => finAfterFirstThirdStarEdgeFinset_pairwiseDisjoint (n a))

end CorrectedExercises

end Asymptotic

end LeanFpAnalysis.HDP
