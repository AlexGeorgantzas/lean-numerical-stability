import LeanFpAnalysis.HDP.Probability.Concentration.Basic
import LeanFpAnalysis.HDP.Probability.Concentration.Chernoff
import Mathlib.Data.Finset.Union
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Random Graph Degree Bounds

Book-facing event and union-bound statements for HDP Chapter 2, Section 2.4.
The degree tail input is kept explicit, so these lemmas can be used both with
the Bernoulli/Chernoff API already formalized in this library and with future
edge-coordinate facts about `SimpleGraph.binomialRandom`.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace LeanFpAnalysis.HDP

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

end StarLowerWitnesses

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

end Asymptotic

end LeanFpAnalysis.HDP
