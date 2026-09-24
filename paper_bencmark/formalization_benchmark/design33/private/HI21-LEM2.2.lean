import NumStability.Algorithms.Summation.Tree.Core

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open NumStability

/-- One paper-model relative-error witness for each actual internal addition
of a `SumTree`, independent of how the tree is balanced. -/
inductive RoundingTrace where
  | leaf : RoundingTrace
  | node : RoundingTrace → RoundingTrace → ℝ → RoundingTrace

/-- The local errors match the computed operands of the actual tree and obey
the source's no-exception relative-addition bound. -/
def ValidTrace (fp : FPModel) :
    (t : SumTree n) → (v : Fin n → ℝ) → RoundingTrace → Prop
  | .leaf, _, .leaf => True
  | .node l r, v, .node tl tr δ =>
      ValidTrace fp l (fun i => v (Fin.castAdd _ i)) tl ∧
      ValidTrace fp r (fun i => v (Fin.natAdd _ i)) tr ∧
      |δ| ≤ fp.u ∧
      fp.fl_add
        (SumTree.eval fp l (fun i => v (Fin.castAdd _ i)))
        (SumTree.eval fp r (fun i => v (Fin.natAdd _ i))) =
          (SumTree.eval fp l (fun i => v (Fin.castAdd _ i)) +
            SumTree.eval fp r (fun i => v (Fin.natAdd _ i))) * (1 + δ)
  | _, _, _ => False

/-- Flattened `(s_k δ_k, product of (1+δ_j) for strict ancestors j)`.
At each parent we multiply every descendant's ancestor product by the
parent's factor; the parent itself enters with empty-product factor one. -/
noncomputable def explicitErrorTerms :
    (t : SumTree n) → (v : Fin n → ℝ) → RoundingTrace → List (ℝ × ℝ)
  | .leaf, _, .leaf => []
  | .node l r, v, .node tl tr δ =>
      ((explicitErrorTerms l (fun i => v (Fin.castAdd _ i)) tl ++
          explicitErrorTerms r (fun i => v (Fin.natAdd _ i)) tr).map
        (fun p => (p.1, p.2 * (1 + δ)))) ++
        [(SumTree.exactSum (.node l r) v * δ, 1)]
  | _, _, _ => []

noncomputable def explicitErrorSum (terms : List (ℝ × ℝ)) : ℝ :=
  (terms.map (fun p => p.1 * p.2)).sum

/-- Hallman--Ipsen Lemma 2.2, equation (2.3): exact final forward error as
the sum of every local exact-partial-sum error, propagated through all strict
ancestor rounding factors. -/
theorem target (fp : FPModel) (t : SumTree n) (v : Fin n → ℝ)
    (trace : RoundingTrace) (htrace : ValidTrace fp t v trace) :
    SumTree.eval fp t v - SumTree.exactSum t v =
      explicitErrorSum (explicitErrorTerms t v trace) := by
  sorry

end HighamBenchCandidate
