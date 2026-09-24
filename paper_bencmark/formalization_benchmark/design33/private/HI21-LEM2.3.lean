import NumStability.Algorithms.Summation.Tree.Core

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open NumStability

/-- One relative-error witness per actual internal addition. -/
inductive RoundingTrace where
  | leaf : RoundingTrace
  | node : RoundingTrace → RoundingTrace → ℝ → RoundingTrace

/-- The witnesses are linked to the *computed* child operands at every node. -/
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

/-- Local terms `(s_j+f_j)δ_j` for the entire subtree, in child-before-parent
order. The computed child sum is exactly `s_j+f_j`. -/
noncomputable def localErrorTerms (fp : FPModel) :
    (t : SumTree n) → (v : Fin n → ℝ) → RoundingTrace → List ℝ
  | .leaf, _, .leaf => []
  | .node l r, v, .node tl tr δ =>
      localErrorTerms fp l (fun i => v (Fin.castAdd _ i)) tl ++
      localErrorTerms fp r (fun i => v (Fin.natAdd _ i)) tr ++
      [(SumTree.eval fp l (fun i => v (Fin.castAdd _ i)) +
        SumTree.eval fp r (fun i => v (Fin.natAdd _ i))) * δ]
  | _, _, _ => []

/-- The sum `f_k` of the two child forward errors at an internal node. -/
noncomputable def childErrors (fp : FPModel) :
    (t : SumTree n) → (v : Fin n → ℝ) → ℝ
  | .leaf, _ => 0
  | .node l r, v =>
      (SumTree.eval fp l (fun i => v (Fin.castAdd _ i)) -
        SumTree.exactSum l (fun i => v (Fin.castAdd _ i))) +
      (SumTree.eval fp r (fun i => v (Fin.natAdd _ i)) -
        SumTree.exactSum r (fun i => v (Fin.natAdd _ i)))

/-- Hallman--Ipsen Lemma 2.3, equations (2.5) and (2.6): the forward error
at every subtree is the sum of its local `(s_j+f_j)δ_j` terms, and `f_k` is
the same sum restricted to the strict descendant internal nodes. -/
theorem target (fp : FPModel) (t : SumTree n) (v : Fin n → ℝ)
    (trace : RoundingTrace) (htrace : ValidTrace fp t v trace) :
    (SumTree.eval fp t v - SumTree.exactSum t v =
      (localErrorTerms fp t v trace).sum) ∧
    (childErrors fp t v =
      match t, trace with
      | .node l r, .node tl tr _ =>
          (localErrorTerms fp l (fun i => v (Fin.castAdd _ i)) tl).sum +
          (localErrorTerms fp r (fun i => v (Fin.natAdd _ i)) tr).sum
      | _, _ => 0) := by
  sorry

end HighamBenchCandidate
