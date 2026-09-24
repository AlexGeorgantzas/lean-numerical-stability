import NumStability.Algorithms.Summation.Tree.Core

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open scoped BigOperators
open NumStability

/-- Independent relative-error witnesses, one at each tree addition. -/
inductive RoundingTrace where
  | leaf : RoundingTrace
  | node : RoundingTrace → RoundingTrace → ℝ → RoundingTrace

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

/-- First-order summands `s_k δ_k` over every internal tree node. -/
noncomputable def firstOrderTerms :
    (t : SumTree n) → (v : Fin n → ℝ) → RoundingTrace → List ℝ
  | .leaf, _, .leaf => []
  | .node l r, v, .node tl tr δ =>
      firstOrderTerms l (fun i => v (Fin.castAdd _ i)) tl ++
      firstOrderTerms r (fun i => v (Fin.natAdd _ i)) tr ++
      [SumTree.exactSum (.node l r) v * δ]
  | _, _, _ => []

/-- Hallman--Ipsen equation (2.7): first-order forward-error expansion for
arbitrary binary summation trees. The quadratic coefficient is uniform across
all admissible local rounding traces at fixed tree and input vector. -/
theorem target :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (t : SumTree n) (v : Fin n → ℝ) (fp : FPModel),
        0 < fp.u → (t.depth : ℝ) * fp.u ≤ (1 / 2 : ℝ) →
          ∀ (trace : RoundingTrace), ValidTrace fp t v trace →
            |(SumTree.eval fp t v - SumTree.exactSum t v) -
                (firstOrderTerms t v trace).sum| ≤
              C * (t.depth : ℝ) ^ 2 * fp.u ^ 2 *
                (∑ i : Fin n, |v i|) := by
  sorry

end HighamBenchCandidate
