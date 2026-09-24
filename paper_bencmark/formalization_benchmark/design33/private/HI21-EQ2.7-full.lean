import NumStability.Algorithms.Summation.Tree.Core

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open scoped BigOperators
open NumStability

inductive RoundingTrace where
  | leaf : RoundingTrace
  | node : RoundingTrace → RoundingTrace → ℝ → ℝ → RoundingTrace

noncomputable def traceEval :
    (t : SumTree n) → (v : Fin n → ℝ) → RoundingTrace → ℝ
  | .leaf, v, .leaf => v ⟨0, by norm_num⟩
  | .node _ _, _, .node _ _ _ rounded => rounded
  | _, _, _ => 0

/-- Local relative-error executions without the stronger `FPModel`
zero-operand exactness rule, which is absent from this source result. -/
def ValidTrace (u : ℝ) :
    (t : SumTree n) → (v : Fin n → ℝ) → RoundingTrace → Prop
  | .leaf, _, .leaf => True
  | .node l r, v, .node tl tr δ rounded =>
      ValidTrace u l (fun i => v (Fin.castAdd _ i)) tl ∧
      ValidTrace u r (fun i => v (Fin.natAdd _ i)) tr ∧
      |δ| ≤ u ∧
      signedRelErrorWitness rounded
        (traceEval l (fun i => v (Fin.castAdd _ i)) tl +
          traceEval r (fun i => v (Fin.natAdd _ i)) tr) δ
  | _, _, _ => False

/-- One exact partial sum times its local error for each internal node. -/
noncomputable def firstOrderTerms :
    (t : SumTree n) → (v : Fin n → ℝ) → RoundingTrace → List ℝ
  | .leaf, _, .leaf => []
  | .node l r, v, .node tl tr δ _ =>
      firstOrderTerms l (fun i => v (Fin.castAdd _ i)) tl ++
      firstOrderTerms r (fun i => v (Fin.natAdd _ i)) tr ++
      [SumTree.exactSum (.node l r) v * δ]
  | _, _, _ => []

/-- Hallman--Ipsen equation (2.7), uniformly across tree shape and input.
The smallness condition exposes the h*u regime implicit in O(h²*u²). -/
theorem target :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (t : SumTree n) (v : Fin n → ℝ) (u : ℝ),
        0 < u → (t.depth : ℝ) * u ≤ (1 / 2 : ℝ) →
          ∀ (trace : RoundingTrace), ValidTrace u t v trace →
            |(traceEval t v trace - SumTree.exactSum t v) -
                (firstOrderTerms t v trace).sum| ≤
              C * (t.depth : ℝ) ^ 2 * u ^ 2 *
                (∑ i : Fin n, |v i|) := by
  sorry

end HighamBenchCandidate
