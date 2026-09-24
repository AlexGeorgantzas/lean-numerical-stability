import NumStability.Algorithms.Summation.Tree.Core

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open NumStability

/-- A source-general rounded value and relative-error witness at every
internal addition. Unlike `FPModel`, this representation does not impose
exactness when an operand is zero. -/
inductive RoundingTrace where
  | leaf : RoundingTrace
  | node : RoundingTrace → RoundingTrace → ℝ → ℝ → RoundingTrace

noncomputable def traceEval :
    (t : SumTree n) → (v : Fin n → ℝ) → RoundingTrace → ℝ
  | .leaf, v, .leaf => v ⟨0, by norm_num⟩
  | .node _ _, _, .node _ _ _ rounded => rounded
  | _, _, _ => 0

/-- Every internal rounded result equals the sum of its *computed* children
times its local factor. `signedRelErrorWitness` is the frozen library's
general relational model, with no extraneous exact-zero rule. -/
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

/-- Flattened `(s_k δ_k, product of strict ancestor factors)` pairs. -/
noncomputable def explicitErrorTerms :
    (t : SumTree n) → (v : Fin n → ℝ) → RoundingTrace → List (ℝ × ℝ)
  | .leaf, _, .leaf => []
  | .node l r, v, .node tl tr δ _ =>
      ((explicitErrorTerms l (fun i => v (Fin.castAdd _ i)) tl ++
          explicitErrorTerms r (fun i => v (Fin.natAdd _ i)) tr).map
        (fun p => (p.1, p.2 * (1 + δ)))) ++
        [(SumTree.exactSum (.node l r) v * δ, 1)]
  | _, _, _ => []

noncomputable def explicitErrorSum (terms : List (ℝ × ℝ)) : ℝ :=
  (terms.map (fun p => p.1 * p.2)).sum

/-- Hallman--Ipsen Lemma 2.2, equation (2.3), for every source-admissible
binary-tree relative-error execution and arbitrary signed real leaves. -/
theorem target (u : ℝ) (t : SumTree n) (v : Fin n → ℝ)
    (trace : RoundingTrace) (htrace : ValidTrace u t v trace) :
    traceEval t v trace - SumTree.exactSum t v =
      explicitErrorSum (explicitErrorTerms t v trace) := by
  sorry

end HighamBenchCandidate
