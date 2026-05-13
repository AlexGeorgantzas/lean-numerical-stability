import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

def opBackwardCompatible (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) (eta : ℝ) : Prop :=
  ∃ DeltaA : Fin n → Fin n → ℝ,
  ∃ Deltab : Fin n → ℝ,
    (∀ i j, |DeltaA i j| ≤ eta * |A i j|) ∧
    (∀ i, |Deltab i| ≤ eta * |b i|) ∧
    ∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x j = b i + Deltab i

theorem oettli_prager_backward_to_forward_error
    (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (x xhat b : Fin n → ℝ) (eta : ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (heta_nonneg : 0 ≤ eta)
    (hback : opBackwardCompatible n A xhat b eta) :
    ∀ i : Fin n, |x i - xhat i| ≤
      eta * ∑ j : Fin n, |A_inv i j| *
        (∑ k : Fin n, |A j k| * |xhat k| + |b j|) := by
  rcases hback with ⟨DeltaA, Deltab, hDeltaA, hDeltab, hPerturbed⟩
  exact componentwise_forward_error_standard n A A_inv x xhat b DeltaA Deltab
    eta heta_nonneg hDeltaA hDeltab hInv hAx hPerturbed

end LeanFpAnalysis.FP
