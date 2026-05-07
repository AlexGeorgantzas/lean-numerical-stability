import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def lapackBerrDenom (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) (i : Fin n) : ℝ :=
  |b i| + ∑ j : Fin n, |A i j| * |x j|

def componentwiseBackwardCompatible (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) (eta : ℝ) : Prop :=
  ∃ DeltaA : Fin n → Fin n → ℝ,
  ∃ Deltab : Fin n → ℝ,
    (∀ i j, |DeltaA i j| ≤ eta * |A i j|) ∧
    (∀ i, |Deltab i| ≤ eta * |b i|) ∧
    ∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x j = b i + Deltab i

theorem lapackBerr_backward_certificate
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (eta : ℝ)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (heta_nonneg : 0 ≤ eta)
    (hcert : ∀ i : Fin n,
      |fl_residual fp n A x b i| +
        gamma fp (n + 1) * lapackBerrDenom n A x b i ≤
          eta * lapackBerrDenom n A x b i) :
    componentwiseBackwardCompatible n A x b eta := by
  sorry

end LeanFpAnalysis.FP
