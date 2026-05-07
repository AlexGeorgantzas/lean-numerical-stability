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
  have hBound : ∀ i : Fin n, |residualVec n A x b i| ≤
      eta * (∑ j : Fin n, |A i j| * |x j| + |b i|) := by
    intro i
    have hreserr :=
      conventional_residual_error fp n A x b hn hn1 i
    have htri : |b i - ∑ j : Fin n, A i j * x j| ≤
        |fl_residual fp n A x b i| +
          |fl_residual fp n A x b i -
            (b i - ∑ j : Fin n, A i j * x j)| := by
      rw [abs_le]
      constructor
      · linarith [neg_le_abs (fl_residual fp n A x b i),
          le_abs_self (fl_residual fp n A x b i -
            (b i - ∑ j : Fin n, A i j * x j))]
      · linarith [le_abs_self (fl_residual fp n A x b i),
          neg_le_abs (fl_residual fp n A x b i -
            (b i - ∑ j : Fin n, A i j * x j))]
    have hdenom :
        lapackBerrDenom n A x b i =
          |b i| + ∑ j : Fin n, |A i j| * |x j| := rfl
    have hres : |residualVec n A x b i| ≤
        eta * lapackBerrDenom n A x b i := by
      unfold residualVec
      calc
        |b i - ∑ j : Fin n, A i j * x j|
            ≤ |fl_residual fp n A x b i| +
                |fl_residual fp n A x b i -
                  (b i - ∑ j : Fin n, A i j * x j)| := htri
        _ ≤ |fl_residual fp n A x b i| +
              gamma fp (n + 1) * lapackBerrDenom n A x b i := by
            exact add_le_add_right (by simpa [lapackBerrDenom] using hreserr) _
        _ ≤ eta * lapackBerrDenom n A x b i := hcert i
    calc
      |residualVec n A x b i|
          ≤ eta * lapackBerrDenom n A x b i := hres
      _ = eta * (∑ j : Fin n, |A i j| * |x j| + |b i|) := by
          rw [hdenom]
          ring
  exact oettli_prager_sufficient n A x b
    (fun i j => |A i j|) (fun i => |b i|) eta
    heta_nonneg (fun i j => abs_nonneg _) (fun i => abs_nonneg _) hBound

end LeanFpAnalysis.FP
