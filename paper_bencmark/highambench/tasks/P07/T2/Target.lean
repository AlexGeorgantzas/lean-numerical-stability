import HighamBench.P07Definitions

namespace HighamBench

/-- P07-T2: the exact four-term backward-error decomposition in the proof of
Theorem 3.5, together with its compositional operator-norm budget. -/
theorem p07_t2_backward_error_product_budget
    {m n : ℕ} (Y ΔY : Fin m → Fin n → ℝ)
    (R ΔR : Fin n → Fin n → ℝ) (A : Fin m → Fin n → ℝ)
    (e₀ eY r y eR : ℝ)
    (heY : 0 ≤ eY) (hy : 0 ≤ y)
    (hBase : p07RectOpNorm2Le
      (fun i j ↦ p07RectMatMul Y R i j - A i j) e₀)
    (hDeltaY : p07RectOpNorm2Le ΔY eY)
    (hR : p07RectOpNorm2Le R r)
    (hY : p07RectOpNorm2Le Y y)
    (hDeltaR : p07RectOpNorm2Le ΔR eR) :
    p07RectOpNorm2Le (p07BackwardError Y ΔY R ΔR A)
      (e₀ + (eY * r + (y * eR + eY * eR))) := by
  -- PROOF_START
  sorry

end HighamBench
