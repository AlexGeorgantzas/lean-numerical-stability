import HighamBench.P07Definitions

namespace HighamBench

/-- P07-T1: the full-rank conclusion in Lemma 3.2. An additive perturbation
strictly smaller than the original map's lower singular-value margin preserves
injectivity of the computed preconditioned matrix. -/
theorem p07_t1_perturbed_preconditioned_map_injective
    {m n : ℕ} (Y ΔY : Fin m → Fin n → ℝ) (μ η : ℝ)
    (hLower : p07RectLowerBound Y μ)
    (hDelta : p07RectOpNorm2Le ΔY η)
    (hStrict : η < μ) :
    Function.Injective (p07MatVec (fun i j ↦ Y i j + ΔY i j)) := by
  -- PROOF_START
  sorry

end HighamBench
