import HighamBench.P19Definitions

namespace HighamBench

/-- P19-T1: exact upper perturbation-norm inequality used in equation (C.8). -/
theorem p19_t1_perturbed_basis_product_upper {n : ℕ}
    (storedProduct correctionProduct : Fin n → ℝ) :
    p19VecNorm2 (p19Add storedProduct correctionProduct) ≤
      p19VecNorm2 storedProduct + p19VecNorm2 correctionProduct := by
  -- PROOF_START
  sorry

end HighamBench
