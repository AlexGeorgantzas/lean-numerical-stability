import HighamBench.P06Definitions

namespace HighamBench

/-- P06-T1: equation (4.20)'s deterministic aggregation step. A common
relative Euclidean bound on every backward-error column gives the same
relative Frobenius bound for the whole matrix. -/
theorem p06_t1_columnwise_to_frobenius
    {m n : ℕ} (A ΔA : Fin m → Fin n → ℝ) (η : ℝ)
    (hη : 0 ≤ η)
    (hcol : ∀ j : Fin n,
      p06VecNorm2 (fun i ↦ ΔA i j) ≤
        η * p06VecNorm2 (fun i ↦ A i j)) :
    p06FrobNorm ΔA ≤ η * p06FrobNorm A := by
  -- PROOF_START
  sorry

end HighamBench
