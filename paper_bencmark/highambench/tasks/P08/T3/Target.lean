import HighamBench.P08Definitions

namespace HighamBench

open scoped BigOperators

/-- P08-T3: the induction core of Lemma 4.3.  A componentwise affine residual
recurrence with a nonnegative propagation matrix has the exact finite geometric
budget displayed below. -/
theorem p08_t3_componentwise_affine_recurrence
    {n : ℕ} (B : Fin n → Fin n → ℝ)
    (q d : ℕ → Fin n → ℝ) (s : Fin n → ℝ)
    (hB : ∀ i j, 0 ≤ B i j)
    (hs : ∀ i, 0 ≤ s i)
    (hd : ∀ m i, |d m i| ≤ s i)
    (hStep : ∀ m i, q (m + 1) i = p08MatVec B (q m) i + d m i) :
    ∀ m i, |q (m + 1) i| ≤
      p08MatVec (p08MatPow B (m + 1)) (fun j ↦ |q 0 j|) i +
        ∑ k ∈ Finset.range (m + 1), p08MatVec (p08MatPow B k) s i := by
  -- PROOF_START
  sorry

end HighamBench
