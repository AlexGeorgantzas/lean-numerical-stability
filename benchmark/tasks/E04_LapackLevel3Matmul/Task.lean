import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def rectInfNorm (m n : ℕ) (hm : 0 < m)
    (A : Fin m → Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
    (fun i => ∑ j : Fin n, |A i j|)

theorem lapack_level3_matmul_forward_error
    (fp : FPModel) (m n p : ℕ) (hm : 0 < m) (hnpos : 0 < n)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hn : gammaValid fp n) :
    rectInfNorm m p hm
        (fun i j => fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j) ≤
      gamma fp n * rectInfNorm m n hm A * rectInfNorm n p hnpos B := by
  sorry

end LeanFpAnalysis.FP
