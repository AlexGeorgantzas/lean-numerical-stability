import HighamBench.P11Definitions

namespace HighamBench

/-- P11-T3: an exact finite-budget version of Theorem 1's bound (7). -/
theorem p11_t3_orthogonality_defect_bound {n : ℕ}
    (A dA Q R Rinv : P11Matrix n) (e a d rho : ℝ)
    (hQR : p11MatMul n Q R = A + dA)
    (hInv : p11MatMul n R Rinv = p11Identity n)
    (he : 0 ≤ e) (ha : 0 ≤ a) (hd : 0 ≤ d) (hrho : 0 ≤ rho)
    (hE : p11FrobNorm (p11NormalEquationResidual A R) ≤ e)
    (hA : p11FrobNorm A ≤ a) (hdA : p11FrobNorm dA ≤ d)
    (hRinv : p11FrobNorm Rinv ≤ rho) :
    p11FrobNorm (p11OrthogonalityDefect Q) ≤
      rho ^ 2 * (e + 2 * a * d + d ^ 2) := by
  -- PROOF_START
  sorry

end HighamBench
