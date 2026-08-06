import HighamBench.P11Definitions

namespace HighamBench

/-- P11-T2: the exact orthogonality-defect identity used to derive (7). -/
theorem p11_t2_orthogonality_defect_identity {n : ℕ}
    (A dA Q R Rinv : P11Matrix n)
    (hQR : p11MatMul n Q R = A + dA)
    (hInv : p11MatMul n R Rinv = p11Identity n) :
    p11OrthogonalityDefect Q =
      p11MatMul n
        (p11MatMul n (p11Transpose Rinv) (p11DefectCore A dA R)) Rinv := by
  -- PROOF_START
  sorry

end HighamBench
