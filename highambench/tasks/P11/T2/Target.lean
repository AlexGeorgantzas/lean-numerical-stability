import HighamBench.P11Definitions

namespace HighamBench

/-- P11-T2: the exact rectangular orthogonality-defect identity used to derive (7). -/
theorem p11_t2_orthogonality_defect_identity {m n : ℕ}
    (hmn : n ≤ m) (k : Fin n)
    (A dA Q : P11RectMatrix m (k.val + 1))
    (R Rinv : P11Matrix (k.val + 1))
    (hQR : p11RectMatMul Q R = A + dA)
    (hInv : p11MatMul (k.val + 1) R Rinv = p11Identity (k.val + 1)) :
    p11RectOrthogonalityDefect Q =
      p11MatMul (k.val + 1)
        (p11MatMul (k.val + 1) (p11Transpose Rinv)
          (p11RectDefectCore A dA R)) Rinv := by
  -- PROOF_START
  sorry

end HighamBench
