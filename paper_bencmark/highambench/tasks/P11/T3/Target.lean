import HighamBench.P11Definitions

namespace HighamBench

/-- P11-T3: the all-prefix spectral loss-of-orthogonality bound in
Theorem 1(7), with the source's hidden second-order term exposed. -/
theorem p11_t3_orthogonality_defect_bound {m n : ℕ}
    (run : P11CGSPTheorem1Run m n) :
    ∀ k : Fin n,
      p11OpNorm2
          (p11RectOrthogonalityDefect (p11ColumnPrefix run.Q k)) ≤
        p11C4 m (k.val + 1) *
              p11Kappa2 (p11LeadingBlock run.R k)
                  (run.leadingInverse k) ^ 2 *
            run.epsilonM +
          p11Theorem1OrthogonalityRemainderCoeff run k *
            run.epsilonM ^ 2 := by
  -- PROOF_START
  sorry

end HighamBench
