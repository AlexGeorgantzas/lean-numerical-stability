import HighamBench.P15Definitions

namespace HighamBench

/-- P15-T3: exact-remainder composition behind Theorem 4.5.  The factorization
perturbation and the two triangular-solve perturbations produce one backward
perturbation of `A` and one perturbation of `v`; the displayed radii retain the
finite cross terms hidden by the paper's `O(u*epsilon)` and `O(u^2)` notation. -/
theorem p15_t3_blr_lu_solve_backward_error {n : ℕ}
    (A L U factorError lowerError upperError : P15Matrix n)
    (v y computed rhsLower rhsUpper : P15Vector n)
    (xi epsilon gammaP gammaC factorRemainder : ℝ)
    (hgammaP : 0 ≤ gammaP) (hgammaPsmall : gammaP < 1)
    (hgammaC : 0 ≤ gammaC)
    (hfactor : p15MatMul L U = A + factorError)
    (hlower : p15MatVec (L + lowerError) y = v + rhsLower)
    (hupper : p15MatVec (U + upperError) computed = y + rhsUpper)
    (hfactorBound :
      p15FrobNorm factorError ≤
        (xi * epsilon + gammaP) * p15FrobNorm A +
          gammaC * p15FrobNorm L * p15FrobNorm U + factorRemainder)
    (hlowerBound : p15FrobNorm lowerError ≤ gammaC * p15FrobNorm L)
    (hupperBound : p15FrobNorm upperError ≤ gammaC * p15FrobNorm U)
    (hrhsLower : p15VecNorm rhsLower ≤ gammaP * p15VecNorm v)
    (hrhsUpper : p15VecNorm rhsUpper ≤ gammaP * p15VecNorm y) :
    p15MatVec
        (A + p15ComposedMatrixError factorError lowerError upperError L U)
        computed =
      v + p15ComposedRhsError rhsLower rhsUpper L lowerError ∧
    p15FrobNorm
        (p15ComposedMatrixError factorError lowerError upperError L U) ≤
      (xi * epsilon + gammaP) * p15FrobNorm A +
        (3 * gammaC + gammaC ^ 2) * p15FrobNorm L * p15FrobNorm U +
          factorRemainder ∧
    p15VecNorm (p15ComposedRhsError rhsLower rhsUpper L lowerError) ≤
      gammaP * p15VecNorm v +
        (gammaP * (1 + gammaC) ^ 2 / (1 - gammaP)) *
          p15FrobNorm L * p15FrobNorm U * p15VecNorm computed := by
  -- PROOF_START
  sorry

end HighamBench
