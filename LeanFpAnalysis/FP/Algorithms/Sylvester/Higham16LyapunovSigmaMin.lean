-- Algorithms/Sylvester/Higham16LyapunovSigmaMin.lean
--
-- Source-facing sigma-min wrappers for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed., Chapter 16.3, equation (16.27).

import LeanFpAnalysis.FP.Analysis.InverseOpNorm2

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    a positive singular-value lower bound for the Lyapunov operator instantiates
    the Lyapunov condition-number predicate with the inverse-operator constant
    `M = 1 / sigma`.

    This is the sigma-min version of the safe condition wrapper. It uses
    `lyapunovInverseOpBound_of_sigmaMin`, so the supplied hypothesis is the
    operator lower bound itself, not a black-box inverse-bound certificate. -/
theorem lyapunovCond_of_sigmaMin_isLyapunovConditionFirstOrderBound (n : ℕ)
    (A X : Fin n → Fin n → ℝ) (alpha gamma sigma : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hSigmaMin : ∀ Y : Fin n → Fin n → ℝ,
      sigma * frobNorm Y ≤ frobNorm (lyapunovOp n A Y)) :
    LyapunovConditionFirstOrderBound n A X alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma)) := by
  have hInv := lyapunovInverseOpBound_of_sigmaMin n A sigma hsigma hSigmaMin
  have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
  exact lyapunovCond_of_inverseOpBound_isLyapunovConditionFirstOrderBound n
    A X alpha gamma (1 / sigma) halpha hgamma hMnn hX hInv

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    sigma-min Lyapunov first-order perturbation bound. If the Lyapunov operator
    satisfies `sigma * ||Y||_F <= ||L(Y)||_F` for all `Y`, then the printed
    relative bound follows with
    `lyapunovCond_of_inverseOpBound ... (1 / sigma)`.

    Scope: this is an exact-arithmetic theorem from a supplied singular-value
    lower-bound certificate for `L`. The remaining unproved glue, documented in
    `InverseOpNorm2.lean`, is the automatic construction of this hypothesis from
    the concrete vec/Kronecker coefficient via a Frobenius/vec isometry. -/
theorem H16_eq16_27_lyapunov_condition_of_sigmaMin (n : ℕ)
    (A X DeltaA DeltaC DeltaX : Fin n → Fin n → ℝ)
    (alpha gamma sigma eps : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 ≤ eps)
    (hX : 0 < frobNorm X)
    (hSigmaMin : ∀ Y : Fin n → Fin n → ℝ,
      sigma * frobNorm Y ≤ frobNorm (lyapunovOp n A Y))
    (hDeltaA : frobNorm DeltaA ≤ eps * alpha)
    (hDeltaC : frobNorm DeltaC ≤ eps * gamma)
    (hLin : ∀ i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X ≤
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  have hCond :=
    lyapunovCond_of_sigmaMin_isLyapunovConditionFirstOrderBound n
      A X alpha gamma sigma halpha hgamma hsigma hX hSigmaMin
  have hPsinn : 0 ≤ lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) := by
    unfold lyapunovCond_of_inverseOpBound
    have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
    have hnum : 0 ≤ 2 * alpha * frobNorm X + gamma := by
      have hXnn : 0 ≤ frobNorm X := le_of_lt hX
      nlinarith [le_of_lt halpha, le_of_lt hgamma, hXnn]
    positivity
  exact lyapunov_relative_first_order_bound_of_condition n
    A X DeltaA DeltaC DeltaX alpha gamma
    (lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma)) eps
    hCond hX hPsinn halpha hgamma heps hDeltaA hDeltaC hLin

end LeanFpAnalysis.FP
