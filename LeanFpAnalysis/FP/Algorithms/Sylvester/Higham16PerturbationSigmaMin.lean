-- Algorithms/Sylvester/Higham16PerturbationSigmaMin.lean
--
-- Sigma-min source wrappers for Higham, Accuracy and Stability of Numerical
-- Algorithms, 2nd ed., Chapter 16.3-16.4, equations (16.25) and (16.28).

import LeanFpAnalysis.FP.Analysis.InverseOpNorm2

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    a positive singular-value lower bound on the Sylvester operator
    instantiates the Frobenius first-order Sylvester perturbation bound. -/
theorem sylvester_perturbation_bound_of_sigmaMin (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound n A B X dA dB dC dX sigma hSigma
      (sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hSigma hSigmaMin)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    the relative Sylvester perturbation bound follows from a positive
    singular-value lower bound on the Sylvester operator. -/
theorem sylvester_relative_perturbation_of_sigmaMin (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation n A B X dA dB dC dX sigma hSigma
      (sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hSigma hSigmaMin)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    a positive singular-value lower bound on the Sylvester operator
    instantiates the Frobenius a posteriori error-residual bound. -/
theorem sylvester_aposteriori_bound_of_sigmaMin (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound n A B C X Xhat sigma hSigma
      (sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hSigma hSigmaMin)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total a posteriori Sylvester residual-error bound from a supplied positive
    singular-value lower bound on the Sylvester operator.

    This removes the nonzero-error side condition by handling the zero-error
    case directly. -/
theorem sylvester_aposteriori_bound_of_sigmaMin_total (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  by_cases hE_ne :
      Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)
  case pos =>
    exact
      sylvester_aposteriori_bound_of_sigmaMin n A B C X Xhat sigma
        hSigma hSigmaMin hExact hE_ne
  case neg =>
    have hE_sq :
        frobNormSq (fun i j => X i j - Xhat i j) = 0 :=
      Classical.not_not.mp hE_ne
    have hE :
        frobNorm (fun i j => X i j - Xhat i j) = 0 := by
      simp [frobNorm_eq_sqrt_frobNormSq, hE_sq]
    rw [hE]
    exact mul_nonneg (by positivity) (frobNorm_nonneg _)

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    the source-shaped relative a posteriori bound follows from a positive
    singular-value lower bound on the Sylvester operator. -/
theorem sylvester_relative_aposteriori_bound_of_sigmaMin (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound n A B C X Xhat sigma hSigma
      (sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hSigma hSigmaMin)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total relative a posteriori Sylvester residual-error bound from a supplied
    positive singular-value lower bound on the Sylvester operator.

    This is the total absolute bound divided by the positive Frobenius norm of
    the exact Sylvester solution. -/
theorem sylvester_relative_aposteriori_bound_of_sigmaMin_total (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  have hAbs :=
    sylvester_aposteriori_bound_of_sigmaMin_total n A B C X Xhat sigma
      hSigma hSigmaMin hExact
  exact div_le_div_of_nonneg_right hAbs (le_of_lt hX_pos)

end LeanFpAnalysis.FP
