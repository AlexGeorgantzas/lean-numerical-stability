import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace HighamBench

open scoped BigOperators Matrix.Norms.L2Operator

/-- Paper-scoped squared Euclidean norm for finite GMRES error vectors. -/
noncomputable def p19VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Paper-scoped Euclidean norm for finite GMRES error vectors. -/
noncomputable def p19VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p19VecNorm2Sq x)

/-- Add two paper-scoped finite error vectors. -/
def p19Add {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i + y i

/-- Scale a paper-scoped finite error vector. -/
def p19Scale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a * x i

/-- Exact four-source representative of the modular error aggregate in (3.8). -/
def p19ModularError {n : ℕ} (alpha beta lambda : ℝ)
    (computationError rhsError gmresError solutionError : Fin n → ℝ) :
    Fin n → ℝ :=
  p19Add (p19Scale alpha computationError)
    (p19Add (p19Scale beta rhsError)
      (p19Add (p19Scale beta gmresError)
        (p19Scale lambda solutionError)))

/-- Exact scalar envelope corresponding to `ξ` in equation (3.8). -/
def p19ModularEnvelope (alpha beta lambda epsilonC epsilonB ug epsilonX : ℝ) : ℝ :=
  alpha * epsilonC + beta * epsilonB + beta * ug + lambda * epsilonX

/-- Paper-scoped exact matrix operator 2-norm. -/
noncomputable def p19OpNorm2 {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  @norm (Matrix (Fin n) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm
    (A : Matrix (Fin n) (Fin n) ℝ)

/-- Paper-scoped condition-number product for a matrix and inverse candidate. -/
noncomputable def p19Kappa2 {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  p19OpNorm2 A * p19OpNorm2 Ainv

/-- Exact scalar envelope represented by the right-preconditioned bound (3.17). -/
noncomputable def p19RightEnvelope {n : ℕ}
    (ug um ua etaR rhoA : ℝ)
    (AMRinv AMRinvInv MR MRinv A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  ug * p19Kappa2 AMRinv AMRinvInv * p19Kappa2 MR MRinv +
    um * etaR * p19Kappa2 MR MRinv +
      ua * p19Kappa2 A Ainv * rhoA

/-- Exact scalar envelope represented by the flexible-preconditioned bound (3.20). -/
noncomputable def p19FlexibleEnvelope {n : ℕ}
    (ug ua rhoA : ℝ)
    (AMRinv AMRinvInv MR MRinv A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  ug * p19Kappa2 AMRinv AMRinvInv * p19Kappa2 MR MRinv +
    ua * p19Kappa2 A Ainv * rhoA

end HighamBench
