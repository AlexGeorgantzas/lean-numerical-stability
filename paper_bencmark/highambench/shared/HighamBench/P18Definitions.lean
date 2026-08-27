import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Sqrt

namespace HighamBench

open scoped BigOperators

/-- Paper-scoped squared Euclidean norm for finite Runge--Kutta error vectors. -/
noncomputable def p18VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Paper-scoped Euclidean norm for finite Runge--Kutta error vectors. -/
noncomputable def p18VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p18VecNorm2Sq x)

/-- Add the scheme and perturbation error components. -/
def p18Add {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i + y i

/-- Scale a finite error vector. -/
def p18Scale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a * x i

/-- Exact representative of the corrected-midpoint error envelope on page 11. -/
def p18CorrectedMidpointError {n : ℕ} (h epsilon : ℝ)
    (scheme perturbation : Fin n → ℝ) : Fin n → ℝ :=
  p18Add (p18Scale (h ^ 2) scheme)
    (p18Scale (epsilon * h ^ 2) perturbation)

/-- Exact representative of Method 4s3pC's smooth-perturbation error. -/
def p18SmoothMethodError {n : ℕ} (h epsilon : ℝ)
    (scheme perturbation : Fin n → ℝ) : Fin n → ℝ :=
  p18Add (p18Scale (h ^ 3) scheme)
    (p18Scale (epsilon * h ^ 3) perturbation)

/-- Exact representative of Method 4s3pC's nonsmooth-perturbation error. -/
def p18NonsmoothMethodError {n : ℕ} (h epsilon : ℝ)
    (scheme perturbation : Fin n → ℝ) : Fin n → ℝ :=
  p18Add (p18Scale (h ^ 3) scheme)
    (p18Scale (epsilon * h ^ 2) perturbation)

end HighamBench
