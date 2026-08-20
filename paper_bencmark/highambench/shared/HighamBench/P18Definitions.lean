import HighamBench.Core

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

/-- Subtract two finite state vectors. -/
def p18Sub {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i - y i

/-- Scale a finite error vector. -/
def p18Scale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a * x i

/-- A coefficient-weighted sum of Runge--Kutta stage vectors. -/
noncomputable def p18StageSum {n s : ℕ}
    (weights : Fin s → ℝ) (values : Fin s → Fin n → ℝ) : Fin n → ℝ :=
  fun k => ∑ j : Fin s, weights j * values j k

/-- One step of the additive Runge--Kutta formulation (3.2), together with
the unperturbed scheme obtained by setting `epsilon = 0`.

The two stage families and two outputs are constrained by the displayed
algorithm equations. They are not arbitrary error vectors. The finite-real
model treats `tau` as the perturbation operator and does not choose between
the inconsistent sign conventions printed in equations (2.3) and (3.2): the
fields below record equation (3.2)'s positive-`epsilon` convention explicitly. -/
structure P18AdditiveRKOneStepRun (n s : ℕ) where
  dimension_pos : 0 < n
  stage_count_pos : 0 < s
  step : ℝ
  epsilon : ℝ
  step_nonneg : 0 ≤ step
  epsilon_nonneg : 0 ≤ epsilon
  initial : Fin n → ℝ
  exactNext : Fin n → ℝ
  F : (Fin n → ℝ) → Fin n → ℝ
  tau : (Fin n → ℝ) → Fin n → ℝ
  aTilde : Fin s → Fin s → ℝ
  aPerturbation : Fin s → Fin s → ℝ
  bTilde : Fin s → ℝ
  bPerturbation : Fin s → ℝ
  schemeStages : Fin s → Fin n → ℝ
  perturbedStages : Fin s → Fin n → ℝ
  schemeNext : Fin n → ℝ
  perturbedNext : Fin n → ℝ
  scheme_stage_equation : ∀ i,
    schemeStages i =
      p18Add initial
        (p18Scale step
          (p18StageSum (aTilde i) (fun j => F (schemeStages j))))
  scheme_output_equation :
    schemeNext =
      p18Add initial
        (p18Scale step
          (p18StageSum bTilde (fun j => F (schemeStages j))))
  perturbed_stage_equation : ∀ i,
    perturbedStages i =
      p18Add initial
        (p18Add
          (p18Scale step
            (p18StageSum (aTilde i) (fun j => F (perturbedStages j))))
          (p18Scale (epsilon * step)
            (p18StageSum (aPerturbation i)
              (fun j => tau (perturbedStages j)))))
  perturbed_output_equation :
    perturbedNext =
      p18Add initial
        (p18Add
          (p18Scale step
            (p18StageSum bTilde (fun j => F (perturbedStages j))))
          (p18Scale (epsilon * step)
            (p18StageSum bPerturbation
              (fun j => tau (perturbedStages j)))))

/-- Total one-step error of the perturbed method. -/
def p18TotalOneStepError {n s : ℕ}
    (run : P18AdditiveRKOneStepRun n s) : Fin n → ℝ :=
  p18Sub run.exactNext run.perturbedNext

/-- Approximation error of the unperturbed Runge--Kutta scheme. -/
def p18SchemeOneStepError {n s : ℕ}
    (run : P18AdditiveRKOneStepRun n s) : Fin n → ℝ :=
  p18Sub run.exactNext run.schemeNext

/-- Error introduced by replacing the scheme output by the perturbed output. -/
def p18PerturbationOneStepError {n s : ℕ}
    (run : P18AdditiveRKOneStepRun n s) : Fin n → ℝ :=
  p18Sub run.schemeNext run.perturbedNext

/-- Finite coefficient dot product used in the P18 order conditions. -/
noncomputable def p18CoeffDot {s : ℕ}
    (x y : Fin s → ℝ) : ℝ :=
  ∑ i : Fin s, x i * y i

/-- Finite coefficient matrix-vector product. -/
noncomputable def p18CoeffMatVec {s : ℕ}
    (A : Fin s → Fin s → ℝ) (x : Fin s → ℝ) : Fin s → ℝ :=
  fun i => ∑ j : Fin s, A i j * x j

/-- Pointwise addition of two coefficient matrices. -/
def p18CoeffMatAdd {s : ℕ}
    (A B : Fin s → Fin s → ℝ) : Fin s → Fin s → ℝ :=
  fun i j => A i j + B i j

/-- Absolute-value dot product in the nonsmooth perturbation conditions (3.4). -/
noncomputable def p18CoeffAbsDot {s : ℕ}
    (x y : Fin s → ℝ) : ℝ :=
  ∑ i : Fin s, |x i| * |y i|

/-- The two-stage corrected implicit-midpoint coefficient matrix `A` printed
after equation (4.1). -/
noncomputable def p18CorrectedMidpointA : Fin 2 → Fin 2 → ℝ :=
  !![0, 0; (1 / 2 : ℝ), 0]

/-- The corrected implicit-midpoint node vector `c`. -/
noncomputable def p18CorrectedMidpointC : Fin 2 → ℝ :=
  ![0, (1 / 2 : ℝ)]

/-- The corrected implicit-midpoint output weights `b`. -/
noncomputable def p18CorrectedMidpointB : Fin 2 → ℝ :=
  ![0, 1]

/-- The low-precision coefficient matrix `A^epsilon` in equation (4.1). -/
noncomputable def p18CorrectedMidpointAPerturbation : Fin 2 → Fin 2 → ℝ :=
  !![(1 / 2 : ℝ), 0; 0, 0]

/-- The low-precision node vector `c^epsilon`. -/
noncomputable def p18CorrectedMidpointCPerturbation : Fin 2 → ℝ :=
  ![(1 / 2 : ℝ), 0]

/-- The low-precision output weights `b^epsilon`. -/
noncomputable def p18CorrectedMidpointBPerturbation : Fin 2 → ℝ :=
  ![0, 0]

/-- The combined corrected-midpoint matrix `A tilde`. -/
noncomputable def p18CorrectedMidpointATilde : Fin 2 → Fin 2 → ℝ :=
  !![(1 / 2 : ℝ), 0; (1 / 2 : ℝ), 0]

/-- The combined corrected-midpoint nodes `c tilde`. -/
noncomputable def p18CorrectedMidpointCTilde : Fin 2 → ℝ :=
  ![(1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- The combined corrected-midpoint output weights `b tilde`. -/
noncomputable def p18CorrectedMidpointBTilde : Fin 2 → ℝ :=
  ![0, 1]

/-- The all-ones coefficient vector `e` for the two-stage order conditions. -/
noncomputable def p18CorrectedMidpointE : Fin 2 → ℝ :=
  ![1, 1]

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
