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

/-- A coefficient-weighted stage sum in an arbitrary real state module. -/
noncomputable def p18ModuleStageSum {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ} (weights : Fin s → ℝ)
    (values : Fin s → State) : State :=
  ∑ j : Fin s, weights j • values j

/-- One execution of the original additive Runge--Kutta method (3.1), together
with the comparison scheme obtained by replacing `F^epsilon` by `F`.

Using (3.1) avoids choosing a side in the paper's sign conflict: equation
(2.3) gives `epsilon * tau = F - F^epsilon`, whereas (3.2) prints the signs
obtained from the opposite convention. The operator equation below records
(2.3), while the stage and output equations record (3.1) directly. -/
structure P18AdditiveRKOneStepRun (State : Type*) [AddCommGroup State]
    [Module ℝ State] (s : ℕ) where
  stage_count_pos : 0 < s
  step : ℝ
  epsilon : ℝ
  epsilon_ne_zero : epsilon ≠ 0
  initial : State
  referenceNext : State
  F : State → State
  FEpsilon : State → State
  tau : State → State
  operator_perturbation : ∀ y,
    epsilon • tau y = F y - FEpsilon y
  a : Fin s → Fin s → ℝ
  aPerturbation : Fin s → Fin s → ℝ
  b : Fin s → ℝ
  bPerturbation : Fin s → ℝ
  schemeStages : Fin s → State
  perturbedStages : Fin s → State
  schemeNext : State
  perturbedNext : State
  scheme_stage_equation : ∀ i,
    schemeStages i =
      initial +
        step • p18ModuleStageSum (a i) (fun j => F (schemeStages j)) +
        step • p18ModuleStageSum (aPerturbation i)
          (fun j => F (schemeStages j))
  scheme_output_equation :
    schemeNext =
      initial +
        step • p18ModuleStageSum b (fun j => F (schemeStages j)) +
        step • p18ModuleStageSum bPerturbation
          (fun j => F (schemeStages j))
  perturbed_stage_equation : ∀ i,
    perturbedStages i =
      initial +
        step • p18ModuleStageSum (a i) (fun j => F (perturbedStages j)) +
        step • p18ModuleStageSum (aPerturbation i)
          (fun j => FEpsilon (perturbedStages j))
  perturbed_output_equation :
    perturbedNext =
      initial +
        step • p18ModuleStageSum b (fun j => F (perturbedStages j)) +
        step • p18ModuleStageSum bPerturbation
          (fun j => FEpsilon (perturbedStages j))

/-- Total one-step error of the perturbed method. -/
def p18TotalOneStepError {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  run.referenceNext - run.perturbedNext

/-- Approximation error of the unperturbed Runge--Kutta scheme. -/
def p18SchemeOneStepError {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  run.referenceNext - run.schemeNext

/-- Error introduced by replacing the scheme output by the perturbed output. -/
def p18PerturbationOneStepError {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  run.schemeNext - run.perturbedNext

/-- Equation (3.1b) unfolded for the difference between the comparison output
and the perturbed output. -/
noncomputable def p18PerturbationOutputExpansion {State : Type*}
    [AddCommGroup State] [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  (run.step •
      p18ModuleStageSum run.b (fun j => run.F (run.schemeStages j)) +
    run.step •
      p18ModuleStageSum run.bPerturbation
        (fun j => run.F (run.schemeStages j))) -
  (run.step •
      p18ModuleStageSum run.b (fun j => run.F (run.perturbedStages j)) +
    run.step •
      p18ModuleStageSum run.bPerturbation
        (fun j => run.FEpsilon (run.perturbedStages j)))

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

/-- Pointwise coefficient product used in Runge--Kutta order conditions. -/
def p18CoeffHadamard {s : ℕ}
    (x y : Fin s → ℝ) : Fin s → ℝ :=
  fun i => x i * y i

/-- Tolerance used to certify identities from coefficients printed to fifteen
decimal places. -/
noncomputable def p18PrintedCoeffTolerance : ℝ :=
  2 / 10 ^ 15

/-- The full-precision Method 4s3pC matrix printed on page 18. -/
noncomputable def p18Method4s3pCA : Fin 4 → Fin 4 → ℝ :=
  !![0, 0, 0, 0;
     -0.050470366527530, 0, 0, 0;
     0.368613367355336, 0.273504374252976, 0, 0;
     1.803794668975043, 0.097485042980759, -1.895660952342050, 0]

/-- The perturbation matrix `A^epsilon` for Method 4s3pC. -/
noncomputable def p18Method4s3pCAPerturbation : Fin 4 → Fin 4 → ℝ :=
  !![0.511243008730995, 0, 0, 0;
     -1.999347282862640, 1.957161067302390, 0, 0;
     0.443312893511937, -0.573131033672219, 0.128283796414019, 0;
     -2, -0.160330320741428, 0.579597314161362, 1.484688928981990]

/-- The Method 4s3pC output weights `b`. -/
noncomputable def p18Method4s3pCB : Fin 4 → ℝ :=
  ![0.002837446974069, 0.336264433650450,
    0.806376720267787, -0.145478600892306]

/-- The Method 4s3pC perturbation output weights `b^epsilon`. -/
noncomputable def p18Method4s3pCBPerturbation : Fin 4 → ℝ :=
  ![0, 0, 0, 0]

/-- The all-ones vector for the four-stage Method 4s3pC conditions. -/
noncomputable def p18Method4s3pCE : Fin 4 → ℝ :=
  ![1, 1, 1, 1]

/-- The Method 4s3pC full-precision nodes `c = A*e`. -/
noncomputable def p18Method4s3pCC : Fin 4 → ℝ :=
  p18CoeffMatVec p18Method4s3pCA p18Method4s3pCE

/-- The Method 4s3pC perturbation nodes `c^epsilon = A^epsilon*e`. -/
noncomputable def p18Method4s3pCCPerturbation : Fin 4 → ℝ :=
  p18CoeffMatVec p18Method4s3pCAPerturbation p18Method4s3pCE

/-- The combined Method 4s3pC matrix `A tilde`. -/
noncomputable def p18Method4s3pCATilde : Fin 4 → Fin 4 → ℝ :=
  p18CoeffMatAdd p18Method4s3pCA p18Method4s3pCAPerturbation

/-- The combined Method 4s3pC nodes `c tilde`. -/
noncomputable def p18Method4s3pCCTilde : Fin 4 → ℝ :=
  p18Add p18Method4s3pCC p18Method4s3pCCPerturbation

/-- The combined Method 4s3pC weights `b tilde`. -/
noncomputable def p18Method4s3pCBTilde : Fin 4 → ℝ :=
  p18Add p18Method4s3pCB p18Method4s3pCBPerturbation

/-- An exact additive Runge--Kutta tableau. The Method 4s3pC decimals are only
a printed representation of such a tableau; the paper does not identify the
unprinted exact values. -/
structure P18AdditiveRKTableau (s : ℕ) where
  A : Fin s → Fin s → ℝ
  APerturbation : Fin s → Fin s → ℝ
  b : Fin s → ℝ
  bPerturbation : Fin s → ℝ

noncomputable def p18TableauE {s : ℕ} : Fin s → ℝ :=
  fun _ ↦ 1

noncomputable def p18TableauATilde {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → Fin s → ℝ :=
  p18CoeffMatAdd tableau.A tableau.APerturbation

noncomputable def p18TableauBTilde {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18Add tableau.b tableau.bPerturbation

noncomputable def p18TableauC {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18CoeffMatVec tableau.A p18TableauE

noncomputable def p18TableauCPerturbation {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18CoeffMatVec tableau.APerturbation p18TableauE

noncomputable def p18TableauCTilde {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18Add (p18TableauC tableau) (p18TableauCPerturbation tableau)

/-- All four consistency conditions through order three on page 7. -/
def p18ThirdOrderConsistency {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Prop :=
  p18CoeffDot (p18TableauBTilde tableau) p18TableauE = 1 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18TableauCTilde tableau) = 1 / 2 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffHadamard (p18TableauCTilde tableau)
          (p18TableauCTilde tableau)) = 1 / 3 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCTilde tableau)) = 1 / 6

/-- Every simplified well-behaved-perturbation condition (3.5a)--(3.5f)
through perturbation order three. Conditions that become automatic when
`b^epsilon = 0` remain explicit. -/
def p18SmoothPerturbationOrderThree {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Prop :=
  p18CoeffDot tableau.bPerturbation p18TableauE = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18TableauCTilde tableau) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18TableauCPerturbation tableau) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18TableauCPerturbation tableau) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffHadamard (p18TableauCTilde tableau)
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffHadamard (p18TableauCTilde tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffHadamard (p18TableauCPerturbation tableau)
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffHadamard (p18TableauCPerturbation tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffHadamard (p18TableauCPerturbation tableau)
          (p18TableauCPerturbation tableau)) = 0

/-- The source-level interpretation of the underlying exact Method 4s3pC
tableau. Exact order conditions are explicit because the rounded decimal table
cannot prove them as literal rational identities. -/
structure P18Method4s3pCSourceModel where
  tableau : P18AdditiveRKTableau 4
  perturbation_weights_zero : tableau.bPerturbation = fun _ ↦ 0
  third_order_consistency : p18ThirdOrderConsistency tableau
  smooth_perturbation_order_three :
    p18SmoothPerturbationOrderThree tableau

/-- The two regularity cases distinguished by the source. The paper describes
but does not uniquely formalize "well behaved", so the tag is kept explicit. -/
inductive P18TauRegime where
  | wellBehaved
  | notWellBehaved
  deriving DecidableEq

/-- A norm-independent two-term interpretation of
`O(h^p) + O(epsilon h^m)` over the supplied asymptotic family. The hidden
constants are existential and the scheme and perturbation contributions stay
separate. -/
def p18UniformTwoTermGlobalOrder {ι : Type*}
    (error schemeError perturbationError step : ι → ℝ)
    (epsilon : ℝ) (p m : ℕ) : Prop :=
  (∀ t, error t = schemeError t + perturbationError t) ∧
    ∃ schemeConstant perturbationConstant : ℝ,
      0 ≤ schemeConstant ∧ 0 ≤ perturbationConstant ∧
        ∀ t,
          |schemeError t| ≤ schemeConstant * step t ^ p ∧
            |perturbationError t| ≤
              perturbationConstant * |epsilon| * step t ^ m

/-- One asymptotic family of stable Method 4s3pC executions. The local errors
are norms of actual additive Runge--Kutta one-step errors. Stability bounds
their accumulated global contributions by the sums of those local errors;
the final global orders are deliberately not fields of this structure. -/
structure P18StableMethod4s3pCBranch
    (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ι : Type*) (method : P18Method4s3pCSourceModel)
    (localPerturbationPower : ℕ) where
  tauRegime : P18TauRegime
  step : ι → ℝ
  epsilon : ℝ
  stepCount : ι → ℕ
  horizon : ℝ
  localSchemeConstant : ℝ
  localPerturbationConstant : ℝ
  stabilityConstant : ℝ
  step_nonneg : ∀ t, 0 ≤ step t
  epsilon_pos : 0 < epsilon
  step_count_pos : ∀ t, 0 < stepCount t
  horizon_nonneg : 0 ≤ horizon
  local_scheme_constant_nonneg : 0 ≤ localSchemeConstant
  local_perturbation_constant_nonneg : 0 ≤ localPerturbationConstant
  stability_constant_nonneg : 0 ≤ stabilityConstant
  F : State → State
  FEpsilon : State → State
  tau : State → State
  computedState : ∀ t, Fin (stepCount t + 1) → State
  exactState : ∀ t, Fin (stepCount t + 1) → State
  oneStep : ∀ t, Fin (stepCount t) →
    P18AdditiveRKOneStepRun State 4
  run_step : ∀ t j, (oneStep t j).step = step t
  run_epsilon : ∀ t j, (oneStep t j).epsilon = epsilon
  run_F : ∀ t j, (oneStep t j).F = F
  run_FEpsilon : ∀ t j, (oneStep t j).FEpsilon = FEpsilon
  run_tau : ∀ t j, (oneStep t j).tau = tau
  run_A : ∀ t j, (oneStep t j).a = method.tableau.A
  run_APerturbation : ∀ t j,
    (oneStep t j).aPerturbation = method.tableau.APerturbation
  run_b : ∀ t j, (oneStep t j).b = method.tableau.b
  run_bPerturbation : ∀ t j,
    (oneStep t j).bPerturbation = method.tableau.bPerturbation
  run_initial : ∀ t j,
    (oneStep t j).initial = computedState t j.castSucc
  run_perturbed_next : ∀ t j,
    (oneStep t j).perturbedNext = computedState t j.succ
  run_reference_next : ∀ t j,
    (oneStep t j).referenceNext = exactState t j.succ
  schemeLocalError : ∀ t, Fin (stepCount t) → ℝ
  perturbationLocalError : ∀ t, Fin (stepCount t) → ℝ
  scheme_local_error_eq : ∀ t j,
    schemeLocalError t j = ‖p18SchemeOneStepError (oneStep t j)‖
  perturbation_local_error_eq : ∀ t j,
    perturbationLocalError t j =
      ‖p18PerturbationOneStepError (oneStep t j)‖
  scheme_local_bound : ∀ t j,
    schemeLocalError t j ≤ localSchemeConstant * step t ^ 4
  perturbation_local_bound : ∀ t j,
    perturbationLocalError t j ≤
      localPerturbationConstant * |epsilon| *
        step t ^ localPerturbationPower
  globalSchemeError : ι → ℝ
  globalPerturbationError : ι → ℝ
  globalError : ι → ℝ
  global_error_eq : ∀ t,
    globalError t =
      ‖exactState t (Fin.last (stepCount t)) -
        computedState t (Fin.last (stepCount t))‖
  global_split : ∀ t,
    globalError t = globalSchemeError t + globalPerturbationError t
  stable_scheme_accumulation : ∀ t,
    |globalSchemeError t| ≤
      stabilityConstant * ∑ j, schemeLocalError t j
  stable_perturbation_accumulation : ∀ t,
    |globalPerturbationError t| ≤
      stabilityConstant * ∑ j, perturbationLocalError t j
  finite_time_horizon : ∀ t,
    (stepCount t : ℝ) * step t ≤ horizon

end HighamBench
