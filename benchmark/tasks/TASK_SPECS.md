# Benchmark Task Specifications

Draft status: not finalized.

This file is benchmark-source material.  Do not copy it into generated solver
workspaces.  The generated Condition A and Condition C workspaces should contain
only the task theorem file for the current task plus the allowed environment
for that condition.

Each task below must eventually become an exact Lean theorem statement.  The
Condition A and Condition C versions should target the same theorem shape; the
difference is only which supporting library material is available.

## Global Requirements

- Every task is a floating-point stability analysis for an algorithm.
- The target theorem must be true under the stated assumptions.
- The theorem should not be an exact restatement of an existing
  `LeanFpAnalysis` theorem.
- Early tasks should require small but real composition.
- Later tasks should require multi-result composition.
- Final solver-facing files should not include expected proof routes.

## T01: Scaled Dot Product Backward Stability

Task-local algorithm:

```lean
noncomputable def fl_scaledDot (fp : FPModel) (n : Nat)
    (alpha : Real) (x y : Fin n -> Real) : Real :=
  fp.fl_mul alpha (fl_dotProduct fp n x y)
```

Target shape:

```lean
theorem scaledDot_backward_error
    (fp : FPModel) (n : Nat)
    (alpha : Real) (x y : Fin n -> Real)
    (hn1 : gammaValid fp (n + 1)) :
    exists eta : Fin n -> Real,
      (forall i, abs (eta i) <= gamma fp (n + 1)) /\
      fl_scaledDot fp n alpha x y =
        alpha * sum_i (x i * y i * (1 + eta i))
```

Reason for inclusion: one scalar rounding operation composed with dot-product
backward error.

## T02: Shifted Dot Product Forward Stability

Task-local algorithm:

```lean
noncomputable def fl_shiftedDot (fp : FPModel) (n : Nat)
    (c : Real) (x y : Fin n -> Real) : Real :=
  fp.fl_add c (fl_dotProduct fp n x y)
```

Target shape:

```lean
theorem shiftedDot_forward_error
    (fp : FPModel) (n : Nat)
    (c : Real) (x y : Fin n -> Real)
    (hn1 : gammaValid fp (n + 1)) :
    abs (fl_shiftedDot fp n c x y - (c + sum_i (x i * y i))) <=
      gamma fp (n + 1) * (abs c + sum_i (abs (x i) * abs (y i)))
```

Reason for inclusion: forward-error analysis for an affine dot-product kernel.

## T03: Residual Stopping Certificate

Algorithm: conventional residual computation
`fl_residual fp n A x b`.

Target shape:

```lean
theorem residual_stopping_certificate
    (fp : FPModel) (n : Nat)
    (A : Fin n -> Fin n -> Real) (x b tau : Fin n -> Real)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (htau_nonneg : forall i, 0 <= tau i)
    (hsmall : forall i, abs (fl_residual fp n A x b i) <= tau i) :
    forall i,
      abs (b i - sum_j (A i j * x j)) <=
        tau i + gamma fp (n + 1) *
          (abs (b i) + sum_j (abs (A i j) * abs (x j)))
```

Reason for inclusion: turns a computed residual test into a certified exact
residual bound.

## T04: Triangular Solve Residual Certificate

Algorithm: forward substitution for a lower-triangular system.

Target shape:

```lean
theorem forwardSub_residual_certificate
    (fp : FPModel) (n : Nat)
    (L : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (hdiag : forall i, L i i != 0)
    (hlower : forall i j, i.val < j.val -> L i j = 0)
    (hn : gammaValid fp n) :
    let xhat := fl_forwardSub fp n L b
    forall i,
      abs (b i - sum_j (L i j * xhat j)) <=
        gamma fp n * sum_j (abs (L i j) * abs (xhat j))
```

Reason for inclusion: converts backward stability into an original-system
residual bound.

## T05: BLAS GEMV Backward Stability

Task-local algorithm:

```lean
noncomputable def fl_gemv (fp : FPModel) (m n : Nat)
    (alpha beta : Real)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) (y : Fin m -> Real) :
    Fin m -> Real :=
  fun i =>
    fp.fl_add
      (fp.fl_mul alpha (fl_matVec fp m n A x i))
      (fp.fl_mul beta (y i))
```

Target shape:

```lean
theorem gemv_backward_error
    (fp : FPModel) (m n : Nat)
    (alpha beta : Real)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) (y : Fin m -> Real)
    (hn2 : gammaValid fp (n + 2)) :
    exists DeltaA : Fin m -> Fin n -> Real,
    exists Deltay : Fin m -> Real,
      (forall i j, abs (DeltaA i j) <= gamma fp (n + 2) * abs (A i j)) /\
      (forall i, abs (Deltay i) <= gamma fp (n + 2) * abs (y i)) /\
      forall i,
        fl_gemv fp m n alpha beta A x y i =
          alpha * sum_j ((A i j + DeltaA i j) * x j) +
          beta * (y i + Deltay i)
```

Reason for inclusion: realistic BLAS-style kernel not already packaged as a
library theorem.

## T06: Combined Triangular Solve As One Backward Error

Algorithm: solve `L*U*x = b` by forward substitution followed by back
substitution.

Target shape:

```lean
theorem triangularSolve_single_backward_error
    (fp : FPModel) (n : Nat)
    (L U : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (hLdiag : forall i, L i i != 0)
    (hUdiag : forall i, U i i != 0)
    (hLT : forall i j, i.val < j.val -> L i j = 0)
    (hUT : forall i j, j.val < i.val -> U i j = 0)
    (hn : gammaValid fp n) :
    let yhat := fl_forwardSub fp n L b
    let xhat := fl_backSub fp n U yhat
    exists DeltaA : Fin n -> Fin n -> Real,
      (forall i j,
        abs (DeltaA i j) <=
          (2 * gamma fp n + gamma fp n ^ 2) *
            sum_k (abs (L i k) * abs (U k j))) /\
      forall i,
        sum_j ((sum_k (L i k * U k j) + DeltaA i j) * xhat j) = b i
```

Reason for inclusion: composes the two triangular-solve backward errors into a
single perturbation of `A = L*U`.

## T07: LU Solve With Growth-Scaled Backward Error

Algorithm: solve using computed LU factors.

Target shape:

```lean
theorem lu_solve_growth_backward_error
    (fp : FPModel) (n : Nat)
    (A Lhat Uhat : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (rho : Real)
    (hLdiag : forall i, Lhat i i != 0)
    (hUdiag : forall i, Uhat i i != 0)
    (hLU : LUBackwardError n A Lhat Uhat (gamma fp n))
    (hn : gammaValid fp n)
    (hrho_nonneg : 0 <= rho)
    (hgrowth : forall i j,
      sum_k (abs (Lhat i k) * abs (Uhat k j)) <= rho * abs (A i j)) :
    let yhat := fl_forwardSub fp n Lhat b
    let xhat := fl_backSub fp n Uhat yhat
    exists DeltaA : Fin n -> Fin n -> Real,
      (forall i j,
        abs (DeltaA i j) <=
          ((3 * gamma fp n + gamma fp n ^ 2) * rho) * abs (A i j)) /\
      forall i, sum_j ((A i j + DeltaA i j) * xhat j) = b i
```

Reason for inclusion: turns the LU factor-product bound into a relative
backward error for the input matrix.

## T08: Cholesky Solve With Growth-Scaled Backward Error

Algorithm: solve using a computed Cholesky factor.

Target shape:

```lean
theorem cholesky_solve_growth_backward_error
    (fp : FPModel) (n : Nat)
    (A Rhat : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (rho : Real)
    (hRdiag : forall i, Rhat i i != 0)
    (hChol : CholeskyBackwardError n A Rhat (gamma fp (n + 1)))
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * n + 1))
    (hrho_nonneg : 0 <= rho)
    (hgrowth : forall i j,
      sum_k (abs (Rhat k i) * abs (Rhat k j)) <= rho * abs (A i j)) :
    let RhatT := fun i j => Rhat j i
    let yhat := fl_forwardSub fp n RhatT b
    let xhat := fl_backSub fp n Rhat yhat
    exists DeltaA : Fin n -> Fin n -> Real,
      (forall i j,
        abs (DeltaA i j) <= gamma fp (3 * n + 1) * rho * abs (A i j)) /\
      forall i, sum_j ((A i j + DeltaA i j) * xhat j) = b i
```

Reason for inclusion: same stability conversion pattern as LU, but through
Cholesky factorization and different gamma constants.

## T09: One-Step Iterative Refinement

Algorithm: compute the conventional residual, solve the correction equation
with a backward-stable abstract solver, and update once exactly.

Target shape:

```lean
theorem one_step_refinement_conventional_residual
    (fp : FPModel) (n : Nat)
    (A : Fin n -> Fin n -> Real)
    (b x0 dhat : Fin n -> Real)
    (DeltaA : Fin n -> Fin n -> Real)
    (mu : Real)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (hmu_nonneg : 0 <= mu)
    (hDelta : forall i j, abs (DeltaA i j) <= mu * abs (A i j))
    (hsolve : forall i,
      sum_j ((A i j + DeltaA i j) * dhat j) =
        fl_residual fp n A x0 b i) :
    let x1 := fun i => x0 i + dhat i
    forall i,
      abs (b i - sum_j (A i j * x1 j)) <=
        mu * sum_j (abs (A i j) * abs (dhat j)) +
        gamma fp (n + 1) *
          (abs (b i) + sum_j (abs (A i j) * abs (x0 j)))
```

Reason for inclusion: composes residual computation with a correction-solve
backward error and the one-step refinement residual identity.

## T10: Stationary Iteration With Inexact Triangular Local Solves

Algorithm: stationary iteration where the local solve with `M` is performed by
floating-point forward substitution.

Target shape:

```lean
theorem stationary_forwardSub_residual_bound
    (fp : FPModel) (n : Nat) (hnpos : 0 < n)
    (A M N Minv : Fin n -> Fin n -> Real)
    (b x : Fin n -> Real)
    (xhat : Nat -> Fin n -> Real)
    (q mu : Real) (m : Nat)
    (hS : SplittingSpec n A M N Minv)
    (hAx : forall i, sum_j (A i j * x j) = b i)
    (hMdiag : forall i, M i i != 0)
    (hMLT : forall i j, i.val < j.val -> M i j = 0)
    (hgamma : gammaValid fp n)
    (hstep : forall k,
      xhat (k + 1) =
        fl_forwardSub fp n M
          (fun i => sum_j (N i j * xhat k j) + b i))
    (hq_nonneg : 0 <= q)
    (hq_lt_one : q < 1)
    (hH : infNorm hnpos (dualIterMatrix n N Minv) <= q)
    (hmu_nonneg : 0 <= mu)
    (hlocal : forall k,
      infNormVec hnpos
        (fun i => gamma fp n * sum_j (abs (M i j) * abs (xhat (k + 1) j)))
        <= mu) :
    infNormVec hnpos (fun i => b i - sum_j (A i j * xhat (m + 1) j)) <=
      q ^ (m + 1) *
        infNormVec hnpos (fun i => b i - sum_j (A i j * xhat 0 j)) +
      mu * infNorm hnpos (matSub_id n (dualIterMatrix n N Minv)) / (1 - q)
```

Reason for inclusion: bridges a concrete floating-point triangular local solve
to the abstract stationary-iteration residual bound.

