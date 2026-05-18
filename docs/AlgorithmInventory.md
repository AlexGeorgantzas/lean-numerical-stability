# Algorithm Implementation Inventory

This note records which algorithmic parts of the library are derived from
explicit rounded operations and which parts are specification-transfer
interfaces. It is intended as an honesty audit for benchmark and thesis claims.

## Classification

- **Rounded implementation**: the library defines a computed object by composing
  `FPModel` operations such as `fp.fl_add`, `fp.fl_sub`, `fp.fl_mul`, and
  `fp.fl_div`, then proves error bounds from those definitions.
- **Hybrid result**: the theorem uses some rounded implementations, but also
  assumes an upstream factorization/error contract.
- **Contract/interface**: the library defines a specification structure or takes
  hypotheses saying that a computed object satisfies an error model, then proves
  consequences from that model.
- **Exact auxiliary**: the file defines exact real-number algebra, matrix
  identities, norms, structural predicates, or perturbation theory; these are not
  floating-point algorithms by themselves.

There are no `sorry`, `admit`, or Lean `axiom` declarations in
`LeanFpAnalysis/FP` at the time of this audit. The distinction below is about
the strength of theorem statements and hypotheses, not about missing proof
holes.

## Rounded Implementations

These are the strongest algorithmic parts of the library. They model the
computed result directly through `FPModel`.

| Area | Main definitions | Main stability results | Status |
| --- | --- | --- | --- |
| Dot product | `fl_dotProduct` in `Algorithms/DotProduct.lean` | `dotProduct_error_bound`, `dotProduct_backward_error`, `dotProduct_backward_stable_x/y`, `dotProduct_isRelBackwardStable` | Full rounded implementation |
| Matrix-vector product | `fl_matVec` in `Algorithms/MatVec.lean` | `matVec_backward_error`, `matVec_error_bound` | Full rounded implementation, row-wise via dot product |
| Matrix-matrix product | `fl_matMul` in `Algorithms/MatMul.lean` | `matMul_error_bound`, `matMul_backward_error_col` | Full rounded implementation, column-wise via matrix-vector product |
| Outer product | `fl_outerProduct` in `Algorithms/OuterProduct.lean` | `outerProduct_error_bound`, `outerProduct_backward_error` | Full rounded implementation |
| Recursive summation | `fl_recursiveSum`, `fl_partialSums` in `Algorithms/RecursiveSum.lean` | `recursiveSum_backward_error`, `recursiveSum_forward_error_bound`, `recursiveSum_running_error_bound` | Full rounded implementation |
| Pairwise summation | `fl_pairwiseSum` in `Algorithms/PairwiseSum.lean` | `pairwiseSum_backward_error`, `pairwiseSum_forward_error_bound` | Full rounded implementation |
| General summation tree | `SumTree.eval` in `Algorithms/SumTree.lean` | `SumTree.backward_error`, `SumTree.forward_error`, chain/balanced specializations | Full rounded implementation over an explicit tree |
| Back substitution | `fl_backSub_steps`, `fl_backSub` in `Algorithms/TriangularSolve.lean` | `backSub_backward_error`, `backSub_backward_error_dual`, `backSub_backward_error_perturbed` | Full rounded implementation |
| Forward substitution | `fl_forwardSub_steps`, `fl_forwardSub` in `Algorithms/ForwardSub.lean` | `forwardSub_backward_error` | Full rounded implementation |
| Residual computation | `fl_residual` in `Algorithms/IterativeRefinement.lean` | `conventional_residual_error` | Full rounded implementation, built from `fl_matVec` and `fp.fl_sub` |
| Tridiagonal LU recurrence | `tridiag_lu_aux`, `tridiag_lu` in `Algorithms/LU/TridiagonalRecurrence.lean` | Structural/growth results for bidiagonal factors | Rounded implementation exists for the recurrence; full backward-error theorem is mostly connected through LU contracts |

## Hybrid Results

These results are partly derived from concrete rounded algorithms, but depend on
abstract factorization or solver hypotheses for another stage.

| Area | Files | What is concrete | What is assumed |
| --- | --- | --- | --- |
| LU solve | `Algorithms/LU/LUSolve.lean` | Forward and back substitution are actual `fl_forwardSub`/`fl_backSub` computations | LU factorization enters as `LUBackwardError` for `L_hat`, `U_hat` |
| Doolittle solve | `Algorithms/LU/Doolittle.lean` | Triangular solves are actual rounded algorithms | The Doolittle factorization itself is represented through `LUBackwardError`; `DoolittleLU` is a specification, not a function returning factors |
| Diagonal-dominant, banded, tridiagonal LU solves | `Algorithms/LU/GrowthFactor.lean`, `Algorithms/LU/Tridiagonal.lean` | Triangular solve stage is concrete when `x_hat` is defined | Factorization/growth properties are supplied as hypotheses or prior contracts |
| Cholesky solve | `Algorithms/Cholesky/CholeskySolve.lean` | Triangular solves are concrete | Cholesky factorization is supplied as `CholeskyBackwardError` |
| Normal equations least squares | `Algorithms/LeastSquares/LSNormalEquations.lean` | Final triangular solve stage is concrete | Gram product/vector errors and Cholesky factorization are supplied as contracts |
| Iterative refinement | `Algorithms/IterativeRefinement.lean` | Residual computation is concrete | Solver behavior and some inverse/condition/resolution properties are represented by structures or hypotheses |
| Matrix inversion methods | `Algorithms/MatrixInversion.lean` | Some residual algebra composes implemented matrix product and triangular-solve results | Many method-specific kernels are exposed as abstract residual/specification hypotheses |

## Contract / Specification-Transfer Interfaces

These are valid mathematical interfaces, but they should not be described as
end-to-end derivations from rounded arithmetic unless a future file supplies the
missing algorithmic implementation and proves the contract.

| Area | Main contracts/results | Status |
| --- | --- | --- |
| General Gaussian elimination / LU factorization | `LUFactSpec`, `LUBackwardError`, `PermutedLUBackwardError` in `Algorithms/LU/GaussianElimination.lean` | Factorization backward error is a contract over computed factors |
| QR, Householder and Givens | `HouseholderAppError`, `GivensAppError`, `OrthogonalSequenceBackwardError`, `HouseholderQRBackwardError`, `GivensQRBackwardError`, `QRSolveBackwardError` | QR results are perturbation/backward-error interfaces, not `fl_householder_qr` or `fl_givens_qr` implementations |
| Cholesky factorization | `CholeskyFactSpec`, `CholeskyBackwardError`, PSD/pivoted/indefinite Cholesky specs | Exact factorization and backward-error contracts; no rounded Cholesky loop returning `R_hat` |
| Block LU | `BlockLUFactSpec`, `BlockLUBackwardError`, partitioned LU recurrence theorems | Mostly exact/block perturbation contracts and growth/stability consequences |
| Gauss-Jordan elimination | `GJEStage2Spec` and abstract stage residual/forward/backward interfaces | Stage bounds are supplied as hypotheses |
| Fast matrix multiplication | `StrassenRecurrence`, `StrassenErrorBound`, `WinogradInnerProductError`, `BilinearAlgorithmError`, `ThreeMMethodError` | Error recurrences/contracts; no implemented Strassen/Winograd/3M rounded algorithm |
| Least-squares QR | `LSQRSolveBackwardError` | QR least-squares stability is axiomatized as a structure |
| Least-squares perturbation theory | `WedinPerturbationBound`, `LSAugmentedPerturbation` | Perturbation interfaces requiring SVD/pseudoinverse infrastructure |
| Underdetermined systems | `MinNormSolution`, `DemmelHighamPerturbation`, `KielbasinskiSchwetlickUndet`, `QMethodBackwardStable` | Mostly minimum-norm and perturbation/stability contracts |
| Sylvester/Lyapunov equations | `SepLowerBound`, `IsBackwardError`, SVD/residual/perturbation interfaces | Exact residual and perturbation theory; not a rounded Sylvester solver |
| Matrix powers | `ComputedMatPowVec`, `JordanFormSpec` | Computed sequence modeled by componentwise perturbations; no repeated `fl_matVec` implementation currently exposed |
| Stationary iteration | `SplittingSpec`, `ComputedIteration` | Iteration/error model structures and convergence consequences |

## Exact Auxiliary Theory

Several files are best viewed as exact mathematical support rather than
floating-point algorithms:

- `Analysis/MatrixAlgebra.lean`: exact matrix multiplication, norms,
  orthogonality, matrix powers, Neumann sums.
- `Algorithms/InverseBounds.lean`,
  `Algorithms/TriangularForwardBound.lean`,
  `Algorithms/TriangularForwardComparison.lean`, and `Algorithms/MMatrix.lean`:
  exact inverse/comparison-matrix bounds and forward-error consequences.
- `Algorithms/CondEstimation.lean`: exact/non-floating-point versions of
  one-norm estimator steps and lower-bound guarantees.
- `Algorithms/Cholesky/CholeskyPerturbation.lean`,
  `Algorithms/Sylvester/SylvesterPerturbation.lean`, and related files:
  perturbation theory interfaces and consequences.

## Claim Guidance

Accurate claim:

> The library formalizes a Higham-style floating-point model and contains full
> rounded-operation stability proofs for core kernels such as summation, dot
> product, matrix-vector/matrix-matrix product, residual computation, and
> triangular solves. It also contains many higher-level stability interfaces for
> LU, QR, Cholesky, least squares, Sylvester equations, matrix inversion, and
> related algorithms.

Claim to avoid:

> The library provides end-to-end rounded-operation implementations and full
> stability proofs for every listed high-level algorithm.

Future work needed for the stronger claim:

- Add rounded implementations for high-level factorizations such as
  `fl_gaussian_elimination`, `fl_cholesky`, `fl_householder_qr`,
  `fl_givens_qr`, and rounded least-squares solvers.
- Prove that each implementation satisfies the existing contracts such as
  `LUBackwardError`, `CholeskyBackwardError`, `HouseholderQRBackwardError`, and
  `QRSolveBackwardError`.
- Then reuse the current contract-level theorems as the final assembly layer.
