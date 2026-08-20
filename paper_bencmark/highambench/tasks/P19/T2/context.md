# P19-T2 context

Source: Theorem 3.1 and equations (3.7)-(3.8) on physical PDF page 9
(printed article page 8). Algorithm 2 is on physical page 7, its four rounding
error modules and conditions (3.2)-(3.6) are on physical pages 8-9, and the
first-order derivation ends with (A.11) on physical page 39.

The standing problem is a nonsingular real system `A xExact = b` with nonzero
`b`. Algorithm 2 uses a nonsingular left preconditioner and an increasing
family of full-column-rank search bases. At its MGS-selected key dimension
`k`, it computes:

- `computedC = M_L^{-1} A Z + deltaC`, with a Frobenius-norm relative bound;
- `computedB = M_L^{-1} b + deltaB`, with a vector 2-norm relative bound;
- a least-squares solution produced through the MGS upper-Hessenberg
  factorization and the paper's Givens/triangular-solve perturbation model; and
- `xHat = Z yHat + deltaX`, with the vector 2-norm bound from (3.4).

`P19ModularGMRESRun` records those equations, the numerical-nonsingularity and
smallness conditions (3.5)-(3.6), and the MGS near-orthogonality defect used to
obtain the two basis bounds. `P19SingularValueData` gives exact extremal-gain
semantics to `sigmaMin` and `sigmaMax`; it is not an arbitrary pair of bounds.

The paper uses an unqualified `kappa` when norm equivalence makes the choice
inessential. This task fixes that ambiguity by using the paper's Frobenius
condition number throughout. A certified inverse represents each nonsingular
square matrix. The right preconditioner is analytical: the theorem quantifies
over every matrix/inverse pair `MR`, while the computed `xHat` remains the same
Algorithm 2 output.

For each such `MR`, the coefficients below (3.8) are represented exactly:

- `alpha` is `kappa(MR) / sigmaMin(MR Z)` times the Frobenius-norm ratio;
- `beta` is the specified maximum times `kappa(MR)`;
- `lambda` is the reciprocal condition number of
  `M_L^{-1} A M_R^{-1}`; and
- `xi = alpha*epsilonC + beta*epsilonB + beta*ug + lambda*epsilonX`.

The Appendix-A certificate keeps the four propagated contributions separately
typed and linked to `deltaC`, `deltaB`, the least-squares perturbations, and
`deltaX`. It records their exact vector decomposition and individual bounds,
not the final combined inequality.

The paper leaves `c(n,k)` as an unspecified low-degree polynomial and uses
`lesssim` after dropping second-order terms. The task represents the former by
an explicit nonnegative polynomial and the latter by `p19FirstOrderLeAt`: the
inequality is eventually exact after adding a remainder that is
`O((epsilonC + epsilonB + ug + epsilonX)^2)`.

All modeled quantities are real. As in the paper's standard floating-point
model, overflow, underflow, NaNs, and infinities are outside this theorem.
