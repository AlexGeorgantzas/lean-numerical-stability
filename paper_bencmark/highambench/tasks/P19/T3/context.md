# P19-T3 context

Sources: Theorem 3.3 and equations (3.14)-(3.17) on physical PDF page 11
(printed article page 10), and Theorem 3.4, equation (3.20), and Remark 4 on
physical page 12 (printed page 11). The right and flexible derivations are in
Appendices C-D on physical pages 41-45.

The standing problem is a nonsingular real system `A xExact = b`, with
nonzero `b`, and one fixed nonsingular, nonidentity right preconditioner `MR`.
`P19FixedRightSystem` records actual inverse certificates for `A`, `MR`, and
the derived product `A MR^{-1}`. Consequently every condition number in the
target is attached to the matrix it denotes rather than to an unrelated pair
of arguments. The paper permits several normwise interpretations of an
unqualified `kappa`; this task consistently chooses its induced 2-norm
condition number.

Algorithm 1 is represented through its correction equation for a general
initial guess. A `P19FixedRightGMRESRun` records one selected positive
iteration `k <= n`, the MGS upper-Hessenberg factorization, the perturbed
MGS/Givens least-squares problem, the stored basis columns
`zHat_j = (MR^{-1} + DeltaMR_j) vHat_j`, and the products with `A`. The
Frobenius bound on `DeltaMR_j` is equation (3.14), while the matrix-product
error has the componentwise model used in Appendix C.

The cancellation quantity from (3.15) is represented exactly as

`rhoAR = || |zHat| |yHat| ||_2 / ||zHat yHat||_2`.

The denominator is required to be positive because the paper gives no
convention for its zero case. Both runs retain the complete five-term
condition (3.16), including `um * etaR * kappa(MR)` even for flexible GMRES.

The two solution-formation paths are distinct:

- right-preconditioned GMRES forms `vHat yHat` in precision `ug` and then
  reapplies `MR^{-1}` in precision `um`;
- fixed-preconditioner flexible GMRES reuses the stored `zHat` basis and forms
  `zHat yHat` directly in precision `ug`.

The Appendix-C and Appendix-D certificates keep the propagated sources linked
to their underlying perturbations. They provide an exact vector decomposition,
individual source bounds, and a second-order remainder, but do not assume the
final normalized forward-error inequalities.

The target preserves separate existential iterations and separate low-degree
polynomial factors for the two algorithms. `p19FirstOrderLeAt` interprets the
paper's first-order comparison by adding a remainder that is
`O(condition316^2)`. The concluding identity compares the two displayed
bracket patterns at the same symbolic parameters and identifies exactly the
additional `um * etaR * kappa(MR)` term. It does not assert that two concrete
runs have identical iterations, polynomial factors, or `rhoAR` values, and it
does not claim that flexible GMRES is wholly independent of `um`.

All modeled quantities are real. Overflow, underflow, NaNs, and infinities are
outside the paper's standard floating-point model for these theorems.
