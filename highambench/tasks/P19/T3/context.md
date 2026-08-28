# P19-T3 paper context

## Fixed source

The selected results are Theorem 3.3 and equations (3.14)-(3.17) on physical
PDF page 11 (printed article page 10), together with Theorem 3.4, equation
(3.20), and Remark 4 on physical page 12 (printed page 11). Their derivations
are Appendix C on physical pages 41-44 and Appendix D on physical pages 44-45.
The local PDF SHA-256 is
`67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad`.

The controlled theorem states the two source theorems as separately quantified
claims. A valid right execution is not required in order to state or use the
flexible result, and conversely. Each claim derives its own dimension
`0 < k <= n` by the finite first-loss MGS argument used by Theorem 3.1; no
execution record stores a key dimension.

## Static numerical meaning

The paper concerns fixed floating-point executions. There is therefore no
filter, precision-indexed family, convergence-to-zero requirement, exact
Big-O remainder, or invented numerical smallness threshold.

`P19FirstOrderSemantics` parameterizes only the two qualitative notions that
the source leaves undefined: "small" for `much-less-than 1` and "second order"
for omitted terms. `p19FirstOrderLe` retains one exact remainder classified by
that interpretation.

Section 2 authorizes both Frobenius and induced-2 readings of an unqualified
square condition number. `P19StaticSquareKappaChoice` makes that choice
explicit and applies it uniformly to `A`, `M_R`, and `A M_R^{-1}`. It does not
attach a condition number to an unrelated inverse. The unspecified low-degree
factor `c(n,k)` is represented only by the nonnegative value
`dimensionFactor` at the selected `n,k`; no coefficients or degree are
invented.

## Algorithm linkage

Both variants use a `P19Theorem31Family`, which supplies source-level Algorithm
2 data at every admissible dimension over one increasing full-rank
mathematical search-space basis. `P19StaticFixedRightPreconditioner` fixes one
nonsingular nonidentity `M_R`, certifies its inverse and the inverse of
`A M_R^{-1}`, and records `M_L = I`.

`P19StaticFixedRightCore` then links the modular data at one dimension to:

- the computed basis columns
  `zHat_j = (M_R^{-1} + DeltaM_R_j) vHat_j` from (3.14);
- the computed products `(A + DeltaA_j) zHat_j` from (C.1);
- the inaccessible mathematical basis
  `zTilde_j = zHat_j + A^{-1} DeltaA_j zHat_j` from (C.2);
- exact zero line-1 and line-2 modular residuals after this absorption and
  because `M_L = I`; and
- the exact ratio
  `rhoAR = || |zHat| |yHat| ||_2 / ||zHat yHat||_2` from (3.15).

The ratio's denominator is required to be positive at the selected dimension,
which makes the paper's displayed division defined. This is an explicit record
of an implicit source-domain requirement rather than a replacement of `rhoAR`
by a constant.

The initial-guess sign is not chosen. Algorithm 1 prints `A*x0-b`, while the
modular proof suppresses `x0`; the reconstruction uses the Algorithm 2
solution variable employed by Appendices C-D and does not add an initial-
residual equation.

## Distinct solution paths

`P19StaticRightIteration` records the right-preconditioned path: a product with
`VHat` followed by a fresh perturbed application of `M_R^{-1}`.
`P19StaticFlexibleIteration` records the flexible path: a direct product with
the persistently stored `ZHat`, with no fresh preconditioner application.

Their source-condition records bound actual perturbation magnitudes by the
corresponding `c(n,k) u` quantities. Both retain all five entries of (3.16):

```text
max(ug*kappa(A*MR^-1), ug*kappa(MR), um*etaR*kappa(MR),
    ua*kappa(A)*rhoAR, ua*kappa(A*MR^-1)*kappa(MR)) << 1.
```

In particular, the flexible hypothesis still contains the `um` terms even
though its displayed attainable-error conclusion does not.

## Appendix dependencies and conclusion

`P19StaticRightAppendixCTheory` and
`P19StaticFlexibleAppendixDTheory` are uniform in the dimension. They receive
the MGS-selected dimension and the source conditions, and return only a raw
error decomposition and sensitivity gains in the actual GMRES,
preconditioner-reapplication, and matrix-product perturbation magnitudes. They
contain no selected dimension, no `c(n,k)`-weighted component estimate, and
neither final bound (3.17) nor (3.20).

Appendix C states that its source conditions are met at any `k` satisfying the
MGS alternative (3.7), and Appendix D invokes the same argument. The target
therefore takes an applicability function that supplies the complete source
conditions for every well-conditioned dimension that is either `n` or near
dependence. The finite first-loss argument chooses such a dimension, applies
that function, and proves the bound itself. The desired bound is not hidden
behind an implication whose antecedent could be false at the chosen witness.

The target proof derives the source-parameter bounds on those magnitudes, uses
the Euclidean triangle inequality, and obtains:

- the three right terms
  `ug*kappa(A*MR^-1)*kappa(MR) + um*etaR*kappa(MR) +
   ua*kappa(A)*rhoAR`; and
- the two flexible terms
  `ug*kappa(A*MR^-1)*kappa(MR) + ua*kappa(A)*rhoAR`.

The final algebraic identity formalizes Remark 4's exact term-list comparison:
the right envelope is the flexible envelope plus the fresh-reapplication term
`um*etaR*kappa(MR)`. It does not remove `um` from condition (3.16) or claim
that concrete right and flexible runs share a witness or a `rhoAR` value.

All quantities are real. As in the source's standard floating-point model,
overflow, underflow, subnormals, infinities, and NaNs are outside this task.
