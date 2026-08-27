# P10-T1 paper context

## Fixed source

The source is James Demmel, Ioana Dumitriu, and Olga Holtz (2007), *Fast
linear algebra is stable*. The local PDF SHA-256 is
`0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`.

The selected result is the inherited-right-input term in equation (8), PDF
page 8, printed page 66, section 3.1. The stable matrix-multiplication interface
used by that equation is equation (1), PDF page 2, printed page 60.

## Mathematical setting

Equation (8) analyzes a computed product `C = A*B` when both operands already
carry absolute normwise errors from prior computations. To first order, its
three additive contributions are

`mu(n)*epsilon*||A||*||B|| + ||A||*err(B,n) + err(A,n)*||B||`.

P10-T1 selects the middle term. It propagates the right-input error on the left
by `A`, has coefficient one, and contains neither `epsilon` nor `mu(n)`. The
paper leaves the matrix norm unnamed and explains after equation (1) that one
may change norms at the cost of dimension-dependent factors. The target must
therefore not silently choose the Frobenius norm.

The equality sign in equation (8) is interpreted as first-order error
bookkeeping, consistently with equation (1)'s inequality and the surrounding
prose. Products of inherited perturbations and the local higher-order remainder
are removed when the realized first-order error is formed. Equation (8) does
not supply a finite coefficient for either omitted part. The cited passages
give no semantics for overflow, underflow, NaNs, or infinities.

## Lean statement

`P10FirstOrderProductRun n` records one positive-dimensional product, an
otherwise unspecified consistent matrix norm, exact operands, their inherited
perturbations, a linked computed product, local multiplication error, and a
higher-order remainder. It does not assume a per-run global polynomial bound
for `mu` or invent a finite coefficient for equation (8)'s omitted terms. In
this model:

- `run.rightPerturbation` is the actual error inherited by the right operand;
- `run.rightInheritedError` is its nonnegative absolute normwise error bound;
- `p10InheritedRightError run` is the propagated matrix
  `run.exactLeft * run.rightPerturbation`;
- `p10InheritedLeftError run` is the symmetric propagated matrix
  `run.leftPerturbation * run.exactRight`;
- `p10InheritedRightErrorContribution run` is exactly
  `||run.exactLeft|| * run.rightInheritedError`.

Using the exact left operand in the norm factor makes explicit the standard
first-order reading of the paper's un-hatted `A`; replacing it by the perturbed
operand would differ only through a discarded higher-order interaction.

`p10FirstOrderProductError run` is the computed product error after subtracting
the inherited-error cross product and the supplied higher-order remainder.
`P10InheritedRightEquation8Term run` first proves the substantive matrix
decomposition

```text
firstOrderProductError
  = localFirstOrderError + (exactLeft * rightPerturbation
      + leftPerturbation * exactRight).
```

It then bounds the norm of the selected middle matrix by
`||exactLeft|| * rightInheritedError`. Thus the selected scalar is linked to a
realized first-order product error rather than merely placed in a scalar
definition. Bounding the norm of the complete three-matrix sum by equation
(8)'s full scalar budget remains the distinct P10-T2 task.
