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

The equality sign in equation (8) is interpreted as first-order error-budget
accounting, consistently with equation (1)'s inequality and the surrounding
prose. Products of inherited perturbations and the local `O(epsilon^2)`
remainder are outside the selected first-order term. The cited passages give no
semantics for overflow, underflow, NaNs, or infinities.

## Lean statement

`P10FirstOrderProductRun n` records one positive-dimensional stable product,
an otherwise unspecified consistent matrix norm, exact operands, their
inherited perturbations, a linked computed product, local multiplication error,
and explicit higher-order terms. In this model:

- `run.rightPerturbation` is the actual error inherited by the right operand;
- `run.rightInheritedError` is its nonnegative absolute normwise error bound;
- `p10InheritedRightError run` is the propagated matrix
  `run.exactLeft * run.rightPerturbation`;
- `p10InheritedRightErrorContribution run` is exactly
  `||run.exactLeft|| * run.rightInheritedError`.

Using the exact left operand in the norm factor makes explicit the standard
first-order reading of the paper's un-hatted `A`; replacing it by the perturbed
operand would differ only through a discarded higher-order interaction.

`P10InheritedRightEquation8Term run` states both required facts. First, the
norm of the actual propagated error matrix is bounded by the selected scalar
contribution. Second, that scalar is exactly the middle additive term of
`p10FirstOrderProductErrorBudget run`, between the local multiplication term
and the inherited-left term. This preserves the source's operand orientation,
coefficient, first-order role, and unspecified norm.
