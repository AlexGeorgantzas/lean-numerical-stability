# P10-T2 paper context

## Fixed source

The source is James Demmel, Ioana Dumitriu, and Olga Holtz (2007), *Fast
linear algebra is stable*. The local PDF SHA-256 is
`0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`.

The selected result is the product-error propagation rule in equation (8),
PDF page 8, printed page 66, section 3.1.

## Local context and statement

The paper defines stable multiplication of `n`-by-`n` matrices in equation (1)
by the normwise model

```text
||Ccomp - A*B|| <= mu(n)*epsilon*||A||*||B|| + O(epsilon^2).
```

Here `epsilon` is machine epsilon and `mu(n)` is bounded by a polynomial in
`n`. The paper deliberately leaves the matrix norm unnamed and notes that a
change of norm can alter the dimension-dependent factor.

For operands carrying errors from earlier computations, equation (8) gives
the complete first-order absolute-error budget

```text
err(C,n) = mu(n)*epsilon*||A||*||B||
             + ||A||*err(B,n)
             + err(A,n)*||B||.
```

The equality is error-accounting notation: equation (1) is an inequality, and
the paragraph introducing equation (8) explicitly says that the analysis is
first order. The target therefore states a rigorous non-strict bound and does
not interpret the printed equality as an exact identity for realized errors.

## Formal product computation

`P10ConsistentMatrixNorm n` represents the one unnamed norm used throughout
the product step. It records nonnegativity, definiteness, homogeneity,
subadditivity, and submultiplicativity. It does not specialize the source to
the Frobenius, spectral, or maximum norm.

`P10FirstOrderProductRun n` is one proof-carrying stable multiplication with
positive dimension. Its exact operands are `exactLeft` and `exactRight`; their
computed values are

```text
exactLeft  + leftPerturbation
exactRight + rightPerturbation.
```

The two perturbation norms are bounded by `leftInheritedError` and
`rightInheritedError`. The computed output is linked to those operands by

```text
computedProduct
  = (exactLeft + leftPerturbation)
      * (exactRight + rightPerturbation)
    + localFirstOrderError + higherOrderRemainder.
```

The local first-order term satisfies exactly

```text
N(localFirstOrderError)
  <= mu(n)*epsilon*N(exactLeft)*N(exactRight),
```

and the separately named remainder has a finite
`higherOrderCoeff*epsilon^2` bound. The run also records nonnegativity and a
finite polynomial-growth certificate for `mu`. As in the source passages, the
model is an axiomatic real-valued normwise model and makes no claim about
overflow, underflow, NaN, or infinity.

## First-order projection

The exact computed-product error contains both the inherited cross term
`leftPerturbation*rightPerturbation` and the local higher-order remainder.
`p10FirstOrderProductError run` removes exactly those two terms:

```text
computedProduct - exactLeft*exactRight
  - leftPerturbation*rightPerturbation - higherOrderRemainder.
```

Using the linked computation, this is exactly

```text
localFirstOrderError
  + exactLeft*rightPerturbation
  + leftPerturbation*exactRight.
```

Thus no quadratic term is silently inserted into equation (8), and no
quadratic term is silently discarded from the full computation.

## Fixed conclusion

The target bounds the norm of that realized first-order error by the three and
only three printed contributions:

```text
mu(n)*epsilon*N(exactLeft)*N(exactRight)
  + N(exactLeft)*rightInheritedError
  + leftInheritedError*N(exactRight).
```

The same `n`, `mu(n)`, `epsilon`, and norm occur in every term, and inherited
right-input error is multiplied by the left-operand norm while inherited
left-input error is multiplied by the right-operand norm.
