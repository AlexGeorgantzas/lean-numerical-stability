# P10-T2 paper context

## Fixed source

The source is James Demmel, Ioana Dumitriu, and Olga Holtz (2007), *Fast
linear algebra is stable*. The local PDF SHA-256 is
`0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`.

The selected result is the product-error propagation rule in equation (8),
PDF page 8, printed page 66, section 3.1.

## Source statement

The paper defines stable multiplication of `n`-by-`n` matrices in equation
(1) by

```text
||Ccomp - A*B|| <= mu(n)*epsilon*||A||*||B|| + O(epsilon^2),
```

where `mu(n)` is bounded by a polynomial in `n`. For operands carrying errors
from earlier computations, equation (8) records the complete first-order
budget

```text
err(C,n) = mu(n)*epsilon*||A||*||B||
             + ||A||*err(B,n)
             + err(A,n)*||B||.
```

The printed equality is first-order error-accounting notation. The formal
target therefore gives a norm inequality for the actual computed-product
error and exposes one uniform quadratic remainder.

## Fixed algorithm and norm

`P10StableMatrixMultiplication` is one multiplication algorithm, not a new
choice for each run. Its output operation, matrix norm at every dimension,
and function `mu` are fixed before the dimension, operands, and precision are
chosen. The structure also records a global polynomial bound for `mu`.

`P10ConsistentMatrixNorm n` represents the paper's deliberately unnamed
matrix norm. It supplies nonnegativity, definiteness, homogeneity,
subadditivity, and submultiplicativity without changing the source to a
particular norm.

## Uniform first-order execution family

`P10FirstOrderProductFamily algorithm n` fixes exact matrices `A` and `B` and
varies positive `epsilon`. At each precision the actual algorithm is called
on

```text
A + leftPerturbation(epsilon)
B + rightPerturbation(epsilon).
```

The perturbation norms are bounded by nonnegative inherited-error functions.
Both inherited errors have one coefficient and one positive radius on which
they are bounded by that coefficient times `epsilon`. Thus they are genuinely
uniform `O(epsilon)` families rather than unrelated values chosen after one
precision is fixed.

The local multiplication certificate bounds the actual output minus the
exact product of those perturbed operands by

```text
mu(n)*epsilon*N(A)*N(B) + localSecondOrderCoeff*epsilon^2
```

on the same radius. This is equation (1) after the first-order effect of the
epsilon-sized operand perturbations has been absorbed into a uniform
quadratic term. It contains neither inherited contribution from equation (8)
nor the desired final bound.

## Fixed conclusion

`p10ProductFamilyError` is the actual error

```text
algorithm.product(epsilon, A + dA(epsilon), B + dB(epsilon)) - A*B.
```

No cross term or local remainder is subtracted from it. The theorem produces
one nonnegative coefficient and one positive radius such that, uniformly for
all smaller positive precisions, its norm is at most the three terms printed
in equation (8), plus that coefficient times `epsilon^2`.

Expanding the perturbed product yields the local error, `A*dB`, `dA*B`, and
`dA*dB`. The first three give the printed budget. Uniform first-order bounds
on both inherited errors make the cross product uniformly quadratic.

As in the source, this is an axiomatic real-valued normwise model. It does not
add overflow, underflow, NaN, or infinity semantics absent from the selected
paper passage.
