# P15-T2 paper context

## Fixed source

The source is Nicholas J. Higham and Theo Mary (2022), *Solving block
low-rank linear systems by LU factorization is numerically stable*. The local
PDF SHA-256 is
`a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`.

The selected result is the complete backward-error statement of Lemma 3.1,
equations (3.1) and (3.2), on PDF page 6 / printed page 956 in section 3.1,
"LR matrix times vector or full matrix." The target retains the exact finite
mixed term that the paper subsequently abbreviates as `O(u epsilon)`.

## Matrices, norms, and numerical model

`P15LowRankMatVecExecution b r` records the quantities in Lemma 3.1:

- `A` is a real `b`-by-`b` matrix, `X` and `Y` are real `b`-by-`r`
  matrices, and `v` is a real vector of length `b`.
- `X` has orthonormal columns, stated as `X^T X = I` entrywise.
- `Atilde = X Y^T = A + truncError`, with
  `||truncError||_F <= epsilon * beta`, `epsilon > 0`, and `beta > 0`.
- `p15RectFrobNorm` is exactly the paper's unsquared, unnormalized Frobenius
  norm `sqrt (sum_i sum_j A_ij^2)`.
- `p15GammaReal k u = k*u/(1-k*u)`. The certificate requires
  `(b + r*sqrt(r))*u < 1`, where `c = b + r^(3/2)`.
- Unit roundoff is positive and smaller than `epsilon`, reflecting the paper's
  standing assumption that `u` is safely smaller than the LR threshold.

The real-valued stage equations are the standard finite relative-error model
used by the proof. Overflow, underflow, NaNs, and infinities are outside this
model, as they are outside the paper's equation (2.5).

## Ordered floating-point computation

The result is tied to the order printed in Lemma 3.1. It first computes

```text
wHat = fl(Y^T v) = (Y + deltaY)^T v,
||deltaY||_F <= gamma_b ||Y||_F,
```

and then computes

```text
zHat = fl(X wHat) = (X + deltaX) wHat,
||deltaX||_F <= gamma_r ||X||_F.
```

The aggregate floating-point perturbation is not assumed. It is the explicit
expansion

```text
deltaAtilde = X deltaY^T + deltaX Y^T + deltaX deltaY^T.
```

Using orthonormality gives `||X||_F = sqrt(r)` and
`||X Y^T||_F = ||Y||_F`. The proof combines the stage bounds as

```text
gamma_b + gamma_r*sqrt(r) + gamma_b*gamma_r*sqrt(r) <= gamma_c.
```

## Fixed conclusion

The target proves both backward-error levels from Lemma 3.1:

```text
zHat = (Atilde + deltaAtilde) v,
||deltaAtilde||_F <= gamma_c ||Atilde||_F,

deltaA = truncError + deltaAtilde,
zHat = (A + deltaA) v,
||deltaA||_F <= gamma_c ||A||_F
                    + epsilon*(1 + gamma_c)*beta.
```

It also records the exact algebraic split

```text
epsilon*(1 + gamma_c)*beta
  = epsilon*beta + epsilon*gamma_c*beta.
```

Thus the mixed `epsilon*gamma_c*beta` contribution is present rather than
dropped or replaced by an unspecified zero remainder. The later specialization
`beta = ||A||_F` and the subsequent forward-error corollary are not selected.
