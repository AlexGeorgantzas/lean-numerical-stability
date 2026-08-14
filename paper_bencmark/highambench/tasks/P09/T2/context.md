# P09-T2 paper context

## Fixed source

The source is George U. Ramos (1971), *Roundoff Error Analysis of the Fast
Fourier Transform*. The local PDF SHA-256 is
`9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`.

The selected result is the fictional-input construction and its two unnumbered
bounds on PDF page 12, printed page 768, section 6. Its transform and constants
come from equations (1.1), (2.1), and (2.2) and Theorem 1.

## Transform and computation

`p09FourierTransform` is the fixed positive-sign, unnormalized complex DFT

```text
(T x)(k) = sum_j exp(i 2 pi j k / N) x(j).
```

The indices are `ZMod N`, so they represent exactly `0,...,N-1` with cyclic
arithmetic. `P09MixedRadixFftPlan` records a Cooley-Tukey or Sande-Tukey
factorization into the paper's permutation, repeated block-Fourier, and
diagonal twiddle factors. Its certified exact composition is the fixed `T`, not
an arbitrary orthogonal operator.

`P09WilkinsonModel` preserves equations (3.1)--(3.2) and the absolute sine and
cosine error model: every scalar operation has a theta in `[-1,1]`, arithmetic
uses `epsilon`, and trigonometric evaluation uses `gamma * theta * epsilon`.
`P09MixedRadixFftRun` links the input and computed output to the factor stages,
their local roundoff vectors, and the exact-input assumption `fl(x)=x` used by
the paper. As in the source model, it does not claim semantics for overflow,
underflow, subnormals, NaN, or infinities.

## Inherited forward certificate

For radix factors `N_l`, the definitions retain the exact Theorem 1 constant

```text
K(N,gamma) = sum_l alpha(N_l) + (M-1)(3+2 gamma),
alpha(2) = sqrt(2),
alpha(4) = 5,
alpha(q) = 2 sqrt(q) (q+gamma) otherwise.
```

`P09TheoremOneRmsCertificate` is the prior Theorem 1(a) result for the linked
run, in absolute form after the exact Fourier norm scaling. Its unspecified
`O(epsilon^2)` contribution is represented by the explicit nonnegative
coefficient `C` and finite term `C * epsilon^2`. The source does not specify
uniformity or a value for `C`, so the target adds none.

## Selected backward result

Let

```text
e = computedOutput - T x.
```

The target constructs a fictional complex input perturbation `delta` and proves

```text
e = T delta,
||delta||RMS = ||e||RMS / sqrt(N),
||delta||RMS <= epsilon K(N,gamma) ||x||RMS
                + C epsilon^2 / sqrt(N),
||delta||infinity <= epsilon sqrt(N) K(N,gamma) ||x||RMS
                     + C epsilon^2.
```

The equality and transform equation are exact. Only the two upper bounds have
second-order remainders. `delta` is the paper's fictional backward
perturbation; it is not the actual input-representation error discussed in the
preceding paragraph. The result implies the exact backward identity
`computedOutput = T (x + delta)`, although that inferred identity is not added
as a separate target conclusion.
