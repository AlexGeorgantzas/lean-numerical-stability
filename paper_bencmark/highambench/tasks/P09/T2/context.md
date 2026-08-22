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
arithmetic. `p09StdAddChar_positive_exp` exposes mathlib's elementary identity
that the kernel is `exp(+i 2 pi j/N)`, resolving the sign directly rather than
relying on the name `stdAddChar`. `P09MixedRadixFftPlan` records a Cooley-Tukey
or Sande-Tukey factorization into the paper's permutation, repeated
block-Fourier, and diagonal twiddle factors. Its certified exact composition is
the fixed `T`, not an arbitrary orthogonal operator.

`P09WilkinsonModel` preserves equations (3.1)--(3.2) and the absolute sine and
cosine error model: every scalar operation has a theta in `[-1,1]`, arithmetic
uses `epsilon`, and trigonometric evaluation uses `gamma * theta * epsilon`.
`p09RoundedMixedRadixStageApply` evaluates each factor operationally. It invokes
`flCos` and `flSin` for roots of unity, four `flMul` operations and two `flAdd`
operations for each complex multiplication, and left-to-right `flAdd`
accumulation for each block Fourier sum. `P09MixedRadixFftRun` requires every
stage state to equal this rounded computation, and `p09FftComputedOutput`
derives the result from the final state and permutation. There are no freely
chosen local-error vectors or per-run remainder coefficients. The run also
retains the exact-input assumption `fl(x)=x`. As in the source model, it does
not claim semantics for overflow, underflow, subnormals, NaN, or infinities.

## Asymptotic execution family

The source's `O(epsilon^2)` notation describes behavior as machine precision
tends to zero. `P09AsymptoticFftFamily` therefore fixes the factorization,
`gamma`, and input first, then supplies an operational run for every positive
`epsilon`. The model at each point has exactly that `epsilon`, the same `gamma`,
and the same exactly represented input.

`P09TheoremOneStageEnvelope` packages the stage-local estimates corresponding
to equations (3.6)--(3.8). For fixed factorization, `gamma`, and input, it
chooses one nonnegative second-order coefficient per stage and one positive
radius before both the operational execution family and the particular
`epsilon`. Its bounds therefore hold uniformly over every permitted rounding
path with that fixed structural data. It contains neither the global Theorem 1
bound nor a fictional-input witness.

## Derived forward result

For radix factors `N_l`, the definitions retain the exact Theorem 1 constant

```text
K(N,gamma) = sum_l alpha(N_l) + (M-1)(3+2 gamma),
alpha(2) = sqrt(2),
alpha(4) = 5,
alpha(q) = 2 sqrt(q) (q+gamma) otherwise.
```

`p09FamilyErrorRms_le_stage_sum` proves that the final operational error is at
most the sum of the stage-local errors after exact propagation through the
remaining factors. `p09StageFirstOrderBudget` combines the local block-Fourier
term from (3.7) with the twiddle term from (3.8), and its sum is proved equal to
the displayed `K(N,gamma)`. Consequently
`p09TheoremOneRmsAsymptotic_exists` is an imported proof of the complete
Theorem 1(a) RMS estimate from the local source envelope; the target no longer
accepts that complete estimate as a caller-supplied certificate.

The source does not provide numerical values for the hidden second-order
coefficients, so the formalization does not invent them. It makes the standard
uniform quantifier content of `O(epsilon^2)` explicit and derives the global
coefficient by summing the stage-local coefficients.

## Selected backward result

At each positive `epsilon`, let

```text
e(epsilon) = computedOutput(epsilon) - T x.
```

The target first derives one nonnegative global second-order coefficient and
one positive radius. It then constructs a family of fictional complex input
perturbations `delta(epsilon)` and proves, for every positive `epsilon`,

```text
e(epsilon) = T delta(epsilon),
||delta(epsilon)||RMS = ||e(epsilon)||RMS / sqrt(N).
```

Throughout the same sufficiently small positive-`epsilon` neighborhood it also
proves

```text
||delta(epsilon)||RMS <= epsilon K(N,gamma) ||x||RMS
                         + C epsilon^2 / sqrt(N),
||delta(epsilon)||infinity <= epsilon sqrt(N) K(N,gamma) ||x||RMS
                              + C epsilon^2.
```

The transform equation and RMS equality are exact at every precision. Only the
two upper bounds have uniform second-order remainders. `delta` is the paper's
fictional backward perturbation; it is not the actual input-representation
error discussed in the preceding paragraph. The result implies the exact backward identity
`computedOutput(epsilon) = T (x + delta(epsilon))`, although that inferred
identity is not added as a separate target conclusion.
