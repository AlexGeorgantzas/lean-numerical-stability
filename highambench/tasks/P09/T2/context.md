# P09-T2 paper context

## Fixed source

The source is George U. Ramos (1971), *Roundoff Error Analysis of the Fast
Fourier Transform*. The local PDF SHA-256 is
`9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`.

The selected result is the fictional-input construction and its two unnumbered
bounds on PDF page 12, printed page 768, section 6. The preceding Theorem 1(a)
and equations (3.6)--(3.8) supply its forward-error estimate.

## Transform, norms, and algorithm

`p09FourierTransform` is the positive-sign, unnormalized complex DFT

```text
(T x)(k) = sum_j exp(i 2 pi j k / N) x(j).
```

The indices `ZMod N` represent `0,...,N-1`. The theorem
`p09StdAddChar_positive_exp` exposes the positive exponential convention.
`p09ComplexRms` is the Euclidean norm divided by `sqrt(N)`, while
`p09ComplexMax` is explicitly the finite maximum of the component magnitudes.

`P09MixedRadixFftPlan` records a Cooley-Tukey or Sande-Tukey factorization into
permutations, block Fourier transforms, and the separately evaluated diagonal
twiddle factors used by the displayed constant. The certified exact
composition is `T`. Its exact stage-norm scaling field records the Parseval
identity for each unnormalized block factor; it is an exact factorization
property, not a rounding-error estimate.

`P09WilkinsonModel` records equations (3.1)--(3.2) and the absolute sine and
cosine error model. `p09RoundedMixedRadixBlockApply` follows the algorithmic
case split on printed page 762:

- radix 2 uses only rounded sums and exact sign changes;
- radix 4 uses only rounded sums and exact sign changes or real/imaginary swaps;
- every other radix computes roots and performs rounded complex products.

`p09RoundedMixedRadixTwiddleApply` then performs the optional rounded diagonal
twiddle multiplication separately. `P09MixedRadixFftRun` links every stage
state to these operations and requires exact input representation. As in the
paper, the real-number model has no additional overflow, underflow, subnormal,
NaN, or infinity clauses.

## Predecessor analysis

`P09AsymptoticFftFamily` fixes one plan, `gamma`, exactly represented input, and
linked operation trace while positive `epsilon` tends to zero. This is only a
formal interpretation of the paper's retained `O(epsilon^2)` notation; the
paper does not state the hidden constants or their dependency order.

For one fixed family, `HighamBench.P09TheoremOne` derives the actual block and
twiddle error vectors from the rounded trace. The theorem
`p09PropagatedFftStageError_eq_block_add_twiddle` proves equation (3.6): after
exact propagation, the stage error is the sum of those two computed
contributions.

The operation-level proof establishes scalar addition, multiplication, sine,
and cosine bounds directly from `P09WilkinsonModel`. It then proves the
radix-2, balanced radix-4, generic-radix, and twiddle bounds, lifts them to the
full vector norm, and propagates them through the remaining exact factors. A
finite-stage growth induction supplies explicit family-specific second-order
coefficients. `p09PrimitiveTheoremOneLocalAnalysis` therefore constructs the
two predecessor estimates (3.7) and (3.8); they are not accepted from the
caller.

The shared theorem `p09TheoremOneRmsAsymptotic_exists` performs the remaining
proof. It applies the RMS triangle inequality to the equation-(3.6)
decomposition, combines the separate block and twiddle estimates, telescopes
the stage errors, and proves that their first-order budgets sum to

```text
K(N,gamma) = sum_l alpha(N_l) + (M-1)(3+2 gamma),
alpha(2) = sqrt(2),
alpha(4) = 5,
alpha(q) = 2 sqrt(q) (q+gamma) otherwise.
```

Thus the target accepts only the linked operational family and invokes an
imported derivation of Theorem 1(a). It receives neither local predecessor
estimates nor a global final-error certificate.

## Selected backward result

For each positive `epsilon`, first fix the actual linked error

```text
e = computedOutput - T x.
```

The target then chooses a fictional complex perturbation `delta`, dependent on
that actual error, and proves

```text
e = T delta,
||delta||RMS = ||e||RMS / sqrt(N).
```

For sufficiently small positive `epsilon`, the same perturbation satisfies

```text
||delta||RMS <= epsilon K(N,gamma) ||x||RMS
                 + C epsilon^2 / sqrt(N),
||delta||infinity <= epsilon sqrt(N) K(N,gamma) ||x||RMS
                      + C epsilon^2.
```

The coefficient and radius are family-specific witnesses for the ordinary
local meaning of `O(epsilon^2)`. The quantifier order is `forall epsilon,
exists delta`, matching the paper's choice of a fictional input after the
actual error is fixed. This `delta` is not the actual input-representation
error discussed earlier in section 6.
