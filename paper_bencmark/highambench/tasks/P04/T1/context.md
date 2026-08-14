# P04-T1 paper context

## Fixed source

The source is Pierre Blanchard, Nicholas J. Higham, Florent Lopez, Theo Mary,
and Srikara Pranesh, *Mixed Precision Block Fused Multiply-Add: Error Analysis
and Application to GPU Tensor Cores*, SIAM Journal on Scientific Computing
42(3), C124--C141, 2020. The local PDF SHA-256 is
`7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`.

The selected result is the compact indexed perturbation factorization
immediately before equation (3.4), equation (3.4), and the evaluation-order
and same-precision consequences stated around it. They occur on PDF page 6 /
printed page C129 in section 3.2.

## Algorithm 3.1 execution

`P04BlockFmaDotRun n b q` represents one scalar output of the chained
block-FMA loop in Algorithm 3.1:

- `n`, `b`, and `q` are positive and `n = q*b`, which is the paper's
  `q = n/b` integral-block condition.
- `x` and `y` are a row and column of the input matrices. `p04Dot x y` is the
  exact dot product `s_n`, while `computed` is the algorithm's `sHat_n`.
- `uBar`, `uFma`, and `uOut` are the internal block-expression, FMA-output,
  and final-output unit roundoffs. They are nonnegative and `uBar <= uFma`.
- `p04EffectiveFmaRoundoff` is exactly the prioritized definition (3.3): use
  `uOut` first when `uOut > uFma`; otherwise use zero when
  `uBar >= uFma`; otherwise use `uFma`.
- The relevant gamma denominators are positive. Gamma notation is
  `gamma v k = k*v/(1-k*v)`.

The run carries the compact consequence of the local recurrence (3.2):

```text
computed = sum_i x_i*y_i*(1+alpha_i)*(1+beta_i),
|alpha_i| <= gamma_q(effective FMA roundoff),
|beta_i|  <= gamma_n(uBar).
```

These witnesses are indexed by the input term and tied to the computed output;
they are not arbitrary scalar assumptions. This factorization is the paper's
finite real execution certificate for Algorithm 3.1. As in the paper, the
model excludes underflow, overflow, NaNs, and infinities, and retains only one
of the two possible successive output roundings.

The paper says the general bound is valid for every evaluation order admitted
by its analysis. The unconditional `beta_bound` records that fact without
inventing a formal class of expression trees. If `rightToLeft` holds, the run
also carries the paper's sharper `gamma_(q+b-1)(uBar)` beta bound.

## Fixed conclusions

The theorem exposes the indexed `alpha` and `beta` witnesses and proves the
absolute forward-error bound (3.4):

```text
|s_n - sHat_n| <=
  (gamma_q(effective) + gamma_n(uBar)
    + gamma_q(effective)*gamma_n(uBar)) * sum_i |x_i|*|y_i|.
```

The right-hand data factor is `p04AbsDot x y = |x|^T|y|`; it is neither
`|x^T y|` nor a vector norm. The mixed gamma product is retained exactly.

For a right-to-left blocked evaluation, the theorem proves the same formula
with `gamma_(q+b-1)(uBar)` in place of `gamma_n(uBar)`. If
`uOut <= uFma` and `uBar = uFma`, branch priority in (3.3) makes the effective
roundoff zero. The theorem then proves `alpha_i = 0` and the exact reduction

```text
|s_n - sHat_n| <= gamma_n(uBar) * |x|^T|y|.
```

No first-order truncation or unstated bound for the omitted second output
rounding is introduced.
