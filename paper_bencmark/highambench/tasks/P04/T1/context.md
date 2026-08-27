# P04-T1 paper context

## Fixed source

The source is Pierre Blanchard, Nicholas J. Higham, Florent Lopez, Theo Mary,
and Srikara Pranesh, *Mixed Precision Block Fused Multiply-Add: Error Analysis
and Application to GPU Tensor Cores*, SIAM Journal on Scientific Computing
42(3), C124--C141, 2020. The local PDF SHA-256 is
`7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`.

The selected result is Algorithm 3.1 and its scalar recurrence (3.1), the local
rounding model (3.2), the effective roundoff (3.3), the compact indexed
perturbation factorization immediately before (3.4), equation (3.4), and the
evaluation-order and same-precision consequences stated around it. These occur
on PDF pages 5--6 / printed pages C128--C129 in sections 3.1--3.2.

## Algorithm 3.1 execution

`P04BlockFmaDotRun n b q` represents one scalar output of Algorithm 3.1's
chained block-FMA loop.

- `n`, `b`, and `q` are positive and `n = q*b`, matching the paper's integral
  block partition `q = n/b`.
- `x k j` and `y k j` are the post-input-conversion values in block `k` at
  local position `j`. `p04BlockedDot x y` is the exact scalar dot product.
- `state 0 = 0`; `computed` is definitionally `state q`.
- Each `state_step` is the equality

```text
state_(k+1) =
  (state_k*(1+carryTheta_k)
    + sum_j x_(k,j)*y_(k,j)*(1+termTheta_(k,j)))*(1+delta_k).
```

This is the local standard-model form (3.2) of recurrence (3.1), rather than
the final factorization being supplied as an assumption.

`uBar`, `uFma`, and `uOut` are the internal block-expression, block-FMA-output,
and final-output unit roundoffs. They are nonnegative and `uBar <= uFma`.
`p04EffectiveFmaRoundoff` is the prioritized definition (3.3): first use
`uOut` when `uFma < uOut`; otherwise use zero when `uFma <= uBar`; otherwise
use `uFma`. The required gamma denominators are positive.

The primitive and compact local errors encode the operation paths used in the
paper's derivation:

- `|delta_k|` is bounded by the effective roundoff.
- Every carry `theta` is bounded by `gamma_b(uBar)`.
- A term `theta` is bounded by `gamma_b(uBar)` in the first block, where
  `state_0 = 0` removes one operation, and by `gamma_(b+1)(uBar)` later.
- Each term-to-output internal path is represented by `n` primitive errors,
  individually bounded by `uBar`; their product equals the corresponding term
  factor followed by the later carry factors.
- For right-to-left evaluation, the run additionally gives the paper's shorter
  `q+b-1` primitive-error path and one-operation carry bound.

The evaluation order is explicit. `other code` covers any parenthesization to
which the paper's general all-orders bound applies; `rightToLeft` enables its
sharper consequence. The run contains no `alpha`, `beta`, compact final
factorization, or final error bound.

As in the paper, all modeled quantities are finite real numbers. Underflow,
overflow, NaNs, infinities, and the deliberately omitted second output
rounding are outside the model.

## Fixed conclusions

The theorem must construct block-indexed witnesses `alpha k j` and `beta k j`
from the trace and prove

```text
computed = sum_(k,j) x_(k,j)*y_(k,j)*(1+alpha_(k,j))*(1+beta_(k,j)),
|alpha_(k,j)| <= gamma_q(effective),
|beta_(k,j)|  <= gamma_n(uBar).
```

It then proves the exact absolute forward-error bound (3.4):

```text
|s_n - sHat_n| <=
  (gamma_q(effective) + gamma_n(uBar)
    + gamma_q(effective)*gamma_n(uBar))
  * sum_(k,j) |x_(k,j)|*|y_(k,j)|.
```

The right-hand data factor is `p04BlockedAbsDot x y = |x|^T|y|`; it is
neither `|x^T y|` nor a vector norm. The mixed gamma product is retained
exactly.

For right-to-left evaluation, the theorem replaces `gamma_n(uBar)` by
`gamma_(q+b-1)(uBar)`. If `uOut <= uFma` and `uBar = uFma`, branch priority in
(3.3) makes the effective roundoff zero. The theorem then proves every
`alpha k j = 0` and the exact reduction

```text
|s_n - sHat_n| <= gamma_n(uBar) * |x|^T|y|.
```

No first-order truncation or unstated estimate for the omitted second output
rounding is introduced.
