# P18-T3 paper context

## Fixed source

The source is Zachary J. Grant, *Perturbed Runge--Kutta Methods for Mixed
Precision Applications*, Journal of Scientific Computing 92, article 6,
2022. The local PDF SHA-256 is
`b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`.

P18-T3 selects the Method 4s3pC result in Section 4.3:

```text
well-behaved tau:      Error = O(Delta t^3) + O(epsilon Delta t^3)
not well-behaved tau:  Error = O(Delta t^3) + O(epsilon Delta t^2).
```

These displays appear after the coefficients on PDF/article page 18. Their
source context includes the additive Runge--Kutta algorithm (3.1), the
one-step/global correspondence after (3.3), the four consistency conditions
through order three on page 7, every simplified smooth perturbation condition
(3.5a)--(3.5f) on page 8, and the inherited stability qualification on pages
2 and 5.

## Exact tableau interpretation

The paper prints the Method 4s3pC coefficients to fifteen decimal places but
states the order conditions as exact equalities. Literal rational arithmetic
on those decimals leaves residuals around `10^-15`, and the paper does not say
whether the decimals are exact or rounded or provide the unprinted values.

`P18Method4s3pCSourceModel` therefore represents the underlying exact tableau
that the paper's claim presupposes. It requires:

- `b^epsilon = 0`;
- all four exact consistency equations through order three; and
- all sixteen exact conditions in (3.5a)--(3.5f), including those made
  automatic by `b^epsilon = 0`.

The existing decimal constants remain a literal transcription of page 18,
but they are not silently equated with the unknown exact tableau and no
project-selected residual tolerance is treated as a source theorem. This is
an explicit interpretation premise forced by the source's rounded-data
ambiguity, not an exactness claim about the printed rationals.

## Algorithm-linked branches

`P18StableMethod4s3pCBranch` records a family of actual executions of the
original additive method (3.1). Every one-step run uses the same `F`,
`F^epsilon`, `tau`, perturbation scale, and exact source tableau. Its initial,
computed-next, and reference-next states are linked to consecutive states of
the family. The local scheme and perturbation errors are norms of those actual
one-step errors, not arbitrary scalar sequences.

The state space and its norm are universally quantified. Thus the task does
not claim that the paper selected a Euclidean norm or a particular dimension.
The paper does not give a unique analytic definition of "well behaved", so a
source-level `P18TauRegime` tag distinguishes the two cases without inventing
derivative orders, domains, or uniformity conditions.

For each branch, the local B-series consequences are explicit:

- the scheme local error is bounded by `C_s * h^4`;
- the well-behaved perturbation local error is bounded by
  `C_p * |epsilon| * h^4`; and
- the non-well-behaved perturbation local error is bounded by
  `C_p * |epsilon| * h^3`.

These bounds are the local forms inherited from the paper's page-5
correspondence. They expose the analytic content that the source leaves inside
its B-series and regularity discussion rather than replacing it with a
coefficient-print tolerance.

## Stability and big-O semantics

The paper requires stability for a global interpretation but does not define
it. The branch makes the needed finite-time property explicit: each global
scheme or perturbation contribution is bounded by one stability constant times
the sum of its local contributions. If `N` steps of size `h` cover at most the
fixed horizon `T`, then `N*h <= T`.

`p18UniformTwoTermGlobalOrder` interprets
`O(h^p) + O(epsilon h^m)` by existential nonnegative constants and keeps the
scheme and perturbation contributions separate. It is uniform over the
supplied asymptotic family but does not choose a limiting path for `epsilon`
and `h`, merge the two terms, or expose numerical constants as part of the
paper claim.

## Fixed conclusion

The theorem retains `b^epsilon = 0`, the exact third-order consistency
conditions, and all exact smooth perturbation conditions. It then derives the
two page-18 global orders. The proof sums the local errors, applies stability,
uses `N*h <= T`, and loses exactly one power of `h`:

```text
local h^4 + epsilon*h^4  ->  global h^3 + epsilon*h^3,
local h^4 + epsilon*h^3  ->  global h^3 + epsilon*h^2.
```

Neither final global order is a field of the execution. No IEEE rounding mode,
overflow, underflow, exceptional-value rule, stability theorem beyond the
stated accumulation property, or comparison of hidden constants is claimed.
