# P12-T3 paper context

## Fixed source

The source is Marko Lange and Shin'ichi Oishi (2020), *A note on Dekker's
FastTwoSum algorithm*. The local PDF SHA-256 is
`0569d969cebaabe42de69fef10fa91002af12d62149af7485d0712414b53c2a1`.

The selected result is Lemma 4 and equation (18), PDF pages 14--15 / printed
pages 396--397. The called `FourSumThreeProduct` and `TwoProduct` contract are
on PDF page 13 / printed page 395. Equation (1), nearest rounding, faithful
rounding, and the original `FastTwoSum` procedure are on PDF page 2 / printed
page 384. Section 4's standing absence-of-overflow convention begins on PDF
page 9 / printed page 391.

## Floating-point system and inputs

`P12RadixFormat` and `P12Representation` are the paper's equation-(1) finite
radix system: arbitrary integer radix `beta >= 2`, positive precision `p`, an
inclusive exponent range, and values `m*beta^e` with integer mantissa
`-beta^p < m < beta^p`. There are no infinities, NaNs, exception flags, or
signed-zero distinction.

`P12LeastRepresentation fmt x` selects the least exponent admitted by equation
(1). Its scale is the local ULP used in the proof. This is proof data, not an
extra restriction on `x`; every execution supplies such witnesses for the
three inputs and relevant `TwoProduct` outputs.

`fmt.noOverflow z` means that the exact operation result lies between the two
finite equation-(1) endpoints, `|z| <= fmt.maxValue`. This is the explicit
finite-range interpretation of Section 4's standing absence-of-overflow
convention; it is not a nearby-candidate certificate.

## Delegated TwoProduct contract

The paper treats `TwoProduct` as a known subroutine. Under absence of underflow
and overflow, equation (17) states that its high output is the rounded product,
the high and low outputs sum exactly to the real product, and the low output is
bounded by one half ULP. `P12TwoProductExecution` records that delegated
semantic contract for each call. `P12TwoProductNoUnderflowError` explicitly
collects the observable consequences of the paper's "no underflow errors"
hypothesis: exact decomposition, no underflow-to-zero, and retention of the
propagated residual scale. The
concrete `leftGrid` and `rightGrid` parameters are fixed by the three algorithm
calls and identify the residual scaling used on printed pages 396--397; operand
and output grid membership are derived, not stored.

The contract has no universal grid-preservation field and no requirement that
artificial positive and negative envelope endpoints be representable. The
nearest high product's propagated grid is instead derived from the operand
representations, nearest rounding, and the exact finite-range assumption. The
half-ULP and propagated-scale residual estimates are the inequalities stated or
derived for the delegated `TwoProduct` calls in equation (17) and the proof of
Lemma 4.

## ThreeProduct execution

`P12ThreeProductExecution fmt x1 x2 x3 tr` links every trace component to the
paper's procedure:

```text
(th, tl) = TwoProduct(x2, x3)
(s1, a2) = TwoProduct(x1, th)
(a3, a4) = TwoProduct(x1, tl)
(s2, r) = FastTwoSum(a2, a3), with intermediate t
s3       = nearest(r + a4).
```

Section 4 says that arithmetic is nearest-rounded unless stated otherwise, so
`P12NearestFastTwoSumExecution` records nearest rounding for the addition and
both subtractions. The execution separately records absence of overflow for
those exact operation results and for the final addition. It contains no exact
merge, nearby representable candidate, output-grid certificate, final
representability certificate, or equation-(18) conclusion. No ordering of
`a2` and `a3`, no comparison of their absolute values or ULPs, and no
restriction to base 2 or 3 is imposed.

## Derived result

The theorem derives rather than assumes the numerical core of Lemma 4:

1. A representation of `a2` satisfying the exact ceiling coefficient
   `ceil(beta^p-beta/2)` in condition (7) with `a3`.
2. Exact evaluation of both `FastTwoSum` subtractions.
3. The exact middle merge `s2 + r = a2 + a3`.
4. Representability and exact evaluation of `s3 = r + a4`.
5. Equation (18), `s1 + s2 + s3 = x1*x2*x3`.

All equalities on the right are exact real equalities. There is no first-order
approximation, relative-error substitution, or omitted higher-order term. The
hypotheses are satisfiable; a private construction check instantiates the full
zero execution in a concrete radix-2 format with a negative minimum exponent.
The private proof derives the propagated grids and all exact operations rather
than receiving them as execution fields.
