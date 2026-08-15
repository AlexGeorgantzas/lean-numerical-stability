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

## Delegated TwoProduct contract

The paper treats `TwoProduct` as a known subroutine. Under absence of underflow
and overflow, equation (17) states that its high output is the rounded product,
the high and low outputs sum exactly to the real product, and the low output is
bounded by one half ULP. `P12TwoProductExecution` records that complete semantic
contract for each call. It also records the radix-grid preservation, exponent
range, and symmetric representable boundary candidates used explicitly in the
proof of Lemma 4. The rounded-product envelope and the high-output exponent
bound are derived from nearest rounding and those candidates; they are not
assumed. These fields are the concrete no-range-error consequences of the
delegated `TwoProduct` call, not arbitrary real decompositions. Product-grid
range obligations apply only when the exact product is nonzero. Thus the formal
execution retains the paper's explicitly trivial zero-product case even when
the format has a negative minimum exponent.

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

The `FastTwoSum` record contains the actual nearest addition and two faithful
subtractions, with range validity, but assumes none of those operations exact.
The middle-addition range witness formalizes that standing no-overflow and
no-underflow do not clip nearest rounding at the product grid. The final
addition records nearest rounding and no overflow. No ordering of `a2` and
`a3`, no comparison of their absolute values or ULPs, and no restriction to
base 2 or 3 is imposed.

## Derived result

The theorem derives rather than assumes the numerical core of Lemma 4:

1. A representation of `a2` satisfying condition (7) with `a3`.
2. Exact evaluation of both `FastTwoSum` subtractions.
3. The exact middle merge `s2 + r = a2 + a3`.
4. Representability and exact evaluation of `s3 = r + a4`.
5. Equation (18), `s1 + s2 + s3 = x1*x2*x3`.

All equalities on the right are exact real equalities. There is no first-order
approximation, relative-error substitution, or omitted higher-order term. The
hypotheses are satisfiable; a private construction check instantiates the full
zero execution in a concrete radix-2 format with a negative minimum exponent,
and the private theorem proof handles zero and nonzero products separately.
