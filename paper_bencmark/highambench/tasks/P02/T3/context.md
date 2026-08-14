# P02-T3 paper context

## Fixed source

The source is Takeshi Ogita, Siegfried M. Rump, and Shin'ichi Oishi,
*Accurate Sum and Dot Product*, 2005. The local file is
`paper_bencmark/reference_papers/P02_ACCURATE SUM AND DOT PRODUCT.pdf`. Its SHA-256
hash is `e7b8523c793ad7345dfc76f681c44d1afbbc3a810fb948912451432ae616512d`.

The target is the no-underflow absolute-error part of Proposition 5.11 and
equation (5.10) on PDF page 24, printed page 1978. Algorithm 5.10 (`DotK`) and
its derivation begin on PDF page 23, printed page 1977. The iterated summation
bound used in that derivation is Proposition 4.10 on PDF page 16, printed page
1970.

## Small amount of local context

The input vectors have paper length `N = n+1`. For each index, `TwoProduct`
splits the exact product into high and low components. Under the selected
no-multiplication-underflow branch,

`high + low = x_i*y_i`,

and the low component is bounded by `u*|x_i*y_i|`, as in Theorem 3.4. `VecSum`
is then applied once to the product high components. The product lows, the
addition lows, and the final addition high form a vector of length `2*N` whose
exact sum is the dot product.

Algorithm 5.10 passes that vector to `SumK` with parameter `K-1`. The shared
`dotKTransform` and `dotK` definitions implement these two stages. Write

`d = sum_i x_i*y_i` and `A = sum_i |x_i|*|y_i|`.

For a vector `w` of length `M`, exact sum `s`, absolute mass `S`, and summation
parameter `q >= 3`, Proposition 4.10 gives, under `4*M*u <= 1`,

`|SumK(w,q)-s| <= (u+3*gamma(u,M-1)^2)*|s|
                   + gamma(u,2*M-2)^q*S`.

The `q = 2` case is the `Sum2` estimate of Proposition 4.5.

The paper assumes `K >= 3` and `8*N*u <= 1`.

## Informal theorem statement

In the absence of multiplication underflow, `DotK` satisfies

`|res-d| <= (u + 2*gamma(u,4*N-2)^2)*|d|
             + gamma(u,4*N-2)^K*A`.

The theorem does not select the paper's relative-error corollary, which would
need the additional assumption `d != 0`. It also does not select the underflow
extension with `5*N*eta`; that would require a larger machine model for the
underflow unit and inexact `TwoProduct` residuals.

## Informal proof from the paper

Exactness of `TwoProduct` and `TwoSum` first shows that the transformed
length-`2*N` vector sums to `d`. The estimates leading to equation (5.3) bound
its total absolute magnitude by

`|d| + gamma(u,2*N)*A`.

For `K >= 4`, apply the `SumK` estimate of Proposition 4.10 to that transformed
vector with parameter `K-1`. At the boundary `K = 3`, the called summation is
`SumK(_,2) = Sum2`, so use Proposition 4.5 instead; this is the boundary case
implicit in the paper's derivation, since Proposition 4.10 itself is stated for
parameters at least three. Substitute the exact-sum and absolute-magnitude
facts, then use the paper's gamma comparisons to replace the intermediate
factors by `gamma(u,4*N-2)`. The smallness assumption implies this gamma factor
is at most one, yielding equation (5.10) and the absolute-error statement of
Proposition 5.11.

## Fixed Lean target

The exact checked statement is `p02_t3_dotK_error_bound` in `Target.lean`.
It uses only mathlib and the neutral shared `ErrorFreeDotModel`, `dotK`,
`exactDot`, `dotMagnitude`, and `gamma`. The exact-product contract records the
chosen no-multiplication-underflow case without exposing an evaluated-library
name in the target.
