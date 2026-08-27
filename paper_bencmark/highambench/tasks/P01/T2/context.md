# P01-T2 paper context

## Fixed source

The source is Nicholas J. Higham, *The Accuracy of Floating Point Summation*, 1993. The local file is `paper_bencmark/reference_papers/P01_THE ACCURACY OF FLOATING POINT SUMMATION.pdf`. Its SHA-256 hash is `d5ad99fac5022da54dbe02721ea57116df3cec15badddd7c96c344328718fea7`.

The finite-product estimate used to define `p01Gamma` appears immediately after equation (2.2) on PDF page 2, printed page 784. The recursive summation estimate is equation (2.6) on PDF page 3, printed page 785, in section 2, “Orderings of Recursive Summation.” The pairwise estimate and its comparison with recursive summation are equation (3.6) and the text immediately after it on PDF page 6, printed page 788, in section 3, “Other Methods.”

## Small amount of local context

There are `n = 2^r` real inputs. Recursive summation adds them from left to right. Pairwise summation repeatedly joins equal halves. The standard addition rule is

`fl(a + b) = (a + b)(1 + delta)`, with `|delta| <= u`.

The model also treats the initial recursive step `fl(0 + x)` as exact. This is why the recursive bound uses `n - 1`, not `n`.

Write

`A = sum_i |x_i|`

and

`p01Gamma(u, k) = k*u / (1 - k*u)`.

The assumption `(2^r - 1)*u < 1` makes the larger error factor valid. It also makes the smaller factor at `r` valid because `r <= 2^r - 1`.

## Informal theorem statement

For the same `2^r` inputs, prove all three facts together:

1. The pairwise computed sum has absolute error at most `p01Gamma(u, r) * A`.
2. The recursive computed sum has absolute error at most `p01Gamma(u, 2^r - 1) * A`.
3. `p01Gamma(u, r) <= p01Gamma(u, 2^r - 1)`.

The third fact compares the two `p01Gamma` coefficients. Both error bounds multiply that coefficient by the same nonnegative value `A`, so it also orders the two certified upper bounds. It does **not** say that pairwise summation has a smaller actual error on every input. An upper bound may be loose, so two upper bounds alone cannot order the two actual errors.

## Informal proof from the paper

For recursive summation, the first input is copied exactly into the zero accumulator and each input is then affected by at most `n - 1` rounded additions. The paper collects those local factors and applies the triangle inequality to obtain equation (2.6), with coefficient `p01Gamma(u, n - 1)`.

For balanced pairwise summation, each input is affected by exactly `r = log_2(n)` rounded additions. The same local-factor argument gives equation (3.6), with coefficient `p01Gamma(u, r)`.

Finally, `r <= 2^r - 1`. For nonnegative `u` in the valid range, `p01Gamma(u, k)` is nondecreasing: increasing `k` cannot make it smaller. Therefore the pairwise coefficient is no larger than the recursive coefficient. The paper describes the pairwise coefficient as significantly smaller when `n` is large.

## Fixed Lean target

The exact checked statement is the theorem `p01_t2_pairwise_vs_recursive_bounds` in `Target.lean`. It uses only the shared `HighamBench` definitions: `P01StandardAddModel`, `P01GammaValid`, `p01Gamma`, `pairwiseSum`, and `p01RecursiveSum`. The same statement and the same shared definitions are used in both benchmark conditions.

The target is one three-part result. It deliberately uses one larger validity assumption, `P01GammaValid u (2^r - 1)`, rather than adding a redundant second assumption for `r`.
