# P01-T1 paper context

## Fixed source

The source is Nicholas J. Higham, *The Accuracy of Floating Point Summation*, 1993. The local file is `paper_bencmark/reference_papers/P01_THE ACCURACY OF FLOATING POINT SUMMATION.pdf`. Its SHA-256 hash is `d5ad99fac5022da54dbe02721ea57116df3cec15badddd7c96c344328718fea7`.

The main result used here is equation (3.6) on PDF page 6, printed page 788, in section 3, “Other Methods.” The finite-product estimate that is used to define `gamma` appears immediately after equation (2.2) on PDF page 2, printed page 784. The nonnegative-input simplification is supported by the discussion after equation (2.6) on PDF page 3, printed page 785, in section 2, “Orderings of Recursive Summation.”

## Small amount of local context

There are `n = 2^r` real inputs. Pairwise summation splits the inputs into two equal halves, sums each half in the same way, and then adds the two half-sums. Thus every input passes through exactly `r` rounded additions.

The standard addition rule says that one computed addition has the form

`fl(a + b) = (a + b)(1 + delta)`, with `|delta| <= u`.

Here `u` is the unit roundoff, meaning the largest local relative error allowed by this model. The usual mathematical model assumes that exceptional machine events, such as overflow or underflow, do not occur.

The accumulated error factor is

`gamma(u, k) = k*u / (1 - k*u)`.

It is used only when `k*u < 1`, so its denominator is positive.

## Informal theorem statement

Assume all `2^r` inputs are nonnegative and `r*u < 1`. The absolute difference between their computed pairwise sum and their exact sum is at most

`gamma(u, r)` times the exact sum.

This is the nonnegative form of the paper’s pairwise estimate (3.6). For nonnegative inputs, the sum of the absolute values is exactly the ordinary sum.

## Informal proof from the paper

The paper first describes any addition order by following the rounded additions that affect each input. In a balanced pairwise tree, every input follows a path of length `r`. The product of the `r` local rounding factors differs from `1` by at most `gamma(u, r)`. Therefore the total error is a sum of the inputs multiplied by small error factors. The triangle inequality, meaning that the size of a sum is no larger than the sum of the sizes, gives equation (3.6):

`|computed sum - exact sum| <= gamma(u, r) * sum_i |x_i|`.

When every `x_i` is nonnegative, `|x_i| = x_i`, so the right side becomes `gamma(u, r) * sum_i x_i`.

## Fixed Lean target

The exact checked statement is the theorem `p01_t1_pairwise_nonnegative` in `Target.lean`. It uses only the shared `HighamBench` definitions: `StandardAddModel`, `GammaValid`, `gamma`, and `pairwiseSum`. The same statement and the same shared definitions are used in both benchmark conditions.

In plain language, its assumptions and conclusion are exactly those stated above. The input is a function `Fin (2^r) -> Real`; `Fin (2^r)` is just the finite index set `0, ..., 2^r - 1`.
