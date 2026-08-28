# P01-T3 paper context

## Fixed source

The source is Nicholas J. Higham, *The Accuracy of Floating Point Summation*, 1993. The local file is `paper_bencmark/reference_papers/P01_THE ACCURACY OF FLOATING POINT SUMMATION.pdf`. Its SHA-256 hash is `d5ad99fac5022da54dbe02721ea57116df3cec15badddd7c96c344328718fea7`.

All three source anchors are on PDF page 11, printed page 793, in section 5, “No Guard Digit Model”:

- equation (5.1) gives the no-guard addition rule;
- equation (5.2) gives the accumulated recursive-summation error as a sum of local errors; and
- equation (5.3) bounds that error using computed earlier sums and new inputs.

## Small amount of local context

Recursive summation starts with the first input exactly. It then adds one new input at each step. Write `S_hat(k)` for the computed sum after the first `k` inputs.

Without a guard digit, one computed addition follows the rule

`fl(a + b) = a(1 + alpha) + b(1 + beta)`,

where `|alpha| <= u` and `|beta| <= u`. The two small errors may be different.

For the step that adds `x_k` to `S_hat(k-1)`, subtracting the exact addition gives the local error

`S_hat(k-1) * alpha_k + x_k * beta_k`.

Adding these local errors over steps `k = 2, ..., n` gives equation (5.2). Taking absolute values and using the triangle inequality, meaning that the size of a sum is no larger than the sum of the sizes, gives equation (5.3).

## Informal theorem statement

For any finite list of real inputs, the absolute error of recursive summation under the no-guard rule is at most

`u * sum from k=2 to n of (|S_hat(k-1)| + |x_k|)`.

The shared definition `noGuardRecursiveRunningBudget` is exactly the sum after the leading `u`. It is zero for zero or one input. At every later step it adds the size of the computed previous sum and the size of the new input.

No `gamma` condition is needed. A `gamma` condition is a restriction such as `k*u < 1`; it is needed for product bounds, but equation (5.3) is a direct sum of local errors.

## Informal proof from the paper

Use induction on the number of inputs. The zero-input and one-input sums are exact.

For a later step, apply the induction result to the earlier inputs. The no-guard rule says that the new computed value differs from the exact addition by `S_hat * alpha + x * beta`. Therefore the new total error is the old total error plus these two local terms. The triangle inequality bounds their sizes by

`old bound + u*|S_hat| + u*|x|`.

This is exactly `u` times the updated running budget. This proof is a concise formalization of the calculation printed in equations (5.2) and (5.3); it does not add a claim absent from the paper.

## Fixed Lean target

The exact checked statement is the theorem `p01_t3_noGuard_recursive_running_error_bound` in `Target.lean`. It uses only the shared `HighamBench` definitions: `NoGuardAddModel`, `recursiveSum`, and `noGuardRecursiveRunningBudget`. The same statement and shared definitions are used in both benchmark conditions.
