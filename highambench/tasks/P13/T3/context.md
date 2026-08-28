# P13-T3 paper context

## Fixed source

The source is Nicholas J. Higham (2004), *The numerical stability of
barycentric Lagrange interpolation*. The local PDF SHA-256 is
`9ebf8adb699f96c82ccbb153dd6ca592c64475a8bc3e0703a50cb659b012c520`.

The selected result is Theorem 4.1 and equations (4.2)--(4.3) on PDF page 6
(printed page 552), together with the exact computed expression immediately
preceding it on PDF page 5 (printed page 551). Its inherited definitions and
operation counts occur in equation (3.2), the floating-point model, equation
(3.3), Lemma 3.1, and the proof of Theorem 3.2 on PDF pages 3--4 (printed pages
549--550).

## Paper contract

For degree parameter `n`, the paper has `n + 1` distinct nodes and data values,
indexed from `0` through `n`, and evaluates at a fixed point `x`. The weights
are computed directly from

`w_j = 1 / product_(k != j) (x_j - x_k)`.

The analyzed algorithm is the second barycentric quotient

`(sum_j w_j f_j / (x - x_j)) / (sum_j w_j / (x - x_j))`.

The standard relative-error model represents each operation by a factor
`(1 + delta)^(+1 or -1)`, with `|delta| <= u`. The exact computed expression
has weight counters of length `2n`, numerator-evaluation counters of length
`n + 3`, denominator-evaluation counters of length `n + 2`, and one final
quotient counter. Collecting them gives numerator counters of length `3n + 4`
and denominator counters of length `3n + 2`.

Theorem 4.1 bounds scalar relative forward error by

`(3n + 4)u * cond(x,n,f) + (3n + 2)u * cond(x,n,1) + O(u^2)`.

Here `cond(x,n,f)` is the data condition number and `cond(x,n,1)` measures
cancellation in the denominator. The sentence following equation (4.3) says
that rounding errors can attain this bound within a constant factor.

## Lean encoding

`P13SecondBarycentricProblem` binds the `n + 1` real input values, distinct
nodes, and an evaluation point away from every node. Its coefficient is exactly
the reciprocal-product weight divided by `x - x_j`.

`P13RelativeErrorCounter` records the paper's literal product of `k` local
relative-error factors, their `u` bounds, and the inherited
`|counter - 1| <= gamma u k` consequence. `P13SecondBarycentricExecution`
records all four uncollected stages, both collected counters, their exact
collection identities, and every required `GammaValid` premise. Thus
`p13SecondBarycentricComputed` is the paper's computed second barycentric
quotient, not an arbitrary perturbed quotient.

The target quantifies a family of such executions whose unit roundoff tends to
zero. It assumes the exact numerator and denominator are nonzero and concludes:

1. the exact finite two-counter forward-error envelope eventually holds;
2. that envelope is exactly the printed first-order coefficient times `u` plus
   `p13SecondBarycentricForwardRemainder`;
3. the remainder is genuinely `O(u^2)` along the execution family; and
4. admissible first-order local-error directions attain at least one third of
   the displayed leading coefficient.

The factor `1/3` is a concrete witness for the paper's unquantified phrase
"within a constant factor"; it is not presented as a paper-specified sharp
constant.

## Scope resolutions

The paper does not specify what formula (4.1) does when `x` is a node, so this
target explicitly assumes `x` differs from every node. It also does not specify
a concrete floating-point format, rounding mode, or IEEE exceptional-value
semantics. Real values therefore denote the exact values of floating-point
inputs, and an execution is in scope precisely when it supplies the paper's
relative-error certificate. Overflow, underflow, infinities, and NaNs are not
claimed to satisfy that certificate.

The paper leaves the `O(u^2)` term unquantified. The Lean target retains it as a
filter-level Big-O statement and additionally exposes an exact finite remainder
derived from the source counter model; it does not delete or replace the
higher-order term.
