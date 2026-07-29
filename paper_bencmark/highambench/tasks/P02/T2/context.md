# P02-T2 paper context

## Fixed source

The source is Takeshi Ogita, Siegfried M. Rump, and Shin'ichi Oishi,
*Accurate Sum and Dot Product*, 2005. The local file is
`paper_bencmark/reference_papers/ACCURATE SUM AND DOT PRODUCT.pdf`. Its SHA-256
hash is `e7b8523c793ad7345dfc76f681c44d1afbbc3a810fb948912451432ae616512d`.

The target is Proposition 4.5, equation (4.8), on PDF page 11, printed page
1965. The supporting estimates and proof are on PDF pages 10--13, printed pages
1964--1967: Lemma 4.2 and equations (4.4)--(4.7), followed by equations
(4.10)--(4.12).

## Small amount of local context

For paper length `N = n+1`, let

`s = sum_i v_i` and `S = sum_i |v_i|`.

One `VecSum` pass produces low components `q` and a final high component
`pi`. Their exact total is `s`. Algorithm 4.4 (`Sum2`) recursively sums the low
components in working precision and finally performs one rounded addition with
`pi`.

The standard addition rule is

`fl(a+b) = (a+b)(1+delta)`, with `|delta| <= u`.

The error-free `TwoSum` contract additionally gives exact preservation and
bounds each emitted low component by `u` times its high component. The usual
accumulated factor is

`gamma(u,k) = k*u / (1-k*u)`.

The assumption `N*u < 1` is written `GammaValid u (n+1)`.

## Informal theorem statement

The result of `Sum2` satisfies

`|res - s| <= u*|s| + gamma(u,N-1)^2*S`.

In the Lean indexing, `N-1 = n`, so the second coefficient is
`(gamma fp.u n)^2`. This is an exact finite bound; no informal big-O term is
used.

## Informal proof from the paper

Lemma 4.2 bounds the total magnitude of the low components by
`gamma(u,N-1)*S`. Ordinary recursive-summation analysis then bounds the error
made while accumulating those lows by
`gamma(u,N-2)*gamma(u,N-1)*S`.

Equation (4.7)(i) identifies the final high component plus the exact low sum
with `s`. Expand the last rounded addition as multiplication by `1+delta`.
The exact-preservation identity cancels the otherwise large high-component
term, leaving the final rounding contribution `u*|s|` plus at most `1+u`
times the low-accumulation error. Finally,

`(1+u)*gamma(u,N-2) <= gamma(u,N-1)`

in the valid range, giving equation (4.8).

## Fixed Lean target

The exact checked statement is `p02_t2_sum2_error_bound` in `Target.lean`.
It uses only the neutral shared `ErrorFreeAddModel`, `GammaValid`, `gamma`, and
`sum2`. The same file compiles without the evaluated library.
