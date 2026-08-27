# P14-T1 paper context

## Fixed source

The source is Pierre Blanchard, Desmond J. Higham, and Nicholas J. Higham
(2021), *Accurately computing the log-sum-exp and softmax functions*.  The
local PDF SHA-256 is
`7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`.

The selected passage is the positive exponential-summation analysis on PDF
page 7 (printed page 2317), immediately before equations (3.2)--(3.3).

## Local context and statement

The paper sums nonnegative approximations to exponential terms and gives a
first-order recursive-summation estimate.  The target isolates that summation
stage and states its standard exact finite form with coefficient
`p14Gamma fp.u (n-1)`.  The nonzero exact sum is the domain condition for relative
error.
