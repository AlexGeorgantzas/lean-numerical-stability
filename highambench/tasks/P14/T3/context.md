# P14-T3 paper context

## Fixed source

The source is Pierre Blanchard, Desmond J. Higham, and Nicholas J. Higham
(2021), *Accurately computing the log-sum-exp and softmax functions*.  The
local PDF SHA-256 is
`7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`.

The shift identity is equation (1.4) on PDF page 3 (printed page 2313).  The
normalization value 1 is used explicitly in the numerical-experiment
discussion on PDF page 17 (printed page 2327).

## Local context and statement

The target connects the paper's shifted formula to the exact softmax map and
packages two invariant checks: the softmax components sum to one and, because
they are nonnegative, their absolute values also sum to one.
