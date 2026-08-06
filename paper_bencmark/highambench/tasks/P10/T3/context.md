# P10-T3 paper context

## Fixed source

The source is James Demmel, Ioana Dumitriu, and Olga Holtz (2007), *Fast
linear algebra is stable*. The local PDF SHA-256 is
`0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`.

The selected result is the recursive Sylvester error recurrence immediately
before equation (20), PDF page 28, printed page 86, section 6.3.

## Local context and statement

The paper bounds each recursive level by the preceding error times a
nonnegative amplification factor plus a fixed forcing budget, and then solves
the recurrence asymptotically in equation (20). The target retains the exact
finite core: after any finite depth, the initial error is amplified by a power
and the forcing term by the corresponding finite geometric sum.
