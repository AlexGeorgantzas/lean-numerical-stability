# P10-T2 paper context

## Fixed source

The source is James Demmel, Ioana Dumitriu, and Olga Holtz (2007), *Fast
linear algebra is stable*. The local PDF SHA-256 is
`0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`.

The selected result is the product-error propagation rule in equation (8),
PDF page 8, printed page 66, section 3.1.

## Local context and statement

The paper's first-order rule separates the local multiplication error from
the errors inherited through the left and right inputs. The target gives its
exact finite algebraic completion: for `(A+dA)(B+dB)+E`, the error budget has
the three displayed first-order contributions and the explicit cross term
`dA*dB` that first-order notation suppresses.
