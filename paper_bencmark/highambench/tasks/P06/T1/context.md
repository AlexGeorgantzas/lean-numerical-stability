# P06-T1 paper context

## Fixed source

The source is Michael P. Connolly and Nicholas J. Higham (2023),
*Probabilistic Rounding Error Analysis of Householder QR Factorization*. The
local PDF SHA-256 is
`c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`.

The selected result is Theorem 4.4, equations (4.16)--(4.17), and its stated
Frobenius consequence (4.20). They occur on PDF pages 9--10, printed pages
1154--1155, in section 4.

## Paper statement

Let `A` be a real `m x n` matrix with `m >= n`, and let `RHat` be the computed
upper-trapezoidal factor produced by Householder QR. Under Model 1.5 and the
assumption that the local bound (4.2) holds with probability one for every
Householder application, Theorem 4.4 gives, on one event, an orthogonal matrix
`Q` and a perturbation `DeltaA` such that

`A + DeltaA = Q * RHat`.

For every column on that event,

`||Deltaa_j||_2 <= c6 * lambda * sqrt(n) * gammaTilde_m(lambda) * ||a_j||_2
                    + O(u^2)`.

The event has probability at least

`p4(lambda,m,n) = 1 - 2*m*n*exp(-lambda^2)`.

The paper then states that these simultaneous column bounds imply (4.20):

`||DeltaA||_F <= c6 * lambda * sqrt(n) * gammaTilde_m(lambda) * ||A||_F
                  + O(u^2)`.

Here

`gammaTilde_m(lambda) = exp((lambda*sqrt(m)*u + m*u^2)/(1-u)) - 1`,

with `lambda > 0`. The Frobenius conclusion inherits the same event and
probability; equation (4.20) does not introduce a second probabilistic
argument.

## Numerical model and execution

`P06Model15` records a general probability measure and a finite scalar
computation trace. Every generated operation satisfies the standard relative
error equation `fl(x op y)=(x op y)(1+delta)`, with `|delta|<=u`. The errors
are measurable, integrable, mean zero, and mean independent in computation
order. `p06MeanIndependent` uses the test-function form of Definition 1.3's
conditional-expectation identity and does not restrict the sample space to be
finite.

`P06HouseholderQRRun` records `n>0`, `m>=n`, the local perturbations
`DeltaP_j`, and the perturbed state recurrence from (4.1). At every step its
reflector is the output of a deterministic builder applied to the current
active column; the padded vector has no support above the pivot, its exact
reflector annihilates the active column below the pivot, and it has squared
norm two. `p06HouseholderQRStep` explicitly assigns those intended
subdiagonal entries to zero. The run also records the exact product of the
same reflectors and its orthogonality. Its last state is the computed `RHat`,
every output entry is linked to the scalar rounding trace, and the output is
upper trapezoidal.

`P06Lemma42Assumption` represents the paper's explicit strengthening: the
event on which every `||DeltaP_j||_2 <= c5*gammaTilde_m(lambda)` holds has
probability one.

## Lean target

The target no longer assumes Theorem 4.4's simultaneous conclusion.
`P06Lemma42ColumnCertificate` is the preceding Lemma 4.2 result specialized to
one input column: it supplies one measurable event, its one-column failure
bound, one column perturbation, the exact relation with the run's canonical
orthogonal factor, and one column bound. P06-T1 must apply that interface to
all columns, intersect the events, derive the factor `n` in `p4` by a finite
union bound, assemble one `DeltaA`, retain every bound in (4.17), and derive
(4.20) on that same event.

The formal theorem is uniform in any positive natural `c5` and `c6` for which
the local and one-column results hold. In particular it applies to the fixed
integer constants of modest size asserted by the paper; it does not choose
different constants after seeing an execution or event.

The paper does not specify whether its additive `O(u^2)` is relative to
`||A||_F`, nor whether its hidden constant is uniform in dimensions or
`lambda`. `P06SecondOrderControl` therefore leaves the scale unspecified but
requires both the asymptotic `O(u^2)` property and one nonnegative constant
that controls the remainder for every unit roundoff between zero and the
distinguished execution's value. This prevents an isolated value at the
fixed unit roundoff from making the asserted inequality automatic. The
derived normwise remainder is `sum_j |remainder_j(u)|`; finite summation
preserves both forms of second-order control.

The condition `sqrt(m)*n^(3/2)*u < 1` in (4.18) belongs to the paper's
subsequent interpretation of when first-order growth dominates omitted terms.
It is documented here but is not silently added as a formal antecedent to
equation (4.20). Likewise, no separate NaN, infinity, underflow, or overflow
clause is added: the result is conditional on the relative-error model, just
as in the paper.

The assumptions are satisfiable. A private construction check instantiates a
one-point, zero-error Model 1.5 execution of a nonzero `1 x 1` Householder QR
factorization, including the active-column reflector builder, explicit-zero
step, exact orthogonal factor, probability-one local event, and the
one-column Lemma 4.2 certificate.
