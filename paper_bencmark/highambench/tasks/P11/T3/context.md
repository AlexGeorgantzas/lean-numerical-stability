# P11-T3 paper context

## Fixed source

The source is Alicja Smoktunowicz, Jesse L. Barlow, and Julien Langou (2006),
*A note on the error analysis of classical Gram-Schmidt*. The local PDF
SHA-256 is
`72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`.

The selected result is the numbered loss-of-orthogonality bound (7) in
Theorem 1, on PDF page 4 / printed page 302. Its exact matrix identity and the
successive norm estimates that derive (7) are on PDF page 14 / printed page
312. The task selects equation (7), not the conjunction of all five equations
(4)-(8); equations (4)-(6) are the preceding source results used in its proof.

## Paper statement

The standing input is a real full-column-rank matrix `A` of size `m x n`, with
positive dimensions and `n <= m`. Algorithm 2, CGS-P, computes rectangular
`Q` and upper-triangular `R`. For each paper prefix `k = 1,...,n`, let
`A_k` and `Q_k` be the first `k` columns and `R_k` the leading square block.

The source constants are

```text
c1(m,1) = 1,
c1(m,k) = 2*sqrt(2)*m*k + 2*sqrt(k)                    for k >= 2,
c2(m,1) = m + 2,
c2(m,k) = 3.5*m*k^2 - 1.5*m*k + 16*k                 for k >= 2,
c3(m,k) = c2(m,k)/2,
c4(m,k) = c2(m,k) + 2*c1(m,k),
kappa2(R_k) = ||R_k||_2 * ||R_k^(-1)||_2.
```

In particular, `m` is outside the square root in the second branch of `c1`.
Under condition (3)

```text
c4(m,k) * epsilonM * kappa2(R_k)^2 < 1,
```

Theorem 1 states, to within `O(epsilonM^2)`, equation (7):

```text
||I_k - Q_k^T Q_k||_2
  <= c4(m,k) * kappa2(R_k)^2 * epsilonM.
```

All matrix norms are spectral operator 2-norms. Lean's `k : Fin n` is
zero-based and denotes the paper's positive prefix `k+1`.

## Operational family

`P11CGSPTheorem1Family m n` fixes one input matrix before the machine unit is
chosen and supplies an execution for every positive `epsilonM`. Each execution
contains the standing dimensions and rank assumption, computed `Q,R`, upper
triangularity, leading inverses, and an operation-linked Algorithm 2 trace.

`P11CGSPNormalizedArithmetic` extends the normalized finite norm/division model
with addition, subtraction, multiplication, square root, and dot-product
operations. `P11CGSPColumnTrace` links the stored values to the actual CGS-P
assignments, including

```text
s_k = Q_(k-1)^T a_k,
v_k = a_k - Q_(k-1) s_k,
psi_k = ||a_k||_2,
phi_k = ||s_k||_2,
r_kk = sqrt(psi_k-phi_k) * sqrt(psi_k+phi_k),
q_k = v_k/r_kk.
```

It stores no factorization, normal-equation, or orthogonality bound. The family
requires condition (3) on one positive right-neighborhood of zero. It also
records local uniform bounds on the computed `R_k` and `R_k^(-1)`; these are
the regularity needed to give the paper's hidden remainder a genuine uniform
big-O meaning after inverse multiplication.

## Prior source estimates

`P11Theorem1ResidualAsymptotics family` represents equations (4), (5), and the
reversed norm comparison from (6), which the appendix establishes before
turning to equation (7). Their residual matrices are definitions of the actual
execution outputs, not supplied witnesses. One coefficient per prefix and one
common positive radius are fixed before any `epsilonM` is selected:

```text
||Q_k R_k - A_k||_2
  <= c1*||A_k||_2*epsilonM + C_Delta(k)*epsilonM^2,

||R_k^T R_k - A_k^T A_k||_2
  <= c2*||A_k||_2^2*epsilonM + C_E(k)*epsilonM^2,

||A_k||_2
  <= (1+c3*epsilonM)*||R_k||_2 + C_R(k)*epsilonM^2.
```

This differs from choosing a new coefficient after seeing one fixed-precision
execution, which would not express `O(epsilonM^2)`.

## Fixed conclusion

For every positive machine unit in the common neighborhood and every prefix,
the target derives the page-312 inverse-conjugated identity and proves

```text
||I_k - Q_k^T Q_k||_2
  <= c4(m,k)*kappa2(R_k)^2*epsilonM
     + C_orth(k)*epsilonM^2.
```

`C_orth(k)` is computed from the uniform residual coefficients and the fixed
family bounds, so it is independent of the selected machine unit. The target
does not assume equation (7), an orthogonality certificate, or a per-execution
remainder witness.

## Scope

The model covers successful normalized finite real executions. Breakdown,
subnormal underflow, overflow, infinities, NaNs, signed-zero behavior, and input
conversion are outside the source claim. A private exact `1 x 1` identity family
shows that all premises, including the common radii and condition (3), are
jointly satisfiable.
