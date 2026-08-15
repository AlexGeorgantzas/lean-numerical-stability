# P11-T3 paper context

## Fixed source

The source is Alicja Smoktunowicz, Jesse L. Barlow, and Julien Langou (2006),
*A note on the error analysis of classical Gram-Schmidt*. The local PDF
SHA-256 is
`72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`.

The selected result is Theorem 1, inequality (7), on PDF page 4 / printed
page 302. Its exact matrix identity and norm derivation are on PDF page 14 /
printed page 312.

## Paper statement

The standing input is a real full-column-rank matrix `A` of size `m x n`,
where `m` and `n` are positive and `n <= m`. Algorithm 2, CGS-P, computes one
rectangular matrix `Q` and one upper-triangular matrix `R`. For every paper
prefix `k = 1,...,n`, let `A_k` and `Q_k` be the first `k` columns and let
`R_k` be the leading `k x k` block.

The paper defines

```text
c1(m,1) = 1,
c1(m,k) = 2*k*sqrt(2*m) + 2*sqrt(k)                       for k >= 2,
c2(m,1) = m + 2,
c2(m,k) = 3.5*m*k^2 - 1.5*m*k + 16*k                    for k >= 2,
c3(m,k) = c2(m,k)/2,
c4(m,k) = c2(m,k) + 2*c1(m,k),
kappa2(R_k) = ||R_k||_2 * ||R_k^(-1)||_2.
```

Under the strict condition

```text
c4(m,k) * epsilonM * kappa2(R_k)^2 < 1                  (3)
```

for every prefix, Theorem 1 states, to within terms of
`O(epsilonM^2)`,

```text
||I - Q_k^T Q_k||_2
  <= c4(m,k) * kappa2(R_k)^2 * epsilonM.                 (7)
```

Every matrix norm here is the spectral/operator 2-norm. Lean's
`k : Fin n` is zero-based and represents the paper index `k+1`, so it cannot
denote the paper-invalid zero-column prefix.

## CGS-P execution contract

`P11CGSPTheorem1Run m n` keeps the one common input and computed `Q,R` pair,
the standing dimensions and full-rank assumption, upper triangularity, a
positive machine unit smaller than one, and two-sided inverses for every
leading block. Condition (3) is retained literally for every prefix.

`P11CGSPColumnTrace` distinguishes Algorithm 2 from standard CGS. It records
the first-column norm and division and, for every later column, the computed
projection `s_k`, residual `v_k`, norms `psi_k` and `phi_k`, the successful
domain `psi_k - phi_k >= 0`, and the pythagorean diagonal

```text
r_kk = sqrt(psi_k - phi_k) * sqrt(psi_k + phi_k)
```

followed by normalization. Each pseudo-code assignment has a named additive
local error bounded by a finite first-order scale times `epsilonM`. This is a
deliberately permissive real-valued normalized-range abstraction: the paper
invokes standard error bounds but does not specify primitive evaluation order
or a complete IEEE semantics for every norm, inner product, square root, and
division. The trace exposes that choice instead of inventing an unprinted
rounding program.

## Source residual certificates

For each prefix, `P11Theorem1PrefixCertificate` records exactly the source
quantities

```text
Q_k R_k = A_k + DeltaA_k,                                (4)
E_k = R_k^T R_k - A_k^T A_k,                             (5)
```

and the corresponding spectral bounds. The paper suppresses all
second-order terms, so the certificate exposes separate nonnegative finite
coefficients `C_Delta`, `C_E`, and `C_R`:

```text
||DeltaA_k||_2
  <= c1*||A_k||_2*epsilonM + C_Delta*epsilonM^2,

||E_k||_2
  <= c2*||A_k||_2^2*epsilonM + C_E*epsilonM^2,

||A_k||_2
  <= (1+c3*epsilonM)*||R_k||_2 + C_R*epsilonM^2.
```

The last line is the reversed norm comparison used explicitly in the appendix
after equation (6). These coefficients are witnesses for the source's hidden
remainders; Lean does not assign values or uniform dimension dependence that
the paper never states.

## Fixed conclusion

The proof first derives the exact page-312 identity

```text
I - Q_k^T Q_k =
  R_k^(-T) *
    (E_k - A_k^T*DeltaA_k - DeltaA_k^T*A_k
         - DeltaA_k^T*DeltaA_k) *
  R_k^(-1).
```

Spectral submultiplicativity gives the paper's intermediate estimate. The
three source remainder coefficients are then propagated explicitly. If

```text
b = c3*||R_k||_2 + C_R,
A2 = 2*||R_k||_2*b + b^2,
core = C_E + 2*||A_k||_2*C_Delta
       + (c1*||A_k||_2 + C_Delta)^2,
```

then `p11Theorem1OrthogonalityRemainderCoeff run k` is

```text
||R_k^(-1)||_2^2 * (c4*A2 + core).
```

The target proves, simultaneously for every prefix,

```text
||I - Q_k^T Q_k||_2
  <= c4(m,k)*kappa2(R_k)^2*epsilonM
     + C_k*epsilonM^2.
```

Thus the exact leading coefficient, condition number, strict hypothesis,
dimensions, algorithm variant, and first-order qualification of (7) are all
present. No Frobenius-norm substitution or arbitrary residual budget remains.

## Scope and source ambiguities

The source forms `kappa2(R_k)` before explaining that condition (3) guarantees
nonsingularity. Lean resolves this by carrying each two-sided prefix inverse
explicitly before stating the condition. Real-valued successful traces model
only normalized finite executions. Breakdown, underflow, overflow, subnormals,
infinities, NaNs, signed zero, and input conversion are outside the claim,
because the paper does not give rules for them.

The assumptions are satisfiable. A private construction check supplies a
nonzero `1 x 1` identity execution with positive machine unit, zero local and
source residuals, and strict condition (3).
