# P05-T1 paper context

## Fixed source

The source is Siegfried M. Rump and Claude-Pierre Jeannerod (2014),
*Improved Backward Error Bounds for LU and Cholesky Factorizations*. The local
PDF SHA-256 is
`dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`.

The selected result is Lemma 4.1, PDF page 10, printed page 693, section 4.1.

## Paper statement

For positive paper index `k`, floating-point inputs
`a_1,...,a_(k-1), b_1,...,b_k, c`, and `b_k != 0`, the paper evaluates

`y = (c - sum_(i=1)^(k-1) a_i*b_i) / b_k`

in round-to-nearest floating-point arithmetic. The products are computed
separately, the subtraction sum may use any binary-tree order, and no operation
may underflow or overflow. The computed result `yHat` satisfies

`b_k*yHat*(1 + theta_0) =
  c - sum_(i=1)^(k-1) a_i*b_i*(1 + theta_i)`,

where every coefficient has magnitude at most `k*u`. The input `c` is not
perturbed. When `b_k = 1`, no division is performed and every coefficient has
the sharper bound `(k-1)*u`.

## Lean encoding

Lean uses `m` product terms, so the paper's positive index is `k = m + 1`.
`P05FiniteRoundToNearestFormat` records a finite radix format, precision,
exponent range, symmetric representability, round-to-nearest operation, and
unit roundoff. Its operation laws include the output-relative bound (2.1b), the
nearest-representable comparison used in (2.2), and `u <= 1/2`.
`P05Lemma41Run m` records the floating-point inputs, nonzero denominator,
rounded products, arbitrary permuted binary summation tree, range checks,
computed numerator, and rounded division or division-free unit case.

The run also carries a `P05ProtectedSumTrace` of that numerator computation.
This is the path from the protected `c` leaf to the root of the arbitrary tree.
Each merge records an actual safe rounded addition and the earlier
arbitrary-order sibling-sum estimate (2.4). It contains neither of the final
residual bounds and no backward coefficients.

The proof follows the induction in Theorem 3.1, including the two estimates
(3.5)--(3.6) and the final case split that removes the quadratic term. It then
derives Corollary 3.2's division residual from (2.1b), and performs Lemma 4.1's
sign-aligned construction. Thus both exact protected-`c` identities and their
respective `(m+1)*u` and `m*u` bounds follow from the execution trace.
