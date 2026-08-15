# P11-T2 paper context

## Fixed source

The source is Alicja Smoktunowicz, Jesse L. Barlow, and Julien Langou (2006),
*A note on the error analysis of classical Gram-Schmidt*. The local PDF
SHA-256 is
`72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`.

The selected result is the exact unnumbered two-line identity in the derivation
of Theorem 1(7), PDF page 14, printed page 312. It begins with
`I - Q_k^T Q_k` and precedes the subsequent spectral-norm estimate.

## Source setting and dimensions

The paper fixes a full-column-rank input matrix `A` in `R^(m x n)`, with
positive dimensions and `n <= m`. Algorithm 2, CGS-P, computes rectangular
`Q` and upper-triangular `R`. For each paper index `k = 1,...,n`:

- `A_k`, `Delta A_k`, and `Q_k` are `m x k` matrices;
- `R_k`, `R_k^(-1)`, `E_k`, and the identity are `k x k` matrices;
- `Q_k R_k = A_k + Delta A_k`;
- `E_k = R_k^T R_k - A_k^T A_k`.

Theorem 1's condition (3) makes each `R_k` nonsingular. The selected equality
then substitutes `Q_k = (A_k + Delta A_k) R_k^(-1)` into the orthogonality
defect and expands the product exactly.

In Lean, `k : Fin n` is zero-based and represents the paper's one-based index
`k+1`. Thus the rectangular factors have type
`P11RectMatrix m (k.val + 1)`, while `R` and `Rinv` have type
`P11Matrix (k.val + 1)`. The hypothesis `hmn : n <= m` preserves the paper's
outer dimension relation and the `Fin n` binder excludes the paper-invalid
zero-column case.

## Fixed statement

The hypotheses are

```text
Q * R = A + dA
R * Rinv = I.
```

For finite square real matrices, the certified right inverse is the inverse
used by the paper. Define

```text
E = R^T*R - A^T*A
core = E - A^T*dA - dA^T*A - dA^T*dA.
```

The target states the exact matrix equality

```text
I - Q^T*Q = Rinv^T * core * Rinv.
```

The order, signs, transpose placement, and quadratic `dA^T*dA` term are the
ones printed on page 312.

## Scope and exclusions

The target is a genuine algebraic strengthening of the selected source
identity. Every computed CGS-P leading-factor tuple in Theorem 1 instantiates
the Lean binders and hypotheses, while Lean also proves the same identity for
arbitrary rectangular tuples with the source dimensions and equations. The
extra tuples do not remove or specialize any paper case.

Although the enclosing theorem concerns computed floating-point factors, the
selected identity is exact post-analysis matrix algebra. Machine precision,
the IEEE normalized-range model, condition (3), spectral norms, and
`O(epsilonM^2)` enter the surrounding theorem and the inequality after this
display; none operates inside the selected equality and none is added to this
task.

The proof rewrites `Q` using the right inverse, transposes that product,
reassociates the compatible rectangular products, expands
`(A+dA)^T(A+dA)`, and collects the four central terms.
