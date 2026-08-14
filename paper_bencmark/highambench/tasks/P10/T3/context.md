# P10-T3 paper context

## Fixed source

The source is James Demmel, Ioana Dumitriu, and Olga Holtz (2007), *Fast
linear algebra is stable*. The local PDF SHA-256 is
`0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`.

The selected result is the ordinary recursive Sylvester solver `SylR`, its
first-order forward-error recurrence, equation (20), and the resulting
logarithmic-stability conclusion in section 6.3. The algorithm and exact block
equations (13)--(19) appear on PDF pages 26--27, printed pages 84--85. The four
block-error estimates, recurrence, equation (20), and comparison with a
conventional solver appear on PDF page 28, printed page 86.

## Mathematical setting

The exact problem is

`A * R - R * B = -C`,

where `A` and `B` are upper triangular and all matrices have positive
power-of-two dimension. `SylR` recursively computes the blocks in this order:

1. `R21` from equation (15),
2. `R11` from equation (16), after forming `C11 + A12 * R21`,
3. `R22` from equation (17), after forming `C22 - R21 * B12`,
4. `R12` from equation (18), after forming
   `C12 - R11 * B12 + A12 * R22`.

The separation is the Frobenius variational quantity

`sep(A,B) = min_{norm(R)_F = 1} norm(A*R - R*B)_F`.

Every recursive diagonal-block problem satisfies equation (19), so its
separation is at least the top-level separation. The matrix-product model (8)
and right-hand-side sensitivity then give the four displayed block estimates
on printed page 86. Their sum has multiplier

`4 + 2 * (norm(A)_F + norm(B)_F) / sep(A,B)`

and forcing term

`epsilon / sep(A,B) *
  (3 * norm(C)_F +
    2 * mu(n/2) * (norm(A)_F + norm(B)_F) * norm(R)_F)`.

## Lean statement

`P10SylRRun depth` is a proof-carrying real-valued execution family for
dimension `n = 2^depth`. It records the exact and first-order computed
solutions, the four recursive calls and their order, upper-triangular block
structure, exact right-hand sides, Frobenius separation certificates,
equation (19), the product-error estimates, a polynomial multiplication-error
factor `mu`, and the attained worst error at every recursion level.
Each recursive problem's forward error is measured against the exact solution
for its rounded input. Separate block errors compare the same computed result
with the parent problem's exact block, so rounded-right-hand-side error is not
silently folded into or removed from the induction hypothesis.

The real-valued model is the finite standard regime. Exceptional values are
out of scope. The forward error is explicitly first order: it represents the
same suppression of higher-order terms used by the paper in applying (8).

The target derives all of the following rather than assuming a detached scalar
recurrence:

- the displayed recurrence at every recursion level;
- an explicit finite version of equation (20), using universal constant `2`
  in place of the paper's unspecified big-O constant;
- the equation-(20) bound rewritten as an amplification of the conventional
  forward-error scale;
- `1 + log2(2^depth) = depth + 1`, making the condition-number exponent
  polynomial in the logarithm of the dimension.
