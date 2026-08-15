# P16-T2 paper context

## Fixed source

The source is Alfredo Buttari, Nicholas J. Higham, Theo Mary, and Bastien
Vieublé (2026), *A modular framework for the backward error analysis of
GMRES*. The local PDF SHA-256 is
`8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`.

The selected result is the backward-error half of Lemma 4.2, equations
(4.14)--(4.15), on PDF page 19 (printed page 1957). Its operation models
(4.1)--(4.3) are on PDF page 17 (printed page 1955), and its proof uses the
exact residual identity (4.18) and following derivation on PDF page 20
(printed page 1958). Section 2 defines `≲` as comparison after negligible
second-order terms are dropped.

## Paper statement

Fix an iteration `i >= 0` of generic iterative refinement for the nonsingular
real system `A x = b`, where `A` is square and `b != 0`. The hatted quantities
are computed. The residual and update models are

```text
rHat_i = b - A xHat_i + deltaR_i,
||deltaR_i||_2 <= epsilonR (||b||_2 + ||A||_F ||xHat_i||_2),

xHat_(i+1) = xHat_i + correctionHat_i + deltaX_i,
||deltaX_i||_2 <= epsilonU ||xHat_(i+1)||_2,
```

with nonnegative small `epsilonR` and `epsilonU`. If nonnegative `w_i` and
`omega_i` satisfy (4.14),

```text
||rHat_i - A correctionHat_i||_2
  <= w_i ||b - A xHat_i||_2
       + omega_i (||b||_2 + ||A||_F ||xHat_(i+1)||_2),
```

then (4.15) states

```text
||b - A xHat_(i+1)||_2
  ≲ w_i ||b - A xHat_i||_2
       + (epsilonR + epsilonU + omega_i)
           (||b||_2 + ||A||_F ||xHat_(i+1)||_2).
```

Before norms and first-order simplification, equation (4.18) is the exact
identity

```text
A xHat_(i+1) - b
  = deltaR_i + A correctionHat_i - rHat_i + A deltaX_i.
```

The result is for a generic correction solver. It does not assume that the
correction is computed by MOD-GMRES.

## Lean encoding

`P16Lemma42BackwardStep` links every quantity to one computed generic
iterative-refinement step and records (4.1), (4.2), (4.14), parameter signs,
and smallness. A fixed natural number records the paper's iteration index.

The paper gives no numerical constant for `≲`. The target therefore uses a
family of fixed-dimension, fixed-iteration steps along a filter. The function
`scale` tends to zero, and

`p16FirstOrderLeAt l scale lhs rhs`

means that eventually

```text
lhs(t) <= rhs(t) + |remainder(t)|
```

for some `remainder = O(scale^2)`. Hidden Big-O constants may depend on the
fixed dimension and iteration, as the paper permits. The residual and update
accuracy parameters are nonnegative families tending to zero, which is the
formal meaning used here for `epsilonR, epsilonU << 1`.

The iterate comparison used after (4.18),
`||xHat_i||_2 ≲ ||xHat_(i+1)||_2`, is recorded with this same relation. The
target derives both the exact identity (4.18) and the first-order recurrence
(4.15). It does not replace either `≲` by exact `<=` and does not add the
stronger hypothesis `||xHat_i||_2 <= ||xHat_(i+1)||_2`.

All vectors use the Euclidean norm and matrices use the Frobenius norm. No
NaN, infinity, overflow, underflow, or subnormal claim is added: the theorem
is conditional on the paper's real-valued normwise operation model.

## Satisfiability

The assumptions have a nontrivial `1 x 1` instance with `A = 1`, `b = 1`,
`xHat_i = 0`, `correctionHat_i = xHat_(i+1) = 1/2`, `rHat_i = 1`, zero
operation errors, `w_i = 1/2`, and `omega_i = 0`. Its next residual norm is
`1/2`, so the target is not satisfied only through a zero residual or an empty
dimension.
