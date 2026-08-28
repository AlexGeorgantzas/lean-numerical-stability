# P16-T2 paper context

## Fixed source

The source is Alfredo Buttari, Nicholas J. Higham, Theo Mary, and Bastien
Vieublé (2026), *A modular framework for the backward error analysis of
GMRES*. The local PDF SHA-256 is
`8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`.

The retained source is the backward-error half of Lemma 4.2, equations
(4.14)-(4.15), on PDF page 19 (printed page 1957). Its operation models
(4.1)-(4.3) are on PDF pages 16-17 (printed pages 1954-1955). The proof uses
the exact residual identity (4.18) and the following derivation on PDF page 20
(printed page 1958).

This is a project-corrected task. The published lemma omits a comparison that
its proof requires; the counterexample and correction are summarized below.

## Printed branch

Fix an iteration `i >= 0` of generic iterative refinement for the
nonsingular real system `A x = b`, where `A` is square and `b != 0`.
The computed residual and update satisfy

```text
rHat_i = b - A xHat_i + deltaR_i,
||deltaR_i||_2 <= epsilonR (||b||_2 + ||A||_F ||xHat_i||_2),

xHat_(i+1) = xHat_i + correctionHat_i + deltaX_i,
||deltaX_i||_2 <= epsilonU ||xHat_(i+1)||_2.
```

For nonnegative `w_i` and `omega_i`, equation (4.14) assumes

```text
||rHat_i - A correctionHat_i||_2
  <= w_i ||b - A xHat_i||_2
       + omega_i (||b||_2 + ||A||_F ||xHat_(i+1)||_2).
```

Equation (4.15) claims the first-order recurrence

```text
||b - A xHat_(i+1)||_2
  lesssim w_i ||b - A xHat_i||_2
       + (epsilonR + epsilonU + omega_i)
           (||b||_2 + ||A||_F ||xHat_(i+1)||_2).
```

Before norms and first-order simplification, equation (4.18) is the exact
identity

```text
A xHat_(i+1) - b
  = deltaR_i + A correctionHat_i - rHat_i + A deltaX_i.
```

The result concerns a generic correction solver. It does not assume that the
correction is computed by MOD-GMRES.

## Source defect

Immediately after (4.18), the proof says that it obtains (4.15) while
"considering"

```text
||xHat_i||_2 lesssim ||xHat_(i+1)||_2.
```

That comparison is absent from Lemma 4.2's hypotheses and does not follow from
(4.1), (4.2), or (4.14). Without it, the recurrence is false. For
`0 < epsilonR < 1`, a one-dimensional counterexample takes `A=b=1`,
`xHat_i=1/epsilonR-1`, `xHat_(i+1)=0`, `deltaR_i=-1`,
`correctionHat_i=-(1/epsilonR-1)`, and
`deltaX_i=epsilonU=w_i=omega_i=0`. All printed operation and correction
bounds hold, but (4.15) reduces to `1 lesssim epsilonR` as
`epsilonR -> 0`.

## Project correction

P16-T2 retains Lemma 4.2 as its cited source and adds the proof-required
iterate comparison as an explicit theorem hypothesis. It is not hidden in the
computed-step structure and is not described as a printed premise. This is a
project-authored correction, not an author-issued erratum.

`P16Lemma42BackwardStep` contains only the data and hypotheses from (4.1),
(4.2), and (4.14), including parameter signs and the selected first-order
regime. The target separately assumes

```text
p16FirstOrderLeAt l scale
  (fun t => ||xHat_i(t)||_2)
  (fun t => ||xHat_(i+1)(t)||_2).
```

The target then derives both exact identity (4.18) and recurrence (4.15).
Neither conclusion is supplied by a certificate field.

## First-order semantics

Section 2 defines `lesssim` only as comparison after negligible second-order
terms are dropped. The paper gives no asymptotic variable or numerical
remainder constant. This task makes one explicit benchmark choice:

`p16FirstOrderLeAt l scale lhs rhs` means that eventually

```text
lhs(t) <= rhs(t) + |remainder(t)|
```

for some `remainder = O(scale^2)`, with `scale -> 0`. The residual and
update accuracy families are nonnegative and tend to zero. Dimensions and the
fixed refinement iteration remain outside the limit.

All vectors use the Euclidean norm and matrices use the Frobenius norm. The
real-valued operation model makes no claim about overflow, underflow,
subnormals, NaNs, or infinities.

Because the iterate comparison and the precise filter-level interpretation of
`lesssim` are project-supplied, this is a project-corrected benchmark target
rather than a literal formalization of the printed lemma.

## Satisfiability

The assumptions have a nontrivial `1 x 1` instance with `A = b = 1`,
`xHat_i = 0`, `correctionHat_i = xHat_(i+1) = 1/2`, zero operation errors,
`w_i = 1/2`, and `omega_i = 0`. The next residual norm is `1/2`, and the
explicit iterate comparison holds with zero remainder.
