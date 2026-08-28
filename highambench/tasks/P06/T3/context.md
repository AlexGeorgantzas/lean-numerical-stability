# P06-T3 paper context

## Fixed source

The source is Michael P. Connolly and Nicholas J. Higham (2023),
*Probabilistic Rounding Error Analysis of Householder QR Factorization*. The
local PDF SHA-256 is
`c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`.

The selected result is the product expansion in equations (4.8)--(4.9), PDF
page 7, printed page 1152, section 4, inside the proof of Lemma 4.2.

## Local context and statement

The source begins with positive integers `m` and `r`, a starting vector `b` in
`R^m`, and normalized Householder vectors `v_j` satisfying
`v_j^T v_j = 2`. Thus

```text
P_j = I - v_j v_j^T,
b_(r+1) = P_r ... P_1 b.
```

Under Model 1.5, Lemma 4.1 represents the computed vector as

```text
bHat_(r+1) = (P_r + DeltaP_r) ... (P_1 + DeltaP_1) b.       (4.1)
```

Lemma 4.2 assumes with probability one that every local perturbation satisfies
the subordinate matrix 2-norm bound (4.2). The execution family
`P06HouseholderApplicationFamily` keeps the distinguished computation at
`model.unitRoundoff` linked to the Model 1.5 scalar trace. Its parameter `u`
also supplies the family needed to interpret the paper's asymptotic notation.
On the probability-one event, `P06Lemma42VectorAssumption` records both (4.2)
at the distinguished unit roundoff and the equivalent local statement
`DeltaP_j(u) = O(u)`.

## Equations (4.8)--(4.9)

The first line of (4.8) expands the perturbed product as the exact result plus
all terms containing exactly one local perturbation and a matrix-valued
second-order remainder:

```text
bHat_(r+1) = b_(r+1)
  + (sum_(j=1)^r P_r ... P_(j+1) DeltaP_j P_(j-1) ... P_1
     + O(u^2)) b.
```

`p06ApplicationFirstOrderMatrix` is exactly this single-insertion sum. The
existential `unfactoredRemainder` contains every product term with at least two
local perturbations. The target proves each matrix entry is `O(u^2)`; for a
fixed finite dimension this preserves the paper's matrix-valued order without
choosing a norm, hidden constant, or parameter uniformity that the source does
not specify.

For the second line of (4.8), the paper sets

```text
Q = (P_r ... P_1)^T,
F_j = P_1 ... P_j DeltaP_j P_(j-1) ... P_1.                 (4.9)
```

The target also derives

```text
bHat_(r+1) = b_(r+1) + Q^T (sum_(j=1)^r F_j + O(u^2)) b.
```

The zero-based Lean index `j : Fin r` represents paper index `j+1`.
`p06HouseholderProduct P 0 = I`, so the endpoint products are identities.
The left factor in `p06ApplicationF` includes `P_j`, while its right factor
ends at `P_(j-1)`, exactly as in (4.9).

Equations (4.8)--(4.9) do not state their own probability bound. The target
therefore retains the probability-one local event as a hypothesis but does not
attach Lemma 4.2's later probability `1 - 2m exp(-lambda^2)` to the algebraic
expansion. It also does not import the later `r=n` estimate for the omitted
higher-order terms.
