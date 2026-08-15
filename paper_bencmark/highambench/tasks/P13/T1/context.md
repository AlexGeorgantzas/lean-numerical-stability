# P13-T1 paper context

## Fixed source

The source is Nicholas J. Higham (2004), *The numerical stability of
barycentric Lagrange interpolation*. The local PDF SHA-256 is
`9ebf8adb699f96c82ccbb153dd6ca592c64475a8bc3e0703a50cb659b012c520`.

The selected result is Definition 2.1 together with Lemma 2.2 and equation
(2.2), all on PDF page 2 / printed page 548. Equation (2.1) on the same page
supplies the exact Lagrange representation used by both statements.

## Fixed interpolation problem

`P13LagrangeProblem n` represents a degree-`n` interpolation problem with
exactly `n+1` pairwise distinct real nodes, real data values, and a fixed real
evaluation point. Its basis values are

```text
ell_j(x) = product_{k != j} (x - x_k) / (x_j - x_k),
```

and its exact interpolated value is

```text
p_f(x) = sum_{j=0}^n ell_j(x) f_j.
```

The nodes and evaluation point remain fixed throughout the condition-number
definition. Only the data values are perturbed. Distinctness makes every
Lagrange-basis denominator nonzero; the target additionally assumes
`p_f(x) != 0`, exactly as Definition 2.1 does.

## Perturbation condition number

At a positive radius `epsilon`, `p13DataPerturbation f deltaF epsilon` is the
paper's componentwise constraint

```text
|deltaF_j| <= epsilon |f_j|  for every j.
```

`p13ScaledPerturbationSet` contains the corresponding relative output changes
divided by `epsilon`, and `p13PerturbationSupremum` is its real supremum.
Definition 2.1 prints `epsilon -> 0` without a separate direction. Since the
perturbation radius is nonnegative and division by zero is excluded, the Lean
definition records the natural positive-radius interpretation
`nhdsWithin 0 (Set.Ioi 0)`.

`p13IsComponentwiseConditionNumber ell f condition` states that these suprema
tend to `condition` through positive radii. This is the equality with the
limit in Definition 2.1; it does not define the condition number circularly as
the closed-form quotient.

## Fixed conclusion

Lemma 2.2 identifies the perturbation-defined condition number exactly as

```text
sum_{j=0}^n |ell_j(x) f_j| / |p_f(x)|
```

and states that this quotient is at least one. The target includes both
conclusions. For every positive radius, the componentwise perturbation bound
gives the quotient as an upper bound, while

```text
deltaF_j = epsilon * sign(ell_j(x)) * |f_j|
```

attains it. Hence the supremum is exactly the quotient at every positive
radius and therefore has the required limit. The lower bound is the triangle
inequality divided by `|p_f(x)|`.

This is an exact real-arithmetic conditioning result. It does not model a
floating-point interpolation algorithm, rounding, exceptional values, or
higher-order terms. The degree-zero, one-node case with data value one
witnesses that the assumptions are satisfiable and the quotient can equal
one.
