# P19-T2 paper context

## Fixed source

The source is Theorem 3.1 and equations (3.7)-(3.8) on physical PDF page 9
(printed article page 8) of Buttari, Higham, Mary, and Vieuble, *Mixed
precision strategies for preconditioned GMRES: a comprehensive analysis*.
The local PDF SHA-256 is
`67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad`.

Algorithm 2 is on physical page 7. Its modular error models (3.2)-(3.4), the
MGS/Givens least-squares model, and the qualitative smallness conditions
(3.5)-(3.6) are on physical page 8. Appendix A derives the forward result on
physical pages 36-39 and ends with (A.11).

The theorem's quantifier order is retained:

1. start with one nonsingular system, one nonsingular left preconditioner, and
   an increasing full-rank search-basis family through dimension `n`;
2. derive the existence of a dimension `0 < k <= n` satisfying both `4/3`
   basis-conditioning inequalities; and
3. at that same dimension, establish (3.8) for every nonsingular analytical
   right preconditioner `M_R`.

There is no precision filter, eventual witness, preselected key dimension, or
exact Big-O remainder in this reconstruction.

## Algorithm 2 model

`P19Algorithm2Iteration` records the source operations at one admissible
dimension:

- `C_hat = M_L^{-1} A Z_tilde + Delta_c`;
- `b_hat = M_L^{-1} b + Delta_b`;
- the MGS upper-Hessenberg factorization and the columnwise MGS/Givens least-
  squares perturbation data; and
- `x_hat = Z_tilde y_hat + Delta_x`.

`P19Algorithm2Conditions` separately packages the four source error bounds,
the least-squares property, numerical nonsingularity, and the three
qualitative smallness obligations from (3.5)-(3.6). The final estimate is
conditional on this package at the dimension selected by the MGS argument;
these conditions are not assumed at unrelated dimensions.

`P19Theorem31Family` supplies these executions at every positive dimension no
larger than `n`, over one increasing full-column-rank basis family. It contains
no selected dimension, source-condition package, or forward-error conclusion.

The source leaves `c(n,k)` unspecified except for saying that it is a generic
low-degree polynomial factor. At a fixed `n` and `k`, `dimensionFactor`
represents only that unknown nonnegative value and is required to be at least
one. No polynomial coefficients or numerical degree are invented.

## Existential MGS step

Appendix A explicitly invokes reference [11, equations (5.15)-(5.17)], which
is the corpus's P16 source, together with the Paige MGS analysis. The cited
argument makes a case split:

- if the computed MGS bases remain well conditioned through dimension `n`,
  use `k = n`; or
- otherwise, take the predecessor of the first dimension that loses the
  `4/3` conditioning property. The preceding basis is well conditioned, and
  the MGS input satisfies the near-dependence condition (A.1).

`P19MGSSelectionLaw` records only the reusable local ingredients of that cited
result: dimension one is well conditioned, and loss at `k+1` implies (A.1) at
`k`. It does not contain a key dimension. The target proof performs the finite
first-loss search and constructs the existential witness.

## Appendix-A dependency

`P19StaticAppendixATheory` is uniform in the dimension and in `M_R`. It exposes
the Appendix's first-order expansion only after receiving a dimension produced
by the MGS case split. `P19StaticAppendixAExpansion` contains:

- four contribution vectors linked by one error decomposition;
- one omitted remainder marked second order; and
- raw sensitivity gains in terms of the actual relative magnitudes of
  `Delta_c`, `Delta_b`, the MGS/Givens perturbation, and `Delta_x`.

It does not contain `k`, equation (3.8), or four bounds already multiplied by
`epsilon_c`, `epsilon_b`, `u_g`, and `epsilon_x`. The target proof derives the
three safe relative-error bounds from (3.2)-(3.4), once the selected
iteration's source conditions are supplied, applies the raw gains, uses the
Euclidean triangle inequality, and collects the four terms into `xi`.

The Appendix theory and the MGS selection law are explicit formal interfaces
for mathematical results that this paper invokes from its Appendix and cited
MGS analyses. They are reusable theorem dependencies, not run-specific
certificates of Theorem 3.1.

## Coefficients, norms, and first-order meaning

The target retains

```text
xi = alpha*epsilon_c + beta*epsilon_b + beta*u_g + lambda*epsilon_x,
```

with `alpha`, `beta`, and `lambda` in exactly the positions displayed after
(3.8). Square condition numbers use the paper-authorized Frobenius
interpretation. `P19StaticRightQuantities` supplies exact singular-value
semantics and positivity evidence for the displayed divisions; it does not
alter the analytical right-preconditioner's universal quantifier.

The paper defines `lesssim` only as omission of negligible second-order terms
and provides neither a threshold nor an asymptotic variable. Accordingly,
`P19FirstOrderSemantics` parameterizes the qualitative predicates "small" and
"second order". `p19FirstOrderLe` retains an exact remainder tagged by that
semantics. This states no filter convergence, no numerical hidden constant,
and no project-selected limit path.

The final result is the normalized vector 2-norm forward error for the actual
Algorithm 2 output. As in the paper's real standard-model analysis, overflow,
underflow, subnormals, infinities, and NaNs are outside this task.
