# P18-T1 paper context

## Fixed source

The source is Zachary J. Grant, *Perturbed Runge--Kutta Methods for Mixed
Precision Applications*, Journal of Scientific Computing 92, article 6,
2022. The local PDF SHA-256 is
`b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`.

The selected result is the exact, unnumbered one-step decomposition immediately
following equation (3.3) on PDF and article page 5:

```text
E = E_sch + E_per.
```

The adjacent local big-O orders and stability-conditional global estimate are
not part of P18-T1. The paper does not specify their norm, constants, limiting
regime, or stability notion, so this task does not assign them exact semantics.

## Additive Runge--Kutta execution

`P18AdditiveRKOneStepRun State s` works over an arbitrary real module `State`.
It therefore does not restrict the paper's unspecified state space to a
positive-dimensional finite Euclidean vector space. The stage count is
positive, as in the paper's `s`-stage method.

The run records the original additive method (3.1) directly:

- `F` and `FEpsilon` are the two operators;
- `a`, `aPerturbation`, `b`, and `bPerturbation` are the two coefficient
  channels;
- `perturbedStages` and `perturbedNext` satisfy (3.1a)--(3.1b); and
- `schemeStages` and `schemeNext` are the comparison method obtained by
  replacing `FEpsilon` with `F`, equivalently using the combined coefficients
  with the unperturbed operator.

The scale `epsilon` is nonzero because equation (2.3) divides by it. Instead of
division, the run records the equivalent exact relation

```text
epsilon * tau(y) = F(y) - FEpsilon(y).
```

This follows the sign in (2.3). The paper's (3.2) prints plus perturbation terms
that are inconsistent with that definition. Since the run uses the original
(3.1) equations rather than the rewritten (3.2) equations, no correction of
the source's conflicting signs is needed. The exact error split is independent
of the conflict.

The source's `F^epsilon-F = O(epsilon)` assumption is needed for its surrounding
order analysis, not for the selected algebraic split. Omitting a bound on
`tau` makes this exact theorem more general; it does not turn a big-O claim into
an exact bound.

## Error definitions

The paper names the three errors but does not define their signed baselines.
The controlled definitions make one orientation explicit for an arbitrary
reference state:

```text
E     = referenceNext - perturbedNext
E_sch = referenceNext - schemeNext
E_per = schemeNext - perturbedNext.
```

Because the theorem holds for every `referenceNext`, it includes whichever
exact one-step reference the paper intends without adding an ODE-flow model or
restricting the baseline. The intermediate scheme output cancels, giving the
paper's split.

## Fixed conclusion

The theorem proves three linked facts:

1. the selected exact decomposition `E = E_sch + E_per`;
2. the exact expansion of `E_per` obtained by subtracting the two algorithmic
   output equations (3.1b); and
3. for every additive observation from `State` into finite real coordinates,
   the Euclidean norm of the observed total error obeys the triangle bound.

The second clause prevents the algorithm fields from being a decorative
premise: it identifies the perturbation contribution with the difference of
the two recorded Runge--Kutta updates. The third clause is a separate universal
corollary. It does not claim that the paper's abstract `E`, its big-O notation,
or its state space uses the Euclidean norm.

No rounding mode, IEEE exceptional-value behavior, smoothness, order
conditions, or stability hypothesis is asserted by this exact split task.
