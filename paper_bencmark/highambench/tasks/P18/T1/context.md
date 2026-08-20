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

The adjacent big-O statements are not part of P18-T1. The paper does not fix
their norm, constants, neighborhoods, or quantifier dependencies, and it makes
the global statement conditional on stability. Those claims therefore cannot
be replaced by an exact Euclidean assertion. P18-T1 selects only the exact
decomposition and adds a universally valid Euclidean-norm corollary.

## Additive Runge--Kutta execution

`P18AdditiveRKOneStepRun n s` represents one positive-dimensional, positive
stage-count execution of the additive Runge--Kutta formulation in equation
(3.2). It records:

- the initial state and exact one-step state;
- the step size `step` and perturbation size `epsilon`;
- the full-precision operator `F` and perturbation operator `tau`;
- the displayed coefficient families;
- the unperturbed stages and output obtained by setting `epsilon = 0`; and
- the perturbed stages and output satisfying both equations (3.2a)--(3.2b).

The run follows the positive `epsilon * tau` signs printed in equation (3.2).
Equation (2.3) prints the opposite definition of `tau`; the paper does not
resolve that sign inconsistency. The selected error split is algebraic and is
valid under either convention, so the target does not infer any sign-dependent
claim.

## Error definitions

The controlled definitions make the paper's three errors explicit:

```text
E     = exactNext - perturbedNext
E_sch = exactNext - schemeNext
E_per = schemeNext - perturbedNext.
```

Consequently `E = E_sch + E_per` must be derived from the algorithm-linked
outputs; it is not supplied as a field of the run.

## Fixed conclusion

The theorem has two conclusions:

1. the exact paper decomposition `E = E_sch + E_per`; and
2. the stronger Euclidean consequence
   `||E||_2 <= ||E_sch||_2 + ||E_per||_2`.

The paper does not claim that its later big-O notation uses the Euclidean norm.
The norm inequality is recorded only as an added corollary for the finite real
execution model, not as an interpretation of those asymptotic statements.
