# P18-T2 paper context

## Fixed source

The source is Zachary J. Grant, *Perturbed Runge--Kutta Methods for Mixed
Precision Applications*, Journal of Scientific Computing 92, article 6,
2022. The local PDF SHA-256 is
`b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`.

P18-T2 selects the exact coefficient calculation for the corrected implicit
midpoint method, not the following conditional global big-O expectation. The
relevant source consists of:

- the second-order consistency and perturbation conditions (3.4)--(3.5) on
  PDF/article pages 7--8;
- the corrected method (4.1a)--(4.1c) and its displayed Butcher arrays on
  page 11; and
- the two unnumbered identities immediately below those arrays, which the
  paper says eliminate the lower-order perturbation term.

The paper does not define the norm, hidden constants, asymptotic neighborhood,
or stability hypothesis needed to turn its subsequent expected global error
into an exact theorem. No such semantics are invented in this task.

## Exact arrays

The controlled definitions transcribe the displayed two-stage arrays:

```text
A  = [[0,   0], [1/2, 0]]       c  = [0,   1/2]    b  = [0, 1]
Ae = [[1/2, 0], [0,   0]]       ce = [1/2, 0]      be = [0, 0]

Atilde = [[1/2, 0], [1/2, 0]]   ctilde = [1/2, 1/2]
btilde = [0, 1].
```

Here `e = [1,1]`, `p18CoeffDot` is coefficient-vector multiplication,
`p18CoeffMatVec` is the row-sum operation, and `p18CoeffAbsDot` is the
absolute-value product in the nonsmooth conditions (3.4).

## Fixed conclusion

The theorem proves all exact facts needed for the paper's second-order claim:

1. each tilde array is the displayed sum of its full- and low-precision parts;
2. `c = A*e` and `ce = Ae*e`;
3. `btilde*e = 1` and `btilde*ctilde = 1/2`, the order-two consistency
   conditions;
4. `be*e`, `be*ctilde`, `btilde*ce`, and `be*ce` are zero, including the two
   identities printed below (4.1); and
5. the corresponding nonsmooth absolute-value conditions are zero.

These are exact real equalities for the method printed in the paper. The target
does not claim a norm, a global trajectory error, or an asymptotic constant.
