# P15-T3 paper context

## Fixed source

The source is Nicholas J. Higham and Theo Mary (2022), *Solving block
low-rank linear systems by LU factorization is numerically stable*. The local
PDF SHA-256 is
`a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`.

The selected result is Lemma 3.3, equations (3.10)--(3.11), on PDF pages
9--10 (printed pages 959--960). This selection replaces the previously audited
Theorem 4.5 task with the project owner's approval.

## Source statement

The paper takes `A,B` in `R^(b x b)` and low-rank representations

```text
Atilde = XA*YA^T,       Btilde = YB*XB^T,
```

where all four factors are `b x r` and `XA` and `XB` have orthonormal
columns. The approximations satisfy

```text
||A - Atilde||_F <= epsilon*betaA,
||B - Btilde||_F <= epsilon*betaB.
```

The product is evaluated in either of the two orders explicitly allowed by
the lemma:

```text
(XA*(YA^T*YB))*XB^T
XA*((YA^T*YB)*XB^T).
```

Writing `Chat` for the computed result and
`gammaC = gamma_(b + 2*r^(3/2))`, the two selected conclusions are

```text
||Chat - Atilde*Btilde||_F
  <= gammaC*||Atilde||_F*||Btilde||_F,                 (3.10)

||Chat - A*B||_F
  <= gammaC*||A||_F*||B||_F
     + epsilon*(1 + gammaC)
         *(betaA*||B||_F + ||A||_F*betaB
           + epsilon*betaA*betaB).                    (3.11)
```

No asymptotic term is introduced: the target retains every term printed in
the lemma.

## Lean execution model

`P15LowRankMatMulExecution b r` records the two original matrices, all four
factors, the two approximation errors, unit roundoff, and one raw computation
trace. It stores

```text
Atilde = A + approximationErrorA,
Btilde = B + approximationErrorB.
```

This reverses the signs of the paper's displayed differences, but Frobenius
norms are invariant under negation, so the two approximation hypotheses are
equivalent. The model does not identify `A` with `Atilde` or `B` with
`Btilde`.

`P15RoundedMatMulStage` contains only a local additive error and the standard
equation-(2.7) bound

```text
||error||_F <= gamma_inner*||left input||_F*||right input||_F.
```

Its output is defined as the exact product plus that error.
`P15LowRankMatMulTrace` contains exactly three such stages and has separate
constructors for the two parenthesizations. Therefore `run.trace.result` is a
computed matrix linked to one of the paper's permitted evaluations; it is not an
arbitrary matrix and the trace contains neither conclusion (3.10) nor (3.11)
as a field.

The condition `0 <= unitRoundoff` and

```text
(b + 2*r*sqrt(r))*unitRoundoff < 1
```

make every gamma denominator used by the proof positive. The model is over
real matrices and is the usual finite standard-error abstraction, so overflow,
underflow, NaNs, and infinities are outside its scope.

## Derived proof obligations

For each trace order, the proof must:

1. derive the first two-product error from the two local stage errors;
2. use orthonormality to prove left and right Frobenius-norm invariance and
   `||XA||_F = ||XB||_F = sqrt(r)`;
3. combine `gamma_b` and `gamma_r*sqrt(r)` into
   `gamma_(b+r^(3/2))`;
4. combine the final stage into `gamma_(b+2*r^(3/2))`, proving (3.10);
5. expand `(A+EA)*(B+EB)-A*B` and use the two approximation bounds to prove
   (3.11).

The private construction includes a concrete `b=r=1` exact execution, so the
execution assumptions are jointly satisfiable. Condition L uses the frozen
NumStability Frobenius nonnegativity, triangle, and rectangular-product
inequalities. The library contains no complete Lemma-3.3 result, no trace
composition theorem, and no real-index gamma-composition theorem, so the task
remains T3.
