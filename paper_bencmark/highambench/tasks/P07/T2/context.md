# P07-T2 paper context

## Fixed source

The source is Maike Meier, Yuji Nakatsukasa, Alex Townsend, and Marcus Webb
(2024), *Are Sketch-and-Precondition Least Squares Solvers Numerically
Stable?* The local PDF SHA-256 is
`4c4d638b359719f47e2c4664a50e9fa8e4704e8b6b39923d73c41883a97c5790`.

The selected result is the unnumbered backward-error construction and its
immediate spectral-norm estimate in the proof of Theorem 3.5, PDF page 16,
printed page 920, section 3.4. It is not the later specialization to the
constants `6.04` and `2.01`.

## Algorithm and error witnesses

The source applies SAA Blendenpik, Algorithm 1.3, without SAS initialization.
The earlier stages compute a sketch and Householder-QR factor `RHat`, then form
`YHat = fl(A RHat^{-1})` by forward substitution. These stages are represented
by `P07Lemma31ComputedPreconditioner` and `P07Lemma32ForwardRun`, including
`m > s > n > 0`, full-rank `A` and `SA`, and the finite-precision operation
trace.

Unpreconditioned LSQR is applied directly to the explicitly formed `YHat`.
Equation (3.9) assumes a backward-error witness

```text
zHat = (YHat + DeltaYHat)^dagger (b + deltaB).
```

`DeltaYHat` is the LSQR matrix perturbation. As footnote 5 stresses, it is not
the earlier forward-substitution error `DeltaY` in
`YHat = A RHat^{-1} + DeltaY`.

The final back substitution computes `xHat`. Equation (2.6) supplies

```text
(RHat + DeltaRHat) xHat = zHat,
||DeltaRHat||_2 <= sqrt(n) gamma_n ||RHat||_2,
```

where `gamma_n = n*u/(1-n*u)`. `P07SAABlendenpikRun` retains all these linked
computed quantities and the required valid-gamma regime.

## Selected result

The proof defines the exact matrix perturbation

```text
DeltaA = (YHat RHat - A)
       + DeltaYHat RHat
       + YHat DeltaRHat
       + DeltaYHat DeltaRHat.
```

The mixed product is retained exactly. The rowwise forward-substitution
certificate records the paper's distinct perturbation `Delta_i RHat`, its
componentwise bound

```text
|Delta_i RHat| <= gamma_n |RHat|,
```

and the stated consequence

```text
||YHat RHat - A||_2 <= n gamma_n ||RHat||_2 ||YHat||_2.
```

Combining this with equation (2.6) gives exactly

```text
||DeltaA||_2 <= ||RHat||_2
  ((n + sqrt(n)) gamma_n ||YHat||_2
   + (1 + sqrt(n) gamma_n) ||DeltaYHat||_2).
```

The target also proves `A + DeltaA = (YHat + DeltaYHat)(RHat + DeltaRHat)` and
the factorized computed-solution relation. Thus `DeltaA` is not an unrelated
matrix carrying a generic norm budget.

## Corrected source conditions

The theorem statement prints `(A + DeltaA)xHat = b + deltaB`, while its proof
writes `xHat = (A + DeltaA)^dagger(b + deltaB)`. For a tall inconsistent
least-squares problem those formulas are not equivalent. Moreover, the proof's
identity

```text
((YHat + DeltaYHat)(RHat + DeltaRHat))^dagger
  = (RHat + DeltaRHat)^(-1) (YHat + DeltaYHat)^dagger
```

requires the perturbed LSQR matrix to have full column rank. Equation (3.9)
places no bound on `DeltaYHat`, so the original full-rank facts do not imply
that condition.

This project-corrected target therefore adds exactly two hypotheses:

1. `YHat + DeltaYHat` has full column rank; and
2. `b + deltaB` lies in the range of `A + DeltaA`.

The first makes the displayed product an actual Moore--Penrose pseudoinverse
of `A + DeltaA`; the second turns its projected least-squares solution into
the exact perturbed-system equation printed by Theorem 3.5. The target retains
both claims, the algorithm linkage, all four terms of `DeltaA`, and the exact
immediate norm estimate. No numerical bound on `deltaB` is added because the
source provides none.

These are sufficient conditions supplied by the project, not hypotheses
printed in Theorem 3.5 and not an author-issued correction. Consequently this
task is excluded from ordinary paper-faithfulness acceptance. The source defect
and benchmark decision are recorded in
`paper_bencmark/faithfulness_audit/source_validity/P07-T2.md`.
