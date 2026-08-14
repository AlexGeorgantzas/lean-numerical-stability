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

## Tall-system wording

The theorem statement prints `(A + DeltaA)xHat = b + deltaB`, while its proof
writes `xHat = (A + DeltaA)^dagger(b + deltaB)`. For a tall inconsistent
least-squares problem those formulas are not equivalent, and the printed
hypotheses do not say that `b + deltaB` lies in the perturbed column space.

The formal target therefore states the consequence that is valid for the
paper's LSQR pseudoinverse witness without adding a consistency assumption:
`xHat` satisfies the least-squares normal equation for
`(A + DeltaA, b + deltaB)`. It also retains the exact factorized solution
chain through `(RHat + DeltaRHat)^{-1}` and
`(YHat + DeltaYHat)^dagger`. No numerical bound on `deltaB` is added, because
Theorem 3.5 does not provide one.
