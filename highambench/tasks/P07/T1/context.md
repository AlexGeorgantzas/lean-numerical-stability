# P07-T1 paper context

## Fixed source

The source is Maike Meier, Yuji Nakatsukasa, Alex Townsend, and Marcus Webb
(2024), *Are Sketch-and-Precondition Least Squares Solvers Numerically
Stable?* The local PDF SHA-256 is
`4c4d638b359719f47e2c4664a50e9fa8e4704e8b6b39923d73c41883a97c5790`.

The selected result is all of Lemma 3.2, PDF page 13, printed page 917,
section 3.1. The paper concludes both that the computed matrix is full rank and
that its spectral condition number satisfies the displayed quantitative bound.

## Paper setup and computation

The standing setup has real matrices

```text
A : m by n,       S : s by m,       m > s > n > 0,
```

with both `A` and `SA` of full column rank. Lemma 3.1 forms the finite-precision
sketch and its computed Householder QR factor:

```text
BHat = SA + E1,
Qtilde RHat = BHat + E2,
```

where `Qtilde` has orthonormal columns and `RHat` is upper triangular and
invertible. Lemma 3.2 uses that computed `RHat`. It obtains `YHat` by solving

```text
YHat RHat = A
```

row by row with finite-precision forward substitution. The target represents
this execution by `P07Lemma32ForwardRun`; its recurrence uses the supplied
rounded addition, subtraction, multiplication, and division operations. Thus
`YHat` is not an arbitrary matrix carrying an unrelated perturbation.

The exact comparison matrix and error are exactly

```text
Y = A RHat^{-1},
DeltaY = YHat - A RHat^{-1}.
```

## Lemma 3.2

The paper defines

```text
epsilon_2 = ||DeltaY||_2 ||(A RHat^{-1})^dagger||_2.
```

If `epsilon_2 < 1`, it proves

```text
YHat has full column rank,

kappa_2(YHat) <=
  (kappa_2(A RHat^{-1}) + epsilon_2) / (1 - epsilon_2).
```

`P07RectSpectralExtrema` records the attained largest and smallest singular
values, so its fields are exact values rather than loose norm certificates.
`P07MoorePenrosePseudoinverse` records all four Penrose equations, and
`P07MatrixPseudoinverseSpectralData` identifies the exact pseudoinverse norm
with the reciprocal smallest singular value when that value is nonzero.
Consequently `p07ConditionNumber2` is the paper's spectral condition number,
and `p07Lemma32Epsilon` is the paper's exact `epsilon_2`.

Lemma 3.2 assumes `epsilon_2 < 1`; it does not itself derive an a priori
roundoff bound for `epsilon_2`. Those later estimates belong to Lemma 3.3 and
are intentionally not added here. The source uses its standard finite-
precision model and gives no separate overflow, underflow, NaN, or infinity
clauses for this lemma.
