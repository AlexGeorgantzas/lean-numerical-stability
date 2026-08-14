# P09-T3 paper context

## Fixed source

The source is George U. Ramos (1971), *Roundoff Error Analysis of the Fast
Fourier Transform*. The local PDF SHA-256 is
`9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`.

The selected result is Theorem 2(a) and its complete telescoping proof on PDF
pages 8--9, printed pages 764--765, section 4. Equation (4.1) and the array
definitions begin on PDF page 7, printed page 763.

## Arrays, norms, and transforms

`P09MultidimensionalFftPlan` has `m > 0` axes. Every axis has a positive
length `N_l` and a certified one-dimensional mixed-radix FFT plan. Arrays are
complex functions on the product index set

```text
ZMod N_1 x ... x ZMod N_m.
```

`p09MultiRms` is the complex Euclidean norm divided by
`sqrt(N_1 * ... * N_m)`, exactly the normalization preceding Theorem 2.
`p09CoordinateTransform` is the positive-sign unnormalized DFT in one
coordinate. `p09ApplyCoordinatePrefix axis m` applies `T_m` first and `T_1`
last, matching the nested order in the proof. The plan certifies the repeated
RMS scaling from equation (4.4).

## Linked computation

`P09MultidimensionalFftRun` records the input `X`, all nested computed states,
and one local roundoff array for each coordinate. Its stage equation is

```text
computedState_l = T_l(computedState_(l+1)) + localError_l.
```

The exact output is `Y = T_1 ... T_m X`; the computed output is
`computedState_0`; and `p09MultiFftRoundoffError` is exactly
`computedOutput - Y`. The run retains the paper's exact telescoping identity:
each local error is propagated through `T_1,...,T_(l-1)`, and all `m` terms sum
to the total output error.

The run also retains the proof's final input condition: applying `fl` to the
input preserves its RMS norm exactly or differs from it by an explicit finite
coefficient times `epsilon`. As in the source, the model adds no semantics for
overflow, underflow, subnormals, NaN, or infinities.

## Local certificates

`P09TheoremTwoRmsCertificate` is the finite form of equations (4.3)--(4.4).
For axis `l`, its first bound uses the inherited one-dimensional constant
`p09AxisK axis_l gamma`, the common Wilkinson `epsilon` and `gamma`, the
coordinate factor `sqrt(N_l)`, the linked computed intermediate state, and an
explicit nonnegative `C_l * epsilon^2` remainder.

The second field records that the propagated intermediate RMS scale equals the
exact output RMS up to `D_l * epsilon`. This includes the exact-or-`O(epsilon)`
input condition on the last stage and the analogous intermediate estimates on
printed page 765. Multiplication by the local first-order error makes these
`D_l` contributions second order.

## Target conclusion

The exact-output RMS is required to be positive because the printed theorem
divides by `Y_RMS` without stating its zero-output convention. The target
proves the exact telescoping identity and

```text
RMS(computedOutput - Y) / RMS(Y)
  <= epsilon * sum_l K(N_l, gamma)
     + (C / RMS(Y)) * epsilon^2,
```

where `C = sum_l (prefixScale_l * C_l + K(N_l,gamma) * D_l)` is the explicit
finite coefficient `p09TheoremTwoRemainderCoeff`. The source does not state
uniformity or values for its `O(epsilon)` and `O(epsilon^2)` constants, so the
formalization adds none.
