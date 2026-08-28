# P08-T3 paper context

## Fixed source

The source is Robert D. Skeel (1980), *Iterative Refinement Implies Numerical
Stability for Gaussian Elimination*. The local PDF SHA-256 is
`f520066b46331dcbf25e51345c5ff5ffffe8fcad573d7f46e68834f83b3a2c54`.

The selected result is Lemma 4.3 on PDF page 12, printed page 827, together
with the definitions and prior bounds it uses on printed pages 823-827.

## Numerical setting

The source studies a nonsingular real system `A*x=b` in positive dimension.
Single-precision arithmetic has positive unit roundoff `u`, all represented
floating-point operations are assumed well-defined, and `n*u <= 0.01`.
Residual accumulation is either single precision, with `ubar=u`, or double
precision followed by conversion to single precision, with `ubar=u^2` and
conversion relative error bounded by `u`.

The iterates are those of column-pivoted iterative refinement. The actual
loop starts at `m=1`:

```text
x_1 = computed(A^{-1}*b),
for m = 1, 2, ...:
  r_m = computed(A*x_m-b),
  d_m = computed(A^{-1}*r_m),
  x_(m+1) = computed(x_m-d_m).
```

The paper then introduces `x_0=0`, `r_0=-b`, and `d_0=-x_1` only as convenient
auxiliary definitions. The Lean run does the same: it does not require a fresh
solve of `A*d_0=-b` or a rounded computation of `x_1=x_0-d_0`.

The subtraction by `b` is performed last when computing `r_m`. The source does
not fix the minor computational details of column-pivoted elimination, so the
Lean run uses the displayed componentwise solve certificate from printed page
823 instead of selecting a particular pivot/update/back-substitution trace.
Likewise, the rounded refinement update is represented by the exact source
equation

```text
x_(m+1) = x_m-d_m+h_(m+1),
|h_(m+1)| <= u*|x_m-d_m|.
```

The real-valued model is conditional on all floating-point results being
well-defined; it does not add NaN, infinity, overflow, or underflow semantics.

## Exact residual and norm

The paper defines

```text
q_(m+1) = A*(x_m-d_m)-b.
```

This is an exact residual of the unrounded corrected value. It is not the
stored computed residual `r_m`. In Lean,
`p08ExactResidualAfterCorrection run m` is exactly this `q_(m+1)`; therefore
Lean index `m=0` is the paper's `q_1` base case and no `q_0` is introduced.

Every displayed vector inequality is componentwise. The chosen norm is an
absolute monotone vector norm normalized by `||e_i||=1`, extended to its
induced matrix norm. The source's nonstandard quantity is retained as

```text
kappa(A^{-1}) = || |A| |A^{-1}| ||.
```

## Source constants and prior lemmas

`P08Lemma43Constants` records the source definitions of `c_1`, `c_3`, `c_4`,
`c_5`, `c_8`, and `C_2`, `C_6`, ..., `C_12`, including the two-sided
resolvent identities. In particular,

```text
C_8  = (1+u) C_6,                    c_8 = ||C_8||,
C_9  = C_6 + c_3 I,
C_10 = C_6 + (n*ubar/u+c_3*u) I + ubar C_7 |A| |A^{-1}|,
C_11 = (I-u C_8 |A| |A^{-1}|)^{-1} C_9,
C_12 = (I-u C_8 |A| |A^{-1}|)^{-1} (n C_8+C_7).
```

The paper describes these nonnegative anonymous quantities as bounded above
by functions of `n`, independently of `A` and `b`. The target therefore fixes
`P08DimensionOnlyConstantBounds` before the problem run, and every scalar and
matrix constant carries the corresponding dimension-only bound in addition
to its exact displayed definition.

`P08Lemma43RoundoffAnalysis` does not assume Lemma 4.1 or Lemma 4.2. It records
the quantities used in their proofs: the residual-accumulation error `f_m`, its
equation and printed componentwise bound, and the correction-solve error `g_m`
after applying equation (3.1). These equations cover the auxiliary `m=0` case
through the original solve, rather than postulating a second solve. From these
data, the proof derives Lemma 4.1 using the definitions of `C_6` and `C_7`. It
separately derives the forward-error half of Lemma 4.2 from the exact identity
`x_m-d_m-x=A^{-1}q_(m+1)` and the rounded subtraction model. Only then does it
derive the page-827 recurrence and perform the Lemma 4.3 induction.

## Selected result

For every `m >= 0`, Lemma 4.3 states componentwise

```text
|q_(m+1)| <= (u C_8 |A| |A^{-1}|)^m u C_10 |A| |x|
             + n ubar |A| |x|
             + u^2 C_11 |A| |x|
             + ubar u C_12 |A| |A^{-1}| |A| |x|,
```

assuming `c_8*u*kappa(A^{-1}) <= 1/2`. The proof first derives the meaningful
`m>=1` recurrence involving `q_m`, `C_8`, `C_9`, and `C_7`; it handles `q_1`
separately with Lemma 4.1 and then performs induction. The Lean bound has the
same four terms, multiplication order, exponent, and base index. It contains
no limit and drops no `O(u^2)` term.
