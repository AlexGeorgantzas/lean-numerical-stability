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

The iterates are those of column-pivoted iterative refinement:

```text
x_0 = 0,  r_0 = -b,  d_0 = -x_1,
r_m = computed(A*x_m-b),
d_m = computed(A^{-1}*r_m),
x_(m+1) = computed(x_m-d_m).
```

The subtraction by `b` is performed last when computing `r_m`. Each solve now
contains an operational column-pivoted Gaussian-elimination trace: every pivot
is selected as the largest active magnitude in the next column, rows are
swapped, the trailing matrix and right-hand side are updated in working
arithmetic, and the final triangular system is solved by rounded back
substitution. The solve's backward-error relation is tied to that trace's
output. The real-valued arithmetic models do not represent NaN, infinity,
overflow results, or undefined operations.

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
the lower-level quantities used in their proofs: the residual-accumulation
error `f_m`, its equation and printed componentwise bound, and the correction
solve error after applying equation (3.1). From these data, the proof derives
Lemma 4.1 using the definitions of `C_6` and `C_7`. It separately derives the
forward-error half of Lemma 4.2 from the exact identity
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
