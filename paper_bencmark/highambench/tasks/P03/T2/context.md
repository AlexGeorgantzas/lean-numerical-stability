# P03-T2 paper context

## Fixed source

The source is Erin Carson and Nicholas J. Higham, *Accelerating the Solution of
Linear Systems by Iterative Refinement in Three Precisions*, SIAM Journal on
Scientific Computing 40(2), A817--A847, 2018. The local PDF SHA-256 is
`952c6827db21fb2a9362b5aa4d38a1b2c75361f2cc7a3badbb7cd4a232d7b7bc`.

The selected result is Theorem 4.1 on PDF page 9, printed page A825, in
section 4, "Normwise backward error analysis." Its derivation uses Algorithm
1.1 (PDF page 2), solver condition (2.4) (PDF page 5), the residual and update
models (3.3) and (3.6) (PDF page 7), and identity (4.1) (PDF page 8).

## Algorithm model

`P03NormwiseIRRun n` represents one complete indexed execution model for the
unscaled Algorithm 1.1. It contains the nonsingular system `A x = b`, an
explicit inverse `Ainv`, and the computed iterates `x i`, residuals `rHat i`,
corrections `dHat i`, residual errors `deltaR i`, and update errors `deltaX i`.
The inverse-action field is the finite-dimensional nonsingularity certificate.

The four unit roundoffs satisfy `uR <= u <= uS <= uF`. Residuals are computed
at `uR` and rounded to `uS`, corrections have effective precision `uS` and are
stored at `u`, and updates are performed at `u`. Because every state is
real-valued and must satisfy the displayed standard-model contracts, this is
the paper's finite-value regime in which underflow and overflow are excluded.

The maximum row nonzero count `p` of the augmented matrix `[A b]` is defined by
`p03MaxAugmentedRowNnz A b`, and `gamma uR p = p*uR/(1-p*uR)`. The run requires
the corresponding positive-denominator condition. The nonnegative solver
quantities `c1 i` and `c2 i` may vary with the iteration, as allowed by the
discussion following (2.4).

For every iteration, the run records exactly the source-level contracts:

- `rHat i = b - A*(x i) + deltaR i`, with the componentwise bound (3.3);
- the infinity-norm correction-defect condition (2.4) for
  `rHat i - A*(dHat i)`;
- `x (i+1) = x i + dHat i + deltaX i`, with the componentwise bound (3.6);
- `c1 i * kappaInf(A) * uS < 1`, where
  `kappaInf(A) = ||Ainv||_inf * ||A||_inf`.

These are algorithm and floating-point-model premises, not preassembled forms
of Theorem 4.1's conclusion.

## Fixed statement

`p03ExactResidual run i` is the exact original-system residual
`b - A*(x i)`. All vector and matrix norms are infinity norms. The target says
that, for every natural iteration index `i`,

`||b - A*(x (i+1))||_inf <= alpha_i * ||b - A*(x i)||_inf + beta_i`,

where

`alpha_i = uS * (1 + (1+uS) * (c1_i*kappaInf(A)+c2_i) /
  (1-c1_i*kappaInf(A)*uS))`

and

`beta_i = (1 + uS * (c1_i*kappaInf(A)+c2_i) /
  (1-c1_i*kappaInf(A)*uS)) * (1+uS) * gamma_p^r *
  (||b||_inf + ||A||_inf*||x_i||_inf)
  + u*||A||_inf*||x_(i+1)||_inf`.

The proof derives the correction-defect estimate through `Ainv`, isolates it
using the strict denominator condition, converts the two componentwise error
models to infinity-norm bounds, applies the exact one-step residual identity,
and collects the coefficients without dropping higher-order factors.
