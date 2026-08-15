# P15-T3 paper context

## Fixed source

The source is Nicholas J. Higham and Theo Mary (2022), *Solving block
low-rank linear systems by LU factorization is numerically stable*. The local
PDF SHA-256 is
`a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`.

The selected result is Theorem 4.5, equations (4.23)--(4.25), and its proof on
PDF pages 24--25 (printed pages 974--975). The target also uses Algorithm 1 on
PDF page 13 (printed page 963), Theorem 4.2 and Table 1 on PDF page 19 (printed
page 969), Algorithm 2 and Theorem 4.3 on PDF page 21 (printed page 971), and
the BLR triangular-solve conclusion in Theorem 4.4 on PDF pages 23--24
(printed pages 973--974).

## Objects and algorithm certificate

`P15BLRLinearSolveExecution b p r` is a proof-carrying completed execution of
the computation selected by Theorem 4.5. It records:

- a nonsingular real BLR input matrix `A` of order `p*b`, a right-hand side
  `v`, and BLR lower and upper factors `L` and `U`;
- positive block size `b`, positive block count `p`, maximum off-diagonal rank
  `r <= b`, and the required block-triangular shapes;
- whether Algorithm 1 (UFC) or Algorithm 2 (UCF) was run, whether the threshold
  was local or global, and whether intermediate recompression was used;
- positive LR threshold `epsilon`, positive unit roundoff `u < epsilon`, and
  `3*c*u < 1` for `c = b + 2*r*sqrt(r) + p`;
- the exact factorization equation and the finite conclusions of Theorem 4.2
  or 4.3, including the Table 1 value of `xi_p` and an explicit
  `K*u*epsilon` bound for the term printed as `O(u*epsilon)`;
- the ordered forward and backward substitution equations and the finite
  perturbation bounds supplied by Theorem 4.4.

This certificate is the formal semantics of "computed by Algorithm 1 or 2"
at the theorem-composition boundary. The task does not ask the prover to
implement either paper algorithm from its pseudocode. It does require all
algorithm parameters, matrix structure, output equations, and preceding
theorem guarantees needed by Theorem 4.5; none of the final (4.23)--(4.25)
composition is assumed.

All matrix bounds use the paper's unsquared, unnormalized Frobenius norm, and
all vector bounds use the Euclidean norm. The execution is a real-valued
standard floating-point error model; overflow, underflow, NaNs, and infinities
are outside its scope.

## Exact finite conclusion

The target constructs the matrix and right-hand-side perturbations appearing
in the proof:

```text
matrixError = factorError + lowerError*U + L*upperError
                + lowerError*upperError,
rhsError    = lowerRhsError + L*upperRhsError
                + lowerError*upperRhsError.
```

It proves the exact perturbed system (4.23), the exact finite matrix bound and
its paper-shaped `gamma_(3c)` form (4.24), and an exact denominator-safe finite
right-hand-side bound for (4.25). For the latter, the coefficient

```text
gamma_p * (1 + gamma_c)^2 / (1 - gamma_p)
```

is split into the printed leading `gamma_p` term and a nonnegative higher-order
coefficient. Under `3*c*u < 1`, the target proves that this coefficient is at
most `16*c^2*u^2`; this is an explicit finite replacement for the paper's
`O(u^2)`. The factorization certificate similarly retains a disclosed
`factorMixedConstant*u*epsilon` term instead of deleting `O(u*epsilon)`.

The theorem statement begins with a BLR matrix denoted by `Atilde` in one line
of the typeset source, while the system, equations, and proof use `A`. The
formalization follows equations (4.23)--(4.25) and the proof by treating `A` as
the BLR input matrix. Theorems 4.2 and 4.3 print `A = LU + DeltaA`, whereas the
proof of Theorem 4.5 uses `A + DeltaA = LU`; the formalization follows the
Theorem 4.5 proof convention. This sign choice does not change the norm bound.
