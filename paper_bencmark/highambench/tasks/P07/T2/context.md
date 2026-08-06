# P07-T2 paper context

## Fixed source

The source is Maike Meier, Yuji Nakatsukasa, Alex Townsend, and Marcus Webb
(2024), *Are Sketch-and-Precondition Least Squares Solvers Numerically
Stable?* The local PDF SHA-256 is
`4c4d638b359719f47e2c4664a50e9fa8e4704e8b6b39923d73c41883a97c5790`.

The selected result is the displayed backward-error decomposition and its
norm-composition step in the proof of Theorem 3.5, PDF page 16, printed page
920, section 3.4.

## Local context and statement

The paper expands the final backward perturbation exactly as
`(Y*R-A) + ΔY*R + Y*ΔR + ΔY*ΔR` before inserting the algorithm-specific
rounding bounds. The target retains this exact four-term matrix and proves its
operator-2 certificate from bounds for the base residual and all four factors.
The scalar budget is deliberately uncollapsed so each contribution remains
visible; the subsequent numerical constants in Theorem 3.5 arise by
specializing these five certificates.
