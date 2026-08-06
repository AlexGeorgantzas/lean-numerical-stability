# P07-T3 paper context

## Fixed source

The source is Maike Meier, Yuji Nakatsukasa, Alex Townsend, and Marcus Webb
(2024), *Are Sketch-and-Precondition Least Squares Solvers Numerically
Stable?* The local PDF SHA-256 is
`4c4d638b359719f47e2c4664a50e9fa8e4704e8b6b39923d73c41883a97c5790`.

The selected result is Lemma 2.1, PDF page 9, printed page 913, section 2.1.

## Local context and statement

In the paper, `T = R_A R^{-1}`, `A P = Q_A T`, and
`(S Q_A) T = Q`, where both thin `Q` factors preserve Euclidean norm. The
paper uses these identities to conclude `κ₂(AP) = κ₂(SQ_A)`. The target makes
that argument finite and denominator-safe: every positive lower/upper
certificate `[α,β]` for `Q_A T` corresponds exactly to the reciprocal
certificate `[β⁻¹,α⁻¹]` for `S Q_A`, and the two upper/lower ratios are equal.
Surjectivity of the square map `T` records the full-rank hypotheses of the QR
factors.
