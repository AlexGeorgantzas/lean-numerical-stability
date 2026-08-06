# P07-T1 paper context

## Fixed source

The source is Maike Meier, Yuji Nakatsukasa, Alex Townsend, and Marcus Webb
(2024), *Are Sketch-and-Precondition Least Squares Solvers Numerically
Stable?* The local PDF SHA-256 is
`4c4d638b359719f47e2c4664a50e9fa8e4704e8b6b39923d73c41883a97c5790`.

The selected result is the full-rank conclusion of Lemma 3.2, PDF page 13,
printed page 917, section 3.1.

## Local context and statement

Write the computed preconditioned matrix as `Y + ΔY`. Lemma 3.2 assumes that
the relative perturbation is strictly below one and concludes, first, that the
computed matrix remains full rank. The target expresses the same fact in
denominator-free vector-action form: `Y` has lower margin `μ`, `ΔY` has upper
margin `η`, and `η < μ`. These hypotheses directly imply injectivity of
`Y + ΔY` and avoid choosing a pseudoinverse in the controlled statement.
