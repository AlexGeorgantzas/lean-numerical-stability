# Higham Chapter 24 Bottleneck Ledger

| Source claim | Blocking Lean theorem | Closed dependencies | Missing dependency | Failed route / audit evidence | Chosen theorem | Status |
|---|---|---|---|---|---|---|
| Theorem 24.2, literal rounded Cooley-Tukey radix-2 forward error | `higham24_theorem24_2_literal` | Primitive complex operations, computed-weight stages, exact scaled isometry, recursive branch join, and the scalar (24.5) accumulator | none | The earlier trace fields were rejected because they did not arise from the executor | Direct recursive producer | resolved |
| Equations (24.6)-(24.7) | `higham24LiteralEq24_7Execution` | Literal Theorem 24.2, `‖Fₙ‖₂=√n`, and a zero-safe rank-one error matrix | none | The earlier exact-zero execution was rejected | Produced forward perturbations for the two actual FFT runs | resolved |
| Theorem 24.3 | `higham24_theorem24_3_literal_quadraticRemainder` | Literal forward perturbations, literal complex division, literal inverse FFT, exact (24.8), inverse bounds for `(I+E)` and `(I+Δ₃F)`, and structured circulant reconstruction | none | `Higham24MixedStabilityExecutionFamily` was only a conditional transfer: its final structured split and budgets were fields. The replacement derives all three witnesses from the literal solver. | Exact rational radii, first-order extraction, and an explicit quadratic remainder coefficient | resolved |
| Backward-stability consequence after Theorem 24.2 | `higham24_literalFFT_backward_stable` | Exact DFT scaling and the literal forward-error bound | none | Exact representation alone did not prove the quantitative consequence | Relative input/output norm equality followed by Theorem 24.2 | resolved |

There is no selected open bottleneck in Chapter 24.  The only deferred prose
claim is the under-specified forward-error sentence after Theorem 24.3; it is
tracked as `DEFER-MISSING-PRECISE-STATEMENT`, not as a failed selected gate.
