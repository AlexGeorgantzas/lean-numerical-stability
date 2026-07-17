# Chapter 26 Not-Proved Ledger

No selected Chapter 26 row remains open. The general MDS simplex transition is
encoded through exact reflection, expansion, contraction/retry, finite maximum
selection, best-vertex reordering, and finite execution traces. It assumes no
global/local optimizer, stationarity theorem, convergence, or termination.
The finite-real outward-directed rounding producer and all four containment
theorems are also verified. The rows below remain deferred or optional under
the source-selection policy.

| Source location | Claim | Status | Why current Lean does not close it | Needed foundation |
|---|---|---|---|---|
| p. 476 | Pattern-search limit points are stationary | out of scope by policy | The printed sentence suppresses "technical conditions" and cites Torczon; inventing them would change the theorem | Acquire the cited theorem and formalize its full hypotheses |
| (26.8), p. 484 | First-order forward-error linearization | out of scope by policy | "To first order" has no remainder, limiting variable, or asymptotic filter | Specify a perturbation parameter and prove a differentiable remainder theorem |
| Problems 26.1-26.4 | Experiments/research tasks | out of scope by policy | Optional problem rows; 26.2's Appendix solution explicitly reports an open theoretical bound | Select benchmark/research mode and specify the algorithms and FP execution model |
