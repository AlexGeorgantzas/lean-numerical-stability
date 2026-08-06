# P17-T3 context

Source: Theorem 4.3 and equations (4.8), (4.10)--(4.12) on PDF page 15 (journal page B1241).

The proof decomposes normalized summation error into a centered random term and a deterministic limited-precision remainder. A second-moment bound gives the centered radius with probability at least `1-lambda`; triangle inequality adds the remainder radius, and the summation condition number scales the event.

The target formalizes exactly that reusable finite-probability assembly. In Theorem 4.3, `varianceBudget` is the paper's `gamma_{n-1}(u_p^2)`, `biasRadius` is `gamma_{n-1}(u_p+u_{p+r})-gamma_{n-1}(u_p)`, and `kappa` is the summation condition number.
