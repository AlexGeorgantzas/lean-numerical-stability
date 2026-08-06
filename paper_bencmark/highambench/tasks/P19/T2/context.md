# P19-T2 context

Source: equation (3.8) in Theorem 3.1 on physical PDF page 9 (printed article page 8 of 46).

The modular forward-error theorem gathers four sources into
`xi = alpha * epsilonC + beta * epsilonB + beta * ug + lambda * epsilonX`.
The target makes that aggregation exact: four finite error vectors bounded by the corresponding source magnitudes are scaled and added, and their Euclidean norm is bounded by the displayed `xi` envelope.

This is an exact finite-dimensional certificate for the modular aggregation. It does not formalize the paper's suppressed low-degree factor `c(n,k)` or claim the complete asymptotic GMRES theorem.
