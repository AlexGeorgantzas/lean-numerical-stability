# P18-T2 context

Source: corrected implicit midpoint method (4.1) and the error statement beneath it on PDF page 11 (article page 11 of 20).

After one high-precision correction, the paper states the global error form `O(Δt²) + O(ε Δt²)`. The target models the two leading error vectors explicitly and proves their Euclidean norm is at most `Δt²` times the sum of the scheme coefficient norm and the magnitude-scaled perturbation coefficient norm.

The statement is a finite exact envelope; it does not assert stability or infer a global error from local dynamics.
