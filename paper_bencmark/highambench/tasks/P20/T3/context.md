# P20-T3 context

Sources: the multiword narrow-range bound (4.32), range-unrestricted bound (4.33), and their surrounding comparison on physical PDF page 11 (journal page B795).

The two bounds share the range-free coefficient `(p + 1)u^p + (n + p²)U`. Equation (4.32) adds the input-underflow term `4 n u^(p-1) theta⁻¹ gmin` and accumulation-underflow term `2 p(p + 1)n² theta⁻² Gmin`.

The target identifies this exact nonnegative gap after multiplication by `‖A‖∞ ‖B‖∞`, proves the range-free envelope is no larger, characterizes equality by the vanishing of both added contributions, and proves strictness when either contribution is positive. These equality and strictness certificates are benchmark-added consequences of the displayed comparison.
