# P20-T2 context

Source: equation (3.26) and the following comparison on physical PDF page 7 (journal page B791).

The simplified single-word error envelope separates input-underflow and accumulation-underflow contributions as `4 n² theta⁻¹ gmin` and `4 n² theta⁻² Gmin`, multiplied by `‖A‖∞ ‖B‖∞`. The paper then states that when `theta ≥ 1`, the latter scalar is no larger than the former because the accumulation format has no larger underflow scale.

The target formalizes that exact comparison for finite rectangular matrices under `Gmin ≤ gmin`. It compares contributions in the displayed envelope, not realized floating-point errors.
