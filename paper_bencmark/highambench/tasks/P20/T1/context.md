# P20-T1 context

Source: equation (3.4a) on physical PDF page 5 (journal page B789).

The paper scales each row of `A` by a power-of-two factor `lambda` satisfying `theta / (2 * ‖x‖∞) < lambda ≤ theta / ‖x‖∞`. Immediately before (3.2), it explains that this places the maximum coefficient of each scaled row in `(theta / 2, theta]`.

The target gives the exact finite-vector certificate: every scaled coefficient is at most `theta`, and some coefficient is strictly larger than `theta / 2`. It assumes the row is nonempty and has positive infinity norm, as required by the displayed quotients.
