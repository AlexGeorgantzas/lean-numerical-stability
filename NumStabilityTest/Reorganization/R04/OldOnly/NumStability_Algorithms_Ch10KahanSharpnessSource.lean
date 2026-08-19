import NumStability.Algorithms.Ch10KahanSharpnessSource

/-!
# Ch10KahanSharpnessSource old-path-only test (R04)

Imports only the historical path. Every declaration checked below moved to
a canonical destination during wave R04, so this compiles only if the
compatibility surface still re-exports it under its original name.
-/
#check @NumStability.Higham10KahanSharpnessSourceCertificate.of_theta
#check @NumStability.higham10KahanFullR_tail_le
#check @NumStability.higham10KahanR_tail_le
#check @NumStability.higham10KahanW_op2_eq_frobenius
#check @NumStability.higham10KahanW_op2_eq_product
#check @NumStability.higham10KahanW_op2_sq
#check @NumStability.higham10_13_kahan_source_closed
#check @NumStability.higham10_13_kahan_theta_op2_tendsto
