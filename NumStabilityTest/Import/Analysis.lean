import NumStability.Analysis

/-!
# Analysis entry-point smoke test

Checks declarations that previously reached the complete tree only through the
Algorithms aggregate, masking an incomplete Analysis entry point.
-/

#check NumStability.RoundoffFamily
#check NumStability.norm_pow_le_two_mul_numericalRadius_pow
#check NumStability.higham18_kreiss_two_sided_proved
#check NumStability.semiconvergent_block_form_exists_of_convergence_real_spectrum
#check NumStability.higham17_22_exists_blockForm_spectralRadius_lt_one_of_forall_orbit_tendsto
#check NumStability.complexSylvesterOp
