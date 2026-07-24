import NumStability.Analysis

/-!
# Analysis entry-point smoke test

Checks reusable analysis declarations and the temporary canonical Section 1.17
re-export retained to preserve the historical `import NumStability.Analysis`
surface. Canonical Chapter 1 tests and isolated old-only wrapper tests exercise
the narrower source paths directly.
-/

#check NumStability.RoundoffFamily
#check NumStability.norm_pow_le_two_mul_numericalRadius_pow
#check NumStability.higham18_kreiss_two_sided_proved
#check NumStability.semiconvergent_block_form_exists_of_convergence_real_spectrum
#check NumStability.higham17_22_exists_blockForm_spectralRadius_lt_one_of_forall_orbit_tendsto
#check NumStability.complexSylvesterOp
#check NumStability.not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid
