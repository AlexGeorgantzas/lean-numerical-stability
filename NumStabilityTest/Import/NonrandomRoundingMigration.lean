import NumStability.Analysis.NonrandomRounding

/-!
# Historical nonrandom-rounding path smoke test

The historical complete import must expose the layered API without help from
co-imported canonical modules.
-/

#check NumStability.kahanRationalFunction
#check NumStability.ieeeDoubleKahanNumeratorNormalTrace_of_source_interval
#check NumStability.kahanRationalFunction_grid_variation_from_first_lt
#check NumStability.ieeeDoubleKahanStoredGridRationalFunction_175_eq
#check NumStability.not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid
