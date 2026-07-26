import NumStability.Analysis.Norms.Core

/-!
# Transitional norms core import smoke test

Checks representative vector, matrix, singular-value, attainment,
conditioning, and inverse-perturbation declarations through the extracted
implementation owner alone. Phase 11B will split and classify this core.
-/

#check NumStability.CVec
#check NumStability.complexVecLpNorm
#check NumStability.CMatrix
#check NumStability.complexMatrixLpNorm
#check NumStability.complexMatrixSingularValue
#check NumStability.exists_unit_vector_attaining_mixedSubordinateNormValue
#check NumStability.complexMatrix_relativeSingularDistance_min_eq_inv_conditionNumberProduct
#check NumStability.inversePerturbation_firstOrder_remainder_identity
