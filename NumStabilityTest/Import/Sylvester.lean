import NumStability.Algorithms.Sylvester

/-!
# Sylvester family import smoke test

Checks the core specification, Chapter 16 problem layer, and rounded
Hessenberg solver through the complete family umbrella.
-/

#check NumStability.sylvesterOp
#check NumStability.Higham16Hurwitz
#check NumStability.Wave17.sylvesterHessenbergShiftedColumn_roundedGEPP_backward_error
