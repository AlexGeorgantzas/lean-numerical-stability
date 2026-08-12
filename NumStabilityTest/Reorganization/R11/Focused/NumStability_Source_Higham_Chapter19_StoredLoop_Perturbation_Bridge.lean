import NumStability.Source.Higham.Chapter19.StoredLoop.Perturbation.Bridge

/-!
# R11 focused test — `Bridge`

Exercises the frozen B0003 declaration route into `NumStability.Source.Higham.Chapter19.StoredLoop.Perturbation.Bridge`
(8 public declarations) and its private-normalized closure
(0 approved private rows).

This destination has no private declaration in the approved 17-row
normalization map, so the private obligation here is exactly that no
private name from any other destination leaked into it.

-/

#check @NumStability.H19_Theorem19_13_firstPivot_storedLoopPerturbation_frobNorm_le
#check @NumStability.H19_Theorem19_13_firstPivot_storedPanelStep_eq_applyMatrixRect_add_perturbation
#check @NumStability.H19_Theorem19_13_storedLoopPerturbation_entry
#check @NumStability.H19_Theorem19_13_storedLoopPerturbation_frobNorm_le
#check @NumStability.H19_Theorem19_13_storedLoopPerturbation_support
#check @NumStability.H19_Theorem19_13_storedPanelStep_eq_applyMatrixRect_add_perturbation
#check @NumStability.storageDiscardComparison
#check @NumStability.storedLoopPerturbation
