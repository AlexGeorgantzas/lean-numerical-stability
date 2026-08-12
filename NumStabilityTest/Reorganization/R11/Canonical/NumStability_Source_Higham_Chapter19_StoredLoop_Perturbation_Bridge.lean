import NumStability.Source.Higham.Chapter19.StoredLoop.Perturbation.Bridge

/-!
# R11 canonical-only test — `Bridge`

Imports exactly the canonical destination `NumStability.Source.Higham.Chapter19.StoredLoop.Perturbation.Bridge`
and nothing else. In particular it imports no historical R11 owner, so a
successful build proves the destination is self-sufficient and does not
depend on a compatibility facade.

Checks all 8 public declarations the frozen B0003 route sends here.
-/

#check @NumStability.H19_Theorem19_13_firstPivot_storedLoopPerturbation_frobNorm_le
#check @NumStability.H19_Theorem19_13_firstPivot_storedPanelStep_eq_applyMatrixRect_add_perturbation
#check @NumStability.H19_Theorem19_13_storedLoopPerturbation_entry
#check @NumStability.H19_Theorem19_13_storedLoopPerturbation_frobNorm_le
#check @NumStability.H19_Theorem19_13_storedLoopPerturbation_support
#check @NumStability.H19_Theorem19_13_storedPanelStep_eq_applyMatrixRect_add_perturbation
#check @NumStability.storageDiscardComparison
#check @NumStability.storedLoopPerturbation
