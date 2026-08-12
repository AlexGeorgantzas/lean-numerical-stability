import NumStability.Algorithms.QR.Higham19StoredLoop

/-!
# R11 historical-only test — `Higham19StoredLoop`

Imports exactly the historical path `NumStability.Algorithms.QR.Higham19StoredLoop`
and nothing else.

Checks the public surface still reachable through that historical path:

* 8 routed from directly imported owner `NumStability.Source.Higham.Chapter19.StoredLoop`

The path is retained, never deleted and never Git-renamed, so every
pre-existing import of it keeps resolving.
-/
#check @NumStability.H19_Theorem19_13_firstPivot_storedLoopPerturbation_frobNorm_le
#check @NumStability.H19_Theorem19_13_firstPivot_storedPanelStep_eq_applyMatrixRect_add_perturbation
#check @NumStability.H19_Theorem19_13_storedLoopPerturbation_entry
#check @NumStability.H19_Theorem19_13_storedLoopPerturbation_frobNorm_le
#check @NumStability.H19_Theorem19_13_storedLoopPerturbation_support
#check @NumStability.H19_Theorem19_13_storedPanelStep_eq_applyMatrixRect_add_perturbation
#check @NumStability.storageDiscardComparison
#check @NumStability.storedLoopPerturbation
