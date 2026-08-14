import NumStability.Algorithms.Higham726Rump

/-!
# R03 historical-only test — `Higham726Rump`

Imports exactly the historical path; checks its preserved public
surface (10 declarations).
-/

#check @NumStability.higham7_26_componentwiseDistance_le_rumpBound
#check @NumStability.higham7_26_exists_functionalCycle
#check @NumStability.higham7_26_exists_perronRowMaxCycle_of_subeigenvector
#check @NumStability.higham7_26_exists_rowSignature_charDet_nonpos
#check @NumStability.higham7_26_exists_sign_update_charDet_nonpos
#check @NumStability.higham7_26_nonempty_rumpEigenpairCertificate
#check @NumStability.higham7_26_nonempty_rumpEigenpairCertificate_of_subeigenvector
#check @NumStability.higham7_26_rump_normalized_fullCycle_eigenpair
#check @NumStability.higham7_26_rump_sign_real_eigenpair_of_componentwise_growth
#check @NumStability.higham7_26_source_distance_sandwich
