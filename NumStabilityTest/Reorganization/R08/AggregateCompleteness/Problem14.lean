import NumStability.Source.Higham.Chapter14.Problem14

/-!
# Problem14 aggregate completeness

`NumStability.Source.Higham.Chapter14.Problem14` is a declaration-free source aggregate after wave R08.
Importing the aggregate alone must still reach every declaration that moved
to `NumStability.Source.Higham.Chapter14.Problem14.FloatingPointDeterminant.HymanBackwardError`.
-/
#check @NumStability.Ch14Ext.ch14ext_backSub_zeroDiag_perturbed
#check @NumStability.Ch14Ext.ch14ext_flDiagProd
#check @NumStability.Ch14Ext.ch14ext_flDiagProdAux
#check @NumStability.Ch14Ext.ch14ext_flDiagProdAux_expand
#check @NumStability.Ch14Ext.ch14ext_flDiagProd_relError
#check @NumStability.Ch14Ext.ch14ext_flHymanDet
#check @NumStability.Ch14Ext.ch14ext_hymanSchur_eq_of_leftInverse
#check @NumStability.Ch14Ext.ch14ext_hyman_diagonalSimilarity_bound_invariant
#check @NumStability.Ch14Ext.ch14ext_hyman_flDet_backward_error
#check @NumStability.Ch14Ext.ch14ext_hyman_flDet_backward_error_original
#check @NumStability.Ch14Ext.ch14ext_hyman_flDet_diagonalSimilarity
