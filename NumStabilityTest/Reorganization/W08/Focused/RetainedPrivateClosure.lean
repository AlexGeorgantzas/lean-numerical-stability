import NumStability.Algorithms.Ch14AsymptoticFamilies
import NumStability.Algorithms.Ch14Cor146UniformInverseBridge
import NumStability.Algorithms.Ch14Cor147FinalDivisionFamilyClosure
import NumStability.Algorithms.Ch14Corollary147SourceClosure
import NumStability.Algorithms.Ch14Corollary147WeakFamily
import NumStability.Algorithms.Ch14ForwardErrorEndpoint
import NumStability.Algorithms.Ch14GJEAsymptoticFamilies
import NumStability.Algorithms.Ch14GJEFinalDivisionClosure
import NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure
import NumStability.Algorithms.Ch14GJETheorem145SourceClosure
import NumStability.Algorithms.Ch14Method1BWhole
import NumStability.Algorithms.Ch14Method2C
import NumStability.Algorithms.Ch14Method2CWhole
import NumStability.Algorithms.Ch14Problem142
import NumStability.Algorithms.Ch14Problem142Families
import NumStability.Algorithms.Ch14Problem142Method2B
import NumStability.Algorithms.MatrixInversion

/-!
# Retained private closures at their historical owners

W08 selects 45 private declarations. Lean mangles a private name to
`_private.<defining module>.<n>.<name>`, so the defining module is part of the
name and relocating one would rename it and break the frozen graph. Its
reverse dependency closure is 179 declarations across these
17 owners, which therefore remain declaration-bearing facades.

This test imports each such facade and checks a retained *public* member. The
private declarations themselves are deliberately not referenced: they are not
visible outside their defining module, which is precisely why they cannot move.
-/
#check @NumStability.Ch14Ext.ch14ext_eq14_6_familyRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_cor146FinalizedRunFamily_of_computedFactors
#check @NumStability.Ch14Ext.ch14ext_cor147Finalized_forward_bound
#check @NumStability.Ch14Ext.ch14ext_luBackward_factorProximity_isBigO
#check @NumStability.Ch14Ext.ch14ext_cor147Weak_forward_bound
#check @NumStability.Ch14Ext.ch14ext_eq14_3_quadraticRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_gamma_family_isBigO_unit
#check @NumStability.Ch14Ext.ch14ext_gjeFinalizedFamily_theorem14_5_endpoint
#check @NumStability.Ch14Ext.ch14ext_gjeConcreteFamilyPabs_le_Xabs
#check @NumStability.Ch14Ext.ch14ext_gjeResidualS2_exact_le_printed_add_correction
#check @NumStability.Ch14Ext.ch14ext_m1bInv_right_residual
#check @NumStability.Ch14Ext.ch14ext_method2C_block_left_residual
#check @NumStability.Ch14Ext.ch14ext_method2CInv_left_residual
#check @NumStability.Ch14Ext.higham14_problem14_2_lowerBlock_one
#check @NumStability.Ch14Ext.ch14ext_problem14_2_method2B_twoBlock_left_family
#check @NumStability.Ch14Ext.higham14_problem14_2_method2B_twoBlock_left_firstOrder
#check @NumStability.higham14_problem14_12_peiMatrix_det
