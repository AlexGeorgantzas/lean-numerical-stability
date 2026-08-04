import NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GJESourceAccumulationBridge
import NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GaussJordanAccumulation
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEActualDoolittleAdapter
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEFinalDivisionClosure
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEOperationalBridge
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GaussJordanSourceClosure
import NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanStep

/-!
# GaussJordanSourceAlgorithm04: Gauss-Jordan boundary

The Chapter 14 Algorithm 4 source destinations, which carry the pivoting, execution, accumulation and second-stage material. B0007 confirms `GaussJordanPivoting` is Algorithm 4 source correspondence, not reusable, and explicitly overrides the stale reusable suggestion for that owner.
-/
#check @NumStability.Ch14Ext.ch14ext_gjeSourceTrace_stage2_forward_error_14_29
#check @NumStability.Ch14Ext.ch14ext_gjeXabs
#check @NumStability.Ch14Ext.ch14ext_gjeActualDoolittleL
#check @NumStability.Ch14Ext.Ch14GJEFinalizedFamily
#check @NumStability.Ch14Ext.ch14ext_mulBiasedModel
#check @NumStability.Ch14Ext.ch14ext_gjeSourceF
#check @NumStability.Ch14Ext.Ch14GJEState
#check @NumStability.Ch14Ext.ch14ext_gammaRem
#check @NumStability.Ch14Ext.ch14ext_gjeMultVec
