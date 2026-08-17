import NumStability.Algorithms.Ch14GJETheorem145SourceClosure

/-!
# Ch14GJETheorem145SourceClosure old-path-only test

Imports only the historical path. Every declaration checked below is part of
the residual C0004 surface that wave R08 relocated to
`NumStability.Source.Higham.Chapter14.Theorem05.PrintedTrace.VanishingEndpoints`,
so this compiles only if the compatibility module still re-exports it
under its original name.
-/
#check @NumStability.Ch14Ext.ch14ext_gjeResidualPrintedEnvelopeCorrection_isBigOOne
#check @NumStability.Ch14Ext.ch14ext_gjeResidualS2_exact_le_printed_add_correction
#check @NumStability.Ch14Ext.ch14ext_gjeSourceResidual1431PrintedRemainder_isBigO_unit_sq
#check @NumStability.Ch14Ext.ch14ext_gjeSourceTrace_14_30abc_printed_vanishing_family_endpoint
#check @NumStability.Ch14Ext.ch14ext_gjeSourceTrace_forward_14_32_printed_vanishing_family_endpoint
#check @NumStability.Ch14Ext.ch14ext_gjeSourceTrace_residual_14_31_printed_vanishing_family_endpoint
#check @NumStability.Ch14Ext.ch14ext_gjeSourceTrace_theorem14_5_printed_vanishing_family_endpoint
