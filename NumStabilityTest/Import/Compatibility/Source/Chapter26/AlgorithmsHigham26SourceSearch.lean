import NumStability.Algorithms.AutomaticErrorAnalysis.Higham26SourceSearch

/-!
# Historical Chapter 26 source-search import smoke test

This old-only smoke verifies both the historical core surface and the source-search declarations that were exposed together.
-/

#check NumStability.DirectSearchSpec
#check NumStability.ADSearchTrace
#check NumStability.higham26ADCrudeSearch
#check NumStability.MDSSimplex.SearchTrace
#check NumStability.higham26MDSInitialScale
#check NumStability.higham26RightAngledSimplex
#check NumStability.higham26RegularSimplex
#check NumStability.cubicRootResidualMeasure
#check NumStability.RealInterval.outwardRounded
