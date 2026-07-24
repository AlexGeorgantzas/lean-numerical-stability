import NumStability.Algorithms.AutomaticErrorAnalysis.Higham26

/-!
# Historical Chapter 26 core import smoke test

This old-only smoke imports no canonical sibling and checks every canonical target family exposed by the historical wrapper.
-/

#check NumStability.IsGlobalMax
#check NumStability.adConverged
#check NumStability.ADSearchTrace
#check NumStability.vecOneNorm
#check NumStability.MDSSimplex.reorderBest
#check NumStability.MDSSimplex.SearchTrace
#check NumStability.inverseResidualStabilityMeasure
#check NumStability.depressedCubicP
#check NumStability.monicCubic
#check NumStability.cubicWCubePlus
#check NumStability.cubicWCubePlusComplex
#check NumStability.algebraicComplexCubeRoot
#check NumStability.higham26_5_printed_eitherSign_zeroBranch_discrepancy
#check NumStability.stableCubicWCubeComplex
#check NumStability.cubicRootResidualMeasure
#check NumStability.eq26_8_linearized_forward_error
#check NumStability.RealInterval.mul_contains
#check NumStability.RealInterval.dependency_sub_example
#check NumStability.RealInterval.outwardRounded
