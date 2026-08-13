# Compatibility policy and path map

This migration changes canonical module paths without changing declaration
names or the historical meaning of `import NumStability`. Every old path in
the table remains an import-only forwarding module.

## Current forwarding paths

| Historical path | Canonical path |
| --- | --- |
| `NumStability.Algorithms.Ch5LejaProducer` | `NumStability.Algorithms.Horner`, `NumStability.Source.Higham.Chapter05.Problem04.LejaOrdering.Basic` |
| `NumStability.Algorithms.Ch5NewtonForm` | `NumStability.Algorithms.Horner`, `NumStability.Analysis.Rounding`, `NumStability.FloatingPoint.Model`, `NumStability.Source.Higham.Chapter05.Section03.NewtonEvaluation.Basic` |
| `NumStability.Algorithms.HighamLemma88Entrywise` | `NumStability.Source.Higham.Chapter08.Lemma08.Entrywise.Basic` |
| `NumStability.Algorithms.OrderingExamples` | `NumStability.Algorithms.Summation.Insertion.ActiveList`, `NumStability.Algorithms.Summation.Recursive.Core`, `NumStability.Algorithms.Summation.Tree.Core`, `NumStability.Source.Higham.Chapter04.Equation05.OrderingExamples.Basic` |
| `NumStability.Analysis.Accumulation` | `NumStability.Analysis.FloatingPointArithmetic.Format`, `NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError`, `NumStability.Analysis.Rounding`, `NumStability.Source.Higham.Chapter01.Problem05.CompensatedLogarithm.Basic`, `NumStability.Source.Higham.Chapter01.Section11.Accumulation.Basic` |
| `NumStability.Analysis.CalculatorWords` | `NumStability.Source.Higham.Chapter01.Problem06.CalculatorWords.Basic` |
| `NumStability.Analysis.Counting` | `NumStability.Analysis.FloatingPointArithmetic`, `NumStability.Source.Higham.Chapter02.Problem01.FloatingPointCounts.Basic` |
| `NumStability.Analysis.HighamChapter2GradualUnderflowExact` | `NumStability.Analysis.FloatingPointArithmetic`, `NumStability.Source.Higham.Chapter02.Problem19.GradualUnderflowExactness.Basic` |
| `NumStability.Analysis.HighamChapter2Tablemaker` | `NumStability.Analysis.FloatingPointArithmetic`, `NumStability.Source.Higham.Chapter02.Section10.Tablemaker.FiniteSeparation.Basic` |
| `NumStability.Analysis.MullerRecurrence` | `NumStability.Source.Higham.Chapter01.Problem08.MullerRecurrence.Basic` |
| `NumStability.Analysis.NearInteger` | `NumStability.Source.Higham.Chapter01.Problem02.NearIntegerTable.Basic` |
| `NumStability.Analysis.Problem2_15_16` | `NumStability.Analysis.FloatingPointArithmetic`, `NumStability.Source.Higham.Chapter02.Problems15And16.SpecialValueProbes.Basic` |
| `NumStability.Analysis.Problem2_18` | `NumStability.Source.Higham.Chapter02.Problem18.ExactSubtractionCounterexample.Basic` |
| `NumStability.Analysis.Problem2_19` | `NumStability.Source.Higham.Chapter02.Problem20.SquareRootIdentities.Basic` |
| `NumStability.Analysis.Problem2_23` | `NumStability.Analysis.FloatingPointArithmetic`, `NumStability.Source.Higham.Chapter02.Problem24.GuardDigitCancellation.Basic` |
| `NumStability.Analysis.Problem2_25` | `NumStability.Source.Higham.Chapter02.Problem27.KahanDeterminant.Basic` |
| `NumStability.Analysis.Problem2_26` | `NumStability.Analysis.Problem2_14`, `NumStability.Source.Higham.Chapter02.Section06.ReciprocalIteration.Basic` |
| `NumStability.Analysis.Problem2_5` | `NumStability.Analysis.FloatingPointArithmetic`, `NumStability.Source.Higham.Chapter02.Problem05.BinaryOneTenth.Basic` |
| `NumStability.Analysis.Problem2_6` | `NumStability.Analysis.FloatingPointArithmetic`, `NumStability.Source.Higham.Chapter02.Problem06.IntegerRepresentability.Basic` |
| `NumStability.Algorithms.HighamChapter8FanInClosure` | `NumStability.Source.Higham.Chapter08.Equation15.GlobalEnvelopeCounterexample.RawCube` |
| `NumStability.Algorithms.IterativeRefinement` | `NumStability.Algorithms.LinearSystems.IterativeRefinement.Core`, `NumStability.Source.Higham.Chapter12.IterativeRefinement.Chapter12Bounds`, and `NumStability.Source.Higham.Chapter12.IterativeRefinement.LegacyChapter11Surface` |
| `NumStability.Algorithms.PriestFiniteFormat` | `NumStability.Algorithms.Summation.Compensated.Priest.FiniteFormat` and `NumStability.Source.Higham.Chapter04.Algorithm03.Priest.SourceAssumptions` |
| `NumStability.Algorithms.TriangularArbitraryOrder` | `NumStability.Algorithms.Summation.Tree.ArbitraryOrderError.PivotNormalized` and `NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.ArbitraryOrder` |
| `NumStability.Algorithms.TriangularNoGuard` | `NumStability.Algorithms.LinearSystems.Triangular.ErrorAnalysis.NoGuardBackward`, `NumStability.Algorithms.LinearSystems.Triangular.ErrorAnalysis.NoGuardForward`, `NumStability.Source.Higham.Chapter08.Problem01.NoGuardSubstitution.BackwardSubstitution`, and `NumStability.Source.Higham.Chapter08.Problem01.NoGuardSubstitution.ForwardSubstitution` |
| `NumStability.Analysis.CramersRule` | `NumStability.Algorithms.LinearSystems.CramersRule.Core`, `NumStability.Source.Higham.Chapter01.Problem09.CramersRule.ForwardError`, and `NumStability.Source.Higham.Chapter01.Section10.CramersRule.PrintedComparison` |
| `NumStability.Analysis.Error` | `NumStability.Analysis.Error.Measures.AccuracyPrecision`, `NumStability.Analysis.Error.Measures.Componentwise`, `NumStability.Analysis.Error.Measures.ScalarDefinitions`, `NumStability.Analysis.Error.Measures.ScalarProperties`, `NumStability.Analysis.Error.Measures.ScalarWitnesses`, `NumStability.Analysis.FloatingPointArithmetic.ErrorModels.Additive`, `NumStability.Analysis.FloatingPointArithmetic.ErrorModels.AdditiveProperties`, `NumStability.Analysis.FloatingPointArithmetic.ErrorModels.NoGuardBasic`, `NumStability.Analysis.FloatingPointArithmetic.ErrorModels.NoGuardModel`, `NumStability.Source.Higham.Chapter01.Problem01.RelativeError.Bounds`, `NumStability.Source.Higham.Chapter01.Section03.ErrorSources.Core`, `NumStability.Source.Higham.Chapter01.Section07.Cancellation.Basic`, and `NumStability.Source.Higham.Chapter02.Section04.NoGuardModel.BinaryT3Example` |
| `NumStability.Analysis.FusedMultiplyAdd` | `NumStability.FloatingPoint.FusedMultiplyAdd.Core`, `NumStability.FloatingPoint.FusedMultiplyAdd.DotProductCounts`, `NumStability.Source.Higham.Chapter02.Problem26.ExactProduct.Discrepancy`, and `NumStability.Source.Higham.Chapter02.Section06.FusedMultiplyAdd.DotProductCount` |
| `NumStability.Analysis.Midpoint` | `NumStability.Analysis.FloatingPointArithmetic.MidpointRounding.DecimalTieExamples` and `NumStability.Source.Higham.Chapter02.Problem08.MidpointRounding.Counterexample` |
| `NumStability.Analysis.ProblemDependentStability` | `NumStability.Analysis.ProblemDependentStability.HessenbergDeterminant`, `NumStability.Source.Higham.Chapter01.Section16.ProblemDependentStability.ExactExample`, and `NumStability.Source.Higham.Chapter01.Section16.ProblemDependentStability.Table13IeeeSingle` |
| `NumStability.Analysis.RoundingProductBounds` | `NumStability.Analysis.Error.RoundingProducts.Core` and `NumStability.Source.Higham.Chapter03.Problem02.ProductBounds.PositiveFactors` |
| `NumStability.Analysis.TrigCancellation` | `NumStability.Analysis.FloatingPointArithmetic.TrigonometricCancellation.Core`, `NumStability.Source.Higham.Chapter01.Problem03.CancellationRewrites.Algebra`, and `NumStability.Source.Higham.Chapter01.Section07.TrigonometricCancellation.Example` |
| `NumStability.Higham` | `NumStability.Source.Higham` |
| `NumStability.Higham.Chapter02.Problem04` | `NumStability.Source.Higham.Chapter02.Problem04` |
| `NumStability.Higham.Chapter02.Problem07` | `NumStability.Source.Higham.Chapter02.Problem07` |
| `NumStability.Higham.Chapter02.Problem22` | `NumStability.Source.Higham.Chapter02.Problem23` |
| `NumStability.Higham.Chapter08.Lemma8_8Discrepancy` | `NumStability.Source.Higham.Chapter08.Lemma08Discrepancy` |
| `NumStability.Higham.Chapter10.Theorem10_7` | `NumStability.Source.Higham.Chapter10.Theorem07` |
| `NumStability.Higham.Chapter11.Theorem11_7Capstone` | `NumStability.Source.Higham.Chapter11.Theorem07` |
| `NumStability.Higham.Chapter13.Table13_1` | `NumStability.Source.Higham.Chapter13.Equation25` and `NumStability.Source.Higham.Chapter13.Table01` |
| `NumStability.Higham.Chapter14.Discrepancies` | `NumStability.Source.Higham.Chapter14.Discrepancies` |
| `NumStability.Higham.Chapter20.SourceAliases` | `NumStability.Source.Higham.Chapter20.Equation32`, `NumStability.Source.Higham.Chapter20.Lemma06`, and `NumStability.Source.Higham.Chapter20.Theorem01` |
| `NumStability.Higham.CrossChapter.Chapter02To03NoGuardDot` | `NumStability.Algorithms.Arithmetic.DotProduct.NoGuard` and `NumStability.Source.Higham.CrossChapter.NoGuardDotProduct` |
| `NumStability.Higham.CrossChapter.Chapter07To15PracticalBound` | `NumStability.Source.Higham.CrossChapter.PracticalConditionBound` |
| `NumStability.Higham.CrossChapter.Chapter09To12GenericSolver` | `NumStability.Source.Higham.CrossChapter.LUSolverWeights.Factorization` |
| `NumStability.Higham.CrossChapter.Chapter09To12Solver` | `NumStability.Source.Higham.CrossChapter.LUSolverWeights.Doolittle` |
| `NumStability.Algorithms.Chapter06Lemma66` | `NumStability.Source.Higham.Chapter06.Lemma06` |
| `NumStability.Algorithms.RecursiveSum` | `NumStability.Algorithms.Summation.Recursive` |
| `NumStability.Algorithms.PairwiseSum` | `NumStability.Algorithms.Summation.Pairwise` |
| `NumStability.Algorithms.InsertionSum` | `NumStability.Algorithms.Summation.Insertion` |
| `NumStability.Algorithms.SumTree` | `NumStability.Algorithms.Summation.Tree` |
| `NumStability.Algorithms.Summation.Tree.RecursiveBridge` | `NumStability.Algorithms.Summation.Tree.Chain` |
| `NumStability.Algorithms.PlusMinusSum` | `NumStability.Algorithms.Summation.PlusMinus` |
| `NumStability.Algorithms.CompensatedSum` | `NumStability.Algorithms.Summation.Compensated` |
| `NumStability.Algorithms.KahanCompensatedFiniteFormat` | `NumStability.Source.Higham.Chapter04.Section03.FiniteFormat` |
| `NumStability.Algorithms.DoublyCompensatedSum` | `NumStability.Algorithms.Summation.DoublyCompensated` |
| `NumStability.Algorithms.AccumulatorSum` | `NumStability.Algorithms.Summation.Accumulator` |
| `NumStability.Algorithms.TriangularSolve` | `NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution` |
| `NumStability.Algorithms.ForwardSub` | `NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution` |
| `NumStability.Algorithms.TriangularForwardBound` | `NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance` |
| `NumStability.Algorithms.InverseBounds` | `NumStability.Algorithms.LinearSystems.Triangular.InverseBounds` |
| `NumStability.Algorithms.TriangularForwardComparison` | `NumStability.Algorithms.LinearSystems.Triangular.ComparisonBounds` |
| `NumStability.Algorithms.TriangularSolveCombined` | `NumStability.Algorithms.LinearSystems.Triangular.Combined` |
| `NumStability.Analysis.Higham6Asides` | `NumStability.Source.Higham.Chapter06.Asides` |
| `NumStability.Analysis.Higham6BlockAntidiag` | `NumStability.Source.Higham.Chapter06.BlockAntidiagonalNorm.InducedLp` |
| `NumStability.Analysis.HighamChapter2PowerLeadingDigits` | `NumStability.Source.Higham.Chapter02.Problem11` and `NumStability.Source.Higham.Chapter02.Section07.PowerLeadingDigits` |
| `NumStability.Analysis.HighamChapter6Duality` | `NumStability.Source.Higham.Chapter06.Equation02` |
| `NumStability.Analysis.LeadingDigitDistribution` | `NumStability.Analysis.LeadingDigits.LogarithmicDistribution` |
| `NumStability.Analysis.Norms` | `NumStability.Analysis.Norms.Core` and `NumStability.Source.Higham.Chapter06.Norms` |
| `NumStability.Analysis.Problem2_11` | `NumStability.Source.Higham.Chapter02.Problem11` |
| `NumStability.Analysis.Problem2_2` | `NumStability.Source.Higham.Chapter02.Problem02` |
| `NumStability.Analysis.Problem2_4` | `NumStability.Source.Higham.Chapter02.Problem04` |
| `NumStability.Analysis.Problem2_7` | `NumStability.FloatingPoint.OperationLaws` and `NumStability.Source.Higham.Chapter02.Problem07` |
| `NumStability.Analysis.Problem2_21` | `NumStability.Source.Higham.Chapter02.Problem22` |
| `NumStability.Analysis.Problem2_22` | `NumStability.Source.Higham.Chapter02.Problem23` |
| `NumStability.Algorithms.HighamChapter8Lemma88SourceDiscrepancy` | `NumStability.Source.Higham.Chapter08.Lemma08Discrepancy` |
| `NumStability.Algorithms.HighamChapter9` | `NumStability.Source.Higham.Chapter09.Problems`, `NumStability.Source.Higham.Chapter09.Section01`, `NumStability.Source.Higham.Chapter09.Section02`, `NumStability.Source.Higham.Chapter09.Section03`, `NumStability.Source.Higham.Chapter09.Section04`, `NumStability.Source.Higham.Chapter09.Section05`, `NumStability.Source.Higham.Chapter09.Section06`, `NumStability.Source.Higham.Chapter09.Section08`, `NumStability.Source.Higham.Chapter09.Section10`, and `NumStability.Source.Higham.Chapter09.Section11` |
| `NumStability.Algorithms.HighamChapter9CompletePivotSharpClosure` | `NumStability.Source.Higham.Chapter09.CompletePivotSharpClosure` |
| `NumStability.Algorithms.HighamChapter9ComplexClosure` | `NumStability.Source.Higham.Chapter09.ComplexClosure` |
| `NumStability.Algorithms.HighamChapter9ComputedCorrection` | `NumStability.Source.Higham.Chapter09.ComputedCorrection` |
| `NumStability.Algorithms.HighamChapter9DoolittleClosure` | `NumStability.Source.Higham.Chapter09.DoolittleClosure` |
| `NumStability.Algorithms.HighamChapter9Theorem914Actual` | `NumStability.Source.Higham.Chapter09.Theorem914Actual` |
| `NumStability.Algorithms.HighamChapter9Theorem914DiagDominant` | `NumStability.Source.Higham.Chapter09.Theorem914DiagDominant` |
| `NumStability.Algorithms.HighamChapter9Theorem914Primitive` | `NumStability.Source.Higham.Chapter09.Theorem914Primitive` |
| `NumStability.Algorithms.HighamChapter9Theorem97Classification` | `NumStability.Source.Higham.Chapter09.Theorem97Classification` |
| `NumStability.Algorithms.HighamChapter9Theorem99Closure` | `NumStability.Source.Higham.Chapter09.Theorem99Closure` |
| `NumStability.Algorithms.HighamChapter9Theorem99ComplexClosure` | `NumStability.Source.Higham.Chapter09.Theorem99ComplexClosure` |
| `NumStability.Algorithms.Cholesky.Higham10Theorem10_7Source` | `NumStability.Source.Higham.Chapter10.Theorem07` |
| `NumStability.Algorithms.Cholesky.BunchTridiagonalCapstoneCh11Closure` | `NumStability.Source.Higham.Chapter11.Theorem07` |
| `NumStability.Algorithms.HighamChapter11` | `NumStability.Source.Higham.Chapter11.Section01.Basic`, `NumStability.Source.Higham.Chapter11.Section01.CompletePivoting`, `NumStability.Source.Higham.Chapter11.Section01.PartialPivoting`, `NumStability.Source.Higham.Chapter11.Section01.RookPivoting`, `NumStability.Source.Higham.Chapter11.Section01.Tridiagonal`, `NumStability.Source.Higham.Chapter11.Section02.Aasen`, `NumStability.Source.Higham.Chapter11.Section03.SkewSymmetric`, and `NumStability.Source.Higham.Chapter11.Problems` |
| `NumStability.Algorithms.Cholesky.Aasen118ReducedCh11Closure` | `NumStability.Source.Higham.Chapter11.Aasen118Reduced` |
| `NumStability.Algorithms.Cholesky.AasenAdjacentPivotOperationalMiddleCh11` | `NumStability.Source.Higham.Chapter11.AasenAdjacentPivotOperationalMiddle` |
| `NumStability.Algorithms.Cholesky.AasenAdjacentPivotResidualDomainCh11Discrepancy` | `NumStability.Source.Higham.Chapter11.AasenAdjacentPivotResidualDomain` |
| `NumStability.Algorithms.Cholesky.AasenAdjacentPivotSourceResidualCh11Closure` | `NumStability.Source.Higham.Chapter11.AasenAdjacentPivotSourceResidual` |
| `NumStability.Algorithms.Cholesky.AasenAdjacentPivotTridiagExecutorCh11Closure` | `NumStability.Source.Higham.Chapter11.AasenAdjacentPivotTridiagExecutor` |
| `NumStability.Algorithms.Cholesky.AasenAdjacentPivotTridiagForwardCounterexampleCh11` | `NumStability.Source.Higham.Chapter11.AasenAdjacentPivotTridiagForwardCounterexample` |
| `NumStability.Algorithms.Cholesky.AasenCoupledFpCh11Closure` | `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Aasen.AasenCoupledFp` |
| `NumStability.Algorithms.Cholesky.AasenDirect118Ch11Closure` | `NumStability.Source.Higham.Chapter11.AasenDirect118` |
| `NumStability.Algorithms.Cholesky.AasenDirectTridiagGEPPSolveCh11Closure` | `NumStability.Source.Higham.Chapter11.AasenDirectTridiagGEPPSolve` |
| `NumStability.Algorithms.Cholesky.AasenFactorNormCh11Closure` | `NumStability.Source.Higham.Chapter11.AasenFactorNorm` |
| `NumStability.Algorithms.Cholesky.AasenFactorResidualCh11Closure` | `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Aasen.AasenFactorResidual` |
| `NumStability.Algorithms.Cholesky.AasenGrowthCh11Closure` | `NumStability.Source.Higham.Chapter11.AasenGrowth` |
| `NumStability.Algorithms.Cholesky.AasenMiddleGEPPCh11Counterexample` | `NumStability.Source.Higham.Chapter11.AasenMiddleGEPPCh11Counterexample` |
| `NumStability.Algorithms.Cholesky.AasenOriginalCoordinateCorrectionCh11` | `NumStability.Source.Higham.Chapter11.AasenOriginalCoordinateCorrection` |
| `NumStability.Algorithms.Cholesky.AasenPermutationSourceCorrectionCh11` | `NumStability.Source.Higham.Chapter11.AasenPermutationSourceCorrection` |
| `NumStability.Algorithms.Cholesky.AasenPrintedCoefficientAlgebraCh11Closure` | `NumStability.Source.Higham.Chapter11.AasenPrintedCoefficientAlgebra` |
| `NumStability.Algorithms.Cholesky.AasenSourceSharpFactorResidualCh11Closure` | `NumStability.Source.Higham.Chapter11.AasenSourceSharpFactorResidual` |
| `NumStability.Algorithms.Cholesky.AasenTheorem118ScalarEdgeCh11Discrepancy` | `NumStability.Source.Higham.Chapter11.AasenTheorem118ScalarEdge` |
| `NumStability.Algorithms.Cholesky.AasenTridiagGEPPCh11Closure` | `NumStability.Source.Higham.Chapter11.AasenTridiagGEPP` |
| `NumStability.Algorithms.Cholesky.AasenUnitOuterSolveCh11Closure` | `NumStability.Source.Higham.Chapter11.AasenUnitOuterSolve` |
| `NumStability.Algorithms.Cholesky.BlockLDLTAllOneByOnePrintedCh11Closure` | `NumStability.Source.Higham.Chapter11.BlockLDLTAllOneByOnePrinted` |
| `NumStability.Algorithms.Cholesky.BlockLDLTBunchTridiagonalCh11Closure` | `NumStability.Source.Higham.Chapter11.BlockLDLTBunchTridiagonal` |
| `NumStability.Algorithms.Cholesky.BlockLDLTMixedPivotCh11Closure` | `NumStability.Source.Higham.Chapter11.BlockLDLTMixedPivot` |
| `NumStability.Algorithms.Cholesky.BlockLDLTSolveBackwardCh11Closure` | `NumStability.Source.Higham.Chapter11.BlockLDLTSolveBackward` |
| `NumStability.Algorithms.Cholesky.BunchKaufmanSolveCh11Closure` | `NumStability.Source.Higham.Chapter11.BunchKaufmanSolve` |
| `NumStability.Algorithms.Cholesky.BunchTridiagonalActualSolveCh11Closure` | `NumStability.Source.Higham.Chapter11.BunchTridiagonalActualSolve` |
| `NumStability.Algorithms.Cholesky.BunchTridiagonalFactorBoundCh11Closure` | `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.BlockLDLT.BunchTridiagonalFactorBound` |
| `NumStability.Algorithms.Cholesky.BunchTridiagonalGrowthCh11Closure` | `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.BlockLDLT.BunchTridiagonalGrowth` |
| `NumStability.Algorithms.Cholesky.BunchTridiagonalGrowthInvariantCh11Closure` | `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.BlockLDLT.BunchTridiagonalGrowthInvariant` |
| `NumStability.Algorithms.Cholesky.BunchTridiagonalHFactorCh11Closure` | `NumStability.Source.Higham.Chapter11.BunchTridiagonalHFactor` |
| `NumStability.Algorithms.Cholesky.BunchTridiagonalSparseFactorCh11Closure` | `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.BlockLDLT.BunchTridiagonalSparseFactor` |
| `NumStability.Algorithms.Cholesky.BunchTridiagonalSparseSolveCh11Closure` | `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.BlockLDLT.BunchTridiagonalSparseSolve` |
| `NumStability.Algorithms.Cholesky.Higham11BunchActualSharpGrowthClosure` | `NumStability.Source.Higham.Chapter11.Higham11BunchActualSharpGrowthClosure` |
| `NumStability.Algorithms.Cholesky.Higham11BunchExactTrace` | `NumStability.Source.Higham.Chapter11.Higham11BunchExactTrace` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanActualSelector` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanActualSelector` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExactGrowth` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanExactGrowth` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExactGrowthArithmetic` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanExactGrowthArithmetic` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExactTrace` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanExactTrace` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExplicitInverseSolve` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanExplicitInverseSolve` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExplicitInverseTerminalClosedForm` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanExplicitInverseTerminalClosedForm` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedAccumulated` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedAccumulated` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedBridge` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedBridge` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedClosure` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedClosure` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedExecution` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedExecution` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedFactors` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedFactors` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGlobal` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedGlobal` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowth` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedGrowth` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowthSolve` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedGrowthSolve` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedMiddleSolve` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedMiddleSolve` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedSolve` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedSolve` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminal` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedTerminal` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminalClosedForm` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedTerminalClosedForm` |
| `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanSourceCorrection` | `NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanSourceCorrection` |
| `NumStability.Algorithms.Cholesky.Higham11BunchSharpGrowthBridge` | `NumStability.Source.Higham.Chapter11.Higham11BunchSharpGrowthBridge` |
| `NumStability.Algorithms.Cholesky.Higham11BunchTraceHadamard` | `NumStability.Source.Higham.Chapter11.Higham11BunchTraceHadamard` |
| `NumStability.Algorithms.Cholesky.Higham11Chapter9ActualExecutorBridge` | `NumStability.Source.Higham.Chapter11.Higham11Chapter9ActualExecutorBridge` |
| `NumStability.Algorithms.Cholesky.Higham11Chapter9BridgeClosure` | `NumStability.Source.Higham.Chapter11.Higham11Chapter9BridgeClosure` |
| `NumStability.Algorithms.Cholesky.Higham11RookExactTrace` | `NumStability.Source.Higham.Chapter11.Higham11RookExactTrace` |
| `NumStability.Algorithms.Cholesky.Higham11RookExecutorAdapter` | `NumStability.Source.Higham.Chapter11.Higham11RookExecutorAdapter` |
| `NumStability.Algorithms.Cholesky.Higham11RookRoundedGap` | `NumStability.Source.Higham.Chapter11.Higham11RookRoundedGap` |
| `NumStability.Algorithms.Cholesky.Higham11RookSourceClosure` | `NumStability.Source.Higham.Chapter11.Higham11RookSourceClosure` |
| `NumStability.Algorithms.Cholesky.Higham11SkewActualSelector` | `NumStability.Source.Higham.Chapter11.Higham11SkewActualSelector` |
| `NumStability.Algorithms.Cholesky.Higham11SkewExactTrace` | `NumStability.Source.Higham.Chapter11.Higham11SkewExactTrace` |
| `NumStability.Algorithms.Cholesky.Higham11SkewSourceCorrection` | `NumStability.Source.Higham.Chapter11.Higham11SkewSourceCorrection` |
| `NumStability.Algorithms.Cholesky.TwoByTwoSchurStepCh11Closure` | `NumStability.Source.Higham.Chapter11.TwoByTwoSchurStep` |
| `NumStability.Algorithms.HighamChapter12` | `NumStability.Source.Higham.Chapter12.IterativeRefinement` |
| `NumStability.Algorithms.HighamChapter12OmegaDiscontinuity` | `NumStability.Source.Higham.Chapter12.OmegaDiscontinuity` |
| `NumStability.Algorithms.HighamChapter12Problem12_2` | `NumStability.Source.Higham.Chapter12.Problem02` |
| `NumStability.Algorithms.LU.BlockLU` | `NumStability.Algorithms.LinearSystems.LU.BlockLU` and `NumStability.Source.Higham.Chapter13.BlockLU` |
| `NumStability.Algorithms.LU.BlockLUArbitraryNormSourceClosure` | `NumStability.Algorithms.LinearSystems.LU.BlockLU.ArbitraryNorm` and `NumStability.Source.Higham.Chapter13.Section03.ArbitraryNormDominance` |
| `NumStability.Algorithms.LU.BlockLUComputationSourceClosure` | `NumStability.Source.Higham.Chapter13.Theorem06.Computation` |
| `NumStability.Algorithms.LU.BlockLUFirstOrderFamilies` | `NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderFamilies`, `NumStability.Source.Higham.Chapter13.Section01.OperationModelFamilies`, `NumStability.Source.Higham.Chapter13.Table01.Families`, and `NumStability.Source.Higham.Chapter13.Theorem05.FamilyErrorAnalysis` |
| `NumStability.Algorithms.LU.BlockLUPointRowGrowthSourceClosure` | `NumStability.Source.Higham.Chapter13.Equation23.PointRowGrowth` |
| `NumStability.Algorithms.LU.BlockLURowSourceClosure` | `NumStability.Source.Higham.Chapter13.Section03.RowDominanceClosure` |
| `NumStability.Algorithms.LU.BlockLUScalarGrowthBridge` | `NumStability.Source.Higham.Chapter13.Problem04.ScalarGrowthBridge` |
| `NumStability.Algorithms.LU.BlockLUSourceClosure` | `NumStability.Algorithms.LinearSystems.LU.BlockLU.OperatorTwo` and `NumStability.Source.Higham.Chapter13.Section03.ColumnDominanceClosure` |
| `NumStability.Algorithms.LU.BlockLUSPDFamilies` | `NumStability.Source.Higham.Chapter13.Equation25.Families` |
| `NumStability.Algorithms.LU.BlockLUSPDSourceClosure` | `NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite`, `NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefiniteFactorBounds`, `NumStability.Source.Higham.Chapter13.Equation25.Factorization`, and `NumStability.Source.Higham.Chapter13.Section03.SPDFactorBounds` |
| `NumStability.Algorithms.LU.BlockLUTable13_1Families` | `NumStability.Source.Higham.Chapter13.Equation25` and `NumStability.Source.Higham.Chapter13.Table01` |
| `NumStability.Algorithms.LU.BlockLUVarying` | `NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks` |
| `NumStability.Algorithms.LU.Higham13DemmelSharpMultiplier` | `NumStability.Source.Higham.Chapter13.DemmelSharpMultiplier` |
| `NumStability.Algorithms.Ch14HymanDeterminant` | `NumStability.Source.Higham.Chapter14.Problem14` |
| `NumStability.Algorithms.Ch14Problem1413Boundary` | `NumStability.Source.Higham.Chapter14.Problem13` |
| `NumStability.Algorithms.Ch14SchulzIteration` | `NumStability.Source.Higham.Chapter14.Section05.SquareIteration` |
| `NumStability.Algorithms.Ch14SchulzRectangular` | `NumStability.Source.Higham.Chapter14.Section05.RectangularIteration` |
| `NumStability.Algorithms.Ch14SchulzSpectralConvergence` | `NumStability.Source.Higham.Chapter14.Section05.SpectralConvergence` |
| `NumStability.Algorithms.Ch14SourceCorrections` | `NumStability.Source.Higham.Chapter14.Discrepancies` |
| `NumStability.Algorithms.Chapter14Problem1415Weyl` | `NumStability.Source.Higham.Chapter14.Problem15` |
| `NumStability.Algorithms.Ch4KahanFiniteFamily` | `NumStability.Source.Higham.Chapter04.Equation08.FiniteFamily` |
| `NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport` | `NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication` |
| `NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport` | `NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR` |
| `NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport` | `NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels` |
| `NumStability.Algorithms.QR.GivensMatrixStep` | `NumStability.Algorithms.LinearSystems.QR.GivensMatrixStep` |
| `NumStability.Algorithms.QR.GivensQR` | `NumStability.Algorithms.LinearSystems.QR.GivensQR` |
| `NumStability.Algorithms.QR.GivensSpec` | `NumStability.Algorithms.LinearSystems.QR.GivensSpec` |
| `NumStability.Algorithms.QR.GramSchmidt` | `NumStability.Algorithms.LinearSystems.QR.GramSchmidt` |
| `NumStability.Algorithms.QR.GramSchmidtPolar` | `NumStability.Algorithms.LinearSystems.QR.GramSchmidtPolar` |
| `NumStability.Algorithms.QR.Higham19` | `NumStability.Source.Higham.Chapter19.Core` |
| `NumStability.Algorithms.QR.Higham19Alg11CGSRounded` | `NumStability.Source.Higham.Chapter19.Algorithm11.CGSRounded` |
| `NumStability.Algorithms.QR.Higham19Alg12MGSClosure` | `NumStability.Source.Higham.Chapter19.Algorithm12.MGSClosure` |
| `NumStability.Algorithms.QR.Higham19Alg12MGSNonbreakdown` | `NumStability.Source.Higham.Chapter19.Algorithm12.MGSNonbreakdown` |
| `NumStability.Algorithms.QR.Higham19Alg12MGSPaddedClosure` | `NumStability.Source.Higham.Chapter19.Algorithm12.MGSPaddedClosure` |
| `NumStability.Algorithms.QR.Higham19Alg12MGSRepair` | `NumStability.Source.Higham.Chapter19.Algorithm12.MGSRepair` |
| `NumStability.Algorithms.QR.Higham19Alg12MGSRounded` | `NumStability.Source.Higham.Chapter19.Algorithm12.MGSRounded` |
| `NumStability.Algorithms.QR.Higham19Alg12MGSSourceRate` | `NumStability.Source.Higham.Chapter19.Algorithm12.MGSSourceRate` |
| `NumStability.Algorithms.QR.Higham19FormedQ` | `NumStability.Source.Higham.Chapter19.FormedQ` |
| `NumStability.Algorithms.QR.Higham19Labels` | `NumStability.Source.Higham.Chapter19.Labels` |
| `NumStability.Algorithms.QR.Higham19Lemma3ActualSequence` | `NumStability.Source.Higham.Chapter19.Lemma03.ActualSequence` |
| `NumStability.Algorithms.QR.Higham19Lemma7Gamma4` | `NumStability.Source.Higham.Chapter19.Lemma07.Gamma4` |
| `NumStability.Algorithms.QR.Higham19Lemma9DisjointSweep` | `NumStability.Source.Higham.Chapter19.Lemma09.DisjointSweep` |
| `NumStability.Algorithms.QR.Higham19PolarNearest` | `NumStability.Source.Higham.Chapter19.PolarNearest` |
| `NumStability.Algorithms.QR.Higham19Problem19_10` | `NumStability.Source.Higham.Chapter19.Problem10` |
| `NumStability.Algorithms.QR.Higham19Problem19_9` | `NumStability.Source.Higham.Chapter19.Problem09` |
| `NumStability.Algorithms.QR.Higham19Problem6ActualStep` | `NumStability.Source.Higham.Chapter19.Problem06.ActualStep` |
| `NumStability.Algorithms.QR.Higham19Sensitivity` | `NumStability.Source.Higham.Chapter19.Sensitivity` |
| `NumStability.Algorithms.QR.Higham19SensitivityClosure` | `NumStability.Source.Higham.Chapter19.Sensitivity.Closure` |
| `NumStability.Algorithms.QR.Higham19StoredLoop` | `NumStability.Source.Higham.Chapter19.StoredLoop` |
| `NumStability.Algorithms.QR.Higham19StoredLoopAllPivots` | `NumStability.Source.Higham.Chapter19.StoredLoop.AllPivots` |
| `NumStability.Algorithms.QR.Higham19StoredLoopStrongModel` | `NumStability.Source.Higham.Chapter19.StoredLoop.StrongModel` |
| `NumStability.Algorithms.QR.Higham19SunBischof` | `NumStability.Source.Higham.Chapter19.SunBischof` |
| `NumStability.Algorithms.QR.Higham19Theorem10ActualMatrix` | `NumStability.Source.Higham.Chapter19.Theorem10.ActualMatrix` |
| `NumStability.Algorithms.QR.Higham19Theorem5Nonbreakdown` | `NumStability.Source.Higham.Chapter19.Theorem05.Nonbreakdown` |
| `NumStability.Algorithms.QR.Higham19Theorem5SourceClosure` | `NumStability.Source.Higham.Chapter19.Theorem05.SourceClosure` |
| `NumStability.Algorithms.QR.Higham19Theorem6ActualSource` | `NumStability.Source.Higham.Chapter19.Theorem06.ActualSource` |
| `NumStability.Algorithms.QR.Higham19Thm6ColPivot` | `NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot` |
| `NumStability.Algorithms.QR.Higham19Thm6ColPivotFull` | `NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivotFull` |
| `NumStability.Algorithms.QR.Higham19Thm6CoxHigham` | `NumStability.Source.Higham.Chapter19.Theorem06.CoxHigham` |
| `NumStability.Algorithms.QR.Higham19Thm6CoxHighamAssembly` | `NumStability.Source.Higham.Chapter19.Theorem06.CoxHighamAssembly` |
| `NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete` | `NumStability.Source.Higham.Chapter19.Theorem06.CoxHighamConcrete` |
| `NumStability.Algorithms.QR.Higham19Thm6CoxHighamFull` | `NumStability.Source.Higham.Chapter19.Theorem06.CoxHighamFull` |
| `NumStability.Algorithms.QR.Higham19Thm6Elementwise` | `NumStability.Source.Higham.Chapter19.Theorem06.Elementwise` |
| `NumStability.Algorithms.QR.Higham19Thm6ElementwiseEntry` | `NumStability.Source.Higham.Chapter19.Theorem06.ElementwiseEntry` |
| `NumStability.Algorithms.QR.Higham19Thm6ElementwisePackaged` | `NumStability.Source.Higham.Chapter19.Theorem06.ElementwisePackaged` |
| `NumStability.Algorithms.QR.Higham19Thm6Final` | `NumStability.Source.Higham.Chapter19.Theorem06.Final` |
| `NumStability.Algorithms.QR.Higham19Thm6Pivoted` | `NumStability.Source.Higham.Chapter19.Theorem06.Pivoted` |
| `NumStability.Algorithms.QR.Higham19Thm6RowSpecific` | `NumStability.Source.Higham.Chapter19.Theorem06.RowSpecific` |
| `NumStability.Algorithms.QR.Higham19Thm6StrongModel` | `NumStability.Source.Higham.Chapter19.Theorem06.StrongModel` |
| `NumStability.Algorithms.QR.Higham19TurnbullAitken` | `NumStability.Source.Higham.Chapter19.TurnbullAitken` |
| `NumStability.Algorithms.QR.Higham19WYApplicationClosure` | `NumStability.Source.Higham.Chapter19.WYApplicationClosure` |
| `NumStability.Algorithms.QR.HouseholderApply` | `NumStability.Algorithms.LinearSystems.QR.HouseholderApply` |
| `NumStability.Algorithms.QR.HouseholderApplySupport` | `NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication` |
| `NumStability.Algorithms.QR.HouseholderConstruction2` | `NumStability.Algorithms.LinearSystems.QR.HouseholderConstruction2` and `NumStability.Source.Higham.Chapter19.Lemma01.Construction2` |
| `NumStability.Algorithms.QR.HouseholderMatrixStep` | `NumStability.Algorithms.LinearSystems.QR.HouseholderMatrixStep` |
| `NumStability.Algorithms.QR.HouseholderOneStep` | `NumStability.Algorithms.LinearSystems.QR.HouseholderOneStep` |
| `NumStability.Algorithms.QR.HouseholderQApply` | `NumStability.Algorithms.LinearSystems.QR.HouseholderQApply` |
| `NumStability.Algorithms.QR.HouseholderQR` | `NumStability.Algorithms.LinearSystems.QR.HouseholderQR` |
| `NumStability.Algorithms.QR.HouseholderQRSupport` | `NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR` |
| `NumStability.Algorithms.QR.HouseholderReflector` | `NumStability.Algorithms.LinearSystems.QR.HouseholderReflector` |
| `NumStability.Algorithms.QR.HouseholderSpec` | `NumStability.Algorithms.LinearSystems.QR.HouseholderSpec` |
| `NumStability.Algorithms.QR.HouseholderSpecSupport` | `NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels` |
| `NumStability.Algorithms.QR.QRSolve` | `NumStability.Algorithms.LinearSystems.QR.QRSolve` |
| `NumStability.Algorithms.LeastSquares.Higham20Algorithms` | `NumStability.Algorithms.LeastSquares.LSQRSolve`, `NumStability.Algorithms.LinearSystems.LeastSquares.Refinement`, `NumStability.Analysis.Perturbation.LeastSquares.Basic`, and `NumStability.Source.Higham.Chapter20.Section02.Algorithms` |
| `NumStability.Algorithms.LeastSquares.Higham20AlternativeBound` | `NumStability.Algorithms.LeastSquares.LSQRSolve`, `NumStability.Algorithms.LinearSystems.LeastSquares.Basic`, `NumStability.Analysis.Perturbation.LeastSquares.AlternativeBound`, and `NumStability.Source.Higham.Chapter20.Theorem02.AlternativeBound` |
| `NumStability.Algorithms.LeastSquares.Higham20CrossProductExample` | `Mathlib.Tactic.FinCases`, `Mathlib.Tactic.NormNum`, `NumStability.Algorithms.LeastSquares.LSNormalEquations`, and `NumStability.Source.Higham.Chapter20.Examples.CrossProduct` |
| `NumStability.Algorithms.LeastSquares.Higham20EliminationActual` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7`, `NumStability.Algorithms.LeastSquares.LSE`, `NumStability.Algorithms.LinearSystems.LeastSquares.RowSorting`, and `NumStability.Source.Higham.Chapter20.Theorem07.Elimination` |
| `NumStability.Algorithms.LeastSquares.Higham20Equations` | `Mathlib.Tactic.Linarith`, `Mathlib.Tactic.Ring`, `NumStability.Algorithms.LeastSquares.LSNormalEquations`, `NumStability.Algorithms.LeastSquares.LSQRSolve`, `NumStability.Analysis.Perturbation.LeastSquares.Basic`, `NumStability.Source.Higham.Chapter12.IterativeRefinement`, and `NumStability.Source.Higham.Chapter20.Equations` |
| `NumStability.Algorithms.LeastSquares.Higham20ExampleCondition` | `NumStability.Algorithms.LeastSquares.Higham20Prose`, `NumStability.Algorithms.Underdetermined.UnderdeterminedSpec`, and `NumStability.Source.Higham.Chapter20.Examples.Condition` |
| `NumStability.Algorithms.LeastSquares.Higham20GeneralWedin` | `NumStability.Algorithms.LeastSquares.Higham20Lemma20_12`, `NumStability.Analysis.Perturbation.LeastSquares.Wedin`, and `NumStability.Source.Higham.Chapter20.Examples.GeneralRank` |
| `NumStability.Algorithms.LeastSquares.Higham20Lemma20_11` | `NumStability.Algorithms.LeastSquares.LSPerturbation`, `NumStability.Algorithms.Underdetermined.UnderdeterminedSpec`, `NumStability.Analysis.SingularValues.WeylMirsky`, and `NumStability.Source.Higham.Chapter20.Lemma11` |
| `NumStability.Algorithms.LeastSquares.Higham20Lemma20_12` | `NumStability.Algorithms.LeastSquares.LSPerturbation`, `NumStability.Algorithms.Underdetermined.UnderdeterminedSpec`, `NumStability.Analysis.Perturbation.LeastSquares.Projection`, and `NumStability.Source.Higham.Chapter20.Lemma12` |
| `NumStability.Algorithms.LeastSquares.Higham20MGSStability` | `NumStability.Algorithms.LeastSquares.LSQRSolve`, `NumStability.Algorithms.QR.Higham19`, `NumStability.Algorithms.QR.Higham19Alg12MGSRepair`, `NumStability.Algorithms.QR.Higham19Alg12MGSRounded`, and `NumStability.Source.Higham.Chapter20.Problem05.MGSStability` |
| `NumStability.Algorithms.LeastSquares.Higham20MPProse` | `NumStability.Algorithms.LeastSquares.Higham20Lemma20_11`, `NumStability.Algorithms.LeastSquares.LSQRSolve`, and `NumStability.Source.Higham.Chapter20.Prose.MoorePenrose` |
| `NumStability.Algorithms.LeastSquares.Higham20MinimumNormBackwardError` | `NumStability.Algorithms.LeastSquares.Higham20WeightedLimit`, `NumStability.Analysis.Perturbation.LeastSquares.MinimumNorm`, and `NumStability.Source.Higham.Chapter20.MinimumNormBackwardError` |
| `NumStability.Algorithms.LeastSquares.Higham20NormalEquationsNorms` | `NumStability.Algorithms.LeastSquares.Higham20Equations`, `NumStability.Algorithms.LeastSquares.Higham20Remaining`, `NumStability.Analysis.Perturbation.LeastSquares.NormalEquations`, and `NumStability.Source.Higham.Chapter20.NormalEquations` |
| `NumStability.Algorithms.LeastSquares.Higham20Problem20_3` | `NumStability.Algorithms.LeastSquares.Higham20MPProse`, and `NumStability.Source.Higham.Chapter20.Problem03` |
| `NumStability.Algorithms.LeastSquares.Higham20Prose` | `NumStability.Algorithms.LeastSquares.LSQRSolve`, `NumStability.Algorithms.Underdetermined.Higham21ProjectorNorm`, `NumStability.Analysis.Perturbation.LeastSquares.Conditioning`, and `NumStability.Source.Higham.Chapter20.Prose` |
| `NumStability.Algorithms.LeastSquares.Higham20QuantitativeProse` | `NumStability.Algorithms.LeastSquares.Higham20Prose`, and `NumStability.Source.Higham.Chapter20.Prose.Quantitative` |
| `NumStability.Algorithms.LeastSquares.Higham20Refinement` | `Mathlib.Tactic.Linarith`, `Mathlib.Tactic.Ring`, `NumStability.Algorithms.LeastSquares.Higham20Equations`, `NumStability.Algorithms.LinearSystems.LeastSquares.Refinement`, `NumStability.Analysis.Perturbation.LeastSquares.Basic`, and `NumStability.Source.Higham.Chapter20.Theorem04.Refinement` |
| `NumStability.Algorithms.LeastSquares.Higham20Remaining` | `Mathlib.Tactic.Linarith`, `Mathlib.Tactic.Ring`, `NumStability.Algorithms.HighamChapter10`, `NumStability.Algorithms.LeastSquares.LSE`, `NumStability.Algorithms.LeastSquares.LSNormalEquations`, and `NumStability.Source.Higham.Chapter20.Remaining` |
| `NumStability.Algorithms.LeastSquares.Higham20ResidualQuality` | `NumStability.Algorithms.LeastSquares.Higham20AlternativeBound`, `NumStability.Algorithms.LeastSquares.Higham20Theorem20_3`, `NumStability.Algorithms.LinearSystems.LeastSquares.Basic`, `NumStability.Analysis.Perturbation.LeastSquares.ResidualQuality`, and `NumStability.Source.Higham.Chapter20.Theorem03.ResidualQuality` |
| `NumStability.Algorithms.LeastSquares.Higham20RowSorting` | `NumStability.Algorithms.LeastSquares.Higham20EliminationActual`, `NumStability.Analysis.Perturbation.LeastSquares.Basic`, and `NumStability.Source.Higham.Chapter20.Theorem07.RowPolicy` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_10` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_3`, `NumStability.Algorithms.LeastSquares.LSE`, `NumStability.Analysis.Perturbation.LeastSquares.Equality.MixedStability`, and `NumStability.Source.Higham.Chapter20.Theorem10` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_3` | `NumStability.Algorithms.LeastSquares.LSQRSolve`, `NumStability.Algorithms.QR.Higham19`, and `NumStability.Source.Higham.Chapter20.Theorem03` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_4Absorption` | `NumStability.Algorithms.LeastSquares.Higham20Refinement`, `NumStability.Analysis.Perturbation.LeastSquares.Absorption`, and `NumStability.Source.Higham.Chapter20.Theorem04` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7` | `NumStability.Algorithms.LeastSquares.LSQRSolve`, `NumStability.Algorithms.LinearSystems.LeastSquares.TraceKernel`, `NumStability.Algorithms.LinearSystems.QR.HouseholderApply`, `NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR`, `NumStability.Algorithms.QR.Higham19Thm6CoxHigham`, `NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete`, `NumStability.Analysis.Perturbation.LeastSquares.Contract`, and `NumStability.Source.Higham.Chapter20.Theorem07` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualAssembly` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualRhs`, and `NumStability.Source.Higham.Chapter20.Theorem07.ActualAssembly` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualBackSub` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualAssembly`, and `NumStability.Source.Higham.Chapter20.Theorem07.ActualBackSub` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualClosure` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualTrace`, and `NumStability.Source.Higham.Chapter20.Theorem07.ActualClosure` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualGrowth` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualClosure`, and `NumStability.Source.Higham.Chapter20.Theorem07.ActualGrowth` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualRhs` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualGrowth`, and `NumStability.Source.Higham.Chapter20.Theorem07.ActualRhs` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualTrace` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7SourceTrace`, `NumStability.Algorithms.LinearSystems.LeastSquares.TraceKernel`, and `NumStability.Source.Higham.Chapter20.Theorem07.ActualTrace` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7Contract` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7QdR`, `NumStability.Algorithms.QR.Higham19Thm6RowSpecific`, and `NumStability.Source.Higham.Chapter20.Theorem07.Contract` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7QdR` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7`, `NumStability.Algorithms.LinearSystems.LeastSquares.TraceKernel`, `NumStability.Analysis.Perturbation.LeastSquares.Contract`, and `NumStability.Source.Higham.Chapter20.Theorem07.QdR` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7Runtime` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7Contract`, `NumStability.Algorithms.LinearSystems.LeastSquares.TraceKernel`, and `NumStability.Source.Higham.Chapter20.Theorem07.Runtime` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7SourceTrace` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_7Contract`, `NumStability.Algorithms.LinearSystems.LeastSquares.TraceKernel`, and `NumStability.Source.Higham.Chapter20.Theorem07.SourceTrace` |
| `NumStability.Algorithms.LeastSquares.Higham20Theorem20_8` | `NumStability.Algorithms.LeastSquares.LSE`, `NumStability.Analysis.Perturbation.LeastSquares.Equality.KKTInverse`, and `NumStability.Source.Higham.Chapter20.Theorem08` |
| `NumStability.Algorithms.LeastSquares.Higham20WeightedLimit` | `NumStability.Algorithms.LeastSquares.LSE`, `NumStability.Analysis.Perturbation.LeastSquares.WeightedLimit`, and `NumStability.Source.Higham.Chapter20.Equations.WeightedLimit` |
| `NumStability.Algorithms.LeastSquares.Higham20ZeroDeltaB` | `NumStability.Algorithms.LeastSquares.Higham20Theorem20_3`, `NumStability.Algorithms.QR.Higham19Labels`, `NumStability.Algorithms.Underdetermined.UnderdeterminedSolve`, and `NumStability.Source.Higham.Chapter20.Theorem03.ZeroDeltaB` |
| `NumStability.Algorithms.LeastSquares.LSE` | `Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Algebra.Order.BigOperators.Group.Finset`, `Mathlib.Data.Fin.Tuple.Sort`, `Mathlib.Data.Real.Basic`, `Mathlib.LinearAlgebra.Dual.Lemmas`, `Mathlib.Tactic.Linarith`, `Mathlib.Tactic.Ring`, `NumStability.Algorithms.LeastSquares.LSQRSolve`, `NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic`, `NumStability.Algorithms.LinearSystems.LeastSquares.Equality.GQR`, `NumStability.Algorithms.LinearSystems.LeastSquares.Equality.KKT`, `NumStability.Algorithms.LinearSystems.QR.GramSchmidtPolar`, `NumStability.Algorithms.QR.Higham19`, `NumStability.Algorithms.QR.Higham19Thm6ColPivot`, `NumStability.Algorithms.QR.Higham19Thm6CoxHigham`, `NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete`, `NumStability.Algorithms.QR.Higham19Thm6ElementwisePackaged`, `NumStability.Algorithms.QR.Higham19Thm6RowSpecific`, `NumStability.Algorithms.Underdetermined.UnderdeterminedSpec`, `NumStability.Analysis.Perturbation.LeastSquares.Equality.MixedStability`, `NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation`, `NumStability.Analysis.Perturbation.LeastSquares.Equality.RowwiseBackwardError`, and `NumStability.Source.Higham.Chapter20.Theorem08.LSE` |
| `NumStability.Algorithms.LeastSquares.LSNormalEquations` | `Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Algebra.Order.BigOperators.Group.Finset`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic.FinCases`, `Mathlib.Tactic.Linarith`, `Mathlib.Tactic.NormNum`, `Mathlib.Tactic.Ring`, `NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic`, `NumStability.Algorithms.Cholesky.CholeskySpec`, `NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations`, `NumStability.Algorithms.MatMul`, `NumStability.Analysis.MatrixAlgebra`, `NumStability.Analysis.Perturbation.LeastSquares.NormalEquations`, `NumStability.Analysis.PerturbationTheory`, `NumStability.Analysis.Rounding`, and `NumStability.FloatingPoint.Model` |
| `NumStability.Algorithms.LeastSquares.LSPerturbation` | `Mathlib.Data.Real.Basic`, `NumStability.Analysis.MatrixAlgebra`, `NumStability.Analysis.MatrixSpectral`, `NumStability.Analysis.Perturbation.LeastSquares.Basic`, `NumStability.Analysis.Perturbation.LeastSquares.Wedin`, `NumStability.Analysis.SingularValues.Realification`, and `NumStability.Source.Higham.Chapter20.Lemma11.Support` |
| `NumStability.Algorithms.LeastSquares.LSQRSolve` | `Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Algebra.Order.BigOperators.Group.Finset`, `Mathlib.Analysis.Matrix.Spectrum`, `Mathlib.Data.Real.Basic`, `Mathlib.LinearAlgebra.Matrix.Rank`, `Mathlib.Tactic.FieldSimp`, `Mathlib.Tactic.Linarith`, `Mathlib.Tactic.Ring`, `NumStability.Algorithms.LeastSquares.LSPerturbation`, `NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem`, `NumStability.Algorithms.LinearSystems.LeastSquares.Basic`, `NumStability.Algorithms.LinearSystems.LeastSquares.GramBasis`, `NumStability.Algorithms.LinearSystems.LeastSquares.MGS`, `NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations`, `NumStability.Algorithms.LinearSystems.LeastSquares.QRSolve`, `NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry`, `NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR`, `NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR`, `NumStability.Algorithms.LinearSystems.QR.QRSolve`, `NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution`, `NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution`, `NumStability.Algorithms.LinearSystems.Triangular.InverseBounds`, `NumStability.Algorithms.RandNLA.LowRankApprox`, `NumStability.Analysis.MatrixAlgebra`, `NumStability.Analysis.Perturbation.LeastSquares.AugmentedSystem`, `NumStability.Analysis.Perturbation.LeastSquares.BackwardError`, `NumStability.Analysis.Perturbation.LeastSquares.Basic`, `NumStability.Analysis.Perturbation.LeastSquares.GramBasis`, `NumStability.Analysis.Perturbation.LeastSquares.NormalEquations`, `NumStability.Analysis.Perturbation.LeastSquares.Normwise`, `NumStability.Analysis.PerturbationTheory`, `NumStability.Analysis.SingularValues.Realification`, and `NumStability.Source.Higham.Chapter20.Theorem03.QRSolve` |
| `NumStability.Algorithms.LeastSquares.Higham20SourceAliases` | `NumStability.Source.Higham.Chapter20.Equation32`, `NumStability.Source.Higham.Chapter20.Lemma06`, and `NumStability.Source.Higham.Chapter20.Theorem01` |
| `NumStability.Algorithms.Underdetermined.Higham21Condition` | `NumStability.Source.Higham.Chapter21.RowScalingInvariance` |
| `NumStability.Algorithms.Underdetermined.Higham21RowwiseMeasure` | `NumStability.Source.Higham.Chapter21.Theorem04.RowwiseBackwardError` |
| `NumStability.Algorithms.Underdetermined.Higham21Theorem21_3Attainment` | `NumStability.Source.Higham.Chapter21.Theorem03.Attainment` |
| `NumStability.Algorithms.Vandermonde.Higham22` | `NumStability.Source.Higham.Chapter22.VandermondeSystems` |
| `NumStability.Algorithms.Vandermonde.Higham22MonomialClosure` | `NumStability.Source.Higham.Chapter22.MonomialResidual` |
| `NumStability.Algorithms.Vandermonde.Higham22Problem22_7` | `NumStability.Source.Higham.Chapter22.Problem07` |
| `NumStability.Algorithms.Vandermonde.Higham22Ch12RefinementBridge` | `NumStability.Source.Higham.Chapter22.Section03.RealRefinement` |
| `NumStability.Algorithms.Vandermonde.Higham22ComplexConfluentRefinementBridge` | `NumStability.Source.Higham.Chapter22.Section03.ComplexConfluentRefinement` |
| `NumStability.Algorithms.FastMatMul.Higham23` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.ThreeM`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FastMatMul.Higham23Bini` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BiniLotti`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.Equation11`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.Theorem02`, `NumStability.Source.Higham.Chapter23.Theorem03`, `NumStability.Source.Higham.Chapter23.ThreeM`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FastMatMul.Higham23Problem23_8` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.Problem08`, `NumStability.Source.Higham.Chapter23.Theorem02`, `NumStability.Source.Higham.Chapter23.Theorem03.Execution`, `NumStability.Source.Higham.Chapter23.ThreeM`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FastMatMul.Higham23Recursive` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.Theorem02`, `NumStability.Source.Higham.Chapter23.Theorem03.Execution`, `NumStability.Source.Higham.Chapter23.ThreeM`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FastMatMul.Higham23Remaining` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.Equation11`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.Theorem02`, `NumStability.Source.Higham.Chapter23.Theorem03`, `NumStability.Source.Higham.Chapter23.ThreeM`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FastMatMul.Higham23ThreeMStrassen` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BiniLotti`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.Equation11`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.Theorem02`, `NumStability.Source.Higham.Chapter23.Theorem03`, `NumStability.Source.Higham.Chapter23.ThreeM`, `NumStability.Source.Higham.Chapter23.ThreeMStrassen`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FFT.Higham24` | `NumStability.Source.Higham.Chapter24.FourierTransform` |
| `NumStability.Algorithms.FFT.Higham24Radix2` | `NumStability.Source.Higham.Chapter24.Radix2FFT` |
| `NumStability.Algorithms.Circulant.Higham24` | `NumStability.Source.Higham.Chapter24.CirculantSystems` |
| `NumStability.Algorithms.Circulant.Higham24ForwardPerturbation` | `NumStability.Source.Higham.Chapter24.ForwardFFTPerturbation` |
| `NumStability.Algorithms.Circulant.Higham24Rounded` | `NumStability.Source.Higham.Chapter24.RoundedDiagonalSolve` |
| `NumStability.Algorithms.Circulant.Higham24InverseFFT` | `NumStability.Source.Higham.Chapter24.InverseFFT` |
| `NumStability.Algorithms.Circulant.Higham24LiteralSolver` | `NumStability.Source.Higham.Chapter24.RoundedCirculantSolver` |
| `NumStability.Algorithms.Circulant.Higham24BackwardStability` | `NumStability.Source.Higham.Chapter24.FFTBackwardStability` |
| `NumStability.Algorithms.Circulant.Higham24Structured` | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` |
| `NumStability.Algorithms.Circulant.Higham24ForwardError` | `NumStability.Source.Higham.Chapter24.CirculantForwardError` |
| `NumStability.Algorithms.Nonlinear.Higham25` | `NumStability.Source.Higham.Chapter25.NonlinearSystems` |
| `NumStability.Algorithms.Nonlinear.Higham25EigenClosure` | `NumStability.Source.Higham.Chapter25.Eigenproblem` |
| `NumStability.Algorithms.Nonlinear.Higham25Problem25_1` | `NumStability.Source.Higham.Chapter25.Problem01` |
| `NumStability.Algorithms.SoftwareIssues.Higham27` | `NumStability.Source.Higham.Chapter27.SoftwareEnvironment` |
| `NumStability.Algorithms.SoftwareIssues.Higham27Pythag` | `NumStability.Source.Higham.Chapter27.Problem06` |
| `NumStability.Algorithms.TestMatrices.Higham28GaussianAbsoluteMoment` | `NumStability.Analysis.Probability.Gaussian.AbsoluteMoment` |
| `NumStability.Algorithms.TestMatrices.Higham28HaarFibers` | `NumStability.Analysis.Probability.Haar.HomogeneousSpaceUniqueness` |
| `NumStability.Algorithms.TestMatrices.Higham28HilbertRatioDiscrepancy` | `NumStability.Source.Higham.Chapter28.Equation02.RatioDiscrepancy` |
| `NumStability.Algorithms.HighamChapter3NoGuardDotBridge` | `NumStability.Algorithms.Arithmetic.DotProduct.NoGuard` and `NumStability.Source.Higham.CrossChapter.NoGuardDotProduct` |
| `NumStability.Algorithms.HighamChapter15Ch7PracticalBoundBridge` | `NumStability.Source.Higham.CrossChapter.PracticalConditionBound` |
| `NumStability.Algorithms.HighamChapter12Ch9GenericSolverBridge` | `NumStability.Source.Higham.CrossChapter.LUSolverWeights.Factorization` |
| `NumStability.Algorithms.HighamChapter12Ch9SolverBridge` | `NumStability.Source.Higham.CrossChapter.LUSolverWeights.Doolittle` |
| `NumStability.Algorithms.AutomaticErrorAnalysis.Higham26` | `NumStability.Source.Higham.Chapter26.AlternatingDirections.ExactExecution`, `NumStability.Source.Higham.Chapter26.CubicRoots.DepressedCubic`, `NumStability.Source.Higham.Chapter26.CubicRoots.MonicCubic`, `NumStability.Source.Higham.Chapter26.Equation01`, `NumStability.Source.Higham.Chapter26.Equation02`, `NumStability.Source.Higham.Chapter26.Equation03`, `NumStability.Source.Higham.Chapter26.Equation04`, `NumStability.Source.Higham.Chapter26.Equation05.CardanoRoots`, `NumStability.Source.Higham.Chapter26.Equation05.ComplexBranches`, `NumStability.Source.Higham.Chapter26.Equation05.RealBranches`, `NumStability.Source.Higham.Chapter26.Equation05.ZeroBranchDiscrepancy`, `NumStability.Source.Higham.Chapter26.Equation06`, `NumStability.Source.Higham.Chapter26.Equation07`, `NumStability.Source.Higham.Chapter26.Equation08`, `NumStability.Source.Higham.Chapter26.IntervalArithmetic.DependencyExamples`, `NumStability.Source.Higham.Chapter26.IntervalArithmetic.DirectedRounding`, `NumStability.Source.Higham.Chapter26.IntervalArithmetic.ExactOperations`, `NumStability.Source.Higham.Chapter26.MultidirectionalSearch.Execution`, and `NumStability.Source.Higham.Chapter26.MultidirectionalSearch.Simplex` |
| `NumStability.Algorithms.AutomaticErrorAnalysis.Higham26SourceSearch` | `NumStability.Source.Higham.Chapter26` |
| `NumStability.Algorithms.HighamChapter4KaoWangScope` | `NumStability.Source.Higham.Chapter04.Section02.KaoWangCitationDiscrepancy` |
| `NumStability.Algorithms.Problem44SixTerm` | `NumStability.Source.Higham.Chapter04.Problem04` |
| `NumStability.Algorithms.StationaryIterationSeries` | `NumStability.Source.Higham.Chapter17.Problem01`, `NumStability.Source.Higham.Chapter17.Results.Series` |
| `NumStability.Analysis.Ch17SemiconvergentBlockFormSourceClosure` | `NumStability.Source.Higham.Chapter17.Equation22` |
| `NumStability.Analysis.NonrandomRounding` | `NumStability.Source.Higham.Chapter01.Section17` |
| `NumStability.Analysis.NonrandomRounding.Conclusions` | `NumStability.Source.Higham.Chapter01.Section17.ErrorSpread` |
| `NumStability.Analysis.NonrandomRounding.Core` | `NumStability.Source.Higham.Chapter01.Section17.HornerEvaluation` |
| `NumStability.Analysis.NonrandomRounding.GridVariation` | `NumStability.Source.Higham.Chapter01.Section17.GridVariation` |
| `NumStability.Analysis.NonrandomRounding.SourceInterval` | `NumStability.Source.Higham.Chapter01.Section17.SourceInterval` |
| `NumStability.Analysis.NonrandomRounding.StoredGrid` | `NumStability.Source.Higham.Chapter01.Section17.StoredGrid` |
| `NumStability.Algorithms.Ch10Ch14Lemma66Op2Bridge` | `NumStability.Algorithms.HighamChapter10`, `NumStability.Source.Higham.Chapter06.Lemma06`, `NumStability.Source.Higham.Chapter06.Lemma06.OperatorTwoNormBound.Bridge`, `NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Bridge`, `NumStability.Source.Higham.Chapter14.Section03.ResidualOperatorTwoNorm.Bridge` |
| `NumStability.Algorithms.Ch10KahanSharpness` | `NumStability.Algorithms.HighamChapter10`, `NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Limit` |
| `NumStability.Algorithms.Ch10Lemma1011Source` | `NumStability.Algorithms.HighamChapter10`, `NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.SourceClosure` |
| `NumStability.Algorithms.Ch10Theorem107FailureVacuity` | `NumStability.Algorithms.HighamChapters1To9SourceClosure`, `NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Vacuity` |
| `NumStability.Algorithms.Cholesky.CholeskyIndefinite` | `NumStability.Algorithms.LU.GaussianElimination`, `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT`, `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLTStep`, `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.Predicates`, `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.SkewSymmetric`, `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Pivoting.Basic`, `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Pivoting.Tridiagonal`, `NumStability.Analysis.Rounding`, `NumStability.FloatingPoint.Model`, `NumStability.Source.Higham.Chapter11.Theorem07.TridiagonalTwoByTwoResidual.Basic` |
| `NumStability.Algorithms.Cholesky.CholeskyPerturbation` | `NumStability.Algorithms.Cholesky.CholeskySpec`, `NumStability.Algorithms.LU.GaussianElimination`, `NumStability.Algorithms.LU.GrowthFactor`, `NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic`, `NumStability.Analysis.Rounding`, `NumStability.FloatingPoint.Model` |
| `NumStability.Algorithms.Cholesky.CholeskySolve` | `NumStability.Algorithms.Cholesky.CholeskySpec`, `NumStability.Algorithms.LU.LUSolve`, `NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic`, `NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution`, `NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution`, `NumStability.Analysis.Rounding`, `NumStability.FloatingPoint.Model` |
| `NumStability.Algorithms.Cholesky.Higham1014SourceSuccess` | `NumStability.Source.Higham.Chapter10.Theorem07`, `NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceSuccess` |
| `NumStability.Algorithms.Cholesky.Higham10Problem10_3` | `NumStability.Algorithms.Summation.Tree.ArbitraryOrderError.PivotNormalized`, `NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.ArbitraryOrder`, `NumStability.Source.Higham.Chapter10.Problem03.ArbitraryEvaluationOrder.Basic` |
| `NumStability.Algorithms.Cholesky.HighamMathiasFirstBreakdown` | `NumStability.Algorithms.Cholesky.Higham1029Source`, `NumStability.Source.Higham.Chapter09.DoolittleClosure`, `NumStability.Source.Higham.Chapter10.Equation29.Mathias.FirstBreakdown` |

The nine W05 import-only historical paths remain intentionally outside the
compatibility tier at C0006. W06 retargeted every accepted consumer authorized
by its delivery, but the integration contract still requires
`NumStability.Algorithms.Sylvester` to retain the W05 historical discovery
imports. Promoting those paths would make the compatibility gate reject that
required production aggregate.

The 44 W06 and 24 W08 pure historical shims are also reviewed, declaration-free
facades rather than compatibility-tier modules at C0006. The global historical
discovery aggregates and frozen W09/W11 consumers still import some of these
paths. The compatibility checker deliberately forbids production imports of a
compatibility-tier path, so promotion must wait for the owning future waves to
retarget those consumers and for a later integrator checkpoint to remove the
remaining historical discovery imports. Their exact declaration routing and
retention evidence is recorded in the W06 and W08 delivery ledgers; all old
paths and every canonical destination have isolated tests in this checkpoint.

The single-target chapter rows above are exact one-to-one forwarders. The
canonical chapter aggregates are discovery entry points, not wrapper targets:
`NumStability.Source.Higham.Chapter02`,
`NumStability.Source.Higham.Chapter12`,
`NumStability.Source.Higham.Chapter14`,
`NumStability.Source.Higham.Chapter14.Section05`,
`NumStability.Source.Higham.Chapter21`,
`NumStability.Source.Higham.Chapter21.Theorem03`,
`NumStability.Source.Higham.Chapter21.Theorem04`,
`NumStability.Source.Higham.Chapter22`,
`NumStability.Source.Higham.Chapter22.Section03`,
`NumStability.Source.Higham.Chapter27`,
`NumStability.Source.Higham.Chapter28`, and
`NumStability.Source.Higham.Chapter28.Equation02` contain only documentation and imports.
The reusable `NumStability.Analysis.Equidistribution`, `LeadingDigits`,
`Asymptotics`, `Conditioning`, `LinearOperators`, `MatrixNorms`,
`OperatorNorms`, `Probability.Haar`, `SingularValues`, and `VectorNorms`
aggregates, and the source `NumStability.Source.Higham.Chapter02.Section07` and
`NumStability.Source.Higham.Chapter06.Norms` aggregates, are likewise
declaration-free discovery entry points. `NumStability.Analysis.Norms.Core` is
also declaration-free and is audited as a reusable entry point for its former
reusable subset; numbered Chapter 6 results are intentionally exposed through
the source aggregate and the broader historical `Analysis.Norms` facade.

The compatibility inventory now contains 337 wrappers with 685 direct project
targets.

Phase 12 completes the cutover of the historical
`NumStability.Algorithms.LU.BlockLU` declaration owner. That path is now a
declaration-free two-target facade over the
canonical reusable `NumStability.Algorithms.LinearSystems.LU.BlockLU` family
and the source-facing `NumStability.Source.Higham.Chapter13.BlockLU` family.
Production consumers use those semantic owners directly; the old-only import
test preserves the complete historical surface. The follow-on ownership
contract also moves all 287 declarations from the ten historical BlockLU
sibling modules into 22 reusable and Chapter 13 destinations. Those ten paths
are now exact declaration-free wrappers with isolated old-only tests; no
production consumer imports them.

Phase 11B2 adds four exact one-target wrappers for the former Chapter 6
`Chapter06Lemma66`, `Higham6Asides`, `Higham6BlockAntidiag`, and
`HighamChapter6Duality` paths. Their declarations now live in the canonical
`Source.Higham.Chapter06` tree; isolated old-only tests preserve each former
import surface.

The historical `NumStability.Analysis.Norms` path remains a two-target facade.
It re-exports the declaration-free reusable Core aggregate and the dedicated
`Source.Higham.Chapter06.Norms` aggregate, preserving its former generic
surface together with Problems 6.1, 6.5, 6.9, and 6.10 and Theorem 6.4. New
production code imports the narrow semantic family or source leaf it needs;
no declaration-bearing production module imports the historical facade or
Core. Core is now classified as an aggregate and owns no declarations. This
Phase 11B1 retained 104 wrappers with 204 direct targets. The four Phase 11B2
wrappers produced 108/208; the Phase 12 two-target `Algorithms.LU.BlockLU`
facade produced 109/210, and the ten sibling wrappers produced 119/228. The
first two QR waves add 17 exact historical wrappers and 18 direct targets,
producing 136/246. The completed Chapter 9 split adds 11 historical facades
and 20 direct targets, producing 147/266 before the 41 LSQ wrappers and their
185 project-facing import targets raised the current totals to 188/451.

`NumStability.Source.Higham.Chapter02.Problem22` has one temporary
canonical-side compatibility exception: in addition to locating the reusable
Problem 2.22 API, it re-exports `Source.Higham.Chapter02.Problem23` because the
Heron surface was previously published from the incorrectly numbered Problem
22 path. This extra import may be removed only in a planned breaking release,
after the release notes identify `Problem23` as the replacement and downstream
users have had a migration window. It is not a precedent for new canonical
modules to re-export adjacent source problems.

The historical nonrandom-rounding path remains the complete compatibility
import for the canonical Section 1.17 aggregate. Its five historical child
paths are exact import-only wrappers for the corresponding semantic leaves;
new code should import the canonical Chapter 1 paths directly.

R11 retains one source-side compatibility boundary in
`NumStability.Source.Higham.Chapter19.Core`. That reviewed source outlier stays
byte-for-byte identical to C0001 and therefore still imports the historical
`NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport` and
`NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport` paths. The
compatibility checker pins the exact C0001 source digest, permits exactly those
two edges, and rejects content drift or a stale allowance. A later Chapter 19
Core migration must retarget both imports to the canonical Householder modules
and remove the source pin and two checker exceptions in the same change.

CI runs `tools/architecture/check_compatibility.py` to require that every
tabled historical file contains only its documented imports and that
production modules use no tabled old path outside the exact retained R11
boundary above. Old-only and canonical-only Lean smoke modules compile the two
surfaces independently; summation wrappers and the Chapter 9-to-12 bridge pair
also have isolated per-wrapper checks where sibling dependencies could
otherwise mask a regression.

| `NumStability.Algorithms.StationaryIteration` | `NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.Projectors.FixedRange`, `NumStability.Source.Higham.Chapter17.Results.Equation20.DiagonalizableBounds`, `NumStability.Source.Higham.Chapter17.Results.Equation27.SingularErrorSplit`, `NumStability.Source.Higham.Chapter17.Results.Equation29.SingularBounds` |
| `NumStability.Algorithms.StationaryIterationDrazin` | `NumStability.Source.Higham.Chapter17.Results.Section04.DrazinConsequences` |
| `NumStability.Algorithms.StationaryIterationRounded` | `NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.Execution.RoundedCertificates`, `NumStability.Source.Higham.Chapter17.Results.Section01.RoundedExecution` |
| `NumStability.Algorithms.StationaryIterationSemiconvergent` | `NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.BlockForm.ProjectorLimit`, `NumStability.Source.Higham.Chapter17.Results.Equation27.SingularErrorSplit` |
| `NumStability.Algorithms.StationaryIterationSemiconvergentExistence` | `NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.BlockForm.Existence`, `NumStability.Source.Higham.Chapter17.Results.Equation27.SingularErrorSplit` |
| `NumStability.Analysis.SemiconvergentBlockFormExists` | `NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.TriangularBlockForm` |
| `NumStability.Analysis.SemiconvergentExistenceComplete` | `NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.PrimarySplitting` |
| `NumStability.Analysis.SemiconvergentExistenceFull` | `NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.QuasiTriangularBlockForm` |
| `NumStability.Analysis.SemiconvergentLimitGeneral` | `NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.Limits.General` |
| `NumStability.Analysis.SemiconvergentRealSpectrumComplete` | `NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.Limits.RealSpectrum` |
| `NumStability.Source.Higham.Chapter17.Equation08` | `NumStability.Source.Higham.Chapter17.Results.Equation08.GeometricSummability` |
| `NumStability.Source.Higham.Chapter17.Equation12` | `NumStability.Source.Higham.Chapter17.Results.Equation12.AttainedPartialSumBound` |
| `NumStability.Source.Higham.Chapter17.Equation15` | `NumStability.Source.Higham.Chapter17.Results.Equation15.UniformForwardBound` |
| `NumStability.Source.Higham.Chapter17.Equation16` | `NumStability.Source.Higham.Chapter17.Results.Equation16.JacobiForwardBound` |
| `NumStability.Source.Higham.Chapter17.Equation17` | `NumStability.Source.Higham.Chapter17.Results.Equation17.SORForwardBound` |
| `NumStability.Source.Higham.Chapter17.Equation20` | `NumStability.Source.Higham.Chapter17.Results.Equation20.ResidualSigmaEnvelope` |
| `NumStability.Algorithms.Ch15CondEstimators` | `NumStability.Algorithms.CondEstimation`, `NumStability.Algorithms.NormEstimation.OneNorm.LINPACK.Basic`, `NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.CondEstimators`, `NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.PowerBounds.CondEstimators`, `NumStability.Analysis.ConditionEstimatorLowerBound`, `NumStability.Analysis.MatrixAlgebra`, `NumStability.Source.Higham.Chapter15.Algorithm05.LINPACKConditionEstimator.Basic`, `NumStability.Source.Higham.Chapter15.Algorithm05.LINPACKConditionEstimator.InverseNormBound.TriangularSolve`, `NumStability.Source.Higham.Chapter15.Equation07.DixonBound.Basic` |
| `NumStability.Algorithms.Ch15DixonClosure` | `NumStability.Algorithms.Ch15CondEstimators`, `NumStability.Algorithms.Ch15DixonProbability`, `NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.DixonCompletion`, `NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.PowerBounds.DixonCompletion`, `NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Probability.DixonCompletion`, `NumStability.Algorithms.TestMatrices.Higham28OrthogonalCoordinates`, `NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic`, `NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic`, `NumStability.Source.Higham.Chapter15.Theorem06.Dixon.Basic` |
| `NumStability.Algorithms.Ch15DixonProbability` | `NumStability.Algorithms.Ch15CondEstimators`, `NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Probability.DixonProbability`, `NumStability.Algorithms.TestMatrices.Higham28OrthogonalCoordinates` |
| `NumStability.Algorithms.Chapter15CondEst` | `NumStability.Algorithms.CondEstimation`, `NumStability.Analysis.ConditionEstimatorLowerBound`, `NumStability.Analysis.MatrixAlgebra`, `NumStability.Source.Higham.Chapter15.Algorithm03.OneNormPowerMethod.Basic`, `NumStability.Source.Higham.Chapter15.Algorithm04.LAPACKNormEstimator.Basic`, `NumStability.Source.Higham.Chapter15.Algorithm04.LAPACKNormEstimator.ConditionEstimate.Bounds`, `NumStability.Source.Higham.Chapter15.Equation06.LAPACKCounterexample.Basic`, `NumStability.Source.Higham.Chapter15.Section01.ConditionNumbers.ConditionEstimators` |
| `NumStability.Algorithms.HighamChapter15BoydBridges` | `NumStability.Algorithms.HighamChapter15ConvergenceProse`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydInterface`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydInterface`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydInterface`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydInterface`, `NumStability.Algorithms.NormEstimation.PNorm.Convergence.BoydInterface`, `NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface`, `NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.BoydInterface`, `NumStability.Algorithms.NormEstimation.PNorm.Rectangular.BoydInterface`, `NumStability.Algorithms.PNormPowerMethodRect`, `NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.BoydInterface`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.BoydInterface`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.BoydInterface` |
| `NumStability.Algorithms.HighamChapter15BoydConcreteLemma3` | `NumStability.Algorithms.HighamChapter15BoydSourceLocal`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydConcrete`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydConcrete`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.SecondVariation.BoydConcrete`, `NumStability.Algorithms.NormEstimation.PNorm.Convergence.BoydConcrete`, `NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.BoydConcrete`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.BoydConcrete`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.BoydConcrete`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.ConstrainedLagrangian.Differentiation`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydConcrete` |
| `NumStability.Algorithms.HighamChapter15BoydLocalStability` | `NumStability.Algorithms.HighamChapter15BoydBridges`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydLocalStability`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.BoydLocalStability`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.BoydLocalStability` |
| `NumStability.Algorithms.HighamChapter15BoydRowwiseDomain` | `NumStability.Algorithms.HighamChapter15BoydSourceDomain`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.RowwiseDomain.Basic`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydRowwise`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydRowwise` |
| `NumStability.Algorithms.HighamChapter15BoydScalar` | `NumStability.Algorithms.HighamChapter15BoydUniqueness`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.ScalarCase.Iteration` |
| `NumStability.Algorithms.HighamChapter15BoydSourceClosure` | `NumStability.Algorithms.HighamChapter15BoydScalar`, `NumStability.Algorithms.HighamChapter15BoydSourceSecondDerivative`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydCompletion`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.StrongLocalMaximum.Convergence` |
| `NumStability.Algorithms.HighamChapter15BoydSourceDomain` | `NumStability.Algorithms.HighamChapter15BoydConcreteLemma3`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydDomain`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydDomain`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydDomain` |
| `NumStability.Algorithms.HighamChapter15BoydSourceLocal` | `NumStability.Algorithms.HighamChapter15BoydLocalStability`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydLocal`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydLocal`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydLocal`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydLocal`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydLocal`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.SecondVariation.BoydLocal`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.BoydLocal`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.BoydLocal`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydLocal` |
| `NumStability.Algorithms.HighamChapter15BoydSourceSecondDerivative` | `NumStability.Algorithms.HighamChapter15BoydRowwiseDomain`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.SecondDerivative.Rowwise` |
| `NumStability.Algorithms.HighamChapter15BoydUniqueness` | `NumStability.Algorithms.HighamChapter15BoydBridges`, `NumStability.Algorithms.NormEstimation.PNorm.Boyd.Uniqueness.Basic`, `NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydUniqueness`, `NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.BoydUniqueness`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.BoydUniqueness` |
| `NumStability.Algorithms.HighamChapter15ConvergenceProse` | `NumStability.Algorithms.NormEstimation.PNorm.Convergence.ConvergenceStatements`, `NumStability.Algorithms.NormEstimation.PNorm.Duality.ConvergenceStatements`, `NumStability.Algorithms.NormEstimation.PNorm.Endpoints.ConvergenceStatements`, `NumStability.Algorithms.PNormPowerMethodGeneralP`, `NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.ConvergenceStatements`, `NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.ConvergenceStatements`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.ConvergenceStatements`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.EndpointTermination.ConvergenceStatements`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.ConvergenceStatements` |
| `NumStability.Algorithms.HighamChapter15RectTermination` | `NumStability.Algorithms.HighamChapter15ConvergenceProse`, `NumStability.Algorithms.NormEstimation.PNorm.Rectangular.RectangularTermination`, `NumStability.Algorithms.PNormPowerMethodRect`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.EndpointTermination.InfinityCounterexample.Trace`, `NumStability.Source.Higham.Chapter15.Section02.Boyd.EndpointTermination.RectangularTermination` |
| `NumStability.Algorithms.LU.Higham15Problem15_4` | `NumStability.Algorithms.LU.GaussianElimination`, `NumStability.Analysis.MatrixAlgebra`, `NumStability.Source.Higham.Chapter15.Problem04.LUConditionBounds.Basic` |
| `NumStability.Algorithms.LU.Higham15Problem15_6` | `NumStability.Algorithms.LU.TridiagonalCondCh15IkebeClosure`, `NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.EntryFormulas`, `NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.TridiagonalInverse` |
| `NumStability.Algorithms.LU.Higham15Problem15_6Closure` | `NumStability.Algorithms.LU.Higham15Problem15_6`, `NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.FactorizationAndNorm`, `NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.TridiagonalInverseCompletion` |
| `NumStability.Algorithms.LU.Higham15Problem15_6Operational` | `NumStability.Algorithms.LU.Higham15Problem15_6Closure`, `NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.ArrayExecution`, `NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.TridiagonalInverseRuns` |
| `NumStability.Algorithms.LU.TridiagonalCondCh15` | `NumStability.Algorithms.LU.TridiagonalCond`, `NumStability.Source.Higham.Chapter15.Theorem07.TridiagonalLU.Basic`, `NumStability.Source.Higham.Chapter15.Theorem08.TridiagonalDiagonalDominance.Basic`, `NumStability.Source.Higham.Chapter15.Theorem09.Ikebe.Basic` |
| `NumStability.Algorithms.LU.TridiagonalCondCh15Closure` | `NumStability.Algorithms.LU.TridiagonalCondCh15`, `NumStability.Source.Higham.Chapter15.Section06.TridiagonalLUConditionBounds.ExactBounds` |
| `NumStability.Algorithms.LU.TridiagonalCondCh15IkebeClosure` | `NumStability.Algorithms.LU.TridiagonalCondCh15`, `NumStability.Source.Higham.Chapter15.Theorem09.Ikebe.IrreducibleRightInverse.RankOneStructure` |
| `NumStability.Algorithms.NormEstimation.PNorm.Endpoints.ConvergenceStatements` | `NumStability.Algorithms.LU.GrowthFactor`, `NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic`, `NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation`, `NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.PNormPowerMethod`, `NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Square`, `NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod`, `NumStability.Analysis.MatrixAlgebra`, `NumStability.Analysis.MatrixNorms.Lp`, `NumStability.Analysis.SingularValues.Realification` |
| `NumStability.Algorithms.NormEstimation.PNorm.Endpoints.PNormRectangular` | `NumStability.Algorithms.LU.GrowthFactor`, `NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation`, `NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.PNormPowerMethod`, `NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Rectangular`, `NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular`, `NumStability.Analysis.MatrixAlgebra`, `NumStability.Analysis.MatrixNorms.Lp`, `NumStability.Analysis.SingularValues.Realification` |
| `NumStability.Algorithms.PNormPowerMethod` | `NumStability.Algorithms.CondEstimation`, `NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.PNormPowerMethod`, `NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod`, `NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod`, `NumStability.Analysis.MatrixAlgebra`, `NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.PNormPowerMethod`, `NumStability.Source.Higham.Chapter15.Equation02.Subgradient.PNormPowerMethod`, `NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormPowerMethod`, `NumStability.Source.Higham.Chapter15.Equation04.NormalizedDualDiscrepancy.Basic`, `NumStability.Source.Higham.Chapter15.Equation05.SubgradientInequality.Basic`, `NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormPowerMethod` |
| `NumStability.Algorithms.PNormPowerMethodGeneralP` | `NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral`, `NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral`, `NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormGeneral`, `NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormGeneral`, `NumStability.Algorithms.PNormPowerMethod`, `NumStability.Analysis.MatrixNorms.Lp`, `NumStability.Analysis.SingularValues.Realification`, `NumStability.Source.Higham.Chapter15.Equation02.Subgradient.PNormGeneral`, `NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormGeneral` |
| `NumStability.Algorithms.PNormPowerMethodRect` | `NumStability.Algorithms.NormEstimation.PNorm.Endpoints.PNormRectangular`, `NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular`, `NumStability.Algorithms.PNormPowerMethodGeneralP`, `NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.PNormRectangular`, `NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormRectangular` |
## Removal rule

No forwarding module is removed in this migration. A future removal requires a
declared breaking release, release-note and migration-guide entries, a search
showing production consumers use canonical paths, and an explicit update to
the old-path smoke tests. Until then, CI compiles both curated entry points and
representative historical imports.
