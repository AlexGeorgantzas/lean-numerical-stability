import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.HashCollisionProbabilities
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.SketchInjectivityBounds
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.SketchedGramLoewnerCovers
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.SketchedGramMoments
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.UniformRowEmbedding
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.GramDotFloatingPoint
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.GramMoments
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm01.ElementwiseSampling.HitPairEvents
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.SparsePreconditionedEmbeddings
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.SparsePreconditionedGramBounds
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.SparsePreconditionedGramGrids
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation02.SpectralApproximation.ResidualMomentBounds
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation02.SpectralApproximation.SpectralEventEndpoints
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation05.GramApproximation.SampledGramEndpoints
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.SampledGramOperatorNorm
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation08.LeastSquaresSketch.FloatingPointObjectiveBounds
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation08.LeastSquaresSketch.SketchedObjectiveBounds

/-!
# R10 private normalization (exhaustive)

Requires every approved destination-private name to be present and every historical private name to be absent.
-/

private def appendNameParts (baseName : Lean.Name) (parts : List String) : Lean.Name :=
  parts.foldl (fun name part => .str name part) baseName

private def mangledPrivateName (moduleName declarationName : String)
    (ordinal : Nat) : Lean.Name :=
  let modulePrefix := appendNameParts .anonymous ("_private" :: moduleName.splitOn ".")
  appendNameParts (.num modulePrefix ordinal) (declarationName.splitOn ".")

private def approvedPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.GramMoments" "NumStability.uniformRowTraceProbMass_two_point_factor" 0,
  mangledPrivateName "NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm01.ElementwiseSampling.HitPairEvents" "NumStability.sqMagTraceProbMass_two_point_factor" 0,
  mangledPrivateName "NumStability.Source.DrineasMahoney.RandNLA2016.Equation05.GramApproximation.SampledGramEndpoints" "NumStability.rowSqNormTraceProbMass_two_point_factor" 0,
]

private def retiredPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Algorithms.RandNLA.HitCountConcentration" "NumStability.sqMagTraceProbMass_two_point_factor" 0,
  mangledPrivateName "NumStability.Algorithms.RandNLA.RowSamplingGram" "NumStability.rowSqNormTraceProbMass_two_point_factor" 0,
  mangledPrivateName "NumStability.Algorithms.RandNLA.UniformRowSampling" "NumStability.uniformRowTraceProbMass_two_point_factor" 0,
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "R10 private normalization: missing approved name {name}"
  for name in retiredPrivateNames do
    if Lean.Environment.contains environment name then
      throwError "R10 private normalization: retired name {name} still present"
