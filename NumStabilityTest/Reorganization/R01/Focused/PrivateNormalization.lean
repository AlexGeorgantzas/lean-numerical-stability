import NumStability.Source.Higham.Chapter17.Results.Equation20.DiagonalizableBounds
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.Projectors.FixedRange
import NumStability.Source.Higham.Chapter17.Results.Equation29.SingularBounds
import NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.TriangularBlockForm

/-!
# R01 approved private normalization

Checks exactly the ten authority-approved destination-private names in the
environment and representative public reverse dependents that exercise them.
-/

private def appendNameParts (baseName : Lean.Name) (parts : List String) : Lean.Name :=
  parts.foldl (fun name part => .str name part) baseName

private def approvedPrivateName (moduleName declarationName : String) : Lean.Name :=
  let modulePrefix := appendNameParts .anonymous ("_private" :: moduleName.splitOn ".")
  appendNameParts (.num modulePrefix 0) (declarationName.splitOn ".")

private def approvedPrivateNames : List Lean.Name := [
  approvedPrivateName "NumStability.Source.Higham.Chapter17.Results.Equation20.DiagonalizableBounds" "NumStability.geom_partial_sum_le",
  approvedPrivateName "NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.Projectors.FixedRange" "NumStability.matMul_matSub_id_left",
  approvedPrivateName "NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.Projectors.FixedRange" "NumStability.matMul_matSub_id_matSub_id",
  approvedPrivateName "NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.Projectors.FixedRange" "NumStability.matMul_matSub_id_right",
  approvedPrivateName "NumStability.Source.Higham.Chapter17.Results.Equation20.DiagonalizableBounds" "NumStability.residualSigmaTsum_entry_le_of_real_diagonalization",
  approvedPrivateName "NumStability.Source.Higham.Chapter17.Results.Equation20.DiagonalizableBounds" "NumStability.residual_geometric_partial_le_ratio",
  approvedPrivateName "NumStability.Source.Higham.Chapter17.Results.Equation20.DiagonalizableBounds" "NumStability.residual_term_entry_abs_le_of_real_diagonalization",
  approvedPrivateName "NumStability.Source.Higham.Chapter17.Results.Equation29.SingularBounds" "NumStability.singularErrorSourceTerm_term_eq",
  approvedPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.TriangularBlockForm" "NumStability.commute_self_sub_one",
  approvedPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.TriangularBlockForm" "NumStability.pow_apply_sub_one_pow"
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "missing authority-approved private declaration {name}"

#check NumStability.residualSigmaTsum_le_diagonalizable_bound
#check NumStability.stationaryDrazinFixedProjector_fixed_by_G
#check NumStability.stationaryDrazinFixedProjector_idempotent
#check NumStability.stationaryDrazinRangeProjector_commutes_with_G
#check NumStability.finiteResidualSigma_le_diagonalizable_bound
#check NumStability.residualSigmaTsum_le_diagonalizable_max_bound_direct
#check NumStability.sigma_bound
#check NumStability.singularErrorSourceTerm_norm_bound
#check NumStability.eigenvector_one_of_maxGen_of_orbit_tendsto
#check NumStability.maxGenEigenspace_one_eq_eigenspace_of_forall_orbit_tendsto
