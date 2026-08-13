import NumStability.Source.Higham.Chapter19.Sensitivity.Bounds.Results

/-!
# R11 focused test — `Results`

Exercises the frozen B0003 declaration route into `NumStability.Source.Higham.Chapter19.Sensitivity.Bounds.Results`
(57 public declarations) and its private-normalized closure
(2 approved private rows).

The private check constructs each mangled `Lean.Name` explicitly, including
the numeric private component via `Name.num`, and requires the P0003
post-delivery name to be present AND the pre-delivery name to be absent.
Requiring the absence is what makes this a normalization test rather than
an existence test.

-/

private def appendNameParts (baseName : Lean.Name) (parts : List String) : Lean.Name :=
  parts.foldl (fun name part => .str name part) baseName

private def mangledPrivateName (moduleName declarationName : String)
    (ordinal : Nat) : Lean.Name :=
  let modulePrefix := appendNameParts .anonymous ("_private" :: moduleName.splitOn ".")
  appendNameParts (.num modulePrefix ordinal) (declarationName.splitOn ".")

/-- The exact P0003-approved post-delivery private names for this destination. -/
private def approvedPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Source.Higham.Chapter19.Sensitivity.Bounds.Results" "NumStability.H19Sensitivity.rectMatMul_mono_left" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter19.Sensitivity.Bounds.Results" "NumStability.H19Sensitivity.rectMatMul_mono_right" 0
]

/-- The pre-delivery names the same rows retire; none may survive. -/
private def retiredPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Source.Higham.Chapter19.Sensitivity" "NumStability.H19Sensitivity.rectMatMul_mono_left" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter19.Sensitivity" "NumStability.H19Sensitivity.rectMatMul_mono_right" 0
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "R11 private normalization: missing approved name {name}"
  for name in retiredPrivateNames do
    if Lean.Environment.contains environment name then
      throwError "R11 private normalization: retired name {name} still present"

#check @NumStability.H19Sensitivity.EconomyQR
#check @NumStability.H19Sensitivity.EconomyQR.casesOn
#check @NumStability.H19Sensitivity.EconomyQR.diagonal_nonnegative
#check @NumStability.H19Sensitivity.EconomyQR.factorization
#check @NumStability.H19Sensitivity.EconomyQR.mk
#check @NumStability.H19Sensitivity.EconomyQR.orthonormal
#check @NumStability.H19Sensitivity.EconomyQR.rec
#check @NumStability.H19Sensitivity.EconomyQR.recOn
#check @NumStability.H19Sensitivity.EconomyQR.upper
#check @NumStability.H19Sensitivity.StewartLocalSensitivity
#check @NumStability.H19Sensitivity.StewartLocalSensitivitySource
#check @NumStability.H19Sensitivity.ZhaColumnwiseSensitivity
#check @NumStability.H19Sensitivity.ZhaWeightedPerturbation
#check @NumStability.H19Sensitivity.add
#check @NumStability.H19Sensitivity.deltaR_eq_scaledRVariation_mul
#check @NumStability.H19Sensitivity.deltaR_frobNormRect_le_scaledRVariation_mul_frobNormRect
#check @NumStability.H19Sensitivity.deltaR_rectOpNorm2_le_scaledRVariation_mul_rectOpNorm2
#check @NumStability.H19Sensitivity.diff
#check @NumStability.H19Sensitivity.diff_decompose
#check @NumStability.H19Sensitivity.economyQRPseudoinverse
#check @NumStability.H19Sensitivity.economyQR_abs_le_abs_factors
#check @NumStability.H19Sensitivity.economyQR_deltaR_upper
#check @NumStability.H19Sensitivity.economyQR_factorVariation_frob_le_forcing_add_scaledR
#check @NumStability.H19Sensitivity.economyQR_normalized_perturbation_factorization
#check @NumStability.H19Sensitivity.economyQR_perturbation_identity
#check @NumStability.H19Sensitivity.economyQR_perturbation_right_inverse_identity
#check @NumStability.H19Sensitivity.economyQR_projectedQVariation_skew_defect
#check @NumStability.H19Sensitivity.economyQR_projected_perturbation_identity
#check @NumStability.H19Sensitivity.economyQR_pseudoinverse_left_inverse
#check @NumStability.H19Sensitivity.economyQR_pseudoinverse_penrose_equations
#check @NumStability.H19Sensitivity.economyQR_pseudoinverse_range_projection_symmetric
#check @NumStability.H19Sensitivity.economyQR_pseudoinverse_rectOpNorm2_eq
#check @NumStability.H19Sensitivity.economyQR_scaledRVariation_frob_quadratic_majorant
#check @NumStability.H19Sensitivity.economyQR_scaledRVariation_gram_identity
#check @NumStability.H19Sensitivity.economyQR_scaledRVariation_upper
#check @NumStability.H19Sensitivity.economyQR_upper_skew_entry_split
#check @NumStability.H19Sensitivity.frobNormRect_eq_sqrt_nat_of_orthonormal
#check @NumStability.H19Sensitivity.frobNormSqRect_eq_nat_of_orthonormal
#check @NumStability.H19Sensitivity.higham19_eq19_37_absorbed
#check @NumStability.H19Sensitivity.higham19_eq19_37_of_zha_and_formedQ
#check @NumStability.H19Sensitivity.normalizedGramForcing
#check @NumStability.H19Sensitivity.projectedForcing
#check @NumStability.H19Sensitivity.projectedQVariation
#check @NumStability.H19Sensitivity.rectOpNorm2_le_of_rectOpNorm2Le
#check @NumStability.H19Sensitivity.scaledRVariation
#check @NumStability.H19Sensitivity.stewart_forcing_frobNormRect_le
#check @NumStability.H19Sensitivity.stewart_projectedForcing_frobNormRect_le
#check @NumStability.H19Sensitivity.stewart_projectedForcing_relative_le
#check @NumStability.H19Sensitivity.upper_inverse_of_isInverse
#check @NumStability.H19Sensitivity.upper_rectMatMul_of_upper
#check @NumStability.H19Sensitivity.zhaConditionMatrix
#check @NumStability.H19Sensitivity.zhaWeightedPerturbation_mul_right_inverse_abs_le
#check @NumStability.H19Sensitivity.zha_forcing_frobNormRect_le_of_source
#check @NumStability.H19Sensitivity.zha_forcing_rectOpNorm2Le
#check @NumStability.H19Sensitivity.zha_forcing_rectOpNorm2_le_of_source
#check @NumStability.H19Sensitivity.zha_projectedForcing_rectOpNorm2Le
#check @NumStability.H19Sensitivity.zha_projectedForcing_rectOpNorm2_le_of_source
