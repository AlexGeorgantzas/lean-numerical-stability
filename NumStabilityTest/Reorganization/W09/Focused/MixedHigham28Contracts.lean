import NumStability.Analysis.TestMatrices.Cauchy.Contracts
import NumStability.Analysis.TestMatrices.Companion.Contracts
import NumStability.Analysis.TestMatrices.Pascal.Contracts
import NumStability.Analysis.TestMatrices.Toeplitz.Contracts

/-!
# Higham28Contracts: the mandated split, all sides at once

B0009 forbids classifying `Higham28Contracts` wholesale. Its split is across
4 reusable destinations rather than across the two
tiers: every declaration here belongs to the printed chapter, and the
split separates the printed loci. Importing exactly those destinations
means a declaration routed to the wrong locus fails to resolve here.
-/
#check @NumStability.cauchyLower
#check @NumStability.cauchyUpper
#check @NumStability.IsLeftCyclicFor
#check @NumStability.pascalLastBasis
#check @NumStability.CauchyAdmissible
#check @NumStability.cauchyLowerEntry
