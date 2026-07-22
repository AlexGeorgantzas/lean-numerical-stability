import NumStabilityTest.Import.All
import NumStabilityTest.Import.Core
import NumStabilityTest.Import.EndpointCanonical
import NumStabilityTest.Import.EndpointMigration
import NumStabilityTest.Import.Higham
import NumStabilityTest.Import.NonrandomRoundingCanonical
import NumStabilityTest.Import.NonrandomRoundingMigration
import NumStabilityTest.Import.PublicApi
import NumStabilityTest.Import.Root
import NumStabilityTest.Import.SourceCanonical
import NumStabilityTest.Import.SourceMigration
import NumStabilityTest.Import.SummationCanonical
import NumStabilityTest.Import.SummationMigration

/-!
# NumStability test suite

This is a separate Lake library so CI can compile compatibility and public-API
checks without adding tests to the production `NumStability` import surface.
-/
