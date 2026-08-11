# B0002 / R02 activation and overlap review

Base checkpoint: `C0000` / `b1b18772d80185ec08f49c818919558645c330a1`.

- Selector: `docs/architecture/phases/2026-08-repository-reorganization-completion/selectors/R02.tsv` / `FE6BAD5F307EB44A12D410A977118ACF389002F243B68B2A0575139C3BB35069`.
- Projection: `docs/architecture/phases/2026-08-repository-reorganization-completion/projections/P0002.tsv.gz` / `283E6773D06E2CBE591115BC1EEE388735CDC55BB1D2F4280917078D014EE5BE`.
- Declaration routes: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0002-declaration-routes.tsv` / `AD7660C76C44A92B1995D652F2925716A64072FBDB26088EC1CCB8D74BBE67C5`.
- Private normalization: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0002-private-normalization.tsv` / `F4E9853B58DA54FBBB1D00340983F796D510DDED3A1ACA79409A62F2D11B66CC`; every private is decided `approved_before_activation` with no deferred worker choice.
- Full-graph private reverse closure: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0002-private-closure.tsv` / `9184F3C8529CAEF816BCA1421B1FA7AD34C80A272C89EE38C4787F1E974376BF`.
- Test plan: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0002-test-plan.tsv` / `530B2428222FE8CB786B059EFC5FA008841077167FE7D3E936E574997B39462A`.
- Shared postimages: `docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0002-postimages.tsv` / `3C2E64B3421D23BBF99749E4637D83F97794A18020E67700548A54754FE3FF6E`.
- Reviewed union: `docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0001-R0002-union-postimages.tsv` / `67AFB0F6FBADBB33B5755E9300972A7F4431EB22330F1366D1165EFBCC3FB163`.

Fresh ordered comparison in both directions (`R02` -> `R01` and `R01` -> `R02`): owner/destination equal-or-ancestor overlap 0; direct import edge 0; transitive import reachability 0; signature edge 0; body/proof edge 0. The common project dependency is exactly protected `NumStability.Analysis.MatrixAlgebra`. Both postimage requests use the same C0000 blobs and their reviewed union is hash-pinned.

Destination prefixes are exact, mutually disjoint, casefold-vacant at C0000, and disjoint from immutable scope, shared paths, forbidden paths, and the peer branch:

- `NumStability/Algorithms/NormEstimation/PNorm/OneAndInfinityNorms/`
- `NumStability/Source/Higham/Chapter15/Algorithm04/LAPACKNormEstimator/ConditionEstimate/`
- `NumStability/Source/Higham/Chapter15/Algorithm05/LINPACKConditionEstimator/InverseNormBound/`
- `NumStability/Source/Higham/Chapter15/Problem06/TridiagonalInverseNorm/Recurrences/`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/InfinityCounterexample/`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/GlobalConvergence/ScalarCase/`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/LocalConvergence/ConstrainedLagrangian/`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/SourceDomain/SecondDerivative/`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/SourceDomain/StrongLocalMaximum/`
- `NumStability/Source/Higham/Chapter15/Section06/TridiagonalLUConditionBounds/`
- `NumStability/Source/Higham/Chapter15/Theorem09/Ikebe/IrreducibleRightInverse/`
- `NumStabilityTest/Reorganization/R02/`
- `docs/architecture/deliveries/R02/`

Full machine-derived facts: `docs/architecture/phases/2026-08-repository-reorganization-completion/reviews/R01-R02-overlap-facts.md` / `BF1EB1EC30D6FCE16336CF5638C824D52ACFB8A203CBBD22D1118FDE4CD88BA4`.
