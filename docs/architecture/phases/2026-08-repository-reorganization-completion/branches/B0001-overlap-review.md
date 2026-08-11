# B0001 / R01 activation and overlap review

Base checkpoint: `C0000` / `b1b18772d80185ec08f49c818919558645c330a1`.

- Selector: `docs/architecture/phases/2026-08-repository-reorganization-completion/selectors/R01.tsv` / `6D839B9008474CD9CBECEF5EE35FE347B91FD50541F8E347AA8648FF55EF81EB`.
- Projection: `docs/architecture/phases/2026-08-repository-reorganization-completion/projections/P0001.tsv.gz` / `DB8ACB22219D5C0C51E3F8F8D5296170FDF92C8C1166C0FDB2598EF6E11728D2`.
- Declaration routes: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0001-declaration-routes.tsv` / `1493383A571EFFDECCD2DF5D5C8DF2657139B2BA140D271B0706C86D32397A52`.
- Private normalization: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0001-private-normalization.tsv` / `0063E4B0E9C1DAD56F0CCD0A5B9D3897D6F18BEF860482AEB609B83DF6CD4F4A`; every private is decided `approved_before_activation` with no deferred worker choice.
- Full-graph private reverse closure: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0001-private-closure.tsv` / `CB19F5F3C66C56CE5F688E5E310D64713834635AFDFB77D7CB24DC1EC9D88598`.
- Test plan: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0001-test-plan.tsv` / `993AC1CCA7022009454622249E6D35A4E327AD1EBB8B55C45CD52F7E25E4EA6C`.
- Shared postimages: `docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0001-postimages.tsv` / `C19BCD0823E2A6279E54DEF210F37D11DBFB7C6D06A5507B74E851CFB97CDA5E`.
- Reviewed union: `docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0001-R0002-union-postimages.tsv` / `67AFB0F6FBADBB33B5755E9300972A7F4431EB22330F1366D1165EFBCC3FB163`.

Fresh ordered comparison in both directions (`R01` -> `R02` and `R02` -> `R01`): owner/destination equal-or-ancestor overlap 0; direct import edge 0; transitive import reachability 0; signature edge 0; body/proof edge 0. The common project dependency is exactly protected `NumStability.Analysis.MatrixAlgebra`. Both postimage requests use the same C0000 blobs and their reviewed union is hash-pinned.

Destination prefixes are exact, mutually disjoint, casefold-vacant at C0000, and disjoint from immutable scope, shared paths, forbidden paths, and the peer branch:

- `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Semiconvergence/`
- `NumStability/Analysis/LinearOperators/MatrixPowers/Semiconvergence/`
- `NumStability/Source/Higham/Chapter17/Results/`
- `NumStabilityTest/Reorganization/R01/`
- `docs/architecture/deliveries/R01/`

Full machine-derived facts: `docs/architecture/phases/2026-08-repository-reorganization-completion/reviews/R01-R02-overlap-facts.md` / `BF1EB1EC30D6FCE16336CF5638C824D52ACFB8A203CBBD22D1118FDE4CD88BA4`.
