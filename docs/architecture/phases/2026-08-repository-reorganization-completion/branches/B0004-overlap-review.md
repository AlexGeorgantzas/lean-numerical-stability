# B0004 / R12 activation and overlap review

Base checkpoint: `C0001` / `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`.
Clean C0001 format-2 graph: `55E0D29D626D746CB165DD7C874DA11A96B72602A66C1A6D8173F986178536C4`.

- Selector: `docs/architecture/phases/2026-08-repository-reorganization-completion/selectors/R12.tsv` / `2A45891E56E976DEAC01B791293D4DF05A4C1A045498D98B7D087B940582AD0F` (3 exact owner modules).
- Projection: `docs/architecture/phases/2026-08-repository-reorganization-completion/projections/P0004.tsv.gz` / `E84302EC06E0215758B91F9B179D89E0A5E17931CF42734828F1253BB4C129D2` (34 declarations; 80 signature edges; 133 body/proof edges; 139 union edges).
- Declaration routes: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0004-declaration-routes.tsv` / `2F82AF4D2A959CC55F48F1CA13D032C4C561F8A3385D2036B8C88AF5E0E7B84D` (34 total, every route public/source with its public name preserved).
- Module routes: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0004-module-routes.tsv` / `7A07B0F5D54F61027201CAABB4EE5120B595E5D01EC1F6FB98B7D7B3A6AE1944` (3 complete declaration-bearing umbrella routes).
- Private normalization: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0004-private-normalization.tsv` / `3266EAFAE1CD51DCBF459760E1D24DC5F88E2E29AA3E633D3B313DCF96CA368C` (exact header only because the projection selects no private declaration).
- Full-graph private reverse closure: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0004-private-closure.tsv` / `E013C92B4965455EF8C0B9D82007458E2E9C3496769FB3879091AF4CCDDB04AD` (exact header only; no selected or reverse-dependent private declaration).
- Test plan: `docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0004-test-plan.tsv` / `0F2662A60ED0286F41BF804D8D9E5B53D07BA44EAF8EF14802255444BA499088` (26 rows over 20 unique module targets: 6 canonical-only, 6 focused, 3 old-only, and 11 protected consumers).
- Official combined baseline: `docs/architecture/phases/2026-08-repository-reorganization-completion/baselines/C0001-combined.json` / `F6AD7BC1267CB73968D8933D1126DCE30AD2748E1B2EFD611C3D6509872243F2`.
- Exact C0001 inventory: `docs/architecture/phases/2026-08-repository-reorganization-completion/checkpoints/C0001-inventory.tsv` / `E07B4BA74EE62737B8B2AB8DDF8FA9E43C8614DFFDC26C5E69535A4E38F1F57F`.

The fresh graph-derived comparison with B0003/R11 is disjoint in both directions: owner overlap 0; declaration overlap 0; signature edge overlap 0; body/proof edge overlap 0; direct owner import edge 0; transitive owner reachability 0; shared direct production consumer overlap 0; and common direct project dependency overlap 0. B0004 owns 3 modules and 34 declarations. Its destination prefixes are casefold-vacant at C0001 and disjoint from immutable scope, shared paths, guarded infrastructure, and all five peer B0003/R11 destination prefixes.

The six exact destination leaves are:

- `NumStability.Source.Higham.Chapter13.Equation23.ProductBounds.PointRow`
- `NumStability.Source.Higham.Chapter13.Equation25.BackwardError.Bounds`
- `NumStability.Source.Higham.Chapter13.Equation25.PartitionedComputation.Implementation1`
- `NumStability.Source.Higham.Chapter13.Table01.BackwardErrorBounds.Endpoints`
- `NumStability.Source.Higham.Chapter13.Table01.DiagonalDominance.Bounds`
- `NumStability.Source.Higham.Chapter13.Table01.ProductTransfers.Families`


The reviewed declaration split is 3 declarations to Equation23 point-row product bounds; Equation25 splits 1 partitioned-computation endpoint and 2 backward-error endpoints; Table01 splits 5 product-transfer declarations, 8 backward-error/Implementation-1 declarations, and 15 diagonal-dominance declarations. Every source owner becomes a documented, declaration-free, complete import-only aggregate over all of its listed children.

The 11 direct protected consumers are frozen in the test plan. The B0004 shared request is limited to `NumStabilityTest.lean`, `docs/architecture/layout-exceptions.json`, and `docs/architecture/tiers.json`. Those are the only shared-request paths intersecting B0003/R11; both requests must be replayed from the same C0001 preimage and reconciled as a reviewed postimage union before integration. No worker may edit a shared path directly.

Lane assignment remains `claude-lane`, while execution is delegated to `codex-local` under the separately reviewed primary-human operator-authority expansion. This review makes no deferred routing, declaration-normalization, compatibility, private-closure, test, or overlap choice.
