# B0003 C0001 activation and joint R11/R12 overlap review

Branch base: `C0001` code at `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`.

This primary-human review is pinned to C0001 inventory SHA-256 `E07B4BA74EE62737B8B2AB8DDF8FA9E43C8614DFFDC26C5E69535A4E38F1F57F`, combined-baseline SHA-256 `F6AD7BC1267CB73968D8933D1126DCE30AD2748E1B2EFD611C3D6509872243F2`, raw format-2 graph SHA-256 `55E0D29D626D746CB165DD7C874DA11A96B72602A66C1A6D8173F986178536C4`, and projection-checker SHA-256 `0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220`. The 65-owner R11 selector has SHA-256 `461D1A0E09A0EADD02B57F3FEB6E097508D02F769A13A11E1CF6896B289A3F23`. P0003 has deterministic gzip SHA-256 `31EC591D949DB6041078C036F0CFF74A0A3EE229B35E351DDF999D15F494D60E` and raw payload SHA-256 `26469E530A4BC43B96D88665E4EAAB0D89AB2F3B624CA592CE4ACCC9FD1F04E3`; it freezes 1,477 declarations, 15,172 signature edges, 18,056 body/proof edges, and 19,873 union edges. The declaration routes have SHA-256 `2454049E9B044E97730D16392B641F7E4850F84BB8508C50EFB38DD28390C5C1` and the module routes have SHA-256 `4F6FE07CFE955B9096156949C44CF2D2829E0AD73D9157CD958EB66F3C7D6CA3`.

## Exact C0001 owners and reviewed destinations

The selector is exactly the 65 C0001 inventory rows assigned to `R11`: 59 declaration-free `NumStability.Algorithms.QR.*` compatibility wrappers, three declaration-bearing `NumStability.Algorithms.LinearSystems.QR.*Support` owners, and the Chapter 19 `Core`, `Sensitivity`, and `StoredLoop` owners. Every selector blob is the exact C0001 inventory blob. The authorized destinations are exactly:

- `NumStability/Algorithms/LinearSystems/QR/Householder/`
- `NumStability/Source/Higham/Chapter19/Sensitivity/Bounds/`
- `NumStability/Source/Higham/Chapter19/StoredLoop/Perturbation/`
- `NumStabilityTest/Reorganization/R11/`
- `docs/architecture/deliveries/R11/`

All three production prefixes are trailing-slash, casefold-vacant at `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`, mutually equal/ancestor-disjoint, and disjoint from the eight R12 destination prefixes. No broader QR or Chapter 19 root is authorized.

## Declaration routing, retention, and private closure

The reviewed route is a whole-owner block contract: 112 declarations from `HouseholderSpecSupport` move to `NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels`; 101 from `HouseholderApplySupport` move to `NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication`; 132 from `HouseholderQRSupport` move to `NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR`; 59 from `Chapter19.Sensitivity` move to `NumStability.Source.Higham.Chapter19.Sensitivity.Bounds.Results`; and 8 from `Chapter19.StoredLoop` move to `NumStability.Source.Higham.Chapter19.StoredLoop.Perturbation.Bridge`. The 1,065 declarations in `Chapter19.Core` remain in that exact owner as a reviewed source outlier. The 59 compatibility wrappers receive module documentation and retain their exact imports except the three `Algorithms.QR.Householder*Support` wrappers, whose single support import retargets to the corresponding reviewed destination.

The exact private normalization map has 17 rows and SHA-256 `12E4D4F517D3678DABA4A11F57D36E22EE4428BC3598D3CA0FC7E41A9323E70E`: 16 private names receive only the destination owner-prefix rewrite and the one `Chapter19.Core` private name is an exact identity. The full typed reverse-dependent closure from those 17 seeds has 954 declarations and SHA-256 `74FA741BC9C9CCF802ED9999D64DB81E40F4D027A25351CAFF78F67196822145`: 937 public dependents plus 17 private seeds, with 280 declarations in selected owners and 674 in protected non-owned owners. Generated constructor/recursor commands and any additional compiler closure stay indivisible. Public names, declaration kinds, visibility, signatures, proof/bodies, and typed incident edges are frozen.

Reusable destinations may not directly or transitively import `NumStability.Source` or a historical compatibility facade. Source destinations may depend on reusable leaves. Old public imports remain through documented import-only wrappers; the retained Core outlier preserves its exact declarations and imports.

## Protected consumers and tests

The test plan has 204 sorted rows over 199 distinct module targets: five canonical-only payload leaves, the same five focused targets, all 65 old-only owners, and 129 exact protected production consumers that directly import one or more of the five moving owners. R11 owners and the integrator-owned `NumStability.Source.Higham.Chapter19` aggregate are excluded from the 129. `NumStability.Analysis.MatrixAlgebra`, all C0001 non-owner production paths, `.github/`, `NumStabilityTest/Import/`, `NumStabilityTest/Worker/`, `benchmark-results/`, `docs/architecture/phases/`, and `tools/architecture/` are forbidden to the worker.

## R11/R12 disjointness and reviewed union

The fresh C0001 graph proves the following ordered comparisons in both directions, R11 -> R12 and R12 -> R11:

- zero owned-path overlap and zero declaration-name overlap;
- zero equal or ancestor/descendant destination overlap;
- zero direct owner imports in either direction;
- zero transitive owner reachability in either direction;
- zero signature edges in either direction;
- zero body/proof edges in either direction;
- zero shared direct production consumers; and
- zero common direct project dependencies.

R11 has 65 owners, 1,477 declarations, 15,172 signature edges, 18,056 body/proof edges, and 19,873 union edges. R12 has 3 owners, 34 declarations, 80 signature edges, 133 body/proof edges, and 139 union edges. Their worker-owned and destination path sets are disjoint.

The independently generated C0001 shared-file requests overlap only on the three integrator-owned paths `NumStabilityTest.lean`, `docs/architecture/tiers.json`, and `docs/architecture/layout-exceptions.json`; R11 additionally requests `COMPATIBILITY.md` and 129 exact production consumer postimages. Workers may not edit any shared path. R0003 and R0004 must each replay from the same `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771` preimage, and the primary-human must apply one reviewed union rather than sequential whole-file replacement.

No migration starts from the planned-control commit. The worker ref must be created at the exact C0001 code SHA `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771` only after planned-control CI is green, and work starts only after the separate active-control commit is green.
