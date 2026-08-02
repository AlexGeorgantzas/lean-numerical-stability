# C0002 acceptance evidence

Checkpoint commit: `e6ef0107edb873f7a05ad8282df7efdf41a986d3`

Accepted at: `2026-08-02T10:09:54Z`

## Remote gate

[GitHub Lean CI run 30738933048](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/30738933048) completed successfully at the exact checkpoint commit. The architecture/contract source-graph step and `lake build NumStability NumStabilityTest` both passed. The job ran from `2026-08-02T08:01:01Z` to `2026-08-02T09:19:07Z`.

## Local gates

The exact checkpoint tree passed the phase self-tests and live contract, layout, compatibility, provenance, strict source graph, focused W01 build, and `lake test`. The focused build covered 20 W01 old-only/canonical-only tests plus affected reusable and source consumers.

The fresh combined extractor completed `lake build NumStability` and generated a clean format-2 graph at commit `e6ef0107edb873f7a05ad8282df7efdf41a986d3`: 56,903 declarations in 992 declaration-bearing modules, 266,387 signature edges, 382,872 body/proof edges, and 424,082 union edges. The source graph covers all 1,406 production modules and retains zero forbidden reusable reachability.

## W01 projection and scope

The frozen P0001 graph replay passed against the fresh full stream: 3,697 declarations, 22,706 signature edges, 45,433 body/proof edges, and 48,076 union edges. Exactly 3,396 declarations moved to allowed canonical owners; names, kinds, visibility, and every incident typed edge were preserved.

The delivered commit `d30fecc70a1d2066e2d147b79d9e6b9d743a21e5` is an ancestor of the checkpoint. Its corrected report and exact 40-path scope evidence are hash-pinned by B0001. No formal shared-path request was applicable: the valid prose requests touched future W02/W12-owned modules and were handled by the integrator without misclassifying them as globally shared paths.

## Next-wave refresh

W02 and W12 selectors contain exactly 73 and 42 immutable owners. Their 67 and 65 destination roots are unique, sorted, vacant, outside shared/current paths, and mutually disjoint across 4,355 comparisons. Both branches start from C0002; W02 must be integrated first, followed by the recorded 17-edge W12 integration delta and the other integrator-only compatibility closures.
