# R0007 integration-overlap evidence

Base checkpoint: C0006 / `a32095e6e50189f7dcc39312bb4c6a36f421fab5`.

R0007 was applied and validated independently in a disposable C0006 Git index.
Its eight sorted patch paths exactly match the request record. The null-preimage
W04 test root is import-and-docstring-only. Existing aggregate and consumer
changes are import-only; after removing import commands, the C0006 and
integrated consumer texts are identical. Blob OIDs are Git SHA-1 object IDs.

| Path | C0006 preimage | Integrated postimage | Class |
| --- | --- | --- | --- |
| `NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean` | `d2ab6d9ea8689c3fd9fd0e2b134856e9484c149a` | `227d2fe497fac8bb191785335a4151f4502a1da8` | R0007/R0009 shared consumer, import-only |
| `NumStability/Analysis/Perturbation/LeastSquares/Wedin.lean` | `2de2b7c45408370eefcc703e4bf0c9d40d4e255b` | `743dccdc11fb6fb828f7a8e6d15db5b89e3e8d6e` | accepted consumer, import-only |
| `NumStabilityTest/Reorganization/W04.lean` | `null` | `a06a7e8c1e7566c6785974af4d9f15cd4d14b953` | import-only test aggregate |

The combined Equality postimage applies both independently C0006-based import
replacements atomically. R0007 intersects R0008 only at `NumStabilityTest.lean`,
`docs/architecture/layout-exceptions.json`, and `docs/architecture/tiers.json`.
It intersects R0009 at those three paths plus the Equality consumer. The final
tree contains the reviewed union; the independent patches were never applied
sequentially over stale shared preimages.

The historical Chapter 21 row-wise-backward-error consumer remains unchanged,
as required by W04's retained private closure.
