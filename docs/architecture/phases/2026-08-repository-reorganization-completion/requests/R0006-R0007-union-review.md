# Reviewed R0006/R0007 union

R0006 (23 paths) and R0007 (49 paths) intersect on exactly five
integrator-owned paths: `NumStability/Algorithms.lean`,
`NumStabilityTest.lean`, `docs/architecture/COMPATIBILITY.md`,
`docs/architecture/layout-exceptions.json`, and
`docs/architecture/tiers.json`. There is no shared production consumer
path. Following the accepted R0003/R0004 precedent, the union postimages
for the shared paths are generated directly from the same exact-C0003
preimages with both waves' retargets, additions, and classification rows
applied together; sequential whole-file request replacement is not used.

`R0006-R0007-union.patch` (67 paths, zero-context, `--unidiff-zero`) is
the reviewed union the integrator applies exactly once after both true
delivery merges. `R0006-R0007-union-postimages.tsv` records the exact
C0003 preimage blob ids and preimage/postimage SHA-256 for all 67 paths.
Freeze-time replay: the union patch applies cleanly to the exact-C0003
tree in a disposable index and every postimage hash verifies (67/67), as
do R0006 (23/23) and R0007 (49/49) individually.
