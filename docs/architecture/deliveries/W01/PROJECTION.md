# W01 projection result — P0001

Run from the worker worktree with the checker at the exact artifact hash `P0001.json`
pins (`29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443`), against
`P0001.tsv.gz` verified at its pinned digest before use. The candidate came from the
locked full extraction documented in `projections/README.md`, run while holding
`Local\lean-reorganization-2026-08`.

```text
python tools/architecture/check_phase_projection.py \
  --projection   <P0001.tsv.gz> \
  --projection-sha256 6278CE1673465F9069A01A9D7FF5005223209E28533BC0F13DB4B90E82042352 \
  --candidate    benchmark-results/W01-candidate.tsv \
  --allow-module NumStability.Analysis.CancellationOfRoundingErrors \
  --allow-module NumStability.Analysis.FloatingPointArithmetic \
  --allow-module NumStability.Analysis.IncreasingPrecision \
  --allow-module NumStability.Analysis.InstabilityWithoutCancellation \
  --allow-prefix NumStability.Analysis.FloatingPointArithmetic. \
  --allow-prefix NumStability.Source.Higham.Chapter01.FloatingPointArithmetic. \
  --allow-prefix NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.
```

```text
phase projection contract passed
projection_sha256: 6278CE1673465F9069A01A9D7FF5005223209E28533BC0F13DB4B90E82042352
candidate_sha256: 357DC24430A8D9592D7A948C6B3568B88CC968E9D096FA0FA58F1340C131C4DA
selected_declarations: 3697
relocated_declarations: 3396
signature_edges: 22706
body_edges: 45433
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 4
allowed_prefixes: 3
exit 0
```

## What this proves

| Requirement | Evidence |
| --- | --- |
| All 3,697 selected declarations preserved | `selected_declarations: 3697`, no `missing declaration` |
| All 48,076 incident union edges preserved | the checker compares the kind-tagged incident edge set: 22,706 signature + 45,433 body = 68,139 entries, which is 48,076 distinct source→target pairs once the 20,063 pairs carrying both a signature and a body edge are counted once. Both figures match `P0001.json`'s `expected_counts` (`signature_edges` 22706, `body_edges` 45433, `union_edges` 48076) |
| No kind drift | no `kind drift` diagnostics |
| No visibility drift | no `visibility drift` diagnostics |
| Every owner within the allowed set | no `owner not allowed` diagnostics |
| Declarations actually moved | `relocated_declarations: 3396` of 3,697 |

The comparison is an exact set equality on incident edges, not a count: `compare_graphs`
reports every edge present in one graph and absent from the other. Passing therefore
means the frozen graph and the candidate agree edge for edge.

## The one attempt that failed, and why it matters

An earlier candidate failed with **357 mismatches**, every one a missing body edge
from a `_private.NumStability.Analysis.IncreasingPrecision.0.…` declaration.

Lean mangles a private declaration to `_private.<defining module>.<n>.<name>`.
Relocating one therefore renames it: the projection expects
`_private.NumStability.Analysis.IncreasingPrecision.0.foo` while the moved declaration
reports as
`_private.NumStability.Source.Higham.Chapter01.FloatingPointArithmetic.IncreasingPrecision.0.foo`.
The checker compares names exactly, so all 21 relocated privates took every incident
edge with them.

Nothing upstream could have caught this. At that moment the full build passed 4,996
jobs, all 18 isolated tests compiled, all three architecture checkers passed, and the
lane's own structural verifier reported 3,523 spans byte-identical with zero import
cycles. The Lean code was correct; the frozen *graph identity* was not.

**Rule for later waves: a private declaration cannot change module.** W01 keeps all 21
in place, together with the declarations that use them — 301 of 3,697 retained, and
3,396 relocated.
