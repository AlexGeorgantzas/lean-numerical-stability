# C0007 acceptance evidence

Checkpoint code commit: `4e26820d1f4989ec4ec77b7113085f593570e11b`

Acceptance status: **accepted** by `primary-human` at `2026-08-25T01:15:00Z`.

This report records the primary-human acceptance of checkpoint C0007 for the
integrated R09 test-matrices and R10 randomized-linear-algebra epoch at exact
code commit `4e26820d1f4989ec4ec77b7113085f593570e11b` on `main`. It accepts
milestones M09 and M10, applies shared requests R0012 and R0013 as the reviewed
25-path common-base union, retires baseline projections P0011 and P0012, and
moves branches B0011 and B0012 to `accepted` with retirement due. Branch
retirement, remote-ref deletion, and worker-worktree removal remain a later
separate control; the exact acceptance-control commit SHA and its CI run are
intentionally deferred to that separate control's hash-pinned attestation
record.

This checkpoint closes the phase's classification queue: it is the first
checkpoint at which every production module is classified.

## Exact green code runs

The integrated code was proved by
[GitHub Lean CI run 32788870454 (job 97626304846)](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/32788870454),
which completed successfully for integration control
`09512c1b15fd4f6892a313341b1edc8c02bb913d` on `main`, and the checkpoint code
commit itself passed
[GitHub Lean CI run 32794282084](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/32794282084)
(success for exact `4e26820d1f4989ec4ec77b7113085f593570e11b`). Both runs are
recorded in the hash-pinned attestation record
`reviews/R09-R10-integration-control-ci.json` and the acceptance-control
attestation to follow.

## Delivery ancestry

Two immutable deliveries share the exact C0006 code commit
`fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5` as sole parent: R09
`3de7b02333d7415664f440ceb6ad7ea899f32f57` (240 paths) and R10
`6be9f1100557c78f7187da99b269eb3767befba0` (80 paths). Neither delivery
contains a shared-request path, so each was preserved by a true merge with no
conflict: R09 at `0089a00082653b6fe0d393003432d0d2a1b7574d` over sidecar
correction `ac2253a514ee2ad25c763f1ee5a6365061f42146`, then R10 at
`fc36ec2a48f276d9c7f0915a3749619ea41627c5`. The reviewed R0012/R0013 union was
applied by the integrator at
`09512c1b15fd4f6892a313341b1edc8c02bb913d` and refreshed at the checkpoint code
commit. The integration ledger below records the exact 38-path
merge-to-checkpoint range.

## Generated evidence

| Artifact | SHA-256 |
| --- | --- |
| `C0007-combined.json` | `EA85C78A41E23A89B428747FB00519184AA557A183E56A659AA8248DB135A932` |
| `C0007-combined.md` | `BDBE0418E6A8F56F4EEE7EDC578252070DE268A329B1525EAE5977A675AD2B5B` |
| raw `benchmark-results/C0007-combined.tsv` | `F12CFF3CF3675077EE1AEB4A2136BAB22E3698E2BB811AA51FACDA231DE99C9E` |
| `C0007-inventory.tsv` | `D6E9473C9A082A5A00150BCBADB54195164B698B3197A2706AC1C440D90E5A48` |
| `C0007-integrator-paths.tsv` | `F308A6EE658D61A535A39C1B25049FC3FDABE81B639167226150A9BF729A75E4` |

The baseline records 2,927 production modules: 2,927 classified, 0
unclassified, and 0 mixed, with 0 noncanonical names, one declaration-bearing
umbrella, zero missing module docstrings, and zero unsorted aggregate imports.
Tier separation is complete with zero reusable-to-source and zero
reusable-to-mixed reachable pairs against 23 reusable entrypoints. The
inventory has 2,927 unique sorted rows: 2,915 already complete and 12 still in
scope, with exactly 1 debt row. The remaining queue is exactly I01=12. The
integrator ledger records the exact 38-path (26 modified, 12 added)
integration range from the R10 merge to the checkpoint code commit, comprising
the 25-path reviewed union, 5 documentation paths, 4 delivery-control paths, 3
integration-control evidence paths, and 1 validator follow-up; unlike C0006 it
carries no request-correction path, the union having applied exactly as
reviewed.

## Declaration graph

The R09/R10 epoch is **not** declaration-preserving, and this checkpoint is the
first to measure that rather than carry it forward. Against the C0005 combined
baseline the elaborated declaration count rises from 56,903 to 56,913, theorems
from 43,173 to 43,179, definitions from 11,978 to 11,982, and cross-module
union edges from 262,803 to 262,888. Every added declaration is private: the
public count is unchanged at 55,219 and the private count rises from 1,680 to
1,690. Public surface preservation, not total declaration preservation, is the
property this epoch holds. The narrative declaration-graph rows, which C0006
carried forward from C0005 under the R07 declaration-preserving review, are
refreshed to these measured C0007 figures.

## Acceptance gates

All twelve acceptance gates PASS at the exact code commit: architecture,
canonical_import, combined_baseline, compatibility, focused_build, full_build,
full_tests, layout, old_import, provenance, scope, and strict_source. The
full build and test gates are carried by the green integrated-code CI runs
above; the static architecture, layout, compatibility, provenance,
strict-source, and baseline gates were rerun locally against this exact tree
during acceptance preparation, all exiting zero.

## Lifecycle

M09 and M10 are accepted at C0007. B0011 and B0012 are accepted with retirement
due. The reviewed B0012-scoped `codex-lane` operator expansion expires here:
it was authorized only while R10 was being operated, so accepting B0012 ends
it and the lane reverts to its immutable single operator, matching the R03 and
R05/R06 expansions that expired at their own accepting checkpoints. P0011 and P0012 are retired, and R0012 and R0013 are applied as the
reviewed union. M13 remains planned: its I01 wave holds the last 12 in-scope
modules, reserved for the hash-pinned integrator import cutover and reviewed
postimage union. With the classification queue empty, M13 is the phase's
remaining wave milestone.
