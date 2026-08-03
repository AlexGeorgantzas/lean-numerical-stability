# W03 projection result — P0005

Replayed from the control worktree with every recorded argument from `P0005.json`,
substituting only the candidate placeholder, as `projections/README.md` requires.

All pinned values were verified before the run:

| artifact | sha256 |
| --- | --- |
| `tools/architecture/check_phase_projection.py` | `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443` |
| `projections/P0005.tsv.gz` | `7B5A07528409CCCDC8B45F94B8F5FC977A2749601F8ED2D6B18D161CD27838B7` |
| `selectors/W03.tsv` | `3BD8827FD306E748AC4150AFC7881FD229BFF10096BDF0C70E9BDDCDBFA36430` |
| `baselines/C0004-combined.json` | `CCF7ACAE1D9306C03D79495B548E598C9A3132DC99A98C4212219A453CB27FA8` |
| `checkpoints/C0004-inventory.tsv` | `26706ADEF2B255BD929572C8EC325E7B1A5F79906929A23DBEC26093D657B463` |
| `branches/B0004-overlap-review.md` | `D4257B721E6DE5EACA0A5D21036CA83A04A3315F9744DCE74043FD57F92E9653` |
| candidate `benchmark-results/W03-candidate.tsv` | `088BD0413F728B1868882F32B0CC7252BFF954593DE64CB213FBFAA80AAA2E65` |

The recorded arguments resolve against a repository root carrying the phase records.
A C0004-based worker branch does not have the B0004/P0005 activation records, so the
checker ran with the read-only control worktree as its working directory and bytecode
writing disabled. It reads only the two graph files; nothing in the control worktree
was modified.

```text
checker   tools/architecture/check_phase_projection.py
  recorded 29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443
  actual   29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443   OK
projection docs/architecture/phases/2026-08-repository-reorganization/projections/P0005.tsv.gz
  recorded 7B5A07528409CCCDC8B45F94B8F5FC977A2749601F8ED2D6B18D161CD27838B7
  actual   7B5A07528409CCCDC8B45F94B8F5FC977A2749601F8ED2D6B18D161CD27838B7   OK
candidate  C:\Users\qed_s\higham-worktrees\reorg-w03-claude\benchmark-results\W03-candidate.tsv
  sha256   088BD0413F728B1868882F32B0CC7252BFF954593DE64CB213FBFAA80AAA2E65
  bytes    116,295,023

recorded arguments: 61 (1 candidate placeholder substituted)
running: python tools/architecture/check_phase_projection.py <61 recorded args>
  cwd: C:\Users\qed_s\higham-worktrees\final-main-audit  (read-only; -B suppresses __pycache__)

phase projection contract passed
projection_sha256: 7B5A07528409CCCDC8B45F94B8F5FC977A2749601F8ED2D6B18D161CD27838B7
candidate_sha256: 088BD0413F728B1868882F32B0CC7252BFF954593DE64CB213FBFAA80AAA2E65
selected_declarations: 1034
relocated_declarations: 806
signature_edges: 8056
body_edges: 11608
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 26
allowed_prefixes: 32

exit 0
```

## What this proves

| requirement | evidence |
| --- | --- |
| all 1,034 selected declarations preserved | `selected_declarations: ?`, no `missing declaration` |
| signature edges preserved | `signature_edges: ?` against `expected_counts` 8056 |
| body/proof edges preserved | `body_edges: ?` against `expected_counts` 11608 |
| no kind drift | no `kind drift` diagnostics |
| no visibility drift | no `visibility drift` diagnostics |
| every owner inside the allowed set | no `owner not allowed` diagnostics |
| declarations actually moved | `relocated_declarations: ?` of 1,034 |

The comparison is exact set equality on typed incident edges, not a count, so passing
means the frozen graph and the candidate agree edge for edge.
