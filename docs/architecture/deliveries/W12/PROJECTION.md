# W12 projection result — P0003

Run with every recorded argument from `P0003.json`, with only the candidate
placeholder substituted, as `projections/README.md` requires.

The checker and the frozen graph were hash-verified against the record before use:

| artifact | sha256 | |
| --- | --- | --- |
| `tools/architecture/check_phase_projection.py` | `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443` | matches record |
| `projections/P0003.tsv.gz` | `892C767A3A72F288283F95B89A06F48B7020C80C61BF9449948C6B4A34F81BFA` | matches record |
| candidate `benchmark-results/W12-candidate.tsv` | `D16C632640D997702C22BEAC795FF2D3E2D1DD9BCE0318FCEBCA2BA06E2E6523` | generated under the shared mutex |

The recorded arguments resolve relative to a repository root that carries the phase
records. At `C0002` the worker tree carries only the W01/`P0001`/`B0001` generation,
so the checker was run with the read-only control worktree as its working directory,
with bytecode writing disabled; it only reads the two graph files and nothing in the
control worktree was modified.

```text
checker   tools/architecture/check_phase_projection.py
  recorded 29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443
  actual   29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443   OK
projection docs/architecture/phases/2026-08-repository-reorganization/projections/P0003.tsv.gz
  recorded 892C767A3A72F288283F95B89A06F48B7020C80C61BF9449948C6B4A34F81BFA
  actual   892C767A3A72F288283F95B89A06F48B7020C80C61BF9449948C6B4A34F81BFA   OK
candidate  C:\Users\qed_s\higham-worktrees\reorg-w12-worker\benchmark-results\W12-candidate.tsv
  sha256   D16C632640D997702C22BEAC795FF2D3E2D1DD9BCE0318FCEBCA2BA06E2E6523
  bytes    116,190,133

recorded arguments: 108 (1 candidate placeholder substituted)
running: python tools/architecture/check_phase_projection.py <108 recorded args>
  cwd: C:\Users\qed_s\higham-worktrees\final-main-audit  (read-only; -B suppresses __pycache__)

phase projection contract passed
projection_sha256: 892C767A3A72F288283F95B89A06F48B7020C80C61BF9449948C6B4A34F81BFA
candidate_sha256: D16C632640D997702C22BEAC795FF2D3E2D1DD9BCE0318FCEBCA2BA06E2E6523
selected_declarations: 4197
relocated_declarations: 2647
signature_edges: 10175
body_edges: 23388
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 42
allowed_prefixes: 63

exit 0
```

## What this proves

| requirement | evidence |
| --- | --- |
| all 4197 selected declarations preserved | `selected_declarations: 4197`, no `missing declaration` |
| incident edges preserved | signature 10175 + body 23388, matching `expected_counts` |
| no kind drift | no `kind drift` diagnostics |
| no visibility drift | no `visibility drift` diagnostics |
| every owner within the allowed set | no `owner not allowed` diagnostics |
| declarations actually moved | `relocated_declarations: 2647` of 4197 |

The comparison is exact set equality on incident edges, not a count, so passing means
the frozen graph and the candidate agree edge for edge.
