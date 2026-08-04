# W09 P0010 projection replay

The projections README requires the worker to generate one full format-2 candidate under the shared Lean mutex, then invoke `check_phase_projection.py` "with every sorted argument in its projection JSON. The candidate placeholder is replaced by the candidate TSV path; no other recorded argument is changed."

`projection.py` takes the argument vector verbatim from `P0010.json` (105 recorded arguments, one candidate placeholder substituted) and hash-verifies both the checker and the frozen graph before use -- running the right arguments against the wrong artifact would prove nothing.

## Frozen counts that must be preserved

| payload | expected |
| --- | ---: |
| declarations | 1865 |
| signature_edges | 3639 |
| body_edges | 7414 |
| union_edges | 7721 |

## Result

```
  actual   29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443   OK
projection docs/architecture/phases/2026-08-repository-reorganization/projections/P0010.tsv.gz
  recorded 2F01FAA44AF7984DAA3769512E879DEB4C1EF328130EF24E93E712C9602E1F71
  actual   2F01FAA44AF7984DAA3769512E879DEB4C1EF328130EF24E93E712C9602E1F71   OK
candidate  C:\Users\qed_s\higham-worktrees\reorg-w09-claude\benchmark-results\W09-candidate.tsv
  sha256   568F6A896E85BB2F9C51339E38343C465B106ABBDAD0479940777E9A2426B04A
  bytes    116,508,810

recorded arguments: 105 (1 candidate placeholder substituted)
running: python tools/architecture/check_phase_projection.py <105 recorded args>
  cwd: C:\Users\qed_s\higham-worktrees\final-main-audit  (read-only; -B suppresses __pycache__)

phase projection contract passed
projection_sha256: 2F01FAA44AF7984DAA3769512E879DEB4C1EF328130EF24E93E712C9602E1F71
candidate_sha256: 568F6A896E85BB2F9C51339E38343C465B106ABBDAD0479940777E9A2426B04A
selected_declarations: 1865
relocated_declarations: 1295
signature_edges: 3639
body_edges: 7414
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 72
allowed_prefixes: 30

exit 0
```
