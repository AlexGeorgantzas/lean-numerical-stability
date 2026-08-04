# W08 projection result — P0008

Replayed with every recorded argument from `P0008.json`, substituting only the
candidate placeholder.

All pinned values were verified before the run:

| artifact | sha256 |
| --- | --- |
| `tools/architecture/check_phase_projection.py` | `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443` |
| `projections/P0008.tsv.gz` | `032F33236618FD21D318344A80F8E5EA02F18CCA533C4E183BD61945E6D77D74` |
| `selectors/W08.tsv` | `03AB94EAAE95A1FD2BDC0E9F3ACBD663D6CA4297008DF958A098D4D6E1038BD3` |
| private-root payload | `E4910ADAEF41B4D7988E899A5E9B50D7B833E96C22BDFB2BD6D2224AB1ABEC20` |
| reverse-closure payload | `B67D6D99436AD99DB2756C929F97B16202FD01FAFC77503F7616F7CD8C8B1724` |
| candidate `benchmark-results/W08-candidate.tsv` | `A8875CFE94A1BAC60D9FE785743E0F9B933FE662881F274C0ADE6B939D184A76` |

B0007, P0008, `P0008.tsv.gz` and `W08.tsv` do not exist at C0005 — they were
published after it — so they were read from `origin/main` with `git show` and
hash-verified. Nothing was merged, rebased or cherry-picked into the worker
branch, and the checker ran with bytecode writing disabled against read-only
copies.

```text
checker   tools/architecture/check_phase_projection.py
  recorded 29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443
  actual   29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443   OK
projection docs/architecture/phases/2026-08-repository-reorganization/projections/P0008.tsv.gz
  recorded 032F33236618FD21D318344A80F8E5EA02F18CCA533C4E183BD61945E6D77D74
  actual   032F33236618FD21D318344A80F8E5EA02F18CCA533C4E183BD61945E6D77D74   OK
candidate  C:\Users\qed_s\higham-worktrees\reorg-w08-claude\benchmark-results\W08-candidate.tsv
  sha256   A8875CFE94A1BAC60D9FE785743E0F9B933FE662881F274C0ADE6B939D184A76
  bytes    116,387,445

recorded arguments: 87 (1 candidate placeholder substituted)
running: python tools/architecture/check_phase_projection.py <87 recorded args>
  cwd: C:\Users\qed_s\AppData\Local\Temp\claude\C--Users-qed-s-OneDrive-Documents-QED-94\f1d57db1-dfa6-44e8-b0c0-ec5f45788fe3\scratchpad\w08\control  (read-only; -B suppresses __pycache__)

phase projection contract passed
projection_sha256: 032F33236618FD21D318344A80F8E5EA02F18CCA533C4E183BD61945E6D77D74
candidate_sha256: A8875CFE94A1BAC60D9FE785743E0F9B933FE662881F274C0ADE6B939D184A76
selected_declarations: 2179
relocated_declarations: 1994
signature_edges: 9266
body_edges: 15315
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 42
allowed_prefixes: 42

exit 0
```

## What this proves

| requirement | evidence |
| --- | --- |
| all 2,179 selected declarations preserved | `selected_declarations: ?`, no `missing declaration` |
| signature edges | `signature_edges: ?` against `expected_counts` 9266 |
| body/proof edges | `body_edges: ?` against `expected_counts` 15315 |
| union edges | `expected_counts` 16573; the checker reports the two typed counts and the union is the distinct source-to-target pair count, so it is smaller than their sum |
| no kind drift | no `kind drift` diagnostics |
| no visibility drift | no `visibility drift` diagnostics |
| every owner inside the allowed set | no `owner not allowed` diagnostics |
| declarations actually moved | `relocated_declarations: ?` of 2,179 |

The comparison is exact set equality on typed incident edges, not a count, so
passing means the frozen graph and the candidate agree edge for edge.
