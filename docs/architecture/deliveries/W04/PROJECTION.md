# W04 projection result — P0009

The final W04 format-2 candidate was generated from the fully rebuilt worker
tree under `Local\lean-reorganization-2026-08`.  The active P0009 checker
argument vector was replayed from the read-only control worktree, changing
only `--candidate=<candidate-format2.tsv>` to the absolute candidate path.

## Recorded hashes

| Artifact | SHA-256 |
| --- | --- |
| projection checker | `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443` |
| selector `W04.tsv` | `92446B8EBF571733212239DBD471A377EA889FC2A7061F1500DE7B03DB96518F` |
| projection `P0009.tsv.gz` | `EAA15F18127E7B77F8AF442760590687B66A8860485590F2EB13D57E3A6F3814` |
| C0006 combined baseline JSON | `E9207AA896EAA547E791FB1CECAC7A6B4E6344E8DC8E15D2EF2372FF90570625` |
| B0008 overlap review | `B285FBD180581D715A208652B713D2A2B85C622F609C2BE3926D7339B133F4C9` |
| C0006 raw format-2 graph | `3BFEFF5663DA3FB5327B9D3AB22806654C9A79A48E1DDFE3C6E2E79073F9DE11` |
| final candidate TSV | `6CA03A2F9F38963AA3DF0D40DC3F3A5ECF57A878F93BA4C9732F7DA3904E47D4` |
| candidate JSON | `124806B44FB3CE6D8BAA20944C4C08ADB159DF7766E4EFE2923330DED5498B06` |
| candidate Markdown | `63AFA0A2DF05BE2B2C54BFDB40060C14EAF2279ECF0B93DC010D8FE44F37B5BE` |
| private-closure TSV | `B55744FBEA898C63D34F7D4F81F7C75C65AF69DC5EDAFA359AAF023095FC4AB7` |

`CHECK_PROJECTION.py` verifies the five active control hashes (checker,
projection, selector, combined baseline, and overlap review), the derived
candidate hash and byte size, and the private-closure hash.  The raw C0006
graph and the two candidate summaries are recorded generation/replay evidence;
they are not additional inputs to the P0009 checker.

The candidate is 116,512,944 bytes.  Its source scan covered 2,326 Lean
modules with zero unresolved project imports and zero import cycles.  The
declaration extractor scanned 56,903 declarations and 649,259 typed edge
rows.  Candidate generation built 5,871 jobs and exited 0 in 144.843 seconds.
After candidate/closure pinning was added to the checker, a second extraction
reproduced the identical TSV SHA and byte size; the strengthened replay exited
0 in 4.800 seconds (3.237 seconds inside the phase checker).

## Exact replay

P0009 contains 74 recorded checker arguments: 29 exact historical modules,
42 reviewed destination prefixes, the candidate placeholder, the pinned
projection hash, and the projection path.  `CHECK_PROJECTION.py` preserves
their order and content, substitutes only the placeholder, verifies the
control/candidate/private-closure hashes described above, and then
independently fixes all 40 private declarations to their original modules.

```text
phase projection contract passed
projection_sha256: EAA15F18127E7B77F8AF442760590687B66A8860485590F2EB13D57E3A6F3814
candidate_sha256: 6CA03A2F9F38963AA3DF0D40DC3F3A5ECF57A878F93BA4C9732F7DA3904E47D4
selected_declarations: 1238
relocated_declarations: 1018
signature_edges: 5684
body_edges: 10044
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 29
allowed_prefixes: 42
retained_declarations: 220
private_declarations_fixed_at_historical_owner: 40
union_edges: 10624
checker_exit: 0
```

This is exact set equality on declaration identity, kind, visibility, owner
permission, and every incident typed edge.  It preserves the required 1,238
declarations (904 theorems, 283 definitions, and 17 each of inductives,
constructors, and recursors), 1,198 public / 40 private visibility split,
5,684 signature edges, 10,044 body/proof edges, and 10,624 union edges.
No projection mismatch is waived.

## Deterministic replay

The frozen TSV was summarized a second time without invoking Lean.  The JSON
and Markdown reproduced byte-identically:

```text
JSON      124806B44FB3CE6D8BAA20944C4C08ADB159DF7766E4EFE2923330DED5498B06
Markdown  63AFA0A2DF05BE2B2C54BFDB40060C14EAF2279ECF0B93DC010D8FE44F37B5BE
```

## Source-tier boundary

`CHECK_STATIC.py` finds zero direct or transitive W04 reusable-to-Source
reachability, zero reusable-to-historical-facade reachability, and zero import
cycles.  The repository-wide strict-source command exits 2 on 56 paths, all
of which are the Cartesian expansion of 14 accepted reusable entrypoints and
four exact Chapter 21 source leaves through one forbidden accepted edge:

```text
NumStability.Analysis.Perturbation.LeastSquares.Wedin
  -> NumStability.Algorithms.Underdetermined.UnderdeterminedSpec
```

`INTEGRATOR_REQUESTS.md` gives the exact one-line canonical retarget that
removes all 56 paths.  W04 may not edit that accepted consumer.  The local
W04 destination graph itself is clean; no Source reachability or projection
mismatch is waived.

The ignored `benchmark-results/W04-*` extraction outputs are deliberately
removed after their hashes and sizes are recorded so that the delivered
worktree contains no generated artifact.  The committed generator and checker
reproduce and verify the exact candidate.
