# R08 projection replay

Baseline projection `P0009`, base checkpoint C0004
`783ae9a4951407ece046adb8631d5a8ff1795a18`.

## Result: PASSED (exit 0, zero mismatch)

The frozen projection was read with `git show` from the exact planned control
commit `2d9dbf7bf8b4b51e9cb7817f5c5dc2d5194e8c42`, because the worker branch
intentionally lacks the later control commit. A fresh format-2 candidate graph
was generated under the named mutex from the built worktree.

| field | value |
| --- | --- |
| projection SHA-256 | `CE770EBE7B3170BA808D22D2AD603B7266A8AADC550864902423FD33162FA1FF` (matches the P0009 pin) |
| candidate SHA-256 | `ED6C505EBC5651BEC7BE0602B0C722BFB16D8D357D2AAD268C5382BA1BC105BA` |
| private map SHA-256 | `335C3FE17716B3391962CC68EFAD81673E1BAE0E4B4C2F0720C0906703786FC0` (frozen B0009 map) |
| allowed exact modules | 66 (P0009 allow-module vector, verbatim) |
| allowed prefixes | 0 |

## Counts against the P0009 expectation

| quantity | replayed | expected |
| --- | ---: | ---: |
| selected declarations | 211 | 211 |
| relocated declarations | 211 | - |
| signature edges | 1229 | 1229 |
| body edges | 2886 | 2886 |
| private normalizations | 48 | 48 |

Candidate scan covered 56,903 declarations and 649,259 edges.

Every selected declaration keeps its name, kind and visibility, and its exact
signature and body incident edge sets; only the owning module changed, and every
candidate owner matched a P0009 allow-module entry. The 48 private
normalizations were authorised by the hash-pinned map.
