# W10 projection replay (P0013)

P0013 freezes 1029 declarations, 2,394 signature edges, 4,844 body/proof edges and
5,075 union edges across 17,260 physical source lines. All four counts, plus the
per-kind and per-visibility splits, were reproduced from the frozen graph before any file
was written, and the 132-member private reverse closure was recomputed rather
than taken from the brief.

## Pinned artifacts, hash-verified before the replay

| artifact | SHA-256 | source |
| --- | --- | --- |
| `P0013.tsv.gz` | `B61F64FC0C2CEF8DF22DDA78C5F28BB8D6B64FC1B57392AA36A2E187F3396ABA` | origin/main |
| P0013 raw payload | `56B8FFD7024AE943C7E35AF3ACCC3106EFCEA068ED68C6AB7B42D0055DE479B0` | decompressed |
| `selectors/W10.tsv` | `444AA9109E4990AD47E281D550EA7A80057A8DBC493D8AF1693760EE7434BBB0` | origin/main |
| `baselines/C0007-combined.json` | `D9372A79DA159CEB50757F6581F650957D2868E738E41C0D5F892C121623CADD` | origin/main |
| `check_phase_projection.py` | `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443` | worker copy at 9eb534a06 |
| `checkpoints/C0007-inventory.tsv` | `56B08C666F4461BE2B425E12B2E250ACFCD4604A43F793A066AA086091365196` | origin/main |

B0012 and P0013 were created by the activation commits **after** C0007, so they exist
neither in the worker checkout nor in the control worktree. Each pinned artifact is
therefore exported read-only from `origin/main` at its exact repository-relative path and
hash-checked against P0013's own record before use. The checker needs no export: its blob
at `9eb534a06` is byte-identical to `origin/main`'s.

## Argument vector

P0013 records **73** checker arguments at `rec["checker"]["arguments"]`. They decompose
exactly as 27 `--allow-module` (the owners), 43 `--allow-prefix` (the destinations),
`--projection`, `--projection-sha256` and the candidate placeholder. The 43 allow-prefixes
match the destination roster derived independently from B0012, which is a second,
independent confirmation of the roster.

Exactly one substitution is made -- the candidate placeholder -- and the other 72
arguments are passed verbatim, as the projections README requires.

## Result

DONE exit=0
exit=0 in 0m
