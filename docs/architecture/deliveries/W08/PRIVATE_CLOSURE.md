# W08 private-declaration and retention closure

P0008 contains **45** private declarations. Lean mangles a private name to
`_private.<defining module>.<n>.<name>`, so the defining module is part of the
name: relocating one renames it and every incident edge is reported missing
against the frozen graph. No private declaration is moved or renamed.

## Reproduction

Derived from the hash-pinned P0008 graph and W08 selector exactly as B0007
specifies: select declarations whose owner is in `W08.tsv`; seed with every
selected private; retain only selected-to-selected `signature` and `body`
edges; build reverse adjacency `target -> source`; breadth-first traverse to a
fixed point; ordinal-sort; serialize UTF-8 without BOM, LF, final newline.

| payload | rows | sha256 | matches B0007 |
| --- | ---: | --- | --- |
| private roots | 45 | `E4910ADAEF41B4D7988E899A5E9B50D7B833E96C22BDFB2BD6D2224AB1ABEC20` | yes |
| reverse closure | 179 | `B67D6D99436AD99DB2756C929F97B16202FD01FAFC77503F7616F7CD8C8B1724` | yes |

Both hashes reproduced exactly; see `closure.py` in the wave scratchpad.

## Per-owner closure

| historical owner | private | pinned public | closure total |
| --- | ---: | ---: | ---: |
| `NumStability.Algorithms.Ch14AsymptoticFamilies` | 2 | 8 | 10 |
| `NumStability.Algorithms.Ch14Cor146UniformInverseBridge` | 0 | 2 | 2 |
| `NumStability.Algorithms.Ch14Cor147FinalDivisionFamilyClosure` | 0 | 20 | 20 |
| `NumStability.Algorithms.Ch14Corollary147SourceClosure` | 0 | 18 | 18 |
| `NumStability.Algorithms.Ch14Corollary147WeakFamily` | 0 | 11 | 11 |
| `NumStability.Algorithms.Ch14ForwardErrorEndpoint` | 5 | 7 | 12 |
| `NumStability.Algorithms.Ch14GJEAsymptoticFamilies` | 14 | 8 | 22 |
| `NumStability.Algorithms.Ch14GJEFinalDivisionClosure` | 0 | 14 | 14 |
| `NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure` | 7 | 15 | 22 |
| `NumStability.Algorithms.Ch14GJETheorem145SourceClosure` | 0 | 7 | 7 |
| `NumStability.Algorithms.Ch14Method1BWhole` | 3 | 4 | 7 |
| `NumStability.Algorithms.Ch14Method2C` | 3 | 1 | 4 |
| `NumStability.Algorithms.Ch14Method2CWhole` | 0 | 3 | 3 |
| `NumStability.Algorithms.Ch14Problem142` | 2 | 6 | 8 |
| `NumStability.Algorithms.Ch14Problem142Families` | 0 | 5 | 5 |
| `NumStability.Algorithms.Ch14Problem142Method2B` | 0 | 1 | 1 |
| `NumStability.Algorithms.MatrixInversion` | 9 | 4 | 13 |
| **total** | **45** | **134** | **179** |

## Command-level closure

B0007 states the 179-declaration figure is a graph-only floor and that command
roots, mutual/generated declarations, sections, attributes, options, namespaces
and ambient imports may require more. The measured command-level closure for
this delivery is **185** declarations across
**18** owners, which is
6 declarations above the floor.
Relocated: **1994**. B0007's graph-only maximum is 2,000.

Every retained declaration is listed in `RETENTION.tsv` with its reason, and
every closure member in `PRIVATE_CLOSURE.tsv` with the private that triggers it.
