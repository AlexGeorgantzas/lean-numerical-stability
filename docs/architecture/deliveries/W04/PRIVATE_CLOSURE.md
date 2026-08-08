# W04 private reverse closure

The W04 retention boundary was computed from the active P0009 format-2
projection before any source edit.  `PRIVATE_CLOSURE_PLAN.py` seeds all 40
private declarations, takes their reverse signature/body union closure within
the 29 selected owners, expands each result to its complete Lean command, and
records the ambient namespace, section, variable, attribute, option, and
include/omit context needed to reproduce that command without changing it.

## Pinned inputs

| Artifact | SHA-256 |
| --- | --- |
| source base | `a32095e6e50189f7dcc39312bb4c6a36f421fab5` |
| selector `W04.tsv` | `92446B8EBF571733212239DBD471A377EA889FC2A7061F1500DE7B03DB96518F` |
| projection `P0009.tsv.gz` | `EAA15F18127E7B77F8AF442760590687B66A8860485590F2EB13D57E3A6F3814` |
| sorted graph union-closure payload | `3E027CF02FDBFA2BFD9692166855245BDA0D8A9428540EA77F2938D819C86D84` |
| generated `PRIVATE_CLOSURE.tsv` | `B55744FBEA898C63D34F7D4F81F7C75C65AF69DC5EDAFA359AAF023095FC4AB7` |

## Exact result

| Quantity | Count |
| --- | ---: |
| selected owners | 29 |
| selected declarations | 1,238 |
| complete declaration-bearing commands | 1,073 |
| private seed declarations / commands | 40 / 40 |
| public declarations in reverse closure | 180 |
| graph reverse-closure floor | **220 = 40 private + 180 public** |
| retained commands / declarations | **220 / 220** |
| move-candidate commands / declarations | 853 / 1,018 |

The command/context expansion did not enlarge the 220-declaration graph
floor.  Every private declaration remains at its original historical module;
the final P0009 replay independently verifies all 40 original module, kind,
and private-visibility triples.

`RETENTION.tsv` gives the exact per-owner arithmetic.  Its totals are 220
retained declarations, 1,018 relocated declarations, 387 reusable
relocations, and 631 exact-source relocations.  Thirteen owners become pure
import-only shims and sixteen remain declaration-bearing facades.  Mutual and
generated families stay with their command roots, and no private declaration
is moved or renamed.
