# R05/R06 private-map totality amendment

Authority: `primary-human` (authored by `claude-local` under the explicit
amendment grant; independent audit belongs to `codex-local` or
`primary-human` since `claude-local` authored both the original maps and
this amendment).

Defect: `check_completion_phase_projection.py` requires a supplied private
normalization map to be **total over every selected private declaration**
of the projection, including privates that do not move. The frozen
B0006/B0007 maps recorded only the privates of relocating owners (61 of
106 for R05; 195 of 200 for R06), so both delivery replays fail the
totality precondition. The R05 gate battery surfaced this at the P0006
delivery replay; the R06 replay would fail identically.

Amendment (nothing else changes — no route, owner, destination, request,
projection, or production content is touched):

| Map | Before | Identity rows appended | After |
| --- | ---: | ---: | ---: |
| `branches/B0006-private-normalization.tsv` | 61 | 45 | 106 |
| `branches/B0007-private-normalization.tsv` | 195 | 5 | 200 |

Each appended row maps a retained owner's private mangled name to itself
(`old_private = new_private`) with `destination_module` recording its
unchanged home, derived from the exact-C0003 graph
`benchmark-results/C0003-combined.tsv` (SHA-256
`98199873425E068D3B74F8595A6CFB9AFE5532974186FD760DFD122B0D273626`, as
pinned in `reviews/C0003-R05-R06-selection.md`). The 45 R05 identity rows belong
to the seven retained outlier-review owners; the 5 R06 identity rows belong
to its six retained owners. Rename semantics for the 61/195 relocated
privates are unchanged.

The `check_completion_phase.py` pins
`R05R06_PLANNED_FACTS["R05"]["private_normalization_sha256"]` and
`["R06"]["private_normalization_sha256"]` are updated to the amended file
hashes; the `private_normalizations` fact constants keep counting genuine
renames (61/195). Both branch records re-pin their evidence hashes.
