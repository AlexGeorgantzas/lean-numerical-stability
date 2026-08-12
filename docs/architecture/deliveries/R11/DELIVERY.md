# R11 delivery — residual QR and Chapter 19 owners

R11 executes the frozen B0003 whole-owner block route over the 65 residual C0001 owners
holding 1,477 declarations. 412 declarations move to five canonical destinations; the
1,065 declarations of `Chapter19.Core` are retained in place as the reviewed source
outlier. No historical path is deleted and none is Git-renamed.

Base: C0001 `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`

Branch: `codex/reorg-completion-2026-08-r11-qr-ch19`

Active control: `5e075b947a63e84c784afecd00e1f130e21ea659`

Projection: P0003 · Shared request: R0003

## Authority

B0003, P0003 and R0003 are deliberately absent from the C0001 worker branch. They were
read from a read-only control checkout at the active-control commit and were never merged
or copied into the branch — `git status` shows no phase-control path. All 25 artifacts
pinned by `B0003.refresh.evidence` were hash-verified before use, as was
`tools/architecture/check_completion_phase_projection.py` at the hash P0003 pins.

B0003 is active, names this exact branch, C0001, the exact base SHA, `claude-lane` and
`claude-local`. The planned-control Lean CI run `31546978830` (job `93961477202`)
completed successfully before either ref existed, and the R11/R12 activation review
records both worktrees verified clean at C0001 before activation.

## Exact delivery

| quantity | value |
| --- | ---: |
| historical owners | 65 |
| selected declarations | 1,477 |
| public declarations | 1,460 |
| private declarations | 17 |
| theorems / definitions | 1,250 / 182 |
| inductives / constructors / recursors | 15 / 15 / 15 |
| relocated declarations | 412 |
| retained declarations | 1,065 |
| canonical destinations | 5 (3 reusable, 2 source) |
| production paths | 69 (64 modified, 5 added) |
| tests | 205 (204 planned targets + 1 aggregate) |
| `#check` assertions | 3,986 |
| delivery artifacts | 16 |
| total changed paths | 290 (64 modified, 226 added) |

Routes: 101 → `…QR.Householder.PanelApplication`, 132 → `…QR.Householder.StoredQR`,
112 → `…QR.Householder.TrailingPanels`, 59 → `…Chapter19.Sensitivity.Bounds.Results`,
8 → `…Chapter19.StoredLoop.Perturbation.Bridge`.

Every public declaration keeps its exact name, namespace, kind, visibility, type,
attributes and proof. The 17 private declarations carry only the approved P0003
module-prefix normalization: 16 rewrites plus the `Chapter19.Core` identity.

## Relocation is a byte transfer, not a re-emission

Each owner sends all of its declarations to one destination, so each destination is a new
header plus the owner's file body carried verbatim — the region from the single top-level
`namespace NumStability` to end of file. `CHECK_STATIC.py` compares those bytes against
`git show C0001:<owner>` and requires equality; all five match exactly (89,580 / 149,026 /
265,439 / 55,224 / 8,808 bytes).

This check is load-bearing. A wave that re-emitted declarations could compile *and* pass a
projection replay on names and edges while having silently reformatted a proof or dropped
a `noncomputable section`. Byte equality rules that out rather than arguing against it.

`NumStability/Source/Higham/Chapter19/Core.lean` is preserved byte-for-byte — it does not
appear in the changed-path ledger at all — and keeps its exact six imports, including two
imports of historical wrappers. `ROUTING.md` records why that is the frozen instruction
rather than an oversight, and `INTEGRATOR_REQUESTS.md` records the one consequence.

## Compatibility contract

| action | owners |
| --- | ---: |
| relocated → documented import-only wrapper | 5 |
| declaration-free wrapper, exact imports retained | 56 |
| declaration-free wrapper, support import retargeted | 3 |
| retained source outlier, untouched | 1 |

All 65 historical paths remain importable. A wrapper importing only its destination still
exposes the entire prior surface, because each destination inherits the owner's original
imports with an owner import replaced by that owner's destination. The 65 old-path-only
tests verify this rather than assert it.

The complete import graph has 5,224 modules and zero cycles. All three reusable
destinations reach neither `NumStability.Source` nor any historical facade; both source
destinations reach no facade.

## Verification

Every Lean and baseline command ran while holding `Local\lean-reorganization-2026-08`.
`GATE_RESULTS.tsv` records each gate's command, measured exit code and timing.

All five isolated matrices pass: 5 canonical-only, 5 focused, 65 old-path-only and 129
protected-consumer targets, plus the declaration-free aggregate. `lake build NumStability`
completed 6,138 jobs and `lake build NumStability NumStabilityTest` completed 8,900 jobs,
both with zero `error:` lines; `lake test` passes. Strict-source reports no unresolved
import, no cycle and no reusable-to-Source reachability. The placeholder and
tracked-artifact scans and `git diff --check` are clean.

The candidate is a full format-2 graph: 116,736,010 bytes, 706,163 rows, 56,903
declarations, 649,259 typed edges, SHA-256
`FBF9B388DF9107D99A64B5427066C38E6325ACFC788731207A14E546D090C3F9`. Re-summarizing the
same TSV reproduced identical output. P0003 replay passed with exactly 1,477 selected
declarations, 412 relocated (hence 1,065 retained), 15,172 signature edges, 18,056
body/proof edges and all 17 private normalizations applied. The comparison is exact set
equality on incident edges, so passing means the frozen graph and the candidate agree edge
for edge.

One measurement caveat, stated rather than hidden: the system clock stepped backwards
twice during the run, so some elapsed times are unreliable and the affected gate is
recorded as not measurable instead of carrying a negative duration. Exit codes and Lake's
own job counts are unaffected.

`placeholder_scan` first exited 1 because the scan's own regular expression was invalid on
Python 3.12 — it crashed instead of scanning. It was corrected and re-run under the mutex,
and reports zero placeholder hits. That failure is recorded here because a harness that
reports `exit 0` on a crashed check is exactly the defect the R02 gate battery was built to
prevent.

## Integration boundary

No shared path was edited. `CHECK_SCOPE.py` proves every changed path lies inside B0003's
`owned_paths` or `destination_prefixes`, that none matches its 2,580 `forbidden_paths`
entries, that nothing was deleted or renamed, and that none of R0003's 133 paths was
touched. `NumStability/Analysis/MatrixAlgebra.lean` is unmodified.

R0003 is integrator-owned and already complete; this wave requests nothing new.
`CHECK_REQUEST_REPLAY.py` validates it in a disposable directory: 133/133 preimage blob
OIDs match C0001, forward replay reproduces all 133 pinned postimage hashes, reverse replay
restores all 133 preimages, and all 209 recorded import replacements across 129 consumers
occur with the old import gone.

Two gates are nonzero at the worker tip — `check_layout` (3 findings) and
`check_compatibility` (3 findings) — and all six are integrator-owned and closed by
applying R0003, verified on the disposable acceptance tree rather than assumed. Two of the
six are ratchets objecting that the tree *improved*: 59 wrappers gained module
documentation and two Chapter 19 umbrellas became declaration-free. Their remedy is
`--write-baseline` on an integrator-owned control file, so the improvement is recorded, not
ratcheted from here.

`INTEGRATOR_REQUESTS.md` additionally records two findings that R0003 alone does **not**
close, both properties of the frozen contract rather than of this implementation: the two
Chapter 19 wrappers are reclassified as aggregates but cannot import their descendants
until R0003 retargets those descendants, and the byte-for-byte `Chapter19.Core` outlier
necessarily keeps importing two paths R0003 registers as compatibility modules. Neither is
fixable from this branch and no gate was weakened to hide either.

This delivery claims no checkpoint acceptance. C0002 is the integrator's to record.
