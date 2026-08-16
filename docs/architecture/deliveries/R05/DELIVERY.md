# R05 delivery — least squares and underdetermined systems, Chapters 20–21

R05 executes the frozen (and once-amended) B0006 route over the 48 residual
C0003 owners holding 3,171 declarations. Every route is a whole-owner route:
574 declarations relocate — 21 owners whole into 21 canonical destinations
and 7 Chapter 20 declaration-bearing umbrellas whole into new `Core.Results`
leaves — while 2,597 declarations across 20 owners stay in place (13
declaration-free legacy wrappers classified `compatibility` by the frozen
R0006 postimage and 7 retained outlier-review owners, byte-identical). No
historical path is deleted and none is Git-renamed.

Base: C0003 `e20de2f931caa12221e708c341e9cb4f64d29b25`

Branch: `codex/reorg-completion-2026-08-r05-least-squares-underdetermined-ch20-ch21`

Controls: planned `b6794f326313f8077c0c3433bb9c76b6e2ed5361` → activation
`405e76f36a342a5d7d31a8e094cc7c580dcb250f` → private-map totality amendment
`d6a241de6c2af12439bc48885461c7190fc751d6` — each with its own green Lean CI
(runs 31844203563, 31845432265, 31893563259).

Projection: P0006 · Shared request: R0006 (integrator-only, 23 paths) ·
Operator: `claude-local` under the reviewed B0006-scoped second-operator
authorization (`reviews/R05-R06-operator-authorization.md`).

## Exact delivery

| quantity | value |
| --- | ---: |
| historical owners | 48 |
| selected declarations | 3,171 (3,065 public / 106 private) |
| relocated declarations | 574 into 28 destinations (21 whole-owner + 7 umbrella `Core.Results`) |
| retained declarations | 2,597 across 7 outlier-review owners |
| declaration-free wrappers created | 21 (single canonical-destination import each) |
| umbrella aggregates created | 7 (declaration-free, casefold-sorted) |
| private normalizations | 106 total map rows: 61 module-scoped mangle renames + 45 identity rows |
| isolated tests | 97 modules + `All.lean` (28 canonical / 48 historical / 19 consumer / 1 aggregate root / exhaustive private normalization) |
| changed paths | 163 (28 modified / 135 added; 56 production / 98 tests / 9 delivery docs) |

## Structural notes

* Destinations carry their owner verbatim — full original import surface,
  byte-identical declaration commands — with only in-wave owner imports
  retargeted to sibling destinations. Consumers therefore keep their full
  transitive surface through either the historical wrapper or the frozen
  R0006 retarget (the Chapter27.SoftwareEnvironment lesson).
* The seven Chapter 20 umbrella aggregates exclude exactly the 15 historical
  descendants that import their umbrella for the relocated declarations
  (1 under Prose, 2 under Theorem03, 12 under Theorem07); each exclusion is
  listed in the aggregate's docstring and keeps the import graph acyclic.
  Those descendants remain reachable and are imported directly by the
  chapter aggregate, which is integrator-wired at integration.
* `check_layout` worker-view reds are integrator items only (umbrella
  baseline improvement plus new-destination aggregate wiring), matching the
  R03 precedent; everything else in the battery is green, including the
  P0006 delivery replay under the complete amended private map.
