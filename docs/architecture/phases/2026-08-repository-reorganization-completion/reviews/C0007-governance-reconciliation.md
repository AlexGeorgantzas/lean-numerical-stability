# C0007 governance reconciliation

Audited revision: `cca0621da6c2b0f19836aec67aa736ef9a06a838` (remote `main`
tip at review time; the I01 implementation landed at
`9fbb1e36bcc85f866893e902cbe206ba468a65b0` under the primary human's
2026-08-30 cutover decision, and the light-regime process is recorded in
`docs/architecture/PROCESS.md`).

Reviewer: primary-human (in-session batch approval recorded verbatim in the
untracked evidence ledger). Operator: claude-local.

## Supersession decision

The active-phase pointer selects
`repository-reorganization-completion-2026-08`, while the predecessor
`repository-reorganization-2026-08` still stores `status: "active"` in its
immutable `phase.json`. The predecessor is preserved byte-for-byte
(SHA-256 `7E19F798C3B14E44F8765CF72E31CE8C47BC6D4862A528305FA7D61E9FB2ECA2`)
and an explicit successor-status record,
`docs/architecture/phases/2026-08-repository-reorganization/supersession.json`,
marks it effectively superseded by the completion phase. `check_phase.py
--all-phases` now enforces the fleet invariants: a stored status is
overridden only by a valid terminal supersession record, exactly one phase
is effectively active, the pointer selects it, every retained nonpointer
phase is effectively terminal, successors exist, chains are acyclic and end
at the active phase, and the preserved hash matches the live bytes.

## Current state (normative)

- Selected phase: `repository-reorganization-completion-2026-08`; accepted
  checkpoint C0007 (code `4e26820d1f4989ec4ec77b7113085f593570e11b`).
- M09/M10 accepted; B0011/B0012 accepted with retirement due; P0011/P0012
  retired; R0012/R0013 applied; R0014/R0015 (M13 I01 + CODE03) applied at
  `9fbb1e36bcc85f866893e902cbe206ba468a65b0`.
- 2,928 of 2,928 production modules classified; zero unclassified, mixed,
  or noncanonical modules; zero declaration-bearing umbrellas; zero
  retained production-import exceptions.
- 712 forwarding modules over 2,364 canonical targets; provenance 137
  Apache-marked production files and 5 evidenced upstream modules.
- Bounded-phase completion and repository-wide completion both remain
  incomplete.

## Measurements

Regenerated baseline at the audited revision (full `lake build`, 6,096
jobs, exit 0): 2,928 production modules; 3,981,679 total lines; 1,457,460
nonblank lines; 31,331 direct imports; zero import cycles; zero missing
module docstrings. Verbatim gate outputs at the audited revision:

- `check_layout.py`: Lean modules 2928, unclassified 0, mixed 0, missing
  module docs 0, legacy naming exceptions 0, declaration-bearing umbrellas
  0, unsorted aggregate imports 0.
- `check_compatibility.py`: 712 forwarding modules, 2364 canonical
  targets, 0 production imports of historical paths.
- `check_provenance.py`: 137 Apache-marked production files and 5
  evidenced upstream modules.

## Searches

The documentation-consistency sweep covered README.md, CHANGELOG.md,
CONTRIBUTING.md, ARCHITECTURE.md, docs/README.md, docs/architecture/
MIGRATION.md, TIERS.md, PROVENANCE.md, COMPATIBILITY.md,
reviews/OUTLIERS.md, phases/README.md, tools/architecture/README.md, and
the completion-phase README, hunting stale figures (2,642/2,818 modules,
711 wrappers, 148 provenance, 277 unclassified, pre-I01 umbrella and
retained-exception counts), claims that C0005 is current or R09/R10
active, claims that M13/I01 remains planned, and premature completion
claims. Corrections keep pinned historical evidence verbatim and move
history under explicitly archived headings; `RENAME_LEDGER.md` and all
accepted checkpoint, baseline, delivery, integration, and request evidence
stay byte-identical.
