# C0007 governance-document reconciliation

## Status and authority

- Audited repository revision: `8960f2a980be22166f321c4ba452eb547529b1fd`.
- Accepted checkpoint: C0007.
- Accepted code: `4e26820d1f4989ec4ec77b7113085f593570e11b`.
- Operating phase: `repository-reorganization-completion-2026-08`.
- Scope: GOV-01, GOV-02 narrative reconciliation, and GOV-04 table repair.
- Implementer/evidence preparer: `codex-local`, under task-bounded authority.
- Independent reviewer: pending review of the integrated candidate revision.
- Acceptance state: pending independent review and the integrated-candidate
  exit packet.

The accepted C0007 checkpoint files and baselines remain immutable. This
change updates mutable current-policy documents and reorders one Markdown
policy block; it does not change any Lean declaration, import, compatibility
mapping, tier assignment, checkpoint, baseline, request, projection, delivery,
or retirement record.

## Reconciled current facts

| Fact | Current authority |
| --- | --- |
| Production modules | C0007 generated baseline: 2,927 |
| Classification | `check_layout.py`: 2,927/2,927; 0 unclassified; 0 mixed; 0 legacy naming exceptions |
| Tier roles | 404 aggregate; 712 compatibility; 5 internal; 0 mixed; 577 reusable; 1,224 source; 5 upstream |
| Compatibility | `check_compatibility.py`: 712 forwarding modules; 2,364 canonical targets; 2 retained production-import exceptions |
| Provenance | `check_provenance.py`: 137 Apache-marked production files; 5 evidenced upstream modules |
| Algorithms import ceilings | Executable layout configuration: 446 total; 44 Analysis; 73 Source |
| Accepted lifecycle | M09/M10 accepted; B0011/B0012 accepted with retirement due; P0011/P0012 retired; R0012/R0013 applied |
| Remaining bounded wave | M13/I01 planned; 12 modules |
| Completion status | Bounded-phase incomplete; repository-wide incomplete |

## Mutable-document reconciliation

- The active phase README and phase index now begin with one normative C0007
  summary. Superseded C0005 and pre-integration worker language is retained
  only below explicit archived-chronology headings.
- `MIGRATION.md`, `TIERS.md`, `docs/README.md`, `README.md`, `CHANGELOG.md`,
  `CONTRIBUTING.md`, `ARCHITECTURE.md`, and `tools/architecture/README.md` now
  state the current inventory and incomplete completion statuses.
- `PROVENANCE.md` uses the executable 137/5 count and labels 148 as an archived
  2026-07-22 snapshot.
- `OUTLIERS.md` records the current 22-module and nine-directory queues, the
  17 split/move dispositions, five profile-and-review dispositions, provisional
  family owners, and exact fanout ceilings. The older LSQR/LSE ordering is
  explicitly archived rather than presented as the current queue.
- `README.md` describes `RENAME_LEDGER.md` as archived package/repository/
  library identity history and directs current forwarding-path users to
  `COMPATIBILITY.md`.
- `COMPATIBILITY.md` has one table header followed by 712 contiguous mapping
  rows. The unchanged removal rule follows the final row.

## Searches and command evidence

The documentation consistency search was run over every mutable document:

```text
rg -n "current C0005|C0005 is the current|B0011/R09 and B0012/R10 are active|No R09 or R10 implementation|Bounded-phase completion is reached|inventory is intentionally partial|deliberately partial|562 of 1,154|148 production Lean files|435 total imports|43 below|15 below" <mutable-document-set>
```

Every retained match is below an explicit `Archived` heading. No match is in a
current-authority section.

The candidate working tree produced these results:

```text
python -B tools/architecture/check_layout.py
Lean modules: 2927
unclassified modules: 0
mixed modules: 0
modules missing module docs: 0
legacy naming exceptions: 0
declaration-bearing umbrellas: 1
unsorted aggregate imports: 0
Layout contract satisfied; no legacy debt increased.

python -B tools/architecture/check_compatibility.py
compatibility contract passed: 712 forwarding modules, 2364 canonical targets, 2 retained production-import exceptions

python -B tools/architecture/check_provenance.py
provenance contract passed: 137 Apache-marked production files and 5 evidenced upstream modules

git diff --check
PASS
```

A direct Markdown-table inspection found one compatibility header, mapping rows
11 through 722 inclusive, 712 contiguous mapping rows, and the removal rule at
line 724. Independent review must repeat these checks at the integrated
candidate SHA and record the reviewer and acceptance decision above.
