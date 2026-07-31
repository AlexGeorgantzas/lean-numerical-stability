# Classification proposal: the 386 frozen unclassified modules

This directory is a **proposal**. It changes no production Lean file, no
aggregate, and no shared manifest. The integrator decides whether and when to
apply it.

- Frozen base: `6487fc33088523b8f27ecde9ad613515b78f9977`
- Lane: `classification-ch09-ch11` (Claude subscription 4),
  branch `codex/org-classification-prep`
- Inputs and outputs are validated by
  `tools/architecture/lane_claude_classification/`.

## Files

| File | Role |
| --- | --- |
| `input-modules.tsv` | byte-for-byte copy of the packet `READ_ONLY_MODULES.tsv` (386 rows, SHA-256 `C0B1C88F34461A44305D269C880F7581BDD7F1D9CC69CF9A144EA099C6A6DF54`) |
| `modules.tsv` | the reviewed proposal, one row per frozen module, sorted by module |
| `summary.json` | generated deterministically from `modules.tsv` |
| `README.md` | this contract |

## Input accounting

The packet inventory is the 386-module slice of the authoritative 603-module
unclassified snapshot at the frozen base. `check_read_only_inventory.py`
proves, against the repository itself, that

- the tracked copy hashes to the frozen packet SHA-256 and has 386 unique,
  sorted rows whose paths all exist and all derive their module names;
- every listed module is still unclassified in `docs/architecture/tiers.json`;
- with the packet `CLASSIFICATION_EXCLUSIONS.tsv` supplied, the inventory and
  the 217 excluded modules are disjoint and their union is exactly the 603
  unclassified production modules that `check_layout.py` reports
  (`386 + 217 = 603`).

`NumStability.Algorithms.RandNLA.LeastSquaresSketch` is deliberately in this
inventory: it consumes least-squares APIs but is not owned by the least-squares
implementation lane, so it is classified here without touching its source.

## How each module was classified

Every module was read: module documentation, every authored declaration with
its kind and visibility, direct project imports, and direct downstream
consumers. No module was classified from its filename.

The reviewed decision is the `proposed_tier` column. Everything else in a row
is derived, and `check_classification_proposal.py --check` recomputes it from
the frozen sources and requires exact agreement, so no evidence column can be
asserted by hand.

### Tier vocabulary

| Tier | Meaning here |
| --- | --- |
| `source` | the module *is* numbered correspondence to the book: numbered results and aliases, printed displays, corrections, discrepancies and counterexamples to printed claims, worked examples, capstones, cross-chapter glue |
| `reusable` | source-independent mathematics; the book appears only as motivation |
| `mixed_pending_split` | a reviewed owner that holds **both** kinds of declaration; `required_action` names the concrete split |
| `aggregate` | declaration-free import-only umbrella |
| `internal`, `compatibility` | available in the vocabulary; not used by this proposal |

The discriminator between `source` and `reusable` is the one
`docs/architecture/TIERS.md` states: classify by mathematical role, and keep
source-independent definitions and theorems reusable even when a book first
motivated them. Concretely, a module is `source` when its declarations are the
numbered correspondence (`higham9_14_*`, `ch14ext_cor147_*`, `problem2_13_*`,
`higham28*`, …) **or** its documentation frames the file as formalising or
auditing a printed problem, theorem, equation, table, or worked example — even
when the declaration names are neutral, as in `Analysis.Heron` (equation (2.7)),
`Analysis.MullerRecurrence` (Problem 1.8), or `Algorithms.OrderingExamples`
(equation (4.5)). A module is `reusable` when it supplies an API — the
floating-point format and standard-model foundation, dot products, matrix
products, LU, Cholesky, condition estimation, finite probability, spectral
analysis — whose statements do not mention the source.

`mixed_pending_split` is used only where the review found both slices in one
file, and only when the source-owned slice is at least 3 declarations *and* the
remaining surface is a coherent reusable API of at least 10 declarations.
Otherwise the dominant role decides. That test matters: the three giant chapter
owners `HighamChapter8`, `HighamChapter9`, and `HighamChapter11` have **no**
source-neutral public declarations at all (223/223, 3,734 of 3,735, and
4,478/4,478 carry numbered locators), so they are `source`, not mixed — which is
also exactly what the Chapter 9 and Chapter 11 contracts in `../ch09/` and
`../ch11/` do, routing 100% of their declarations into
`Source.Higham.ChapterNN` destinations. The reviewed split queue is therefore
the four modules listed below.

### Confidence

`confidence` is derived, not asserted:

- `high` — an aggregate row; a `source` row where at least half of the public
  declarations carry a numbered locator; a `reusable` row with a fully neutral
  public surface and a clean import closure.
- `medium` — a `source` row decided from documentation rather than declaration
  names; a mixed row; a deferred reusable row.
- `low` — the three RandNLA rows whose numbered correspondence is to a
  **non-Higham** source (the Drineas–Mahoney CACM RandNLA survey: Algorithm 1,
  Algorithm 3, equation (9)). The repository has no non-Higham source family,
  so those rows are proposed `reusable` conservatively and marked
  `NON_HIGHAM_SOURCE_REVIEW_REQUIRED`. Creating such a family is an integrator
  decision, not a worker decision.

### Actions

| `required_action` | Meaning |
| --- | --- |
| `plan_source_extraction` | move to `NumStability.Source.Higham.ChapterNN`, leaving an import-only wrapper at the historical path |
| `plan_reusable_relocation` | move to the named reusable family, leaving an import-only wrapper |
| `plan_semantic_split: <detail>` | split a mixed owner; `<detail>` names both destinations |
| `register_tier_only` | add the tier rule, move nothing |
| `defer_pending_upstream_split` | source-neutral content whose closure still reaches the source tier: do **not** register it reusable yet |

## The two dependency gates this proposal satisfies

`docs/architecture/TIERS.md` treats every direct or transitive path from
`reusable` into `source` or `mixed` as forbidden. The proposal is therefore
constrained in both directions, and the checker proves both:

**G1 — nothing already depended on as reusable is proposed source or mixed.**
15 frozen modules lie inside the transitive closure of an already-classified
reusable module. All 15 are proposed `reusable`. Three of them
(`Analysis.StatisticalRounding`, `Analysis.FirstOrderFramework`,
`Analysis.RoundingProductBounds`) read as Chapter 2/3 correspondence from their
documentation, but they are imported by classified reusable modules, so
classifying them `source` would immediately break the strict-source gate. They
are the reusable rounding-model foundation and are classified accordingly.

`Analysis.Monotonicity` is the mirror-image case: Chapter 2 §2.9 merely *notes*
monotonicity as a property of correct rounding, and all 51 of the module's
public declarations are general `FloatingPointFormat` theorems with no printed
example and no numbered locator. It is classified `reusable`, but it imports
`Analysis.TieRules` — 23 of whose 28 declarations are the printed decimal chain
— so it is deferred under G2 rather than registered today.

**G2 — no proposed reusable row reaches source or mixed.** 14 rows would, so
they are deferred: their tier records the source-neutral content honestly, their
`cross_lane_dependency` names the blocker as `REUSABLE_BLOCKED_BY:<module>`,
their action is `defer_pending_upstream_split`, and
`apply_tier_proposal.py` skips them unless `--include-deferred` is passed. The
blockers are the giant owners in the split queue (`HighamChapter8/9`,
`Analysis.HighamChapter7`, `MatrixInversion`, `StationaryIteration`), the pure
source owners `HighamChapter8` and `HighamChapter9`, and
`Analysis.TieRules`, whose five general round-to-odd declarations
`Analysis.Monotonicity` depends on while its other 23 declarations are the
printed decimal 2.445/1.05/0.95 chain.

Applying the proposal without the deferred rows was verified to leave **zero**
forbidden `reusable -> source/mixed` reachable pairs and to raise tier coverage
from 451/1054 (42.8%) to 823/1054 (78.1%) production modules.

**A third structural rule** is also enforced: a proposed canonical family may
not be an existing *declaration-bearing* module, because relocating leaves under
`X` while `X.lean` still owns declarations turns `X.lean` into a
declaration-bearing umbrella beside a new `X/` directory — which
`check_layout.py` counts as new legacy debt. Three families were renamed for
this reason: `Analysis.RoundingProductBounds` targets
`NumStability.Analysis.Asymptotics` rather than the declaration-bearing
`Analysis.Rounding`; `Analysis.StatisticalRounding` targets
`NumStability.Analysis.Probability.Rounding`; and the dot-product family is
`NumStability.Algorithms.Arithmetic.DotProduct.Core`, mirroring the existing
`Arithmetic.DotProduct.NoGuard.Core` leaf rather than occupying the shared
`DotProduct` node.

## Counts

| Tier | Rows |
| --- | --- |
| `source` | 313 |
| `reusable` | 68 |
| `mixed_pending_split` | 4 |
| `aggregate` | 1 |
| **total** | **386** |

Confidence: 183 high, 200 medium, 3 low. Public declarations covered: 28,798.

`alias new := old` is extracted as an authored public declaration, because a
source alias is exactly the shape this migration relocates. 74 of the covered
declarations are aliases (71 in `Algorithms.HighamChapter9`, 3 in
`Analysis.HighamChapter7`).

Chapter destinations for the 313 source rows: Ch01 14, Ch02 33, Ch03 12,
Ch04 9, Ch05 7, Ch07 2, Ch08 5, Ch09 12, Ch10 17, Ch11 66, Ch14 39, Ch15 25,
Ch28 72.

Every source row's chapter was cross-checked mechanically against the chapter
numbers embedded in its own declaration names. Two rows are genuinely
cross-chapter and the integrator may prefer the repository's existing
`NumStability.Source.Higham.CrossChapter` family for them:

| Row | Assigned | Declaration-name evidence |
| --- | --- | --- |
| `Algorithms.HighamChapters1To9SourceClosure` | Ch09 | 42 `higham7_*`, 23 `higham8_*`, 6 `higham9_*` — an audit closure spanning Chapters 1–9, assigned to its terminal chapter |
| `Algorithms.Ch10Ch14Lemma66Op2Bridge` | Ch10 | four `lemma66c_*` declarations bridging Chapter 6 Lemma 6.6 into the Chapter 10 and Chapter 14 two-norm steps |

They are left on chapter destinations here so that their
`CH09_BLOCKED_ON_BLOCKLU_INTEGRATION` marker stays derivable from the row
itself; moving them to `CrossChapter` is a one-line integrator decision.

### Split queue (4 modules)

| Module | source-owned | source-neutral |
| --- | --- | --- |
| `Analysis.HighamChapter7` | 995 | 49 |
| `Algorithms.MatrixInversion` | 211 | 69 |
| `Algorithms.HighamChapter10` | 110 | 50 |
| `Algorithms.StationaryIteration` | 3 | 128 |

Each row's `required_action` names both destinations. Chapters 9 and 11 need no
split entry: they are pure source owners and are already prepared in full in
this lane's `../ch09/` and `../ch11/` contracts.

### Cross-lane markers

| Marker | Rows | Meaning |
| --- | --- | --- |
| `BLOCKLU_REFRESH_REQUIRED` | 3 | `Ch14Problem142`, `HighamChapter9`, `MatrixInversionMethod2BInstance`: the preserved BlockLU/Chapter 13 wave changes their **imports** (not their declaration bodies), so their direct-import evidence is provisional and the integrator must revalidate these rows against integrated `main`. See `../REFRESH-APPENDIX.md`. |
| `CH09_BLOCKED_ON_BLOCKLU_INTEGRATION` | 12 | Chapter 9 rows; release only after BlockLU/Chapter 13 is merged and globally verified |
| `CH11_BLOCKED_ON_CH09_INTEGRATION` | 66 | Chapter 11 rows; strictly after Chapter 9 |
| `NON_HIGHAM_SOURCE_REVIEW_REQUIRED` | 18 | the RandNLA family; numbered correspondence is to a non-Higham source |
| `REUSABLE_BLOCKED_BY:<module>` | 14 | deferred reusable rows (gate G2) |

## What the integrator must expect when applying this

`apply_tier_proposal.py` only ever writes a review copy of a tier manifest. It
refuses its own input, `docs/architecture/tiers.json`, and any other shared
`docs/architecture/` path. Applying the resulting rules to the real manifest is
integrator work, and it has two known consequences that this lane cannot and
must not perform itself:

1. `docs/architecture/layout-exceptions.json` becomes stale. `check_layout.py`
   fails on both *resolved* debt (the `unclassified_modules` list shrinks by up
   to 372 entries) and *new* debt (`mixed_modules` gains the 8 split-queue
   entries). The integrator must review the improvement and rerun
   `python tools/architecture/check_layout.py --write-baseline`.
2. Coverage is still partial afterwards (231 production modules remain
   unclassified — the 217 modules owned by other lanes plus the 12 deferred
   rows), so the physical-source-target gate stays unsatisfied, exactly as
   `TIERS.md` requires while any module is unclassified or mixed.

## Reproducing the checks

```console
python tools/architecture/lane_claude_classification/check_read_only_inventory.py
python tools/architecture/lane_claude_classification/check_classification_proposal.py --self-test
python tools/architecture/lane_claude_classification/check_classification_proposal.py --check
python tools/architecture/lane_claude_classification/apply_tier_proposal.py --self-test
python tools/architecture/lane_claude_classification/apply_tier_proposal.py \
    --output <lane-owned review copy>.json --report <report>.json
```
