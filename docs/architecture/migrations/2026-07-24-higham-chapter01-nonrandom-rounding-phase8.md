# Phase 8: Higham Chapter 1 nonrandom rounding

Date: 2026-07-24

Execution base: `e27c25af3d975dfc9e9032e94b6dd06cfe057a42`

This record is the authoritative pre-edit ownership map for Phase 8. Source
line intervals below are inclusive and refer to the immutable execution base.
The tracked blob identifiers, old owners, declaration anchors, and exact body
regions identify the source that moves. Declaration names, types, bodies,
visibility, and the namespace `NumStability` must be preserved.

## Scope and completion rule

The historical `Analysis.NonrandomRounding` family formalizes the Kahan
nonrandom-rounding example from Higham Section 1.17. This phase moves its five
declaration-bearing owners into a semantic source hierarchy rooted at
`Source.Higham.Chapter01.Section17`, leaves all six historical paths as exact
import-only compatibility wrappers, and rewrites the broad `Analysis` entry
point to the canonical aggregate while preserving its historical re-export
surface.

The migration is complete only when:

1. every declaration is owned by one canonical Section 1.17 leaf;
2. `Source.Higham.Chapter01.Section17` and `Source.Higham.Chapter01` are
   documented, sorted, declaration-free aggregates;
3. no production module imports an old `Analysis.NonrandomRounding` path;
4. each old path preserves its historical transitive declaration surface;
5. all 164 public declarations and all 13 source-written private declaration
   blocks are preserved; and
6. isolated canonical, aggregate, and old-only import tests plus the repository
   architecture gates pass.

## Immutable source inventory

The five historical declaration owners contain 147 source-written
declarations: 134 public and 13 private. Their compiled environments contain
242 constants: 164 public, 65 internal, and 13 private.

| Historical owner | Git blob | Lines | Exact declaration-body region | Source declarations | Compiled constants | First declaration | Last declaration |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- |
| `Analysis.NonrandomRounding.Core` | `30e2524bf38c2b287dff7389df73132747752461` | 526 | 27--520 | 40 public | 70 public + 38 internal | `kahanHornerNumerator` | `ieeeDoubleKahanRationalFunction_eq_errorEval_of_finiteNormal` |
| `Analysis.NonrandomRounding.SourceInterval` | `1a013c98c84a69b6833dbf4240bb014261db5de4` | 972 | 9--970 | 11 public + 8 private | 11 public + 8 private + 2 internal | private `kahanIeeeDoubleUnitRoundoff_lt_one_thousandth`; first public `ieeeDouble_finiteNormalRange_of_abs_between_one_thousand` | `ieeeDoubleKahanRationalFunction_eq_errorEval_on_source_interval` |
| `Analysis.NonrandomRounding.GridVariation` | `a0bafb775e659d84fe4a4767b1c12f7a25841072` | 622 | 10--620 | 40 public | 40 public + 23 internal | `kahanHornerNumerator_eq_poly` | `ieeeDoubleKahanRationalFunction_175_289_error_spread_gt_of_output_spread` |
| `Analysis.NonrandomRounding.StoredGrid` | `c4ab2f0a2540cf56b69f37758ac64346b92015ab` | 1,755 | 12--1,753 | 36 public + 5 private | 36 public + 5 private | `ieeeDoubleKahanStoredGridPoint` | `ieeeDoubleKahanStoredGridRationalFunction_289_eq` |
| `Analysis.NonrandomRounding.Conclusions` | `78f96e1413ae4bc9e6c82aa31adaafe0b5a53df7` | 115 | 11--113 | 7 public | 7 public + 2 internal | `ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_of_output_spread` | `not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid` |
| **Total** |  | **3,990** |  | **134 public + 13 private** | **164 public + 65 internal + 13 private** |  |  |

The encompassing namespace/scaffold regions are lines 14--526 for `Core`,
3--972 for `SourceInterval`, 3--622 for `GridVariation`, 3--1,755 for
`StoredGrid`, and 3--115 for `Conclusions`. In `Core`, the
`noncomputable section IeeeDoubleHorner` scaffold occupies lines 213--522.
Canonical files may replace only file headers, direct imports, module docs, and
the orphan trailing comment. The enclosing `namespace NumStability` and
`noncomputable section IeeeDoubleHorner` scaffolds are preserved semantically
and verbatim; the declaration bodies above remain the authoritative
preservation target.

The source declaration-kind inventory is:

- `Core`: 31 definitions, six theorems, and three structures;
- `SourceInterval`: 19 theorems;
- `GridVariation`: two definitions and 38 theorems;
- `StoredGrid`: two definitions and 39 theorems; and
- `Conclusions`: one definition and six theorems.

The immutable Phase 6 compiled-declaration TSV supplies the compiled counts.
Phase 7 did not change any of these five blobs.

## Exact old-to-new ownership map

| Historical owner | Canonical owner |
| --- | --- |
| `Analysis.NonrandomRounding.Core` | `Source.Higham.Chapter01.Section17.HornerEvaluation` |
| `Analysis.NonrandomRounding.SourceInterval` | `Source.Higham.Chapter01.Section17.SourceInterval` |
| `Analysis.NonrandomRounding.GridVariation` | `Source.Higham.Chapter01.Section17.GridVariation` |
| `Analysis.NonrandomRounding.StoredGrid` | `Source.Higham.Chapter01.Section17.StoredGrid` |
| `Analysis.NonrandomRounding.Conclusions` | `Source.Higham.Chapter01.Section17.ErrorSpread` |

The semantic dependency chain is:

`HornerEvaluation` -> `SourceInterval` -> `GridVariation` -> `StoredGrid` ->
`ErrorSpread`.

Here `A -> B` means that `B` directly imports `A`. The Section 1.17 aggregate
imports the five canonical leaves; the Chapter 1 aggregate imports Section
1.17; `Source.Higham` imports Chapter 1.

## Historical transitive surfaces

At the execution base, `Core` directly imports:

- `Mathlib.Data.Real.Basic`;
- `Mathlib.Tactic.FieldSimp`;
- `Mathlib.Tactic.FinCases`;
- `Mathlib.Tactic.Linarith`;
- `Mathlib.Tactic.NormNum`;
- `Mathlib.Tactic.Ring`;
- `NumStability.Analysis.FloatingPointArithmetic`; and
- `NumStability.FloatingPoint.Model`.

The remaining historical chain is `Core` -> `SourceInterval` ->
`GridVariation` -> `StoredGrid` -> `Conclusions`, and the historical umbrella
imports `Conclusions`. The accumulated public compiled surfaces contain 70,
81, 121, 157, and 164 declarations respectively; the umbrella also exposes
all 164.

Each old path therefore becomes a single canonical import-only wrapper:

| Compatibility wrapper | Direct canonical target |
| --- | --- |
| `Analysis.NonrandomRounding` | `Source.Higham.Chapter01.Section17` |
| `Analysis.NonrandomRounding.Core` | `Source.Higham.Chapter01.Section17.HornerEvaluation` |
| `Analysis.NonrandomRounding.SourceInterval` | `Source.Higham.Chapter01.Section17.SourceInterval` |
| `Analysis.NonrandomRounding.GridVariation` | `Source.Higham.Chapter01.Section17.GridVariation` |
| `Analysis.NonrandomRounding.StoredGrid` | `Source.Higham.Chapter01.Section17.StoredGrid` |
| `Analysis.NonrandomRounding.Conclusions` | `Source.Higham.Chapter01.Section17.ErrorSpread` |

Because the canonical leaves retain the same dependency chain, each one-target
wrapper preserves the corresponding accumulated surface without importing a
broader compatibility path. The only production consumer outside this family
is `NumStability.Analysis`, which imports old `Conclusions`; this import is
replaced by canonical `Source.Higham.Chapter01.Section17`, while
`Source.Higham` gains the canonical Chapter 1 aggregate. The direct canonical
import from `Analysis` is a temporary historical re-export that preserves all
164 declarations already available from `import NumStability.Analysis`; it may
be removed only in an explicitly breaking release.

## Private and generated declaration audit

Moving modules changes the `_private.<module>.0...` prefixes of the eight
private `SourceInterval` declarations and five private `StoredGrid`
declarations. Their 13 source blocks must compare byte-for-byte after UTF-8/LF
normalization. Compiled private owner prefixes may be normalized only for the
serialized compiled comparison wherever `_private.<old owner>.0` occurs in a
name, type, or body; no other normalization is permitted.

The eight `SourceInterval` private anchors are
`kahanIeeeDoubleUnitRoundoff_lt_one_thousandth`,
`kahanIeeeDouble_delta_bounds`,
`ieeeDouble_finiteNormalRange_of_pos_between_one_thousand`,
`mul_interval_mono`, `kahan_source_interval_x_bounds`,
`kahan_source_interval_ieeeDouble_finiteNormalRange`,
`kahan_source_interval_numerator_m0_normal`, and
`kahan_source_interval_denominator_s0_normal`. The five `StoredGrid` private
anchors are
`ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_one_adjacent`,
`ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_adjacent`,
`ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent`,
`ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_tie_even`, and
`ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_tie_odd`.

After that narrowly defined prefix normalization, all 164 public and 65
internal names, kinds, types, bodies, visibility, and unique ownership must
match exactly. The 13 source-private blocks must remain byte-identical. Unlike
a file split, this one-file-to-one-file move is expected to preserve the total
compiled count of 242 and produce no generated-helper delta; any difference
requires an explicit investigation and record update.

## Planned isolated import coverage

The migration adds isolated tests for:

- each of the five canonical declaration leaves;
- the Section 1.17 and Chapter 1 aggregates;
- all six old-only compatibility imports; and
- the `Source.Higham` and shared entry-point surfaces affected by the move.

The two legacy top-level `NonrandomRoundingCanonical` and
`NonrandomRoundingMigration` test modules are replaced by the structured
canonical/compatibility test layout, so the test tree follows the production
hierarchy without retaining another naming exception.

## Measured migration result

The completed candidate implements the ownership map above without a
declaration split. The five canonical leaves contain the exact historical
declaration bodies, and the two new entry points are documented, sorted,
declaration-free aggregates. All six historical modules are now one-import
compatibility wrappers, and no production module imports one of those old
paths. `NumStability.Analysis` intentionally imports the canonical Section
1.17 aggregate to retain its historical transitive public surface.

An isolated audit compiled the five immutable execution-base modules and the
five canonical modules independently. Both environments contain exactly 242
owned constants with the same per-owner distribution: 164 public, 65
internal, and 13 private. After normalizing only the five owner paths and the
two allowed `_private` owner prefixes, the sorted inventories have zero
missing, added, or mismatched constants across names, owners, declaration
kinds, visibility, normalized type structural hashes, and normalized
body/proof structural hashes. There is no generated-helper delta.

The source audit counted the same 147 explicit declaration blocks, including
all 13 private blocks. Four canonical files are byte-identical to their
immutable owners from `namespace NumStability` onward. The fifth differs only
by removal of the orphan trailing module-section comment identified in the
pre-edit inventory, so every declaration block is byte-identical.

Thirteen isolated import tests cover the five declaration leaves, both
canonical aggregates, and all six old-only compatibility imports. Shared
`Analysis`, `All`, `Higham`, root, `Source`, `Source.Higham`, canonical-source,
and migration smokes exercise the changed entry-point surfaces. The final
candidate passed `lake test`, the combined production-and-test build, the
library-lookup example, baseline generation and reproduction, and every
architecture gate listed below.

## Architecture and validation gates

The new canonical leaves and aggregates are classified at creation; all six
old paths are classified as compatibility wrappers with exact direct targets.
Module-doc and naming-exception manifests, complete-aggregate coverage, import
ceilings, source-coverage ledgers, README/library examples, the test registry,
and the baseline index are updated in the same phase.

Validation requires targeted leaf/wrapper builds, all registered import tests,
`lake test`, `lake build NumStability NumStabilityTest`, the library lookup
example, layout/compatibility/provenance/source-boundary checks, aggregate
ordering, baseline generation and clean reproduction, JSON validation,
`git diff --check`, and a final clean-checkout rerun.
