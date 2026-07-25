# Phase 10D: Higham Chapter 2 leading-digit family map

Date: 2026-07-24

Base revision: `ce3811681e9a9a1c6d4a334b9928e12210232832`

This is the immutable pre-edit ownership and validation record for the Phase
10D leading-digit migration. It is committed before any production Lean file,
test, entry point, compatibility table, tier rule, or architecture exception is
changed. Later implementation departures belong in the build-evidence record,
not in this map.

## Scope and objective

Three flat `NumStability.Analysis` modules currently mix reusable probability
and equidistribution theory with exact Higham source correspondence:

1. `Analysis.LeadingDigitDistribution` contains the reusable logarithmic
   leading-digit distribution;
2. `Analysis.Problem2_11` combines a reusable decimal predicate, reusable
   finite empirical histograms, and the source-specific Problem 2.11 sample
   families; and
3. `Analysis.HighamChapter2PowerLeadingDigits` combines reusable AddCircle
   equidistribution, reusable decimal-power reductions, and one source-facing
   Section 2.7 conclusion.

Phase 10D moves every declaration to a semantic owner, adds declaration-free
family and source aggregates, preserves all declaration names and old import
surfaces, and removes the three flat files from active implementation use.

The exact destination tree is:

```text
NumStability/Analysis/
  Equidistribution.lean
  Equidistribution/
    AddCircle.lean
  LeadingDigits.lean
  LeadingDigits/
    Decimal.lean
    DecimalPowers.lean
    Empirical.lean
    LogarithmicDistribution.lean
NumStability/Source/Higham/Chapter02/
  Problem11.lean
  Section07.lean
  Section07/
    PowerLeadingDigits.lean
```

The historical paths remain import-only compatibility modules:

- `Analysis.LeadingDigitDistribution`;
- `Analysis.Problem2_11`; and
- `Analysis.HighamChapter2PowerLeadingDigits`.

## Frozen source inventory

| Historical owner | SHA-256 | Lines | Explicit declarations | Compiled owned constants |
| --- | --- | ---: | ---: | ---: |
| `Analysis.LeadingDigitDistribution` | `EAC62B50BA4EF28FCD4F1B6A4DDBB1411E434830918AF2A6EB83E1A6F414EB8D` | 299 | 23 | 26: 23 public, 3 internal |
| `Analysis.Problem2_11` | `FE2BF0D8E8F7E6A31DB095E3CE60F60CB7CEBF2AB8FE6AFA23A913C3AFEBEB85` | 273 | 33 | 77: 67 public, 10 internal |
| `Analysis.HighamChapter2PowerLeadingDigits` | `FB1E64A34A8F01DFF349A0517262B8C2F5F7A73B2DF58FEC99C455D41EDC5E0C` | 709 | 53 | 69: 53 public, 16 internal |

The compiled baseline is
`benchmark-results/architecture/phase10c-declarations.tsv`. Across the three
owners it records exactly 172 constants: 143 public and 29 generated internal
constants. There are no private constants.

Production importers at the base revision are deliberately small:

- `Analysis` imports all three historical modules;
- `Problem2_11` imports `LeadingDigitDistribution`; and
- `HighamChapter2PowerLeadingDigits` imports `Problem2_11`.

No production declaration outside this three-module family consumes their
declarations. Within the family, the compiled graph records four outgoing
references from the power-leading-digits owner to the logarithmic-distribution
owner and seven to the Problem 2.11 owner. The Problem 2.11 partitions are
declaration-independent of one another.

## Exact declaration ownership

### Logarithmic distribution

All 23 explicit declarations in
`Analysis.LeadingDigitDistribution` move intact to
`Analysis.LeadingDigits.LogarithmicDistribution`.

The compiled population is exact at 26 constants: 23 public declarations and
three generated internal constants. Its outgoing compiled graph contains 43
signature edges and 59 body/proof edges.

### Problem 2.11 decimal predicate

Source lines 47--99 of `Analysis.Problem2_11` move to
`Analysis.LeadingDigits.Decimal`:

- `problem2_11_decimalLeadingDigit`;
- `problem2_11_decimalLeadingDigit_digit_between`;
- `problem2_11_decimalLeadingDigit_abs_pos`;
- `problem2_11_decimalLeadingDigit_normalized_bin`; and
- `problem2_11_decimalLeadingDigit_exists_scaled_mem_one_ten`.

The compiled population is exact at six constants: five public and one
generated internal constant. Its outgoing graph contains three signature edges
and seven body/proof edges. The historical `problem2_11` declaration prefix is
retained for API compatibility even though the owner is now reusable.

`Mathlib.Data.Real.Basic` is the direct foundation import required by the
extracted block.

### Problem 2.11 empirical histograms

Source lines 177--269 of `Analysis.Problem2_11` move to
`Analysis.LeadingDigits.Empirical`:

- `problem2_11_digitCount` and its bound;
- `problem2_11_digitFrequency` and its bounds;
- the count and frequency sum theorems; and
- `problem2_11_empiricalDigitProbability` and its projection bounds.

The compiled population is exact at 14 constants: 12 public and two generated
internal constants. Its outgoing graph contains 17 signature edges and 25
body/proof edges. Its only project import is
`NumStability.Analysis.FiniteProbability`.

### Problem 2.11 source samples

Source lines 27--45 and 101--175 of `Analysis.Problem2_11` move to
`Source.Higham.Chapter02.Problem11`:

- `problem2_11EmpiricalSource` and its exhaustive theorem;
- the `problem2_11_powerSample` API; and
- the `problem2_11_factorialSample` API.

The compiled population is exact at 57 constants: 50 public and seven
generated internal constants, including the inductive recursor, constructors,
derived instances, and size machinery. Its outgoing graph contains 111
signature edges and 135 body/proof edges.

The owner directly imports `Mathlib.Data.Nat.Factorial.Basic` and
`Mathlib.Data.Real.Basic`. As the complete canonical Problem 2.11 locator, it
also re-exports `Analysis.LeadingDigits.Decimal`,
`Analysis.LeadingDigits.Empirical`, and
`Analysis.LeadingDigits.LogarithmicDistribution`. Those three reusable imports
preserve the former complete `Analysis.Problem2_11` import surface and reflect
the problem's classifier, empirical distribution, and comparison law.

### AddCircle equidistribution

Source lines 18--535 of
`Analysis.HighamChapter2PowerLeadingDigits` move to
`Analysis.Equidistribution.AddCircle`. The block runs from the positive-period
`Fact` instance through `orbit_halfOpenArc_frequency_tendsto` and contains the
finite uniform probability, empirical orbit measures, Fourier convergence,
Haar comparison, ball frequencies, and half-open-arc frequencies.

The compiled population is exact at 41 constants: 34 public and seven generated
internal constants. Its outgoing graph contains 39 signature edges and 90
body/proof edges.

The direct Mathlib imports are:

- `Mathlib.Algebra.Field.GeomSum`;
- `Mathlib.Analysis.Asymptotics.Lemmas`;
- `Mathlib.Analysis.Fourier.AddCircle`;
- `Mathlib.MeasureTheory.Group.AddCircle`;
- `Mathlib.MeasureTheory.Measure.Portmanteau`; and
- `Mathlib.Probability.UniformOn`.

The old `Mathlib.MeasureTheory.Measure.Prokhorov` import is unused by this block
and is not retained.

### Decimal powers

Declaration lines 541--674 of
`Analysis.HighamChapter2PowerLeadingDigits` move to
`Analysis.LeadingDigits.DecimalPowers`. The block starts with
`IsRationalPowerOfTen` and ends with
`orbit_mem_decimalDigitArc_iff`.

The compiled population is exact at 27 constants: 18 public and nine generated
internal constants. Its outgoing graph contains 22 signature edges and 43
body/proof edges.

The module directly imports:

- `Mathlib.Analysis.SpecialFunctions.Log.Base`;
- `Analysis.Equidistribution.AddCircle`;
- `Analysis.LeadingDigits.Decimal`; and
- `Analysis.LeadingDigits.LogarithmicDistribution`.

It must not import either historical Problem 2.11 path or any `Source` module.

### Section 2.7 source conclusion

The source-facing docstring and final declaration at lines 676--707,
`higham2_power_decimalLeadingDigit_frequency_tendsto`, moves to
`Source.Higham.Chapter02.Section07.PowerLeadingDigits`.

This is one public compiled theorem with three signature edges and 13 body/proof
edges. Its sole project import is
`Analysis.LeadingDigits.DecimalPowers`.

## Import-surface preservation

The three old paths preserve their complete former surfaces, not merely their
owned declarations:

| Historical path | Direct canonical target or targets |
| --- | --- |
| `Analysis.LeadingDigitDistribution` | `Analysis.LeadingDigits.LogarithmicDistribution` |
| `Analysis.Problem2_11` | `Source.Higham.Chapter02.Problem11` |
| `Analysis.HighamChapter2PowerLeadingDigits` | `Source.Higham.Chapter02.Problem11` and `Source.Higham.Chapter02.Section07.PowerLeadingDigits` |

The second row is one import because canonical Problem 11 re-exports the three
reusable parts visible from the old module. The third row needs two imports:
the canonical Section 2.7 leaf supplies the power/equidistribution surface, and
canonical Problem 11 preserves every declaration formerly exposed through the
old file's `Problem2_11` import.

No canonical production module may import any of the three historical paths.
`Analysis` replaces them with the reusable `Analysis.Equidistribution` and
`Analysis.LeadingDigits` aggregates. `All` and the root remain complete because
they also import the `Source` tree.

## Aggregates, tests, and manifests

Three new declaration-free, sorted aggregates are required:

- `Analysis.Equidistribution` over `AddCircle`;
- `Analysis.LeadingDigits` over `Decimal`, `DecimalPowers`, `Empirical`, and
  `LogarithmicDistribution`; and
- `Source.Higham.Chapter02.Section07` over `PowerLeadingDigits`.

The Chapter 2 aggregate adds `Problem11` and `Section07`.

Thirteen isolated import tests cover all ten new production modules and the
three historical wrappers. Existing `Analysis`, Chapter 2, Source, endpoint,
compatibility, all-library, and root smoke tests gain representative checks for
the reusable and source surfaces. Every new test is registered from
`NumStabilityTest.lean`.

The tier manifest records:

- the three aggregates as `aggregate` and the two analysis aggregates as
  reusable entry points;
- `AddCircle`, `Decimal`, `DecimalPowers`, `Empirical`, and
  `LogarithmicDistribution` as `reusable`;
- `Problem11` and `Section07.PowerLeadingDigits` as `source`; and
- all three old paths as `compatibility`.

The compatibility inventory is expected to move from 94 wrappers and 192
direct targets to 97 wrappers and 196 direct targets. The layout exception
inventory adds complete-aggregate contracts for the three new aggregates and
removes all three old paths from unclassified and noncanonical debt.

## Expected structural ratchet

Relative to the Phase 10C base, the expected pre-measurement ratchet is:

| Measure | Phase 10C | Expected Phase 10D |
| --- | ---: | ---: |
| Production modules | 967 | 977 |
| Classified modules | 349 | 362 |
| Unclassified modules | 618 | 615 |
| Aggregate modules | 67 | 70 |
| Compatibility modules | 94 | 97 |
| Reusable modules | 51 | 56 |
| Source modules | 130 | 132 |
| Missing module docstrings | 219 | 218 |
| Noncanonical legacy modules | 411 | 408 |

Exact source lines, import edges, classification percentage, and fan-out counts
are deferred to the generated post-edit baseline.

## Required proof-preservation audit

After extraction, compare the Phase 10C compiled TSV with a fresh Phase 10D
extraction. The audit must establish:

1. exactly 172 constants before and after across the seven new declaration
   owners;
2. the exact names, kinds, visibility, types, and bodies/proofs after
   normalizing only the seven recorded owner moves;
3. exact per-owner outgoing and incident signature/body edge sets;
4. no added, removed, duplicated, or accidentally re-owned declaration; and
5. an unchanged global declaration and union dependency graph.

## Required gates

The candidate worktree must pass, in order:

1. source-region ownership, import-surface, and wrapper-shape audits;
2. all thirteen isolated canonical and compatibility tests;
3. the changed aggregate and entry-point smokes;
4. `python tools/architecture/check_layout.py`;
5. `python tools/architecture/check_compatibility.py`;
6. `python tools/architecture/check_provenance.py`;
7. `lake test`;
8. `lake build NumStability NumStabilityTest`;
9. `lake env lean examples/LibraryLookup.lean`;
10. compiled declaration/dependency extraction and normalized ownership audit;
11. architecture baseline generation and strict ratchet comparison; and
12. the same relevant gates from the clean committed implementation revision.

The generated baseline pair and build-evidence record are separate later
commits, following the established clean-capture workflow.
