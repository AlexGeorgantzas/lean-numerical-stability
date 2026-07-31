# Deterministic refresh appendix: this proposal against integrated `main`

This lane is deliberately frozen at base `6487fc33088523b8f27ecde9ad613515b78f9977`
and was **not** rebased. `origin/main` was fetched read-only and never merged.
Everything below is a `git show`/`git ls-tree` comparison against the fetched
ref; no file in this branch was regenerated from `main`.

- Frozen base: `6487fc33088523b8f27ecde9ad613515b78f9977`
- `origin/main` at fetch time: `48242807d4149210926eccf90a326d287fc0860c`
  ("docs(readme): refresh repository statistics")
- The frozen base is an ancestor of `origin/main`; `main` is **73 commits** ahead.

The integrator performs the final revalidation. This appendix exists so that
revalidation is a checklist, not a re-derivation.

## 1. The three `BLOCKLU_REFRESH_REQUIRED` rows

The lane contract states that the preserved BlockLU wave changes **imports but
not declaration bodies** in three frozen rows. That is now verified blob by blob.

### `NumStability.Algorithms.Ch14Problem142`

| | |
| --- | --- |
| base blob | `16c55f505385983fc9b10e426dc1b4e1040cd099` |
| `main` blob | `09680f5d1000524225c0329d574cf5e62e100545` |
| import change | `NumStability.Algorithms.LU.BlockLU` → `…LinearSystems.LU.BlockLU.FirstOrderModels`, `…Analysis.FirstOrder.FixedPrecision`, `…Analysis.MatrixNorms.EntrywiseMaximum` |
| non-import diff | **none** |
| lines | 581 → 583 (exactly the two added import lines) |

### `NumStability.Algorithms.MatrixInversionMethod2BInstance`

| | |
| --- | --- |
| base blob | `41754b827feb4c55fdfcec077ae05c97886e65ee` |
| `main` blob | `826109bcaf98b9f4787fb16bf993732c3e7bc0b8` |
| import change | `NumStability.Algorithms.LU.BlockLU` → `…LinearSystems.LU.BlockLU.FirstOrderModels`, `…Analysis.FirstOrder.FixedPrecision`, `…Analysis.MatrixNorms.EntrywiseMaximum`, `…Source.Higham.Chapter13.Section01.OperationModels` |
| non-import diff | **none** |
| lines | 798 → 801 (exactly the three added import lines) |

**Consequence for the proposal.** For these two rows the proposal's
`proposed_tier`, `confidence`, `proposed_canonical_family`, and `rationale` are
unaffected — the declarations, their names, visibilities, and counts are
identical. Only the `direct_project_imports` count moves: 3 → 5 for
`Ch14Problem142` and 5 → 8 for `MatrixInversionMethod2BInstance`.
`check_classification_proposal.py --check` recomputes that column from the
working tree, so running it against integrated `main` will report exactly those
two mismatches until the integrator refreshes the rows. That is the intended
signal, not a defect.

Note also that `MatrixInversionMethod2BInstance` now imports
`Source.Higham.Chapter13.Section01.OperationModels`, i.e. a **source-tier**
module. Its proposed tier is already `source`, so no dependency gate changes.

### `NumStability.Algorithms.HighamChapter9`

| | |
| --- | --- |
| base blob | `714585c4069df967e465ce4e1efd08c9f2302e6b` |
| `main` blob | `cfad22e520d9781aaf7cfcdd832d34db7307074c` |
| lines | 113,808 → **16** |

On `main` this module is no longer a giant owner: it is a declaration-free
historical facade importing ten `NumStability.Source.Higham.Chapter09.*`
destinations. Therefore, against integrated `main`:

- this proposal classifies the row `source` with destination
  `NumStability.Source.Higham.Chapter09` and action `plan_source_extraction`,
  which is exactly what the landed wave did. Against `main` that action is
  **already discharged**, and the row should be re-registered as
  `compatibility` — the tier the repository uses for an import-only historical
  forwarding path — rather than re-extracted;
- the split queue is unaffected: this proposal does not list `HighamChapter9`
  as mixed, because all 3,734 of its 3,735 public declarations carry numbered
  locators;
- every `CH09_BLOCKED_ON_BLOCKLU_INTEGRATION` row must be re-read against the
  landed destinations rather than the historical owner.

## 2. Frozen rows that moved on `main`

31 of the 386 frozen modules have a different blob on `main`; **none** were
removed. Grouped by cause:

| Group | Rows | Cause |
| --- | --- | --- |
| Chapter 9 candidates | 11 | the landed Chapter 9 physical split |
| BlockLU import retargeting | 2 | `Ch14Problem142`, `MatrixInversionMethod2BInstance` |
| Chapter 9 consumers retargeted | 8 | `Ch10Theorem108Componentwise`, `Ch14Cor147SourceDomainConstructor`, `Ch14Corollary147`, `Ch14GJEActualDoolittleAdapter`, `Cholesky.Higham1014SourceError`, `Cholesky.HighamMathiasFirstBreakdown`, `GaussJordan`, `HighamChapters1To9SourceClosure` |
| Chapter 11 candidates retargeted | 2 | `Cholesky.AasenMiddleGEPPCh11Counterexample`, `Cholesky.Higham11Chapter9BridgeClosure` |
| other giants and QR/LSQ neighbours | 8 | `HighamChapter8`, `HighamChapter10`, `MatrixInversion`, `StationaryIteration`, `RandNLA.LeastSquaresSketch`, `TestMatrices.Higham28Contracts`, `Higham28GaussianQRHaar`, `Higham28Stewart` |

The two Chapter 11 candidate changes are **exactly** the retargeting this
proposal predicted: each replaced `import NumStability.Algorithms.HighamChapter9`
with the ten landed `Source.Higham.Chapter09.*` imports. Nothing else in those
files changed.

**Consequence for the proposal.** The reviewed tier of every one of the 31 rows
is unchanged in content; what changes is the mechanical evidence
(`direct_project_imports`, and for `HighamChapter9` the declaration counts) and,
for `HighamChapter9`, the tier that should be *registered* (`compatibility`
instead of `source`, because the extraction has already happened). The dependency gates need one re-run:
`GaussJordan` is a deferred reusable row blocked by `HighamChapter8` and
`HighamChapter9`; with Chapter 9 split, its blocker set shrinks but does not
vanish, so it stays deferred until `HighamChapter8` is split too.

## 3. Chapter 9 contract reconciliation

`main` already contains a completed Chapter 9 split with **20** canonical
destinations under `NumStability/Source/Higham/Chapter09/`:

```text
Problems  Section01  Section02  Section03  Section04  Section05  Section06
Section08 Section10  Section11
CompletePivotSharpClosure  ComplexClosure  ComputedCorrection  DoolittleClosure
Theorem914Actual  Theorem914DiagDominant  Theorem914Primitive
Theorem97Classification  Theorem99Closure  Theorem99ComplexClosure
```

Cross-validation of this lane's extraction against that landed wave:

| Quantity | This contract (frozen base) | Landed on `main` |
| --- | --- | --- |
| declarations | 4,420 | 4,420 |
| authored command groups | 4,108 | 4,108 |
| private declarations | 28 | 28 |
| declaration-free historical facades | 11 | 11 |
| canonical destinations | 35 | 20 |

The first four agree exactly, which independently validates the extractor,
the command-group partition, and the private-declaration accounting. The
destination granularity differs: this contract splits the sectioned owner at all
53 of its declared seams (hence `Equation12`, `Equation13`, `Equation14`,
`Equation16`, `Theorem11.BohteBandOne`, `Theorem11.BohteGeneral`,
`Problem02`–`Problem14.*`, and the `Section06` sub-split), whereas the landed
wave keeps one destination per book section plus a single `Problems` module.

Two differences the integrator may want to keep from this contract:

1. **Canonical leaf names.** The landed satellites `Theorem914Actual`,
   `Theorem914DiagDominant`, and `Theorem914Primitive` are recorded as
   *noncanonical* legacy debt in `main`'s
   `docs/architecture/layout-exceptions.json` (three Chapter 9 entries). This
   contract names the same slices `Theorem14.Actual`,
   `Theorem14.DiagonallyDominant`, and `Theorem14.Primitive`, which satisfy the
   two-digit locator rule in `check_layout.py` and would remove that debt rather
   than baseline it.
2. **Explicit numbered destinations** for the growth-factor equations and the
   Bohte/Foster developments, which are currently folded into `Section04`,
   `Section06`, and `Problems`.

Neither is a defect in the landed wave; both are reviewed proposals. This lane
does not rebase onto them.

## 4. Chapter 11 contract status against `main`

`NumStability/Source/Higham/Chapter11/` on `main` still contains only
`Theorem07.lean`. The Chapter 11 split has **not** started, 64 of the 66
candidate files are byte-identical to the frozen base, and the remaining two
differ only by the Chapter 9 import retargeting described above. The Chapter 11
contract in `ch11/` therefore applies to integrated `main` essentially unchanged;
the required update is mechanical and already specified in `ch11/README.md`:
retarget the eleven recorded Chapter 9 dependency edges from
`NumStability.Algorithms.HighamChapter9` onto the Chapter 9 canonical
destinations that own the referenced declarations.

`ch09/ownership.tsv` in this branch maps each referenced declaration to a
destination in *this* contract's naming; against `main` the same mapping is
available from the landed Chapter 9 modules.

## 5. Integrator revalidation checklist

1. Re-run `check_read_only_inventory.py` on integrated `main`. Expect the
   inventory hash to still match (the tracked copy is frozen input, not a
   snapshot of `main`) and expect `HighamChapter9` to be reported as **already
   classified** once the landed split has registered it — that is the signal to
   re-tier that row.
2. Re-run `check_classification_proposal.py --check` on integrated `main`.
   Expect mismatches confined to the 31 rows in §2, and confirm the only
   semantic change is `HighamChapter9`'s tier.
3. Re-read the three `BLOCKLU_REFRESH_REQUIRED` rows using §1; two need only an
   import-count refresh.
4. Re-run `check_ch09_contract.py --mode pre` only if you intend to apply this
   contract's finer destination naming; otherwise treat `ch09/` as the
   frozen-base cross-validation record described in §3.
5. Re-run `check_ch11_contract.py --mode pre` on integrated `main` after
   retargeting the eleven Chapter 9 edges.
6. Re-baseline `docs/architecture/layout-exceptions.json` when the tier proposal
   is applied (`main` currently records 564 unclassified modules and 0 mixed;
   this proposal adds 4 `mixed` entries and removes up to 372 unclassified
   ones).
