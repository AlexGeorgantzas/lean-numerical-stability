# B0005 / R03 exact-C0002 singleton overlap and consumer review

Authority: `primary-human`
Planning operator: `codex-local`
Checkpoint/code preimage: C0002 `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`
Branch lifecycle at this review: `planned`; no ref, worktree, activation tip, delivery, or integration exists.

This is a singleton review for M03/R03. R07 is compared only to decide whether
it may be co-selected. It is not selected, allocated, projected, requested,
branched, or activated by this review.

## Reproducible inputs

| Input | SHA-256 |
| --- | --- |
| `checkpoints/C0002-inventory.tsv` | `BB5AE8029CC3DC547BA1E4C8B581BA11948E527810AC29F0EBE8E1CC5D81BF02` |
| `baselines/C0002-combined.json` | `0A062C8EB887E34907BF15F9423EDA6E7FB3DD032495B6DE98A7ED8538A32485` |
| `benchmark-results/C0002-combined.tsv` | `E03DB7A24886AD0B45C7371FE30ACE3AD135B3C4CC9866D65186753CD14FAD4C` |
| `projections/P0005.tsv.gz` | `9D221D2DF34D79D67799F2F4F3ED16D74365A7EEBBDB372700EF574242F16D53` |
| normalized C0002 production source tree | `C4CAF90EE1CB6B58667CD79C45DAE34D1E8529990883E0254F4DB52D22B5D032` |
| `branches/B0005-consumers.tsv` | `3AFD072408026219BDB07D1004E3768B27576AEB88AFBC8312FA9D9467155400` |

The exact selector query is `phase_scope == in_scope && wave_id == R03` over
the pinned inventory. It returns 47 owners. The corresponding sorted LF TSV
with header `module<TAB>path` hashes to
`176BC214ABAE4B9CC2E9822E3177033213C4BD730D0057FBE8BAB524412C6B3A`.
The audit-only R07 query returns 45 owners; the same representation hashes to
`62DE8B696298B5AE913FD10DC7736A1414E3B903C2652D6E883584FABEBCF715`.

The exact R03 format-2 projection vector is 2,389 declarations (1,987 public,
398 private, and 4 internal), 28,180 incident signature edges, and 42,404 incident body/proof
edges. The audit-only R07 vector is 194 declarations (150 public, 44 private),
243 signature edges, and 752 body/proof edges.

## Ordered R03/R07 comparison

The full machine evidence is in `B0005-consumers.tsv`. Its 47
`owner_reachability` rows each contain the ordered source owner, target owner,
shortest exact-C0002 import witness, and distance.

| Fact | Exact result |
| --- | ---: |
| R03 selected owners | 47 |
| R07 audit-only owners | 45 |
| direct owner import edges, either direction | 0 |
| R03 -> R07 transitive owner pairs | 24 |
| R07 -> R03 transitive owner pairs | 23 |
| declaration signature edges, either direction | 0 |
| declaration body/proof edges, either direction | 0 |
| shared outside dependent declarations | 0 |
| common direct project dependencies | 7 |
| shared direct outside production consumers | 5 |

Every R03 -> R07 pair targets
`NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. The exact 24 R03
source owners are:

```text
NumStability.Algorithms.Ch5DerivativeError
NumStability.Algorithms.Ch5SourceClosure
NumStability.Algorithms.Higham5FastPolynomialEvaluation
NumStability.Algorithms.Higham726Rump
NumStability.Algorithms.HighamChapter8
NumStability.Algorithms.HighamChapters1To9SourceClosure
NumStability.Algorithms.Horner
NumStability.Algorithms.KahanAbsolute
NumStability.Algorithms.LU.Doolittle
NumStability.Algorithms.LinearSystems.IterativeRefinement.Core
NumStability.Algorithms.LinearSystems.LU.Doolittle.BackwardError
NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
NumStability.Algorithms.LinearSystems.LU.Doolittle.Budgets
NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates
NumStability.Algorithms.LinearSystems.LU.Doolittle.RoundedEntries
NumStability.Analysis.AccuracyTests
NumStability.Analysis.HighamChapter7
NumStability.Analysis.IncreasingPrecision
NumStability.Analysis.InstabilityWithoutCancellation
NumStability.Source.Higham.Chapter06.Theorem05.DistanceToSingularity.Chapter07Equation26
NumStability.Source.Higham.Chapter08.Equation15.GlobalEnvelopeCounterexample.RawCube
NumStability.Source.Higham.Chapter12.IterativeRefinement
NumStability.Source.Higham.Chapter12.IterativeRefinement.Chapter12Bounds
NumStability.Source.Higham.Chapter12.IterativeRefinement.LegacyChapter11Surface
```

Every R07 -> R03 pair targets `NumStability.FloatingPoint.Model`. The exact 23
R07 source owners are:

```text
NumStability.Algorithms.MatrixPowers
NumStability.Algorithms.MatrixPowersComplex
NumStability.Algorithms.MatrixPowersJordan
NumStability.Algorithms.MatrixPowersLp
NumStability.Algorithms.MatrixPowersLpJordan
NumStability.Algorithms.MatrixPowersPseudospectral
NumStability.Algorithms.MatrixPowersPseudospectralCriterion
NumStability.Algorithms.MatrixPowersSpectral
NumStability.Analysis.DunfordResidue
NumStability.Analysis.MatrixPowersBaiDemmelGu
NumStability.Analysis.MatrixPowersBaiDemmelGuDistance
NumStability.Analysis.MatrixPowersGautschi
NumStability.Analysis.MatrixPowersKreiss
NumStability.Analysis.MatrixPowersKreissSpijker
NumStability.Analysis.MatrixPowersLp185Primary
NumStability.Analysis.MatrixPowersSpijkerClosure
NumStability.Analysis.MatrixPowersSpijkerPlanar
NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis
NumStability.Analysis.MatrixPowersSpijkerRational
NumStability.Analysis.PseudospectralLowerBound
NumStability.Analysis.PseudospectralPowerBound
NumStability.Analysis.PseudospectralResolvent
NumStability.Analysis.ResolventFunctionalCalculus
```

A normalized four-column LF extract of all 47 witnesses, with header
`direction<TAB>source_owner<TAB>target_owner<TAB>shortest_import_witness`,
hashes to `F984F7D2D2ADBF936D6825FB5C2EC91ACF49E2EEE780F6502FF5D966128C76FA`.

## Common dependencies and direct-both consumers

The seven common direct project dependencies are exactly:

```text
NumStability.Algorithms.MatVec
NumStability.Algorithms.PolynomialEvaluation.MatrixNorms
NumStability.Analysis.Conditioning.DistanceToSingularity
NumStability.Analysis.MatrixAlgebra
NumStability.Analysis.MatrixNorms.Basic
NumStability.Analysis.MatrixNorms.SpectralRadius
NumStability.Analysis.Rounding
```

The five outside consumers are all **direct-both** consumers: each file
directly imports at least one R03 owner and at least one R07 owner. The TSV
records every imported owner, not merely a count.

| Outside consumer | Direct R03 owners | Direct R07 owners |
| --- | ---: | ---: |
| `NumStability.Algorithms` | 12 | 36 |
| `NumStability.Analysis` | 21 | 15 |
| `NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.TraceMGF.LeverageScore` | 1 | 1 |
| `NumStability.Source.DrineasMahoney.RandNLA2016.Equation02.SpectralApproximation.ElementwiseSpectral` | 1 | 1 |
| `NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.LeverageTraceMGF` | 1 | 1 |

The three 1/1 consumers directly import `NumStability.FloatingPoint.Model` and
`NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`.

## R03 consumer surface

`B0005-consumers.tsv` contains one `r03_module_consumer` row for every outside
production module reaching an R03 owner. It records 492 direct consumers and
1,566 transitive-only consumers, 2,058 distinct outside consumers in total.
The direct files contain 669 selected-owner import occurrences.

| Consumer disposition | Direct | Direct or transitive |
| --- | ---: | ---: |
| already complete | 457 | 1,783 |
| I01 | 2 | 11 |
| R04 | 5 | 18 |
| R05 | 16 | 46 |
| R06 | 2 | 55 |
| R07 | 0 | 23 |
| R08 | 7 | 45 |
| R09 | 0 | 59 |
| R10 | 3 | 18 |

Each row contains all direct selected-owner imports and one shortest witness to
the selected set. Transitive consumers are protected-consumer/test evidence;
they are not patch paths unless their file also receives a direct token or
control change.

The TSV also has 14,287 `r03_external_declaration_consumer` rows, one per
outside declaration with a format-2 edge into an R03 declaration. Exact totals
are:

| Edge class | Edges | Outside declarations | Outside modules | R03 target declarations |
| --- | ---: | ---: | ---: | ---: |
| signature | 19,706 | 13,908 | 543 | 33 |
| body/proof | 23,514 | 13,747 | 557 | 97 |
| union | - | 14,287 | 561 | 97 |

The edge-bearing declarations are projection and protected-consumer evidence,
not automatic shared-file patch paths.

## Integrator-owned request evidence

The inventory marks 24 owners with `rename`. Those owners have nine direct
outside production consumers containing 29 old-import occurrences. Together
with four global controls, this gives an audit-only lower bound of exactly 13
paths. Every preimage below is from exact C0002.

| Path | Blob OID | Preimage SHA-256 |
| --- | --- | --- |
| `NumStability/Algorithms.lean` | `e6dbe0d48cf1f72a59d49267def0ad9b56ca980f` | `1B37ECE4668D38454708C93ED5F6323AA9AEF599E908968D0894A1F0EBA921A2` |
| `NumStability/Algorithms/Ch10Theorem107FailureVacuity.lean` | `af2f6f5200451ae78f5ec90f43649eab5edc2eb9` | `47A1833A3646693DE2C78173BCF5DE9CF674123165EB566E82E08854770A871A` |
| `NumStability/Algorithms/IterativeRefinement.lean` | `7e9ef8d7d5cb4cf8807168787e1985b52155b8cd` | `B3925D157F21CAF436C76D9DA4B7303ABFA03B871E452B61C46FB6B4CE676E6F` |
| `NumStability/Analysis.lean` | `ea2218f1f7446e828c1bcbbe8bf5fa5356bc8011` | `67CE03FA396D21AA498961D331FB9AEC32DD95D7F2DA70C87BDE4093DD6F3A32` |
| `NumStability/Analysis/Problem2_26.lean` | `6df30ed45b13ab49d4d0209b421dc78ef84691b8` | `2450CA702FE4CAC4257129F48063E700E36D4154DB6AAA3E597E9B1F5AD4BCBB` |
| `NumStability/Source/Higham/Chapter06/Theorem05/DistanceToSingularity/All.lean` | `a71038c7d1796ee27191d4d91e428d167404efe9` | `432B10FDD9DB278C60C395AA0A1D6DA0163F012DD282FDFC0916A90504B0CF0B` |
| `NumStability/Source/Higham/Chapter10/Theorem07/FailureVacuity/Vacuity.lean` | `24e33850bea9b90f87cd445fdadf1bc09100db5f` | `9404E435E3D8577C28B03D4411EE8CE600843B5D34761DCBFA957CFA754A7939` |
| `NumStability/Source/Higham/Chapter12/IterativeRefinement/All.lean` | `f8ad5ab557ccb5d115574b21c8f92fa0ec2548da` | `282BF0A6B5A72D96F1A7D46705E5C7746D3D86F0D0627573F70B29EB8E59C1ED` |
| `NumStability/Source/Higham/Chapter27/SoftwareEnvironment.lean` | `90239ca919d6686c3e8c3a5e05e4af523846a8eb` | `78986E2072E8510D87CCF89808DDAA7FEAFD7CBA49CFEBA7559C2E1819D955C7` |
| `NumStabilityTest.lean` | `b1171d36717c80838f4ba9590c12a1838f390d5d` | `92678054B0C019CD51812F65DCB6F310A2EB725054B8B90CE11A1369D179E488` |
| `docs/architecture/COMPATIBILITY.md` | `384fd0f282c898b0461287aa556c0f008de822b0` | `EE2E5EFFACDE52C7B0E4E185D506BA6A35EABB72459DF3F6D179F571E28C4658` |
| `docs/architecture/layout-exceptions.json` | `8d5e4da300f3b37545f22a363eb39d338953d29b` | `1F746E55E28374702CCDB7355A11ECEB8E0AEF44BB86F751F86C62B8AF059725` |
| `docs/architecture/tiers.json` | `879c545fcf270fdc4eb23ad38722892a51d85163` | `D85BB4F2A8A53C038D31241ED5FA77962E5783FB96B88970AFE2B17F080FB889` |

The sorted newline-delimited 13-path list hashes to
`CE3FEC6A24D94031D9A70F5FE002FE89276612060B17E535541A2FEAF8DAB7E1`.

The 13-path set is lower-bound evidence, not the frozen request. The reviewed
module routes classify 36 owners for `migrate`, `rename`, `split`, or
`aggregate_cleanup`; those owners have exactly 117 direct outside consumer
paths containing 152 old-to-new import replacements. R0005 adopts all 117
consumer paths plus the four global controls, for an exact 121-path request
whose sorted path-list SHA-256 is
`22D7FB62215BA50D4C9E5E83254B3196C2920CC7B8BF2A835201D7730694E3FB`.
Historical wrappers remain, but these frozen direct consumers retarget to the
reviewed canonical routes rather than depending on compatibility fallbacks.

Workers may not edit any request path. R0005 carries every path's
C0002 blob OID, preimage SHA-256, postimage SHA-256, and every exact old-to-new
import replacement. Every aggregate or entry-point path in this request is
integrator-owned and manifested.

## Replay

From a checkout containing the planning controls and the ignored raw graph:

```powershell
git diff --exit-code 9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd -- NumStability NumStability.lean
Get-FileHash -Algorithm SHA256 docs/architecture/phases/2026-08-repository-reorganization-completion/checkpoints/C0002-inventory.tsv
Get-FileHash -Algorithm SHA256 docs/architecture/phases/2026-08-repository-reorganization-completion/baselines/C0002-combined.json
Get-FileHash -Algorithm SHA256 benchmark-results/C0002-combined.tsv
Get-FileHash -Algorithm SHA256 docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0005-consumers.tsv
```

The pinned raw graph was generated at C0002 while holding Windows named mutex
`Local\lean-reorganization-2026-08`, as recorded by `C0002-gates.md`. Reading
that immutable graph and scanning source imports require no Lean operation. Any
replay that regenerates a declaration graph, projection, baseline, or other
Lean-derived artifact must acquire the same mutex before starting and hold it
through extraction and verification.

Recompute module imports with the comment-aware scanner used by
`tools/architecture/generate_baseline.py`; select exact inventory wave sets;
use breadth-first traversal in source import order for shortest witnesses; and
parse format-2 `declaration` and `edge` rows for declaration consumers. Emit
the TSV header and records in ascending full-column tuple order with UTF-8 LF
line endings. Required record counts are 47 `owner_reachability`, 7
`common_direct_project_dependency`, 5 `shared_direct_outside_consumer`, 2,058
`r03_module_consumer`, and 14,287 `r03_external_declaration_consumer`, for
16,404 data rows total.

R0005 replay must materialize every path from `9d2334d...`, configure the
disposable repository with `core.autocrlf=false`, `core.eol=lf`, and
`core.safecrlf=false`, run
`git apply --check --unidiff-zero --whitespace=error-all -p1`, verify all
postimage hashes and replacement occurrences, reverse the context-free patch
with `git apply --unidiff-zero --whitespace=error-all -R -p1`, and recover
every preimage byte-for-byte. Any preimage mismatch stops integration; the
request is never rebased onto the retirement or planning-control HEAD.

## Decision

The declaration graph is cross-wave disjoint, but the module graph is not:
there are 47 bidirectional transitive owner pairs, seven common direct project
dependencies, and five shared direct-both consumers. Therefore this review
authorizes a singleton R03 plan only and explicitly defers R07.
