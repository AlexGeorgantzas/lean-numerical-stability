# W09 routing: 72 owners to 30 authorized destinations

Base commit `a32095e6e50189f7dcc39312bb4c6a36f421fab5`, branch `codex/reorg-2026-08-w09-test-matrices-ch28`.

B0009 authorizes 30 production destinations and gives **no per-owner routing table**: all 72 queue rows are `frozen_proposal_requires_refresh`, and B0009 warns its 21 reusable / 48 source / 3 mixed labels are "frozen suggestions, not a legal final dependency proof". The map was therefore derived from owner names and declaration semantics and then *checked* against B0009's hard constraints.

## Measured outcome

* **1865** declarations across **72** owners
* **647** classified reusable, **1218** source (the measured split, not B0009's 21/48/3 suggestion)
* **1295** relocated into **93** canonical destination modules; **570** retained behind **54** declaration-bearing facades

## Invariants proved by `assign.py`

| invariant | result |
| --- | --- |
| zero reusable-to-source declaration edges | 0 |
| command-level closure at least the union floor | 570 >= 423 |
| all private declarations retained | 165 of 165 |
| `GinibreProjectiveIntegral` wholly retained | 13 of 13 |
| one owner per destination module | yes |

`reach.py` independently confirms on the built tree that **no reusable module reaches a Source module**, directly or transitively, and that every intra-wave reference lies inside its module's import closure.

## Authorized-but-unpopulated destinations

Two authorized destinations carry no relocated declaration. As with W08's D38 this is a finding, not a defect, and `assign.py` proves the arithmetic rather than asserting it: every declaration routed to such a destination must be retained.

| destination | routed | why every one is pinned |
| --- | ---: | --- |
| `NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProjectiveIntegral` | 20 | 18 in the frozen closure, 2 file-local ambient, 0 consuming one |
| `NumStability.Source.Higham.Chapter28.Section02.UniformPerron` | 3 | 0 in the frozen closure, 0 file-local ambient, 3 consuming one |

`S_PERRON`'s three declarations each reference `instMeasurableSpaceRSqMat_1`, the file-local instance in `Higham28Probability`, so none can leave that module.

## The three mandated mixed splits

B0009 forbids classifying these owners wholesale.

| owner | destinations | reusable | source |
| --- | ---: | ---: | ---: |
| `Higham28` | 11 | 69 | 11 |
| `Higham28Contracts` | 4 | 80 | 0 |
| `Higham28Exact` | 5 | 10 | 22 |

`Higham28Exact` splits across printed equations rather than across tiers: its Cholesky material is all printed source.

## Routing decisions that needed evidence, not names

* **No declaration in this wave cites a printed locator in its doc comment.** All 753 Cauchy, companion and Ginibre declarations were checked: zero hits. So there is no textual signal separating a printed conclusion from the machinery beneath it. The structural signal is consumption -- Higham prints conclusions, not lemmas -- so the *endpoints* of the Cauchy and companion owners route to `Section01.Cauchy` and `Section06.Companion`, and the machinery under them stays reusable. Source may depend on reusable, so the direction is legal.
* **`RealGinibre` (reusable) carries the ensemble carrier only** -- `GinibreRawMatrix` and its measurable-space and Borel instances. 412 of the 591 Ginibre declarations have a pin-free closure and *could* have been routed reusable; that was rejected because section 28.2's development of the expected number of real eigenvalues is printed source, and moving it would misrepresent the chapter.
* **`hilbertInvCholeskyEntry` routes to Equation 28.3, not 28.4.** Despite its name, `hilbertCholeskyFactor` is *defined using* it, so it is a prerequisite of the factor. Routing it by name made Equations 28.3 and 28.4 mutually importing.
* **`higham9_sineMatrix_isOrthogonal` is retained.** Routed reusable, it needs Chapter 9's `higham9_12_sineMatrix`. P0010 holds exactly this wave's declarations, so no in-wave edge check can see a reference into another chapter -- the build found it. Retention is B0009's third remedy and is preferred over inventing a Chapter 28 locus for material that is not Chapter 28.
* **`GinibreDimensionTwo`, `ToeplitzSpectrum` and `StewartRawFiber`** are routed to source despite reusable suggestions, as B0009 requires.
* **`Higham28Companion`'s reusable child imports the accepted canonical `Jordan.NormalForm.PrimaryDecomposition` directly**, never the historical Jordan implementation and never a facade.

## Destination inventory

| code | destination prefix | modules | declarations |
| --- | --- | ---: | ---: |
| R_CAUCHY | `NumStability.Analysis.TestMatrices.Cauchy` | 3 | 86 |
| R_COMPANION | `NumStability.Analysis.TestMatrices.Companion` | 4 | 29 |
| R_GAUSSIAN | `NumStability.Analysis.TestMatrices.Gaussian` | 2 | 35 |
| R_GINIBRE | `NumStability.Analysis.TestMatrices.RealGinibre` | 1 | 1 |
| R_HILBERT | `NumStability.Analysis.TestMatrices.Hilbert` | 5 | 78 |
| R_ORTHOGONAL | `NumStability.Analysis.TestMatrices.Orthogonal` | 5 | 71 |
| R_PASCAL | `NumStability.Analysis.TestMatrices.Pascal` | 8 | 151 |
| R_RANDOMSVD | `NumStability.Analysis.TestMatrices.RandomSVD` | 4 | 86 |
| R_TOEPLITZ | `NumStability.Analysis.TestMatrices.Toeplitz` | 2 | 9 |
| S_EQ01 | `NumStability.Source.Higham.Chapter28.Equation01.HilbertInverse` | 2 | 17 |
| S_EQ02 | `NumStability.Source.Higham.Chapter28.Equation02.ExactHilbertDeterminant` | 2 | 5 |
| S_EQ03 | `NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor` | 2 | 7 |
| S_EQ04 | `NumStability.Source.Higham.Chapter28.Equation04.HilbertCholeskyInverse` | 1 | 4 |
| S_GIN_ASYM | `NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Asymptotics` | 1 | 15 |
| S_GIN_FINEXP | `NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation` | 11 | 148 |
| S_GIN_INC | `NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence` | 4 | 65 |
| S_GIN_PLANES | `NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes` | 6 | 156 |
| S_GIN_PROB | `NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw` | 4 | 31 |
| S_GIN_PROJ | `NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProjectiveIntegral` | 0 | 0 |
| S_GIN_ROOT | `NumStability.Source.Higham.Chapter28.Section02.RealGinibre.RootMeasurability` | 2 | 35 |
| S_GIN_SIGNED | `NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence` | 8 | 61 |
| S_PERRON | `NumStability.Source.Higham.Chapter28.Section02.UniformPerron` | 0 | 0 |
| S_S01_CAUCHY | `NumStability.Source.Higham.Chapter28.Section01.Cauchy` | 1 | 2 |
| S_S01_HILBERT | `NumStability.Source.Higham.Chapter28.Section01.HilbertConditioning` | 2 | 19 |
| S_S03_RSVD | `NumStability.Source.Higham.Chapter28.Section03.RandomSVD` | 1 | 16 |
| S_S03_STEWART | `NumStability.Source.Higham.Chapter28.Section03.Theorem01.StewartHaar` | 3 | 63 |
| S_S04_PASCAL | `NumStability.Source.Higham.Chapter28.Section04.Pascal` | 4 | 39 |
| S_S04_RSPD | `NumStability.Source.Higham.Chapter28.Section04.ReciprocalSpectrumSPD` | 1 | 24 |
| S_S05_TOEPLITZ | `NumStability.Source.Higham.Chapter28.Section05.TridiagonalToeplitz` | 2 | 34 |
| S_S06_COMPANION | `NumStability.Source.Higham.Chapter28.Section06.Companion` | 2 | 8 |
