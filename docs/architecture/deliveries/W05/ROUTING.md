# W05 semantic routing

W05 starts from C0004 code revision
`b56f609f3bf66b5d7d0b677567cce82fee0c275b` and covers exactly the ten
owners selected by P0006.  The command-span audit covers all 921 declarations:
783 are relocated and 138 remain in the historical `Higham16` owner because
of genuine-private declaration identity.

## Routing totals

| Destination layer | Declarations | Purpose |
| --- | ---: | --- |
| reusable canonical modules | 502 | Sylvester/Lyapunov, inverse-bound, and Schur APIs |
| Chapter 16 source modules | 281 | exact numbered/source-facing declarations and six proof-pinned endpoints |
| historical `Higham16` facade | 138 | three private declarations and their 135-public reverse closure |
| **total** | **921** | exact P0006 declaration set |

The 62 declaration-bearing leaves are supplemented by three import-only
source locators and fourteen reviewed `All` entry points.  No reusable leaf
imports a `NumStability.Source` module or a historical W05 facade.

## Reusable Sylvester and Lyapunov APIs

| Canonical leaf | Declarations | Historical source |
| --- | ---: | --- |
| `Algorithms.MatrixEquations.Sylvester.Equation.Basic` | 5 | `SylvesterSpec` |
| `...Equation.Lyapunov` | 8 | `SylvesterSpec`, `Higham16` |
| `...Equation.Rectangular` | 6 | `Higham16` |
| `...Equation.Vectorization` | 10 | `Higham16` |
| `...Equation.Diagonal` | 24 | `Higham16`, `Higham16Psi`, `Higham16Lyapunov` |
| `...Equation.SchurCoordinates` | 4 | `Higham16` |
| `...BackwardError.Specification` | 4 | `SylvesterSpec` |
| `...BackwardError.SylvesterSVD` | 56 | `SylvesterBackward` |
| `...BackwardError.LyapunovSpectral` | 65 | `SylvesterBackward` |
| `...Perturbation.Basic` | 6 | `SylvesterPerturbation` |
| `...Perturbation.Vectorization` | 3 | `Higham16` |
| `...Perturbation.SeparationBounds` | 25 | `Higham16` |
| `...Conditioning.FirstOrder` | 9 | `SylvesterPerturbation` |
| `...Conditioning.PracticalErrorBounds` | 95 | `Higham16` |
| `...Conditioning.Separation` | 16 | `Higham16` |
| `...Conditioning.StructuredSylvester` | 15 | `Higham16Psi` |
| `...Conditioning.StructuredLyapunov` | 40 | `Higham16Lyapunov` |
| `...Conditioning.SingularValue` | 3 | `InverseOpNorm2` Sylvester/Lyapunov bridge |
| `...GeneralizedEquations.Basic` | 10 | `Higham16` |

The six generic-named relative first-order endpoints at `Higham16Psi` lines
558, 583, and 791 and `Higham16Lyapunov` lines 879, 904, and 1776 remain with
their Chapter 16 Equation 24/27 proof dependencies.  Moving them to reusable
modules byte-identically would create forbidden reusable-to-source edges.

## Generic inverse bounds

`Analysis.InverseOpNorm2` is split rather than classified wholesale.

| Canonical leaf | Declarations |
| --- | ---: |
| `Analysis.SingularValues.InverseBounds.Rayleigh` | 1 |
| `Analysis.SingularValues.InverseBounds.Gram` | 4 |
| `Analysis.SingularValues.InverseBounds.OperatorTwo` | 4 |

The three Sylvester/Lyapunov bridge declarations live in
`Algorithms.MatrixEquations.Sylvester.Conditioning.SingularValue`; the nine
generic spectral results have no Sylvester import.

## Reusable Schur hierarchy

The 89 Schur/invariant-subspace declarations are routed to fourteen reviewed
leaves under `Analysis.LinearOperators.Schur`:

- real invariant subspaces: `Complexification`, `TwoByTwo`, and `Existence`;
- real quasi-triangularization: `Basic`, `BlockEmbedding`, `Deflation`,
  `OrthogonalFrame`, `Reindex`, `TrailingConjugation`, `Existence`, and `API`;
- complex Schur theory: `BlockEmbedding`, `Deflation`, and `Triangulation`.

The Chapter 16 real-Schur and Chapter 18 complex-Schur destinations are
import-only source locators.  The declarations themselves are generic APIs;
the reusable modules never import those locators.

## Chapter 16 source routes

| Topic | Leaves | Relocated declarations |
| --- | --- | ---: |
| Section 1 Sylvester equation | `Equation01`, `Equation02`, `Equation03` | 28 |
| Section 2 Sylvester/Lyapunov backward error | `Equation09`, `10`, `11`, `12`, `13`, `15`, `16`, `18`, `19`, `21`, `LyapunovDefinition` | 76 |
| Section 3 perturbation and conditioning | `Equation22` through `Equation27`, `LyapunovSolutions` | 95 |
| Section 4 practical error bounds | `Equation28`, `Equation29` | 72 |
| Section 5 generalized matrix equations | `Equation30`, `Equation31`, `Equation32` | 10 |
| **total** | 26 leaves | **281** |

Compound labels route to their terminal displayed equation: `14_15` to
`Equation15`, `17_18` to `Equation18`, and `17_19` to `Equation19`.

## Compatibility boundary

All ten historical import paths remain present.  Nine are import-only facades.
`NumStability.Algorithms.Sylvester.Higham16` remains declaration-bearing with
the exact private reverse closure recorded in `PRIVATE_CLOSURE.tsv`.  Every
public declaration keeps its original fully qualified name, kind, statement,
and proof text.  `DECLARATION_ROUTES.tsv` is the declaration-level authority.
