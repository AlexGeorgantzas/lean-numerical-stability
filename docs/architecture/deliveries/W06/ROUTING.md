# W06 semantic routing

W06 routes all 3,512 P0007 declarations from exactly 67 historical owners.
`DECLARATION_ROUTES.tsv` is the declaration-level authority; every row records
the original owner, final module, decision, kind, visibility, atomic command
root, and frozen start line.

| Outcome | Declarations | Declaration-bearing leaves |
| --- | ---: | ---: |
| Reusable Sylvester/matrix-power algorithms | 1,052 | 24 |
| Reusable analysis APIs | 1,062 | 43 |
| Higham Chapter 16 source material | 575 | 26 |
| Higham Chapter 18 source material | 48 | 19 |
| Retained historical closure | 775 | 23 historical facades |
| **Total** | **3,512** | **112 new declaration leaves** |

The 2,737 relocated declarations comprise 2,114 reusable and 623 source-
numbered declarations. All 94 private declarations remain historical. The
retained 681 public declarations are the private reverse closure plus seven
commands pinned by `Higham16Problem16_2` section/local-instance context.

## Reusable destinations

Reusable Sylvester/Lyapunov material is split under the exact B0006 children of
`NumStability.Algorithms.MatrixEquations.Sylvester`:

- attained minima, automatic bounds, practical estimation, and sigma-minimum
  conditioning;
- vectorization identities;
- complex-Schur, Hessenberg-Schur, pivoted-small-block, quasi-triangular, and
  triangular Bartels--Stewart solvers.

Computed matrix-power iteration lives under
`NumStability.Algorithms.MatrixPowers.ComputedIteration`; reusable one-norm
estimation lives under `NumStability.Algorithms.NormEstimation.OneNorm`.

Reusable analysis material is separated into exact children for C*-matrices,
functional calculus, Jordan normal form, matrix-power bounds, numerical radius,
pseudospectra, real Schur triangularization, and Lieb trace concavity. This
includes Berger, Henrici, Kreiss, Spijker, Bai--Demmel--Gu, Gautschi, Laszlo,
Jordan-scaling, resolvent, and pseudospectral APIs.

## Source destinations

Chapter 16 material is routed to exact children of:

- `Problem02.LyapunovIntegral`;
- `Section01.SylvesterEquation`;
- `Section02.BartelsStewart` and backward-error attained minima;
- `Section03.PerturbationAndConditioning`;
- `Section04.PracticalErrorBounds`.

Chapter 18 material is routed to exact equation/named-bound children in
`Section01.MatrixPowerBounds` and exact theorem/equation children in
`Section02.FinitePrecisionPowers`.

Each of B0006's 49 production destination prefixes has an isolated `.All`
entry point. There are 15 honest source locators that import only reusable
canonical content. Seventeen C0005-reviewed suggestions are deliberately not
emitted as leaves: their public endpoint is retained, or the reusable suggestion
is empty. Creating such a leaf would either fabricate an API or require a
canonical-to-historical dependency. `REVIEWED_ROUTE_STATUS.tsv` classifies all
143 reviewed suggestions plus the semantically required Chapter 16 equation-29
spectrum leaf. The two prefix-level `.All` modules with no children document the
empty reviewed destination without pretending declarations moved there.

## Compatibility

Every historical module remains importable. Forty-four owners are pure sorted
import shims; 23 remain declaration-bearing facades. `RETENTION.tsv` gives exact
per-owner counts. Facades re-export every relocated destination and retain their
original import surface except for the exact accepted-W05 retargets:

- singular-value, vectorization, practical-error-bound, and Schur uses point to
  accepted narrow W05 canonical APIs;
- four original retained-closure consumers keep `Higham16`, and
  `Higham16PerturbationSigmaMin` is the fifth historical importer because its
  mixed route still consumes retained material; together they preserve 26 body
  edges to nine retained `Higham16` declarations;
- `Higham16PerturbationSigmaMin` uses both canonical singular-value material and
  retained `Higham16`;
- `MatrixPowersHenrici` drops its typed-unused old Schur import;
- `Higham16NormEstimator` keeps the future-W10 `CondEstimation` dependency.

The stale physical `infNorm_add_le` copy in `MatrixPowers` is removed and the
accepted canonical `PolynomialEvaluation.MatrixNorms` module is imported.
`PRIVATE_CLOSURE.md` records this and the two private notation forms: five
notation commands remain historical, while 46 use sites are expanded in four
owners (37 Euclidean-space uses and nine algebra-map uses).

## Import invariants

The generated graph has no unresolved project imports or cycles. Reusable W06
modules have zero transitive `Source` reachability and do not import a W06
historical facade. Exactly 53 canonical-root reachability paths currently pass
through the one integrator-owned edge
`Analysis.Error.RoundingProducts.Core -> Analysis.LiebTrace`; the exact
hash-pinned integration request retargets that edge. The worker checker rejects
any other facade edge or any growth in this reviewed set. No Source module is
imported by a reusable generated module directly or transitively.
