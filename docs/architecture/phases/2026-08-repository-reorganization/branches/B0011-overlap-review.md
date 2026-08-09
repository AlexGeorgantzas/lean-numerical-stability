# B0011 C0007 activation and joint W07/W10 overlap review

Branch base: `C0007` at `9eb534a06db267203c2b9b88227edd44fc64f5db`.

This review is pinned to inventory SHA-256 `56B08C666F4461BE2B425E12B2E250ACFCD4604A43F793A066AA086091365196`, combined-baseline
SHA-256 `D9372A79DA159CEB50757F6581F650957D2868E738E41C0D5F892C121623CADD`, raw format-2 graph SHA-256 `80AE3FBB3948104C60FF7EA80E899CC11CE542D0A772EA087375C00EB0ED9ED3`, and
projection-checker SHA-256 `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443`. The 5-owner W07
selector has SHA-256 `478EFA94CE2311ECD54A7AA4A155336EF3DB8219BFA42E137BA7C37D0D97176A`. P0012
has deterministic gzip SHA-256 `9B683940DE4C94D17E48E200D1F10594EB26614CFD2AEF2BCB036F667BB5159C` and raw payload
SHA-256 `768C89419A7CF0F0FC7F326AC4ADCFC8E61C22AB43691B2CEE71F48D20FB6728`; it freezes 252
declarations, 800 signature edges,
1,400 body/proof edges, and
1,474 union edges across 7,094 physical
source lines.

## Exact C0007 owners and blobs

| Owned path | C0007 blob | Scope comparison |
| --- | --- | --- |
| `NumStability/Algorithms/StationaryIteration.lean` | `08cfea98cba754d35f7de2d620c00d0cc84300f8` | accepted import-only refresh |
| `NumStability/Algorithms/StationaryIterationDrazin.lean` | `258490a358f3991f2cc206f99c33c76033fb3c8e` | accepted import-only refresh |
| `NumStability/Algorithms/StationaryIterationRounded.lean` | `87464ba92a7339bc2560c90252f6eeb319b1376a` | current |
| `NumStability/Algorithms/StationaryIterationSemiconvergent.lean` | `38461840f7f6f4c856c1986087de86786356c0b8` | accepted import-only refresh |
| `NumStability/Algorithms/StationaryIterationSemiconvergentExistence.lean` | `5bda3a7f1f1adb2582ab6b980d78631a4541ec04` | current |

The immutable selector paths do not change when an accepted integration updates
an owner's import-only preimage:

- `NumStability/Algorithms/StationaryIteration.lean` refreshed from scope blob `34c1d8e3a7511878e18449282e7928f467009272` to C0007 blob `08cfea98cba754d35f7de2d620c00d0cc84300f8` by accepted import-only integration.
- `NumStability/Algorithms/StationaryIterationDrazin.lean` refreshed from scope blob `f1a3be1f6f625fa32d751d52b37e477a1303c80b` to C0007 blob `258490a358f3991f2cc206f99c33c76033fb3c8e` by accepted import-only integration.
- `NumStability/Algorithms/StationaryIterationSemiconvergent.lean` refreshed from scope blob `0239b2e47b0a590cc8e7c685e7957a6015b9341e` to C0007 blob `38461840f7f6f4c856c1986087de86786356c0b8` by accepted import-only integration.

## Reviewed destinations

The semantic audit authorizes exactly 34 vacant production
children (9 reusable and 25 source), plus the exact
`NumStabilityTest/Reorganization/W07/` and
`docs/architecture/deliveries/W07/` prefixes:

- `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Convergence/Singular/`
- `NumStability/Algorithms/LinearSystems/Iterative/Stationary/ErrorAnalysis/Forward/`
- `NumStability/Algorithms/LinearSystems/Iterative/Stationary/ErrorAnalysis/Local/`
- `NumStability/Algorithms/LinearSystems/Iterative/Stationary/ErrorAnalysis/Residual/`
- `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Execution/Computed/`
- `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Projectors/Drazin/`
- `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Recurrences/Affine/`
- `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Splittings/Core/`
- `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Splittings/Scaling/`
- `NumStability/Source/Higham/Chapter17/Equation01/ComputedIteration/`
- `NumStability/Source/Higham/Chapter17/Equation02/LocalError/`
- `NumStability/Source/Higham/Chapter17/Equation03/ComputedRecurrence/`
- `NumStability/Source/Higham/Chapter17/Equation04/FixedPoint/`
- `NumStability/Source/Higham/Chapter17/Equation05/ErrorExpansion/`
- `NumStability/Source/Higham/Chapter17/Equation06/ComponentwiseForward/`
- `NumStability/Source/Higham/Chapter17/Equation07/NormwiseGrowth/`
- `NumStability/Source/Higham/Chapter17/Equation08/NormwiseForward/`
- `NumStability/Source/Higham/Chapter17/Equation09/ComponentwiseGrowth/`
- `NumStability/Source/Higham/Chapter17/Equation10/LocalErrorSimplification/`
- `NumStability/Source/Higham/Chapter17/Equation12/PartialSumBound/`
- `NumStability/Source/Higham/Chapter17/Equation13/ComponentwiseForward/`
- `NumStability/Source/Higham/Chapter17/Equation15/NormwiseForward/`
- `NumStability/Source/Higham/Chapter17/Equation16/Jacobi/`
- `NumStability/Source/Higham/Chapter17/Equation17/SOR/`
- `NumStability/Source/Higham/Chapter17/Equation18/ResidualRecurrence/`
- `NumStability/Source/Higham/Chapter17/Equation19/ResidualBound/`
- `NumStability/Source/Higham/Chapter17/Equation20/ResidualSigma/`
- `NumStability/Source/Higham/Chapter17/Equation21/SingularIteration/`
- `NumStability/Source/Higham/Chapter17/Equation27/SingularErrorSplit/`
- `NumStability/Source/Higham/Chapter17/Equation28/SingularErrorSplit/`
- `NumStability/Source/Higham/Chapter17/Equation29/SingularSource/`
- `NumStability/Source/Higham/Chapter17/Equation33/StoppingTests/`
- `NumStability/Source/Higham/Chapter17/Section02/ScaleIndependence/`
- `NumStability/Source/Higham/Chapter17/Section04/PrintedConclusions/`

Every production prefix is trailing-slash, casefold-vacant in the C0007 tree
and immutable scope, pairwise equal/ancestor-disjoint, and disjoint from all
W10 destinations. No broad family or source root is authorized.

## Declaration routing and private closure

Only `StationaryIteration.lean` has `classify;document;migrate;split` authority. The four Drazin/rounded/semiconvergent owners remain `classify;document` only and may not be relocated. Reusable leaves separate splitting/scaling, affine recurrence, computed execution, generic local/forward/residual analysis, Drazin projector algebra, and singular convergence. Explicit Chapter 17 equations, source-sign structures, printed conclusions, Jacobi/SOR specializations, sigma/growth formulas, and stopping endpoints route only to their exact source children.

The selected-induced signature/body union reverse-private floor is exactly
31 declarations = 8 private + 23
public. Its sorted LF payload has SHA-256 `6A1B37537E0002E89B1B88F2BED03C6F7A701936A237FF33A49DFBD58E76E2B7`. Private declarations
encode their defining module and may never move, rename, or be promoted;
generated constructor/recursor commands and any additional ambient compiler
closure also remain indivisible. Final routing must preserve every public name,
kind, visibility, signature, proof/body, and typed incident edge.

Reusable destinations may not directly or transitively import Source or a
historical compatibility facade. Source may depend on reusable leaves. Old
imports and public declarations remain available through import-only wrappers
where possible and honest declaration-bearing facades where private closure
requires retention.

## Protected boundaries and joint proof

Protected consumers include `NumStability/Analysis/SemiconvergentBlockFormExists.lean`, the existing Chapter17 Equation08/12/15/16/17/20 modules, `NumStabilityTest/Import/Algorithms/StationaryIteration.lean`, and `NumStabilityTest/Reorganization/W06/Focused/ProtectedW07.lean`. They are non-owned and forbidden.

The W07 and W10 selectors have zero owned-path overlap. Their reviewed
production destinations have zero equal or ancestor/descendant overlap. C0007
has zero direct owner imports, zero signature edges, and zero body/proof edges
in either cross-wave direction. Their sole common direct production consumer
is the integrator-owned `NumStability/Algorithms.lean`. Global aggregates,
test roots, tier/layout manifests, phase controls, CI, and every non-owned
accepted consumer are integrator-owned and forbidden to workers.

No source migration is performed by the activation commits. Workers begin only
after the active-control commit is green, and every worker ref begins at the
exact C0007 code SHA rather than a later control commit.
