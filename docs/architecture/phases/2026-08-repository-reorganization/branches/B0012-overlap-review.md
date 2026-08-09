# B0012 C0007 activation and joint W07/W10 overlap review

Branch base: `C0007` at `9eb534a06db267203c2b9b88227edd44fc64f5db`.

This review is pinned to inventory SHA-256 `56B08C666F4461BE2B425E12B2E250ACFCD4604A43F793A066AA086091365196`, combined-baseline
SHA-256 `D9372A79DA159CEB50757F6581F650957D2868E738E41C0D5F892C121623CADD`, raw format-2 graph SHA-256 `80AE3FBB3948104C60FF7EA80E899CC11CE542D0A772EA087375C00EB0ED9ED3`, and
projection-checker SHA-256 `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443`. The 27-owner W10
selector has SHA-256 `444AA9109E4990AD47E281D550EA7A80057A8DBC493D8AF1693760EE7434BBB0`. P0013
has deterministic gzip SHA-256 `B61F64FC0C2CEF8DF22DDA78C5F28BB8D6B64FC1B57392AA36A2E187F3396ABA` and raw payload
SHA-256 `56B8FFD7024AE943C7E35AF3ACCC3106EFCEA068ED68C6AB7B42D0055DE479B0`; it freezes 1,029
declarations, 2,394 signature edges,
4,844 body/proof edges, and
5,075 union edges across 17,260 physical
source lines.

## Exact C0007 owners and blobs

| Owned path | C0007 blob | Scope comparison |
| --- | --- | --- |
| `NumStability/Algorithms/Ch15CondEstimators.lean` | `e0ffd658cc8a77ee8f152068e691ce7b7a63dd3c` | current |
| `NumStability/Algorithms/Ch15DixonClosure.lean` | `6319161f894d5a6cd7686bfe90def57d8c796c38` | accepted import-only refresh |
| `NumStability/Algorithms/Ch15DixonProbability.lean` | `81de7300344cbf762ad9e71771d30a510e318e27` | current |
| `NumStability/Algorithms/Chapter15CondEst.lean` | `3f687df1663909c7ad1f736ed4a4a4150a516397` | current |
| `NumStability/Algorithms/CondEstimation.lean` | `7488aa6ef42092b039b585cf3ad0eae39e6b8e2f` | current |
| `NumStability/Algorithms/HighamChapter15BoydBridges.lean` | `59c3f63155e38b1f7b616341d24fe7c36267df18` | current |
| `NumStability/Algorithms/HighamChapter15BoydConcreteLemma3.lean` | `d40f9a107e7bc69f3c56089996a8e1ceee0beb8f` | current |
| `NumStability/Algorithms/HighamChapter15BoydLocalStability.lean` | `1c5c96039d730e3bbdcacaecd03200aa4d45a13e` | current |
| `NumStability/Algorithms/HighamChapter15BoydRowwiseDomain.lean` | `fb9312b232c5d2d9956a1c5efc81f1b4b3a4aaf1` | current |
| `NumStability/Algorithms/HighamChapter15BoydScalar.lean` | `4c0603c06a1ee64bf46635efe8cf08c1df5d7957` | current |
| `NumStability/Algorithms/HighamChapter15BoydSourceClosure.lean` | `767769c85aa2df74a27a061edf5c1e9ad11a064c` | current |
| `NumStability/Algorithms/HighamChapter15BoydSourceDomain.lean` | `76f669e32099a7b693cb5d18dd82a7cab84ffbfe` | current |
| `NumStability/Algorithms/HighamChapter15BoydSourceLocal.lean` | `a81813d4c78e1c9102d8579b7dade9b4b9bf43c7` | current |
| `NumStability/Algorithms/HighamChapter15BoydSourceSecondDerivative.lean` | `449994a3131194cc48e83d57a587c8fb8fe4bfaa` | current |
| `NumStability/Algorithms/HighamChapter15BoydUniqueness.lean` | `3bf9bf460258222ff46fd8c3b6da1006ee2ff497` | current |
| `NumStability/Algorithms/HighamChapter15ConvergenceProse.lean` | `d693c166bcb20fa96f62278927bccb60f00fb6d5` | current |
| `NumStability/Algorithms/HighamChapter15RectTermination.lean` | `47bffc674289117830c9c4aaead73ed784e3abf5` | current |
| `NumStability/Algorithms/LU/Higham15Problem15_4.lean` | `66cc703cd3d16828cbf407f55f9e365e14b40e39` | current |
| `NumStability/Algorithms/LU/Higham15Problem15_6.lean` | `983bfbd83e38156dc0cc6cf29c97ab41e2dfed26` | current |
| `NumStability/Algorithms/LU/Higham15Problem15_6Closure.lean` | `3867c59e0d6d11020abf3b1fff0f61212ac40a67` | current |
| `NumStability/Algorithms/LU/Higham15Problem15_6Operational.lean` | `a0920784cae6e635850e36c5481606ba47163ca4` | current |
| `NumStability/Algorithms/LU/TridiagonalCondCh15.lean` | `b82d6e6144d6cc229033ab54e2397d42dffd0bb8` | current |
| `NumStability/Algorithms/LU/TridiagonalCondCh15Closure.lean` | `13889a51ff01ce2a6d4cb7acd0f0f6bc6eab6819` | current |
| `NumStability/Algorithms/LU/TridiagonalCondCh15IkebeClosure.lean` | `d513bb8fea4efb18066ae3fa96b46d0f90c3f45f` | current |
| `NumStability/Algorithms/PNormPowerMethod.lean` | `7897f90918868b7085e6dbc1d440acf458d2b3b5` | current |
| `NumStability/Algorithms/PNormPowerMethodGeneralP.lean` | `bbd156ae9d8dcfdc0fec68e242cf4676cc30617a` | current |
| `NumStability/Algorithms/PNormPowerMethodRect.lean` | `012bd13618b996b7c7dcf1cf8b7cc78c5d4232db` | current |

The immutable selector paths do not change when an accepted integration updates
an owner's import-only preimage:

- `NumStability/Algorithms/Ch15DixonClosure.lean` refreshed from scope blob `45a218325f3097908a395347e61fff7f62dede4d` to C0007 blob `6319161f894d5a6cd7686bfe90def57d8c796c38` by accepted import-only integration.

## Reviewed destinations

The semantic audit authorizes exactly 43 vacant production
children (20 reusable and 23 source), plus the exact
`NumStabilityTest/Reorganization/W10/` and
`docs/architecture/deliveries/W10/` prefixes:

- `NumStability/Algorithms/NormEstimation/OneNorm/FiniteIndex/`
- `NumStability/Algorithms/NormEstimation/OneNorm/LAPACK/`
- `NumStability/Algorithms/NormEstimation/OneNorm/LINPACK/`
- `NumStability/Algorithms/NormEstimation/OneNorm/PowerMethod/`
- `NumStability/Algorithms/NormEstimation/PNorm/Boyd/Carrier/`
- `NumStability/Algorithms/NormEstimation/PNorm/Boyd/Differentiation/`
- `NumStability/Algorithms/NormEstimation/PNorm/Boyd/FixedPoints/`
- `NumStability/Algorithms/NormEstimation/PNorm/Boyd/LocalStability/`
- `NumStability/Algorithms/NormEstimation/PNorm/Boyd/RowwiseDomain/`
- `NumStability/Algorithms/NormEstimation/PNorm/Boyd/Scalar/`
- `NumStability/Algorithms/NormEstimation/PNorm/Boyd/SecondVariation/`
- `NumStability/Algorithms/NormEstimation/PNorm/Boyd/Uniqueness/`
- `NumStability/Algorithms/NormEstimation/PNorm/Convergence/`
- `NumStability/Algorithms/NormEstimation/PNorm/Duality/`
- `NumStability/Algorithms/NormEstimation/PNorm/Endpoints/`
- `NumStability/Algorithms/NormEstimation/PNorm/PowerMethod/`
- `NumStability/Algorithms/NormEstimation/PNorm/Rectangular/`
- `NumStability/Algorithms/NormEstimation/TwoNorm/Dixon/Algebra/`
- `NumStability/Algorithms/NormEstimation/TwoNorm/Dixon/PowerBounds/`
- `NumStability/Algorithms/NormEstimation/TwoNorm/Dixon/Probability/`
- `NumStability/Source/Higham/Chapter15/Algorithm01/PNormPowerMethod/`
- `NumStability/Source/Higham/Chapter15/Algorithm03/OneNormPowerMethod/`
- `NumStability/Source/Higham/Chapter15/Algorithm04/LAPACKNormEstimator/`
- `NumStability/Source/Higham/Chapter15/Algorithm05/LINPACKConditionEstimator/`
- `NumStability/Source/Higham/Chapter15/Equation02/Subgradient/`
- `NumStability/Source/Higham/Chapter15/Equation03/GradientQuotient/`
- `NumStability/Source/Higham/Chapter15/Equation04/NormalizedDualDiscrepancy/`
- `NumStability/Source/Higham/Chapter15/Equation05/SubgradientInequality/`
- `NumStability/Source/Higham/Chapter15/Equation06/LAPACKCounterexample/`
- `NumStability/Source/Higham/Chapter15/Equation07/DixonBound/`
- `NumStability/Source/Higham/Chapter15/Lemma02/PNormPowerMethod/`
- `NumStability/Source/Higham/Chapter15/Problem04/LUConditionBounds/`
- `NumStability/Source/Higham/Chapter15/Problem06/TridiagonalInverseNorm/`
- `NumStability/Source/Higham/Chapter15/Section01/ConditionNumbers/`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/Corrections/`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/GlobalConvergence/`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/LocalConvergence/`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/SourceDomain/`
- `NumStability/Source/Higham/Chapter15/Theorem06/Dixon/`
- `NumStability/Source/Higham/Chapter15/Theorem07/TridiagonalLU/`
- `NumStability/Source/Higham/Chapter15/Theorem08/TridiagonalDiagonalDominance/`
- `NumStability/Source/Higham/Chapter15/Theorem09/Ikebe/`

Every production prefix is trailing-slash, casefold-vacant in the C0007 tree
and immutable scope, pairwise equal/ancestor-disjoint, and disjoint from all
W07 destinations. No broad family or source root is authorized.

## Declaration routing and private closure

One-norm routing separates finite-index, power-method, LAPACK, and LINPACK APIs. P-norm routing separates duality, iteration, convergence, rectangular/endpoints, and seven Boyd mathematical seams. Two-norm/Dixon routing separates algebra, power bounds, and probability. Printed Algorithms 15.1/15.3/15.4/15.5, Lemma 15.2, equations 15.2-15.7, Theorems 15.6-15.9, Problems 15.4/15.6, and Boyd printed/global/local/domain/correction/termination endpoints route to Source. Fourteen owners require declaration-level mixed review; frozen tier suggestions are not executable classifications.

The selected-induced signature/body union reverse-private floor is exactly
132 declarations = 80 private + 52
public. Its sorted LF payload has SHA-256 `19B36D816074EEC2401724AC84EFA107FB4ACD3672F7D91960247E65223B570E`. Private declarations
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

Seventy-five external production consumers import a W10 owner; `NumStability/Algorithms.lean` plus 74 accepted consumers of `CondEstimation` remain integrator-owned and forbidden. The W06 `Higham16NormEstimator`/canonical `OneNorm.GeneralIndex` boundary is preserved. Dixon code keeps the accepted W09 Gaussian/orthogonal canonical dependencies (28 signature and 48 body/proof incident edges) and must not restore the historical Higham28 facade. Two full-graph re-entry declarations outside the 132-member induced closure are separate retention hazards, not closure members.

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
