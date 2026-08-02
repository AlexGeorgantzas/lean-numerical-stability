# W02 delivery — foundational numerical-analysis split

| | |
| --- | --- |
| Phase | `repository-reorganization-2026-08` |
| Phase branch | `B0002` |
| Wave | `W02` |
| Branch | `codex/reorg-2026-08-w02-foundations` |
| Base checkpoint | `C0002` |
| Base SHA | `e6ef0107edb873f7a05ad8282df7efdf41a986d3` |
| Control snapshot | `3a307fc9eb5792109c78a9cc7a9f55f8d1bcefba` |
| Implementation/evidence commit | `8e6c0cc3e125c57898e4bf487e38a3d1834d1f73` |
| Projection | `P0002`, gzip SHA-256 `EA781015CD00CDC9EC152D71BE9D6F2993148294E8B3EBEF28B56E81C9C002DB` |
| Final status | **worker delivery ready for integrator; integration acceptance pending** |

This report describes the fully gated W02 worker implementation committed at
`8e6c0cc3e125c57898e4bf487e38a3d1834d1f73`. All worker-authorized build, test,
projection, replay, precommit-scope, and committed-tip gates completed. The branch's
published delivery-record tip is reported by the remote ref rather than embedded in
its own content.

## Scope and result

W02 owns 73 historical modules. The reviewed classification ledger records two
outcomes:

- 54 modules remain canonical in place. Of these, 23 receive concise module
  documentation and 31 remain byte-identical classification-only owners.
- 19 modules are physically split while retaining their old import paths as
  compatibility facades.

The 19 physical owners contribute 2,268 source commands. The hash-pinned private
closure plan retains 258 commands and marks 2,010 commands as move candidates.
The distinction between commands and declarations matters: one Lean command can
generate several declarations. In the 4,195-declaration `P0002` selection, 1,717
declarations stay canonical in place, 258 remain in historical modules, and 2,220
are routed to new semantic leaves.

The emitted production surface consists of:

| Artifact | Count |
| --- | ---: |
| Changed historical production modules | 42 |
| New declaration-routing modules | 127 |
| New family `All` modules | 65 |
| Production build targets | 234 |
| Canonical import tests | 123 |
| Compatibility import tests | 19 |
| Generated W02 tests | 142 |

The 127 routing modules include four import-only semantic locators, so 123
declaration-bearing leaves have isolated canonical tests. Every physical owner has
one old-only compatibility test. `TEST_MATRIX.tsv` records each import and its
representative declarations.

## Semantic organization

Reusable material now lives below the dedicated families for Cramer's rule,
iterative refinement, Doolittle LU, triangular error analysis, arbitrary-order
summation, Neumaier and Priest compensation, linear-system conditioning, error
measures and models, double and midpoint rounding, trigonometric cancellation,
problem-dependent stability, sample variance, and fused multiply-add.

Source-specific material is separated beneath Higham Chapters 1, 2, 3, 4, 6, 7,
8, and 12. Source modules import reusable APIs; no reusable destination is intended
to depend on a `Source` destination. Family `All` modules provide stable entry
points without placing peer umbrellas outside B0002's authorized prefixes.

### Historical Chapter 11 labels inside Chapter 12 material

The old `Algorithms.IterativeRefinement` file calls a portion of its surface
"Section 11" and uses identifiers such as `thm_11_3_*`, `thm_11_4_*`, and
`eq_11_15_*`. The repository's current source correspondence, however, identifies
iterative refinement with Higham's second-edition Chapter 12. W02 does not rename
public declarations or silently relabel old theorem numbers. It therefore places
that historically named portion in
`Source.Higham.Chapter12.IterativeRefinement.LegacyChapter11Surface`, while the
genuine second-edition Chapter 12 bounds live in
`Source.Higham.Chapter12.IterativeRefinement.Chapter12Bounds`.

### Equation (8.15) and the counterexample closure

The primary Equation (8.15) residual-transfer and fan-in results remain in
`Source.Higham.Chapter08.Section04.FanInCore.ResidualForwardBounds`. Only the
local-cancellation obstruction and the strict-audit raw-cube witness are classified
under
`Source.Higham.Chapter08.Equation15.GlobalEnvelopeCounterexample`. This prevents a
counterexample to a global all-orders rewrite from being presented as the printed
Equation (8.15) theorem itself.

## Private declarations and retained facades

Lean private names encode their defining module. Moving a private declaration would
change its name and invalidate the projection's identity and incident edges. W02
therefore retains every private seed and its complete reverse user closure in the
historical owner. The closure is computed at command granularity from the frozen
`.ilean` data and the `P0002` edge graph.

Seven historical owners retain declarations for this reason:

- `NumStability.Algorithms.HighamChapter8`
- `NumStability.Algorithms.LU.Doolittle`
- `NumStability.Algorithms.NeumaierCompensatedFiniteFormat`
- `NumStability.Analysis.DoubleRounding`
- `NumStability.Analysis.HighamChapter7`
- `NumStability.Analysis.HighamChapter7Rectangular`
- `NumStability.Analysis.SampleVariance`

Their frozen original imports are preserved because retained declarations must
elaborate under their historical environment. The other 12 physical owners become
import-only compatibility facades. No private declaration is promoted, renamed, or
encoded with an escaped numeric component.

## Evidence ledgers

| File | Evidence |
| --- | --- |
| `CLASSIFICATION.tsv` | all 73 owners and reviewed outcomes |
| `DECLARATION_ROUTES.tsv` | all 4,195 selected declarations, exactly one route each |
| `PRIVATE_CLOSURE.tsv` | 19 owners, 2,268 commands, 258 retained, 2,010 movable |
| `TEST_MATRIX.tsv` | 123 canonical plus 19 compatibility tests |
| `GENERATE_MIGRATION.py` | deterministic source reconstruction and test emission |
| `PRIVATE_CLOSURE_PLAN.py` | hash-pinned private/user closure construction |
| `PROJECTION.md` | projection procedure and final comparison result |
| `CHANGED_PATHS.md` | exact delivery-scope path inventory |
| `SHARED_PATCH_REQUEST.md` | integrator-only retargets and global wiring |

The locked comparison passed for all 4,195 declarations, 18,256 signature edges,
30,343 body edges, and 32,459 distinct incident edges. The exact checker, projection,
and candidate hashes and the successful result are recorded in `PROJECTION.md`.

## Compiler evidence

The following results are coordinator-recorded. Full command strings were not
available to this documentation task, so the target set and observed result are
reported without reconstructing or inventing commands.

| Gate | Coordinator-recorded result |
| --- | --- |
| Frozen historical-owner refresh | `Build completed successfully (3082 jobs)`, approximately 909 seconds |
| Focused production set | 234 targets total; the initial run compiled 232/234 |
| Two repaired retained facades | targeted build of `NumStability.Algorithms.HighamChapter8` and `NumStability.Analysis.HighamChapter7Rectangular` completed successfully (`3144 jobs`) after frozen original imports were restored |
| Focused production conclusion | all 234 production targets compile |
| Representative private/reusable/source batch | historical DoubleRounding, Chapter 7 PerronFrobenius, and Chapter 8 Equation 15 RawCube completed successfully (`3080 jobs`), approximately 935 seconds |
| Generated W02 tests | all 142 completed successfully (`3347 jobs`), approximately 532 seconds |
| Full candidate build for locked extraction | `Build completed successfully (5121 jobs)` |
| Authoritative full build | `lake build NumStability NumStabilityTest` — `Build completed successfully (6293 jobs)` |
| Package test suite | `lake test` — exit 0 |

## Static gate evidence

The worker ran the repository's non-Lean delivery and architecture checks. Passing
self-tests establish that the checker code is healthy; the two nonzero architecture
results below identify frozen shared wiring that B0002 is not authorized to edit.

| Check | Result |
| --- | --- |
| Python compilation of delivery scripts | **passed** (`py_compile`) |
| Phase checker self-test | **passed** (`check_phase --self-test`) |
| Projection checker self-test | **passed** |
| Provenance | **passed** — 207 Apache-marked production files and 5 evidenced upstream modules |
| Compatibility | **passed** — 296 forwarding modules and 566 canonical targets |
| Layout | exit 1 only for integration-owned frozen shared wiring: all 142 W02 tests are not yet root-reachable, new W02 modules are not yet classified, and parent/global aggregates do not yet reach their new descendants |
| Strict source layering, worker | exit 1 with 365 reusable-to-source/mixed pairs |
| Strict source layering, frozen control | **passed**, exit 0 with the same checker |

The strict-source control result distinguishes migration delta from a checker or
baseline defect. The 365 worker pairs require integrator-owned import retargeting and
tier/classification updates, including the `StandardModel` transitive closure recorded
in `SHARED_PATCH_REQUEST.md`. Layout likewise cannot become green until the integrator
wires tests and descendants through the frozen shared aggregates.

## Reproducibility and precommit evidence

| Check | Result |
| --- | --- |
| Exact private-closure recheck | **passed** using all 19 pinned `.ilean` inputs: 2,268 commands, 258 retained, 2,010 movable |
| External evidence manifest | SHA-256 `FA1FFF043B5011731C9DC7A02484999A6E77C1731ED9536231CA2227CF52A63F` |
| Isolated frozen FMA build | **passed**, 1,485 jobs; pinned `.ilean` SHA-256 `8C62295DFA248A403914E3DFC57222B1E30D3EA2099A8378BB19905710041259` |
| Midpoint frozen input | exact `.ilean` SHA-256 `0997719F34C0ADFC601998C67DC2010AE3C6AB9B046030671C0BD86B3A580D9A`, supplied by the verified W12 cache |
| Package-tree fingerprint | unchanged at `25B3A00644655A43D873C2FDE8F75F1C602921B102C76B0C0754BE03F8870280` |
| No-build graph replay | **deterministic**; TSV, JSON, and Markdown hashes all matched the locked extraction recorded in `PROJECTION.md` |
| Migration dry run | **passed** with the exact recorded owner, route-module, `All`-module, and test counts |
| Precommit scope | **passed**: 386 paths; unowned 0, forbidden 0, shared 0 |
| Precommit diff check | **passed** |

## Final gate ledger

| Gate | Result |
| --- | --- |
| 234 focused production targets | **passed**, coordinator-recorded as above |
| 142 isolated W02 import tests | **passed**, coordinator-recorded as above |
| Locked candidate extraction and `P0002` comparison | **passed** — `phase projection contract passed`; 4,195 selected, 2,220 relocated |
| Python/static checker self-tests | **passed** — `py_compile`, phase self-test, projection self-test |
| Provenance | **passed** — 207 production, 5 upstream |
| Compatibility | **passed** — 296 forwarding modules, 566 canonical targets |
| Layout | **integration pending** — exit 1 only for shared classification, root test, and aggregate reachability wiring |
| Strict source layering | **integration pending** — worker exit 1 with 365 pairs; frozen control exit 0 |
| Full `lake build NumStability NumStabilityTest` | **passed** — `Build completed successfully (6293 jobs)` |
| `lake test` | **passed**, exit 0 |
| Exact private closure | **passed** — 19 pinned inputs, 2,268 commands, 258 retained, 2,010 movable |
| Deterministic no-build graph replay | **passed** — all three candidate artifacts matched |
| Migration dry run | **passed** — exact counts matched |
| Precommit scope and diff check | **passed** — 386 paths, unowned/forbidden/shared 0 |
| Clean committed implementation-tip SHA and scope check | **passed** at `8e6c0cc3e125c57898e4bf487e38a3d1834d1f73` — 386 paths, unowned/forbidden/shared 0, clean worktree |

At implementation commit `8e6c0cc3e125c57898e4bf487e38a3d1834d1f73`, all 386
paths pass the committed contract check with zero unowned, forbidden, or shared
paths; the worktree is clean, the exact C0002 base is the merge base, and the committed
diff check passes. The subsequent record-only commit changes this delivery report and
is rechecked before publication.

## Integrator boundary

W02 intentionally does not modify global aggregates, tier/layout manifests, root
tests, compatibility tables, phase controls, workflows, toolchain files, or
architecture tooling. Two correctness-critical shared retargets and the ordinary
global wiring are specified in `SHARED_PATCH_REQUEST.md`. The layout and strict-source
exit-1 results remain explicit blockers for **integrator acceptance** until that shared
wiring is applied and the checks are rerun. They are neither worker failures nor
waivers. With all authorized gates green, this worker delivery is ready for the
integrator.
