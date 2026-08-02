# W02 shared-file patch request

Branch `codex/reorg-2026-08-w02-foundations`, phase branch `B0002`, wave `W02`.

Nothing in this file has been applied by W02. The requested targets are outside
B0002's `owned_paths` and slash-terminated `destination_prefixes`; the worker records
them for the single integrator instead of crossing the phase contract.

## Critical request 1: narrow `StandardModel` off the error facade

File:
`NumStability/Analysis/FloatingPointArithmetic/StandardModel.lean`

Replace its broad historical import:

```lean
import NumStability.Analysis.Error
```

with the exact minimal explicit canonical pair:

```lean
import NumStability.Analysis.Error.Measures.ScalarProperties
import NumStability.Analysis.Error.Measures.ScalarWitnesses
```

This pair is established by static declaration lookup against the frozen `C0002`
graph, not inferred from names. Its 47 `StandardModel` declarations have 59 outgoing
edges to declarations formerly supplied by `Analysis.Error`, covering exactly five
unique targets:

| Required declaration | Canonical declaring leaf | Why needed |
| --- | --- | --- |
| `NumStability.relError` | `ScalarDefinitions` | used in a proof body |
| `NumStability.signedRelErrorWitness` | `ScalarDefinitions` | used in signatures and proof bodies |
| `NumStability.relErrorComputedDenom` | `ScalarProperties` | used throughout signatures and proof bodies |
| `NumStability.relErrorComputedDenom_eq_relError_swap` | `ScalarProperties` | used in a proof body |
| `NumStability.relError_eq_abs_of_signedRelErrorWitness` | `ScalarWitnesses` | used in a proof body |

Both `ScalarProperties` and `ScalarWitnesses` import `ScalarDefinitions`, so a third
direct import is unnecessary. Neither `Componentwise` nor `AccuracyPrecision` is
referenced. `Measures.All` would supply the same declarations but would expose a
strictly broader, non-minimal surface.

### Required transitive follow-up

Replacing only `StandardModel`'s direct import does **not** remove the old facade
from its import closure. Each of the following reusable W01 leaves still directly
imports `NumStability.Analysis.Error`:

- `NumStability/Analysis/FloatingPointArithmetic/Format.lean`
- `NumStability/Analysis/FloatingPointArithmetic/NearestRoundingError.lean`
- `NumStability/Analysis/FloatingPointArithmetic/RoundToEvenLocalError.lean`
- `NumStability/Analysis/FloatingPointArithmetic/Rounding.lean`

Consequently, a focused `StandardModel` build can succeed even with no replacement
leaves at all, because one of those imports supplies the compatibility facade
transitively. The integrator must separately audit and narrow the four broad imports
to the canonical error leaves each file actually uses, then verify both compilation
and the absence of a reusable-to-compatibility/source path in the semantic graph.

After W02, `Analysis.Error` is a compatibility facade that also exposes
source-specific destinations. Leaving any of these broad reusable edges in place
defeats the semantic boundary and can make strict source-layer checks report a
reusable-to-mixed/source path. These are import-only changes; no declaration should
move.

## Critical request 2: retarget the existing Chapter 12 source peer

File:
`NumStability/Source/Higham/Chapter12/IterativeRefinement.lean`

Replace:

```lean
import NumStability.Algorithms.IterativeRefinement
```

with:

```lean
import NumStability.Source.Higham.Chapter12.IterativeRefinement.All
```

The existing peer file contains its own Chapter 12 declarations and is imported by
the Chapter 12 aggregate and several cross-chapter modules. Its path is not writable
by B0002 because the authorized destination is the child prefix
`NumStability/Source/Higham/Chapter12/IterativeRefinement/`. Retargeting the peer to
the new `All` child preserves its declarations and public import surface while
removing the stale edge through the old algorithm compatibility facade. The child
`All` module does not import the peer, so this direction avoids a cycle.

After this retarget, retain these existing callers unchanged unless a focused reason
requires otherwise:

- `NumStability/Source/Higham/Chapter12.lean`
- `NumStability/Algorithms/HighamChapter12.lean`
- the Chapter 12 problem/cross-chapter modules that already import the peer

## Global classification and reachability wiring

The integrator should apply the normal shared updates after the two critical
retargets compile:

1. Classify the 127 route modules and 65 `All` modules in
   `docs/architecture/tiers.json` according to reusable, source, compatibility, or
   mixed role.
2. Record the seven declaration-bearing historical facades in
   `docs/architecture/layout-exceptions.json` if the layout checker requires an
   explicit temporary exception. Import-only facades should use the normal
   compatibility mechanism instead of a declaration-bearing exception.
3. Add the new family entry points to the appropriate global and chapter aggregates
   (`NumStability.lean`, `NumStability/Algorithms.lean`,
   `NumStability/Analysis.lean`, `NumStability/FloatingPoint.lean`,
   `NumStability/Source.lean`, or their established narrower umbrellas).
4. Wire the 142 W02 import tests through `NumStabilityTest.lean` or the accepted root
   test aggregate.
5. Update `docs/architecture/COMPATIBILITY.md`, `docs/architecture/MIGRATION.md`,
   root documentation, and phase control records only after the accepted green
   checkpoint is known.
6. Review external direct importers of the 19 historical owners. Canonical consumers
   should move to the new semantic `All`/leaf modules when doing so does not widen
   their import surface; old imports remain supported by the compatibility facades.

The primary Equation (8.15) API must remain under Chapter 8 Section 4 FanInCore.
Only the local-cancellation and raw-cube obstruction belongs under
`Equation15/GlobalEnvelopeCounterexample`; aggregate wiring must not make the
counterexample directory the canonical home of Equation (8.15) itself.

Likewise, the `LegacyChapter11Surface` name is intentional. It preserves old public
identifiers and comments while locating iterative refinement in the current
second-edition Chapter 12 source hierarchy. Do not mechanically rename `thm_11_*`
or `eq_11_*` declarations during integration.

## Observed acceptance-gate debt

The worker static run makes the shared work measurable:

- `check_layout` exits 1 only because all 142 W02 tests are not yet root-reachable,
  new W02 modules are not yet present in the frozen tier classification, and the
  parent/global aggregates do not yet reach their new descendants.
- The strict-source checker reports 365 reusable-to-source/mixed pairs on the W02
  worker. The identical checker exits 0 on the frozen control tree, so this is
  integration retarget/classification work rather than pre-existing control debt or
  a checker regression.
- Provenance already passes with 207 Apache-marked production files and 5 evidenced
  upstream modules. Compatibility already passes with 296 forwarding modules and
  566 canonical targets.

Acceptance should rerun layout and strict-source after applying the requests above;
neither current exit-1 result should be waived as a worker-local exception.

## Forbidden/shared paths respected by W02

The following exact paths are forbidden to the worker and remain integrator-owned:

```text
.github/workflows/lean_action_ci.yml
ARCHITECTURE.md
CONTRIBUTING.md
NumStability.lean
NumStability/Algorithms.lean
NumStability/All.lean
NumStability/Analysis.lean
NumStability/Core.lean
NumStability/FloatingPoint.lean
NumStability/Higham.lean
NumStability/Source.lean
NumStabilityTest.lean
README.md
docs/README.md
docs/architecture/COMPATIBILITY.md
docs/architecture/MIGRATION.md
docs/architecture/layout-exceptions.json
docs/architecture/phases/2026-08-repository-reorganization/README.md
docs/architecture/phases/2026-08-repository-reorganization/phase.json
docs/architecture/phases/2026-08-repository-reorganization/scope.tsv
docs/architecture/phases/2026-08-repository-reorganization/semantic-review.tsv
docs/architecture/phases/2026-08-repository-reorganization/unclassified-queue.tsv
docs/architecture/phases/README.md
docs/architecture/tiers.json
lake-manifest.json
lakefile.toml
lean-toolchain
```

The following prefixes are also forbidden to W02:

```text
NumStabilityTest/Import/
NumStabilityTest/Reorganization/W01/
NumStabilityTest/Worker/
docs/architecture/deliveries/W01/
docs/architecture/phases/2026-08-repository-reorganization/baselines/
docs/architecture/phases/2026-08-repository-reorganization/branches/
docs/architecture/phases/2026-08-repository-reorganization/checkpoints/
docs/architecture/phases/2026-08-repository-reorganization/projections/
docs/architecture/phases/2026-08-repository-reorganization/requests/
docs/architecture/phases/2026-08-repository-reorganization/selectors/
tools/architecture/
```

The worker's report-snapshot scope audit covered 385 changed paths and found zero out
of scope. The integrator must rerun the exact clean-tip scope gate after the delivery
commit and replace this snapshot with the committed evidence.
