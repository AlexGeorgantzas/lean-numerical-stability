# R03 delivery — floating-point foundations and Higham Chapters 01–12

R03 executes the frozen (and once-amended) B0005 route over the 47 residual C0002
owners holding 2,389 declarations. 2,132 declarations relocate into 47 canonical
destinations plus one documented declaration-free bridge; 257 declarations across 11
owners are retained in place. No historical path is deleted and none is Git-renamed.

Base: C0002 `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`

Branch: `codex/reorg-completion-2026-08-r03-floating-point-foundations-ch01-ch12`

Controls: planned `fb5a021b4…` → activation `1166874cb…` → operator authorization
`c4f66cbdf…` → route amendment `09b3962dc…` — each with its own green Lean CI
(runs 31691727184, 31697060516, 31719287142, 31732612464).

Projection: P0005 · Shared request: R0005 · Operator: `claude-local` under the
reviewed second-operator authorization (`reviews/R03-operator-authorization.md`);
`codex-local` remains the recorded planning/activation operator.

## Exact delivery

| quantity | value |
| --- | ---: |
| historical owners | 47 |
| selected declarations | 2,389 (1,987 public / 398 private / 4 internal) |
| relocated / retained | 2,132 / 257 |
| owner classes | 32 whole-owner moves, 4 declaration-level splits, 11 retained |
| canonical destinations | 47 + 1 declaration-free Equation15 bridge |
| historical wrappers | 36 (imports = destinations plus retargeted original imports) |
| tests | 2,150 (47 canonical, 1 focused, 36 old-only, 2,058 consumer, 7 aggregate, +All) |
| private normalization checks | 398 present + 398 absent, all green |
| changed paths | 2,251 (47 M + 2,204 A) |

`Higham726Rump` routes to
`NumStability.Source.Higham.Chapter07.Equation26.RumpCycle.Results.Theorems`;
`Chapter72` appears nowhere.

## The route amendment

The pre-activation route split `HighamChapters1To9SourceClosure` between two modules
while its private helper is used by BOTH of its public theorems — uncompilable under
Lean's module-scoped privates, and unsalvageable without breaking the exact P0005 edge
set. The primary-human amendment (`reviews/R03-route-amendment.md`, control commit
`09b3962dc…`) re-routes one theorem so the indivisible three-declaration component
lands whole at the Equation18 destination; the Equation15 module ships as a documented
bridge so every frozen consumer postimage keeps resolving. One route cell, one
module-route row and one test-plan row changed; every hash re-pinned; validator
ratchets extended and green.

## Method

Whole-owner moves transfer the post-import body verbatim from the pristine C0002 blob
(git show), never from the mutated worktree. Split owners cut per-declaration spans
from a pristine-build .ilean snapshot, with dependency-ordered sibling-destination
imports (cycle-asserted). Destination imports are the owner's originals with
owner-imports retargeted to destinations and — for non-Source destinations — Source
imports kept only when the emitted body references a declaration the C0002 graph
locates there. Wrappers re-state the retargeted original imports so every historical
transitive surface is preserved exactly; strict-source holds zero forbidden pairs at
the worker tip. Exactly two reusable-classified destinations
(`…PolynomialEvaluation.DerivativeEvaluation.ErrorBounds`,
`…Approximation.SineTaylor.OddDegreeFiveError.Theorems`) genuinely depend on
pre-existing canonical Source modules; the frozen R0005 tiers postimage classifies
both `reusable`, so integration carries a bounded documented reclassification to
`source` (C0002 postimage-superset precedent).

## Verification

`GATE_RESULTS.tsv` records all gates. Green: 47-target canonical matrix, 36-target
old-only matrix, the exhaustive 398-row private-normalization module, all 2,058
protected consumers unedited, 7 aggregate entrypoints, `R03.All`, full production
build, full production+test build, `lake test`, compatibility, provenance,
strict-source (0 unresolved / 0 cycles / 0 forbidden pairs), placeholder and diff
hygiene, format-2 candidate
(SHA-256 `98199873425E068D3B74F8595A6CFB9AFE5532974186FD760DFD122B0D273626`), and the
P0005 delivery replay with the complete 398-row private map: 2,389 selected, 2,132
relocated, exact frozen 28,180 signature and 42,404 body edges.

`check_layout` is red in the worker view only, for integrator-owned reasons: the
frozen R0005 postimages wire `NumStabilityTest.Reorganization.R03.All` into the test
root and classify the new destinations; two ratchet baselines (missing-docstrings,
declaration-bearing umbrellas) must be re-written because this wave improved them;
and `…Problem09.DoubleRounding.Counterexample` becomes an umbrella by gaining a child.
All are closed at integration; none is a worker defect.

This delivery claims delivery only — never C0003 acceptance.
