# W04 delivery — Chapter 21 underdetermined systems

| Field | Result |
| --- | --- |
| branch | `codex/reorg-2026-08-w04-ch21-underdetermined` |
| source base | `a32095e6e50189f7dcc39312bb4c6a36f421fab5` (`C0006`) |
| controls | active `B0008`, active `P0009`, current `C0006`, operator exactly `codex-remote` |
| owner scope | 29 / 29 exact owners modified; no accepted, W90, shared, control, aggregate, or root-test path edited |
| production destinations | 84 modules: 31 reusable and 53 exact Chapter 21 source modules |
| historical compatibility | 29 facades: 13 pure import-only shims and 16 declaration-bearing facades |
| tests | 124 modules: 84 canonical-only, 29 old-path-only, 11 focused |
| changed-path classes | 253 paths: 29 owners, 31 reusable, 53 source, 84 canonical tests, 29 old-path tests, 11 focused tests, 16 evidence files |
| projection | **exact P0009 pass; no mismatch waived** |
| delivery state | worker payload complete; integrator-only wiring listed in `INTEGRATOR_REQUESTS.md` |

## Activation and baseline

The worker fetched origin without merging, rebasing, or cherry-picking main and
read B0008, P0009, W04.tsv, the overlap review, phase records, and C0006
evidence from a separate read-only control worktree.  Activation verified
`status == active` for B0008/P0009, current C0006, operator IDs exactly
`["codex-remote"]`, and a successful active-activation Lean CI run.

The mandatory baseline is preserved exactly: 29 owners, 37,621 source lines,
1,238 declarations (904 theorems, 283 definitions, 17 inductives, 17
constructors, 17 recursors), 1,198 public / 40 private, 5,684 signature edges,
10,044 body/proof edges, and 10,624 union edges.

## Routing result

The declaration ledger partitions every selected declaration exactly once:

| Decision | Declarations |
| --- | ---: |
| relocate to reusable APIs | 387 |
| relocate to exact Chapter 21 source | 631 |
| retain at historical owner | 220 |
| **total** | **1,238** |

Reusable destinations cover minimum-norm specifications, pseudoinverses and
solvers; componentwise/fixed-radius perturbation and conditioning; normwise
and rowwise backward error; complementary projectors; QR foundations; Givens
replay/backward error; corrected and rounded modified Gram--Schmidt; full-row
rank stability; and reusable seminormal-equation solves and transfers.

Exact source destinations cover equations 21.1--21.11, Lemma 21.2, Theorems
21.1/21.3/21.4, Section 21.3 method comparison, the Problem 19.12 correction,
and Chapter 21 source closures.  All 84 concrete modules appear as the 84
canonical rows in `TEST_MATRIX.tsv`; all 42 reviewed B0008 production prefixes
are reproduced in `ROUTING.md`.  Forty-one prefixes receive a module.  The
reviewed reusable `SeminormalEquations/ConditionTransfer/` prefix is correctly
empty because every nominal command is Source-dependent.

`CHECK_STATIC.py` proves zero canonical import cycles, zero direct canonical
imports of a historical facade, zero transitive W04 reusable-to-Source
reachability, and zero transitive W04 reusable-to-historical reachability.
It pins exactly two temporary source-to-historical boundary edges: accepted
`Wedin -> UnderdeterminedSpec` (integrator retarget requested) and the existing
Chapter 21 rowwise endpoint to the declaration-bearing solve facade (retained
closure required).  No other such edge is accepted.

## Private closure and compatibility

The private floor is exact: **220 = 40 private + 180 public**.  All 40 private
declarations retain their original name, kind, visibility, statement, proof,
and historical module.  P0009 independently rechecks their original module
triples.  Complete commands, generated/mutual families, attributes, sections,
namespaces, include/omit state, options, local instances, and ambient imports
are preserved.  See `PRIVATE_CLOSURE.md`, `PRIVATE_CLOSURE.tsv`, and
`RETENTION.tsv`.

Every public declaration name and typed incident edge is preserved.  There is
no `sorry`, `admit`, axiom/constant replacement, weakened statement,
replacement proof, or fabricated compatibility API.  Pure facades contain
imports and comments only; declaration-bearing facades retain exactly their
closure payload.

## Test result

`TEST_MATRIX.tsv` is an exact bijection with all 124 files on disk and pins
the imports and ordered `#check` representatives for each test.

| Test class | Files | Final result |
| --- | ---: | --- |
| canonical-only | 84 | 3,289 jobs, exit 0 |
| old-path-only | 29 | 3,265 jobs, exit 0 |
| focused | 11 | 3,258-job focused suite plus isolated protected retarget, exit 0 |
| all W04 explicitly | 124 | 3,379 jobs, exit 0 |

Focused coverage includes specifications/solves, QR/Givens/MGS, the SNE
pipeline, perturbation/conditioning/projectors/rank stability, Chapter 21
source endpoints, retained private closure, accepted interfaces, W90
dependencies/consumers, and the exact integrator consumer retarget.  The W04
worker does not edit `NumStabilityTest.lean`; root wiring is requested.

## Gates and projection

| Gate | Result |
| --- | --- |
| deterministic migration generator | pass: 84 canonical modules, 29 facades, 124 tests, 1,238 routes |
| exact B0008 scope/static audits | pass: zero unowned/forbidden/artifact paths; zero cycles/source reachability in W04 graph |
| compatibility | pass: 337 forwarding modules, 685 canonical targets |
| provenance | pass: 199 Apache-marked files, 5 evidenced upstream modules |
| `lake build NumStability` | pass: 5,871 jobs, 6,552.111 s |
| `lake build NumStability NumStabilityTest` | pass: 7,903 jobs; cold 5,769.100 s, exact warm replay 105.474 s |
| `lake test` | pass: 7,901-job target graph, 7.085 s |
| layout | integrator-only: root/aggregate/tier/ratchet updates are forbidden to W04 and listed exactly in `INTEGRATOR_REQUESTS.md` |
| strict-source | W04 graph has zero paths; repository command reports 56 paths, all through one forbidden accepted Wedin import with an exact retarget request |
| final format-2 candidate | pass: 56,903 declarations, 649,259 typed edge rows |
| exact P0009 replay | pass: 1,238 declarations; 5,684 signature, 10,044 body/proof, 10,624 union edges |

The final candidate SHA-256 is
`6CA03A2F9F38963AA3DF0D40DC3F3A5ECF57A878F93BA4C9732F7DA3904E47D4`.
`PROJECTION.md` records all control hashes, 74 checker arguments, candidate
size, exact output, and deterministic summary hashes.  `GATE_RESULTS.tsv`
records commands, actual jobs, timings, exits, and the two integrator-required
global-gate outcomes.

Every `lake` command, migration extraction, strict/source baseline generation,
format-2 candidate generation, and candidate-summary replay held the named
Windows mutex `Local\lean-reorganization-2026-08` from immediately before the
command until after its exit.  `GATE_RESULTS.tsv` records that mutex on every
applicable row.  The two required repository-global commands are explicitly
nonzero on the worker branch: layout exits 1 and strict-source exits 2 with 56
paths.  Both depend only on forbidden integrator-owned or accepted-consumer
changes listed in `INTEGRATOR_REQUESTS.md`; neither is represented as green.

## Scope and handoff

`CHANGED_PATHS.md` is generated from
`a32095e6e50189f7dcc39312bb4c6a36f421fab5..DELIVERY_HEAD` by
`CHECK_SCOPE.py`.  It proves all 29 owners are modified, every addition lies
under a reviewed destination, and there are zero forbidden, unowned, or
generated-artifact paths.

The protected equality-constrained consumer, accepted Wedin consumer, W90,
root tests, aggregates, tiers, layout exceptions, compatibility records,
phase controls, CI/toolchain/tools, main, and every other wave remain
untouched.  Exact post-acceptance changes are in `INTEGRATOR_REQUESTS.md`.
