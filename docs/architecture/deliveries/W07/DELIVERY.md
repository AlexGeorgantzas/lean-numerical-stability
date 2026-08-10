# W07 delivery

W07 reorganizes all and only B0011's five stationary-iteration owners and their
7,094 base source lines from checkpoint C0007 at
`9eb534a06db267203c2b9b88227edd44fc64f5db`. It preserves all 252 selected
declarations and every P0012 typed incident edge while separating reusable
stationary-iteration APIs from exact Higham Chapter 17 endpoints.

The delivery branch is
`codex/reorg-2026-08-w07-stationary-ch17`. The immutable final delivery SHA is
the Git object reported in the handoff; a commit cannot embed its own object
name. The worker never merges, rebases, or cherry-picks `origin/main`.

## Scope and path inventory

The exact delivery inventory contains 103 paths:

| Class | Paths |
| --- | ---: |
| Historical W07 owners modified | 5 |
| Canonical production modules added | 34 |
| W07 test modules added | 48 |
| W07 delivery and evidence files added | 16 |
| **Total** | **103** |

`CHECK_SCOPE.py` generates `CHANGED_PATHS.md` from the exact C0007-to-delivery
inventory. It understands every B0011 exact and prefix rule, requires all five
owners to be modified, permits only new files below authorized destination,
W07-test, and W07-delivery prefixes, and rejects forbidden paths, pre-existing
non-owner files, deletes, renames, and generated artifacts. No shared
aggregate, root test, tier manifest, layout exception, compatibility manifest,
consumer, phase control, CI/toolchain path, or another wave is modified.

## Declaration routing

| Route | Declarations |
| --- | ---: |
| Relocated to nine reusable API modules | 47 |
| Relocated to 25 Chapter 17 Source modules | 89 |
| **Relocated total** | **136** |
| Retained in historical owners | 116 |
| **Selected total** | **252** |

The selected kinds are 192 theorems, 48 definitions, and four each of
inductives, constructors, and recursors; visibility is 244 public and eight
private. `StationaryIteration` is split declaration-by-declaration into the 34
authorized leaves. It remains an honest declaration-bearing historical facade
with 29 retained declarations and direct imports of every destination that
received one of its declarations.

B0011 authorizes only classify/document work for Drazin, Rounded,
Semiconvergent, and SemiconvergentExistence. Those four owners retain all 87
declarations and all historical imports; their only textual change is module
documentation. `DECLARATION_ROUTES.tsv` records one exact route for every
selected declaration, and `ROUTING.md` records all reviewed destinations.

## Private reverse closure and retention

All eight private declarations remain unrenamed, unpromoted, and physically in
`StationaryIteration`. Reverse traversal of the W07-selected union of signature
and body/proof edges retains exactly the required 31-declaration graph floor:
eight private seeds and 23 public dependents. The floor comprises 29
declarations in `StationaryIteration` and two in Drazin, with witness depths
zero through four. Every chosen non-seed witness is a body/proof edge; the
traversal nevertheless includes both typed edge classes.

No additional ambient/compiler closure is required. Actual retention is 116
because the classify/document-only authority retains 85 companion declarations
outside that graph floor. The ordered 31-name payload SHA-256 is
`6A1B37537E0002E89B1B88F2BED03C6F7A701936A237FF33A49DFBD58E76E2B7`.
`PRIVATE_CLOSURE.tsv`, `PRIVATE_CLOSURE.md`, and `RETENTION.tsv` record every
retained declaration, source command, depth, reason, and witness edge.

## Tests

| Test class | Count | Isolation |
| --- | ---: | --- |
| Canonical-only reusable | 9 | exactly one reusable destination import |
| Canonical-only source | 25 | exactly one Source destination import |
| Old-path-only | 5 | exactly one historical owner import |
| Focused | 9 | semantic, private, protected, and accepted-consumer boundaries |
| **Total** | **48** | all below `NumStabilityTest/Reorganization/W07/` |

The focused set covers reusable iteration, rounded execution,
semiconvergence/projectors, Drazin algebra, the Chapter 17 boundary, private
retention, protected W06, six accepted Chapter 17 consumers, and the accepted
`SemiconvergentBlockFormExists` consumer. `TEST_MATRIX.tsv` records every exact
import and representative check.

## Integration boundary

Worker-owned reusable modules have zero direct or transitive Source imports;
all 34 emitted canonical leaves have zero historical-facade reachability; and
the production import graph is acyclic. The forbidden shared test root,
LinearSystems and Chapter17 aggregates, tiers, and layout debt are unchanged.

`INTEGRATOR_REQUESTS.md` gives each required shared path's exact C0007 blob,
minimal postimage, rationale, protected tests, and gate unblocked. The reviewed
postimage adds only discovery/test wiring and classification: nine canonical
reusable leaves, five historical mixed owners, and five accepted
semiconvergence consumers whose unchanged declarations genuinely reach Source
endpoints. `CHECK_INTEGRATOR_PATCH.py` applies that postimage only in a
disposable C0007 clone and verifies the worker's shared preimages again after
the replay. W07 does not create R0010.

## Evidence artifacts

| File | Purpose |
| --- | --- |
| `DECLARATION_ROUTES.tsv` | one exact route for all 252 declarations |
| `PRIVATE_CLOSURE.tsv` / `PRIVATE_CLOSURE.md` | private seeds, reverse closure, and witnesses |
| `RETENTION.tsv` | every retained declaration and reason |
| `ROUTING.md` / `ROUTE_SUMMARY.json` | destinations and exact route totals |
| `TEST_MATRIX.tsv` | all 48 isolated and focused tests |
| `GENERATE_MIGRATION.py` | deterministic C0007 reconstruction and byte verification |
| `CHECK_STATIC.py` | routing, graph, test, facade, placeholder, and retention audit |
| `CHECK_PROJECTION.py` / `PROJECTION.md` | hash-pinned exact P0012 replay |
| `CHECK_SCOPE.py` / `CHANGED_PATHS.md` | exact B0011 scope proof |
| `CHECK_INTEGRATOR_PATCH.py` / `INTEGRATOR_REQUESTS.md` | executable shared-postimage request |

## Measured gate results

Every Lake, Lean extraction, baseline-generation, and projection command below
held `Local\lean-reorganization-2026-08`. Timings are wall-clock seconds measured
after mutex acquisition; the two long builds started from the deliberately cold
worker cache.

| Gate | Result | Seconds | Exact evidence |
| --- | --- | ---: | --- |
| Planned-control Lean CI | PASS | 425 | run `31300495624` |
| Active-control Lean CI | PASS | 404 | run `31300899785` |
| Final control `check_phase.py` | PASS | 85.306 | 8 checkpoints, 13 milestones, 12 branches, 9 requests, 13 projections |
| Frozen C0007 owner-cache reconstruction | PASS | 778.459 | all five pinned `.ilean` hashes reproduced; control tree clean |
| Deterministic migration `--check` | PASS | 3.6 | 92 generated files byte-identical |
| W07 static/routing/private audit | PASS | 5.3 | 252 routes, 136 relocated, 116 retained, 34 canonical modules, 48 tests; zero cycles or forbidden reachability |
| Comment-stripped placeholder/axiom scan | PASS | 5.3 | zero `sorry`, `admit`, `axiom`, or `constant` commands in changed Lean sources |
| Exact B0011 scope audit | PASS | 15 | 103 paths: 98 added, 5 modified owners, 0 forbidden |
| Staged `git diff --check` | PASS | 0.5 | zero whitespace errors |
| Compatibility checker | PASS | 24.6 | 337 forwarding modules, 685 targets |
| Provenance checker | PASS | 1.1 | 139 Apache-licensed and 5 upstream files checked |
| Canonical-only tests | PASS | 206.215 | all 34 isolated modules; 3,439 jobs |
| Old-path-only tests | PASS | 48.626 | all 5 historical owners; 3,415 jobs |
| Focused semantic tests | PASS | 26.292 | 6 reusable/rounded/semiconvergence/Drazin/Chapter17/private modules; 3,415 jobs |
| Protected/accepted-consumer tests | PASS | 39.563 | 3 W06/Chapter17/semiconvergence modules; 3,422 jobs |
| `lake build NumStability` | PASS | 8,192.443 | clean-cache build, 6,036 jobs |
| `lake build NumStability NumStabilityTest` | PASS | 7,076 | clean test-cache build, 6,610 jobs |
| `lake test` | PASS | 7.384 | warm timing replay after the successful full run |
| Worker `check_layout.py` | EXPECTED SHARED FAILURE | 182.417 | 2,490 modules; missing forbidden aggregate/root/tier wiring only |
| Worker strict-source generation | EXPECTED SHARED FAILURE | 17.698 | exactly 125 reusable-to-Source reachable pairs; no direct or worker-owned canonical violation |
| Disposable integrator postimage replay | PASS | 190.979 | layout green and zero strict-source direct/reachable pairs |
| Final full format-2 candidate | PASS | 140.331 | 56,903 declarations and 649,259 typed edge rows |
| Exact P0012 replay | PASS | 4.331 | 252 selected, 136 relocated, 800 signature, 1,400 body/proof, 1,474 union edges |

The worker layout output is the exact consequence of respecting B0011's shared
path prohibitions: 318 modules remain unclassified, 9 mixed, 86 lack module
docs, 266 retain naming exceptions, 27 are declaration-bearing umbrellas, and
zero aggregates are unsorted; it additionally reports the missing W07 test
root, nine LinearSystems imports, nine reusable tier rows, five stale
documentation exceptions, and six new accepted umbrella shapes. The worker
strict-source run exits 2 with
`125 classified reusable-to-source/mixed reachable pair(s)`, exactly five
unchanged accepted consumers times 25 Source leaves. Neither result is waived.
The executable integrator replay applies only IR-W07-1--4 in a disposable C0007
clone and proves the complete postimage green: 2,490 modules, 2,186 classified,
304 unclassified, 19 mixed, 504 reusable roots, and zero forbidden direct or
reachable pairs.

The immutable final candidate hashes are:

| Artifact | SHA-256 |
| --- | --- |
| `benchmark-results/W07-candidate.tsv` | `52AA6A6AAF8C2A843B3C78C7D1AC6198381FDDC30DDFCD1BCDC3FFAA8648CF98` |
| `benchmark-results/W07-candidate.json` | `D556FDDCF4AF07194905E0F87C3D4F0B583FC946CA642D5BF85176CC2D73454D` |
| `benchmark-results/W07-candidate.md` | `FB8DD7FE622059B679971878A06B3AFAB8B37D3DCCA1A80470C5C49C92C31558` |
| P0012 projection | `9B683940DE4C94D17E48E200D1F10594EB26614CFD2AEF2BCB036F667BB5159C` |

Candidate files are ignored build evidence and are not staged or committed.
The projection replay replaces only P0012's candidate placeholder and preserves
the recorded 42-argument vector exactly.
