# Worker lane `lsq-ch20` — baseline, route contract, and migration design

Lane: least squares and Higham Chapter 20
Engine: Claude (subscription 3, local-worktree mode)
Frozen base: `6487fc33088523b8f27ecde9ad613515b78f9977`
Branch: `codex/org-lsq-ch20` (local only; never pushed)
Worktree: `C:\Users\qed_s\higham-worktrees\lsq-ch20-claude`

This document is the reviewed lane contract required before any production
move. It records the measured baseline, the frozen declaration selection, the
reviewed declaration routes with their evidence, the destination topology, the
compatibility policy, and the checker self-test evidence.

## 1. Baseline gate

### 1.1 Repository identity

| Item | Value |
| --- | --- |
| Frozen base commit | `6487fc33088523b8f27ecde9ad613515b78f9977` |
| Base subject | Document recursive BlockLU validation |
| Branch | `codex/org-lsq-ch20` (descends from the frozen base, 0 commits at gate time) |
| Worktree status at gate | clean (`git status --short` empty) |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| `NumStability` modules | 1053 Lean files |
| `NumStabilityTest` modules | 419 Lean files |

Dependency revisions are pinned by the base `lake-manifest.json`, which is
byte-identical to the host checkout's manifest, so the prebuilt dependency
artifacts of the shared repository are valid for this worktree. The worker
worktree keeps its own `.lake/build`; only the immutable dependency package
tree is shared, and every large Lean command runs through the packet's
`scripts/with_lean_lock.ps1` mutex so it cannot overlap the integrator's
builds.

### 1.2 Inventory verification

`INITIAL_OWNED_FILES.tsv` was verified against the frozen base:

- 53 inventory rows: **47 production modules** and **6 existing lane tests**.
- All 53 `base_blob` Git object IDs match `git ls-tree -r <base>` exactly.
- All 53 `base_nonblank_lines` counts match the base blobs exactly.
- The historical family `NumStability/Algorithms/LeastSquares/**` contains
  **exactly 42 files** at the base, all of which are inventory rows, with no
  extra file on disk.
- `NumStability/Algorithms/LeastSquares.lean` does **not** exist at the base;
  the family has no umbrella module.

### 1.3 Frozen semantic stream

`baseline/parallel-base-declarations-v2.zip` was extracted to the external,
non-repository directory `PACKET_ROOT/runtime/baseline` and verified:

| Artifact | Expected | Measured |
| --- | --- | --- |
| archive bytes | 3955168 | 3955168 |
| archive SHA-256 | `1C2538B428B8EC3610B3C09BBB6A4CF23ECA9F0DB17EE4AE5B63E4F371AECDED` | identical |
| stream bytes | 115724349 | 115724349 |
| stream SHA-256 | `32ADA469E27A971E9B0BB972F29C51E1DCBE99104A1492D4C69549C339825563` | identical |

The stream is format 2 and contains **56,898 declarations** and **649,224
typed edges** for the whole project. Signature edges and body/proof edges are
retained separately throughout this lane; they are never merged.

### 1.4 Lane slice

Restricted to the 42 historical owners:

| Measure | Value |
| --- | --- |
| Selected declarations | **5,129** |
| of which private | **151** (require reviewed name rewrites) |
| Authored source spans owning them | 4,693 |
| Outgoing typed edges from lane declarations | 82,645 |
| Incoming typed edges from outside the lane | 1,722 |

The gap between 5,129 selected declarations and 4,693 authored spans is
entirely Lean-generated material — structure field projections, `casesOn`,
`recOn`, `ctorIdx`, `mk.inj*`, `noConfusion`, `sizeOf_spec`, and equation
lemmas. Every one was attributed to its parent authored span; there are zero
unattributed declarations and zero scanned declarations absent from the stream.

Largest external consumers of lane declarations at the base:
`Algorithms.RandNLA.LeastSquaresSketch` (1300 edges),
`Algorithms.Underdetermined.UnderdeterminedSolve` (243),
`Algorithms.Underdetermined.Higham21QRFoundations` (39).

## 2. Chapter 7 reachability

`Algorithms.LeastSquares.LSPerturbation` imports the unclassified
`Analysis.HighamChapter7` at the base. The declaration-level trace finds
**exactly 21 lane declarations** that reach Chapter 7, in six modules:

| Module | Declarations | Position |
| --- | --- | --- |
| `Higham20Prose` | 8 | body, plus signature on 4 van-der-Sluis/scaling statements |
| `LSPerturbation` | 5 | body only (`wedinLemma20_11_*`, `wedinLemma20_12_*`) |
| `Higham20ExampleCondition` | 3 | body only |
| `Higham20GeneralWedin` | 2 | body only (private counterexample helpers) |
| `Higham20ZeroDeltaB` | 1 | body only |
| `Higham20ResidualQuality` | 1 | body only |

Every one of these is source-facing material: the named van der Sluis column
normalization and column-scaling invariants, the printed δ-example condition
computations, the general-rank counterexample, the Theorem 20.3 zero-Δb
identity, and the Lemma 20.11/20.12 Wedin support steps. All 21 are therefore
routed into `Source/Higham/Chapter20`, which may depend on Chapter 7. **No
reusable canonical destination reaches `Analysis.HighamChapter7`**, and Chapter
7 is neither edited nor absorbed. No integrator request is needed for this.

Two further pre-existing inversions were measured and routed the same way:
`Higham20Equations` and `Higham20Refinement` each reach
`Source.Higham.Chapter12.IterativeRefinement`; the declarations involved are
the numbered (20.16) refinement statements and are routed to the source tier.

## 3. Reviewed route design

### 3.1 Authority order

1. `INITIAL_OWNED_FILES.tsv` is immutable packet data. Its `base_role` and
   `required_end_state` columns fix each file's expected end shape and are the
   primary routing authority.
2. Within a file, declaration-level evidence discriminates the book's asserted
   or printed material from generic machinery.
3. Two dependency fixpoints then enforce the architecture. They may only
   promote reusable → source and algorithm → analysis, never the reverse, so
   the reviewed table is a lower bound on source content.

### 3.2 Evidence used

Signals that mark source-facing material, each independently reviewable:

- a result-scoped enclosing namespace (`Theorem20_7`, `Theorem20_3_ZeroDeltaB`,
  `Theorem20_8`, `Theorem20_10`, `Problem20_5`, `Theorem20_3`) — 789
  declarations;
- the repository's `higham20`/`Higham20` name convention for source-facing
  declarations;
- printed/displayed/prose/correction/counterexample/execution-trace markers,
  including the `source<Word>` and `_source_` convention used for printed
  traces;
- reaching `Analysis.HighamChapter7` or an external `Source.*`/`Higham.*`
  module.

Two signals were considered and **rejected** after review:

- A bold numbered claim in a doc comment (`**Theorem 20.3**`) selects only the
  `LSQRSolveBackwardError` and `WedinPerturbationBound` specification
  structures. The repository's own doc comments describe these as parallels of
  the reusable `HouseholderQRBackwardError` and `QRSolveBackwardError` specs in
  the QR algorithm tier, so the citation is provenance rather than semantics
  and both structures stay reusable.
- A bare `theorem20_N` fragment inside a name. In `LSE` this fragment appears
  in 825 declarations that are budget, slack and certificate machinery named
  after the theorem they serve (for example
  `theorem20_7_completionB_budget_of_signed_stage_norm_coeff_slack_nat`).
  `_source`/`sourceA` is likewise ambiguous: in the Theorem 20.7 trace files
  `source<Word>` marks the printed trace, but in `LSE` `sourceA` names the
  *source matrix*. Single capitals not followed by a lowercase letter are
  therefore excluded from the marker.

### 3.3 Largest judgment call

The 825 `theorem20_*`/`Theorem20_*` declarations in `LSE` are routed to the
**reusable analysis** tier, not to source. Evidence:

- they are budget/slack arithmetic, rowwise backward-error structures and
  perturbation certificates, i.e. source-independent statements that are merely
  motivated by the numbered theorems;
- the bundled skill directs exactly this: *"Keep source-independent definitions
  and theorems in reusable tiers even when first motivated by a book"*;
- none of them reaches Chapter 7, a `Source.*` module, a `Higham.*`
  compatibility module, or a legacy least-squares wrapper;
- the numbered capstone statements for Theorems 20.7, 20.8 and 20.10 are owned
  by the dedicated `Higham20Theorem20_7`, `Higham20Theorem20_8` and
  `Higham20Theorem20_10` source modules, so the numbered correspondence is not
  lost.

### 3.4 Resulting partition

| Tier | Declarations |
| --- | --- |
| Source correspondence (`Source/Higham/Chapter20`) | 1,649 |
| Reusable algorithm (`Algorithms/LinearSystems/LeastSquares`) | 1,256 |
| Reusable analysis (`Analysis/Perturbation/LeastSquares`) | 2,224 |
| **Total** | **5,129** |

Proven properties of the partition, computed over all 82,645 lane edges:

- **0** reusable → source declaration edges (both signature and body);
- **0** algorithm → analysis declaration edges;
- 38 of the 42 historical files produce a split that agrees with their frozen
  `required_end_state`.

The four deliberate exceptions, each recorded rather than waived:

| File | Outcome | Reason |
| --- | --- | --- |
| `LSNormalEquations` | all reusable | The file contains no numbered or printed declaration; its numbered correspondence is owned by `Higham20NormalEquationsNorms` and `Higham20Equations`. |
| `Higham20Theorem20_7ActualBackSub` | all source | Every declaration is `sourceConstructed*` execution-trace material; the reusable kernel named by its end state is the panel-step/`applyProd` family separated in the `ActualTrace` and `QdR` leaves. |
| `Higham20Theorem20_7ActualRhs` | all source | Same as above. |
| `Higham20Theorem20_7ActualGrowth` | all source | All four declarations are `sourceConstructedPivotedStoredQR*` closure steps. |

## 4. Destination topology

Reusable algorithm leaves below
`NumStability/Algorithms/LinearSystems/LeastSquares`: `Basic`,
`AugmentedSystem`, `NormalEquations`, `QRSolve`, `StoredQR`, `MGS`,
`RankGeometry`, `RowSorting`, `Refinement`, `TraceKernel`, `MinimumNorm`,
`Projection`, `Equality.Basic`, `Equality.GQR`, `Equality.KKT`.

Reusable analysis leaves below
`NumStability/Analysis/Perturbation/LeastSquares`: `Basic`, `Normwise`,
`BackwardError`, `StoredQRBudget`, `Wedin`, `Conditioning`, `ResidualQuality`,
`NormalEquations`, `Contract`, `Runtime`, `Absorption`, `WeightedLimit`,
`MinimumNorm`, `AlternativeBound`, `Projection`,
`Equality.RowwiseBackwardError`, `Equality.DataCorrection`,
`Equality.MixedStability`, `Equality.GQR`, `Equality.FullRowRank`,
`Equality.Minimizer`, `Equality.KKTInverse`.

Source leaves below `NumStability/Source/Higham/Chapter20` keep the three
preserved base leaves (`Equation32`, `Lemma06`, `Theorem01`) and add the
numbered and printed owners: `Theorem02.AlternativeBound`, `Theorem03`,
`Theorem03.QRSolve`, `Theorem03.ResidualQuality`, `Theorem03.ZeroDeltaB`,
`Theorem04`, `Theorem04.Refinement`, `Theorem07` with the
`Contract`/`QdR`/`Runtime`/`RowPolicy`/`SourceTrace`/`ActualTrace`/
`ActualAssembly`/`ActualBackSub`/`ActualClosure`/`ActualGrowth`/`ActualRhs`/
`Elimination` subleaves, `Theorem08`, `Theorem08.LSE`, `Theorem10`, `Lemma11`,
`Lemma11.Support`, `Lemma12`, `Problem03`, `Problem05.MGSStability`,
`Equations`, `Equations.WeightedLimit`, `NormalEquations`,
`MinimumNormBackwardError`, `Prose`, `Prose.MoorePenrose`,
`Prose.Quantitative`, `Examples.CrossProduct`, `Examples.Condition`,
`Examples.GeneralRank`, `Section02.Algorithms`, and `Remaining`.

Reusable leaf names are deliberately source-neutral: the LSE analysis families
are named `RowwiseBackwardError`, `Perturbation` and `MixedStability` rather
than after theorem numbers, so no reusable module name couples to the book.

### 4.1 Verified topology

The frozen ownership manifest assigns all 5,129 declarations to **72
destination modules** with **244 owner edges**. Measured over the whole lane
edge set:

| Property | Result |
| --- | --- |
| Destination graph acyclic | yes (Tarjan, no nontrivial component) |
| reusable module → source module edges | 0 |
| algorithm module → analysis module edges | 0 |
| destination modules holding more than one tier | 0 |
| source spans straddling two destinations | 0 |
| Manifest SHA-256 | `288CA74AD3534B6B7E39D38B11BDF831738643392F4C13A4C898BA0309722D63` |

Final partition: **1,688** source, **1,234** reusable algorithm, **2,207**
reusable analysis.

Four sibling cycles appeared in the first assignment and were resolved without
weakening the partition. Because the declaration-level invariants forbid
reusable → source and algorithm → analysis edges, every destination cycle
necessarily lies inside one tier, so each was broken by relocating the
declarations behind its thinnest internal edge into the module they already
depend on — 54 same-tier relocations in five rounds, each logged:

| Relocation | Declarations |
| --- | --- |
| algorithm `Basic` → `NormalEquations` | 2 |
| algorithm `NormalEquations` → `RankGeometry` | 1 |
| algorithm `Equality.Basic` → `Equality.GQR` | 5 |
| analysis `StoredQRBudget` → `Basic` | 26 |
| analysis `Equality.Minimizer` → `Equality.GQR` | 2 |
| analysis `Equality.Perturbation` → `Equality.GQR` | 7 |
| analysis `Equality.GQR` → `Equality.Perturbation` | 11 |

Only one component was genuinely mutual: the LSE data-correction, full-row-rank
and KKT-inverse analyses depend on each other in both directions (208/65 and
141/77 edges), so they are one mathematical unit and are merged into
`Analysis.Perturbation.LeastSquares.Equality.Perturbation` rather than split
arbitrarily. The generalized-QR infrastructure that the packet asks to be kept
separate **is** separate: `Equality.GQR` owns 292 algorithm declarations and is
not merged into `Equality.Basic`.

### 4.2 Private-name logical keys

Lean private names encode both their owning module and an unstable per-scope
ordinal. The BlockLU precedent normalized both away, which is sound for three
historical owners but not for 42: the private helper suffix
`NumStability.higham20_realRectMatrixRank_finiteTranspose` occurs in more than
one historical owner of this lane, so dropping the module collapses distinct
declarations onto one manifest key. This lane therefore removes only the
ordinal and retains the historical owner, which is unique (verified: zero
suffix collisions within any single module) and stable, because a declaration's
historical owner never changes. The checker's own `pre` mode caught this
collision before any manifest was committed.

All **151** private declarations have a reviewed rewrite whose candidate name
re-encodes the destination module and preserves the declaration suffix exactly.

### 4.3 Authoritative spans and span coherence

The first version of this contract derived declaration spans with a regex
scanner. After the base build produced `.ilean` data, the spans were rebuilt
from the compiler's own records and cross-checked, which found two defects the
scanner had hidden:

- **Indented top-level declarations.** `LSQRSolve` writes some declarations
  indented by two spaces. The scanner treated indented lines as proof
  continuations and missed one declaration head entirely; its name was then
  silently absorbed by a sibling that happened to share a long prefix. Lean's
  `.ilean` entry is `[startLine, startCol, endLine, endCol, selStartLine,
  selStartCol, selEndLine, selEndCol]`, giving both the declaration's full range
  *including its doc comment* and the exact position of the declared
  identifier, so no heuristic is needed for attachment, wrapped names or
  indentation.
- **Span coherence.** A Lean `structure` or `inductive` emits its constructors,
  eliminators and field projections from a single source command, so all of them
  share one span and cannot be separated. The declaration-level classification
  had split 12 such spans across two tiers — for example
  `Theorem20_7.PivotedStoredQRRawReady` sat in a reusable trace-kernel module
  while its `.mk`, `.recOn`, `.casesOn` and several field projections were routed
  to `Source.Higham.Chapter20.Theorem07`. That is physically impossible to emit.

The contract now enforces, as an invariant of the partition, that every
declaration sharing a span shares its tier and destination. Where a span
straddles tiers, the **most restrictive** tier wins: if any member must be
source because it reaches source material, the whole span is source. That rule
is monotone, so it is interleaved with the two dependency fixpoints and
converges; after convergence **0** spans straddle a tier and **0** straddle a
destination.

Correcting this moved 248 declarations relative to the first manifest, of which
39 moved from a reusable tier into `Source/Higham/Chapter20` precisely because a
structure's projections forced their span up. The remaining 209 are within-tier
consolidations.

An independent cross-check confirms the result: for all **5,129** declarations,
the source line Lean records for the declaration falls inside the span this
lane assigned it, and the spans tile every historical file — no source line is
dropped and none is duplicated, verified across all 42 files.

### 4.4 Frozen historical owners

All 42 pristine historical sources were copied to the external, non-repository
directory `PACKET_ROOT/runtime/frozen-owners`. Each row of
`frozen-owners/frozen-owners.tsv` records the module, repository path, Git blob
ID re-verified against the frozen base, source SHA-256, physical and non-blank
line counts, and the compiled `.ilean` SHA-256 and size. Manifest SHA-256:
`99DA51FDBEC5858378A1A2B72DC4BA523E807CF70F87DBBDBEA15EBA8FC97ACF`.

41 of the 42 owners have a frozen `.ilean`. `Higham20SourceAliases` has none
because no production module imports it — only the isolated historical import
test `NumStabilityTest.Import.Compatibility.Source.Chapter20.AlgorithmsHigham20SourceAliases`
does, so `lake build NumStability` never builds it. It owns zero declarations
and therefore needs no span data; it is a structural compatibility wrapper.

### 4.5 Base build

`lake build NumStability` at the frozen base completed successfully under the
shared build lock: 4,845 jobs, exit code 0, 944 modules with `.olean`/`.ilean`
output. Only pre-existing Mathlib-style linter warnings were emitted, none in a
lane-owned file. This is the "before edits" gate of `ACCEPTANCE_GATES.md` and
the reference point for every later graph comparison.

## 5. Compatibility policy

Every one of the 42 historical modules ends as a documented exact import-only
wrapper over its destinations; no public name, namespace, signature,
visibility, theorem body, proof or licence notice changes, and no declaration
is duplicated. `Higham20SourceAliases` and `Higham/Chapter20/SourceAliases`
remain exact compatibility wrappers. `Source/Higham/Chapter20.lean` remains the
sorted declaration-free aggregate of every canonical Chapter 20 leaf. Shims are
removed only in a future declared breaking release, never in this lane.

### 5.1 Cross-lane contract

The 19 frozen `LS_TO_QR` rows and four `QR_TO_LS` rows of
`KNOWN_CROSS_LANE_EDGES.tsv` are frozen as checker inputs. Three of the 19
(`LSE → QR.GramSchmidtPolar`, `LSE → QR.Higham19Thm6ColPivot`,
`Higham20ZeroDeltaB → QR.Higham19Labels`) carry no declaration-level edge at
the base and are import-level dependencies; the remaining 16 carry
declaration-level edges. After owner normalization the checker requires, for
each row, that some destination owning a declaration of that historical module
directly imports the QR target and that the historical path still reaches it.
No QR or Chapter 19 file is edited or substituted. The four QR consumers keep
their historical least-squares imports and are built, never edited.

## 6. Lane ownership checker

`tools/architecture/check_lsq_ch20_ownership.py` implements the lane contract
with `--mode pre`, `--mode stage`, `--mode post` and `--self-test`.

- `pre` verifies the frozen stream digest, selects exactly the 5,129
  declarations with the frozen per-module counts, generates the manifest from
  the reviewed route map through the historical `.ilean` source ranges,
  compares it against the committed manifest, validates the destination DAG and
  the reusable/source boundary, validates proposed tier coverage, and checks the
  cross-lane contract.
- `stage` accepts a partially migrated tree: it takes the completed
  destinations, requires reviewed private-name rewrites only for those, proves
  candidate ownership, and requires exact normalized graph equality.
- `post` additionally requires all destinations complete, all 151 reviewed
  private rewrites, and proves that no reusable destination transitively
  reaches a `Source.*`, `Higham.*`, legacy least-squares, or
  `Analysis.HighamChapter7` module.

`--self-test` passes and rejects each of these mutations:

1. a missing historical declaration;
2. a duplicated historical declaration;
3. public declaration name drift;
4. declaration kind (signature shape) drift;
5. private visibility without a normalized private name;
6. a destination left inside the legacy least-squares family;
7. a reusable destination depending on a source declaration;
8. a destination ownership cycle;
9. a private rewrite that does not normalize from its destination;
10. missing private-rewrite coverage;
11. a lost typed edge;
12. an extra typed edge;
13. a lost declaration self-edge;
14. a baseline stream whose digest changed;
15. a reusable module importing a canonical source leaf;
16. a reusable module transitively reaching `Analysis.HighamChapter7`;
17. a dropped `LS_TO_QR` dependency;
18. a `QR_TO_LS` consumer that lost its historical import;
19. a wrapper that still owns a compiled declaration;
20. a wrapper containing non-import code, an unsorted import list, or no module
    docstring;
21. proposed tier rows that do not match the lane surface, contradict a
    destination role, or declare a `mixed` tier;
22. overlapping route ranges and a declaration outside every reviewed range;
23. a manifest digest mismatch.

## 7. Integrator requests

None required so far. The Chapter 7 inversion is resolved entirely inside the
lane by routing the 21 affected declarations to the source tier, so no shared
file needs editing. Global `docs/architecture/tiers.json`,
`layout-exceptions.json`, `COMPATIBILITY.md` and the root aggregates remain
integrator-owned; the lane records its proposed tiers in
`docs/architecture/declaration-ownership/lsq-ch20-tiers.tsv` and will capture
any sole remaining registration delta as an exact proposed patch in
`PACKET_ROOT/INTEGRATOR_REQUEST.md` rather than editing those files.

## 8. Committed contract artifacts

| Path | Content |
| --- | --- |
| `tools/architecture/check_lsq_ch20_ownership.py` | lane checker, pre/stage/post modes plus self-test |
| `docs/architecture/declaration-ownership/lsq-ch20-routes.tsv` | 5,129 reviewed `exact` routes |
| `docs/architecture/declaration-ownership/lsq-ch20-ownership.tsv` | generated ownership manifest, 5,129 rows |
| `docs/architecture/declaration-ownership/lsq-ch20-tiers.tsv` | 78 proposed module tiers (44 source, 32 reusable, 2 compatibility) |
| `docs/architecture/declaration-ownership/lsq-ch20-private-rewrites.tsv` | 151 reviewed private-name rewrites |
| `docs/architecture/migrations/worker-lsq-ch20-migration.md` | this contract |

The route map uses `exact` routes throughout rather than source line ranges.
The reviewed partition is declaration-level and deliberately non-contiguous —
54 declarations were relocated across sibling leaves to break cycles — so an
exact route per declaration is the faithful representation and is strictly more
precise than a range. It also makes the contract independent of source layout,
which is what the later waves rewrite.

Gate command and result:

```text
python tools/architecture/check_lsq_ch20_ownership.py --mode pre \
  --dependency-tsv <frozen base stream> \
  --routes docs/architecture/declaration-ownership/lsq-ch20-routes.tsv \
  --manifest docs/architecture/declaration-ownership/lsq-ch20-ownership.tsv \
  --tiers docs/architecture/declaration-ownership/lsq-ch20-tiers.tsv \
  --skip-cross-lane --project-root .
-> pre mode passed: 5129 declarations, 72 destinations, 244 owner edges,
   manifest sha256 288CA74AD3534B6B7E39D38B11BDF831738643392F4C13A4C898BA0309722D63
```

`--skip-cross-lane` is used in `pre` mode only, because at the frozen base the
destination modules do not exist yet, so no destination can yet carry the
frozen QR imports. The cross-lane contract is enforced unconditionally in
`stage` and `post` mode.

## 9. Remaining lane work

1. ~~Base `lake build NumStability` and the `.ilean` freeze~~ — done, see §4.5.
2. Wave group 1 — `LSQRSolve` and `LSPerturbation`.
3. Wave group 2 — the normal-equations family.
4. Wave group 3 — `LSE`, GQR and KKT, with the seven frozen QR imports retained
   and QR-dependent Chapter 20 tails in separate late commits.
5. Wave group 4 — every remaining Chapter 20 owner in dependency order.
6. Wrappers, canonical and source aggregates, isolated canonical-only and
   old-only tests, then the full static, focused, downstream and global gates.
7. Delivery report and `scripts/deliver_local.ps1`.

Each wave commits on `codex/org-lsq-ch20` after its own scope, ownership stage,
focused build, canonical-only/old-only test, axiom and `git diff --check` gates
pass. The branch is never pushed; the integrator reads it from the shared local
repository.
