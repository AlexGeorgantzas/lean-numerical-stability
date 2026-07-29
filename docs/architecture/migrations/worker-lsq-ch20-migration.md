# Worker lane `lsq-ch20` — baseline, route contract, and migration design

Lane: least squares and Higham Chapter 20
Engine: Claude (subscription 3, local-worktree mode)
Frozen base: `6487fc33088523b8f27ecde9ad613515b78f9977`
Branch: `codex/org-lsq-ch20` (local only; never pushed)
Worktree: `C:\Users\qed_s\higham-worktrees\lsq-ch20-claude`

Contract audit repair: branch `codex/review-lsq-contract-repair`, worktree
`C:\Users\qed_s\higham-worktrees\lsq-contract-repair`, based exactly on
`7d876bc241d46e7192be2acaf46bb148aec76908`. The repair changes only contract,
checker, artifact, and report files; the preserved dirty Wave 1 worktree above
was not modified.

A subsequent soundness review tightened that repair without changing the
ownership allocation or any production file. The semantic-stream gate is now
scoped to the exact LS incident contract, so unrelated integrated BlockLU/QR
module moves do not themselves make eventual post mode impossible, while every
declaration row and typed edge touching an LS declaration remains exact. The
review also made the 4,224-row cross-lane base freeze deterministic in pre,
stage, and post mode.
A second review closed two further trust-boundary gaps: selected historical
and canonical owners now contain exactly the 5,129 contracted declarations,
and QR placeholders cannot be resolved from file/import existence or an
unreviewed path.

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
| Authoritative compiler source-command groups owning them | 4,694 |
| Outgoing typed edges from lane declarations | 82,645 |
| Incoming typed edges from outside the lane | 1,722 |

The gap between 5,129 selected declarations and 4,694 authored command groups is
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

The repaired format-2 route contract now records one row for every selected
declaration: its historical actual name, authoritative authored root, all eight
`.ilean` coordinates, `authored` or `compiler_generated` provenance, exact
LF-normalized source-command SHA-256, and destination. All 5,129 rows are
therefore compiler-span-bound; there is no `exact` row form that can bypass the
compiler evidence. The 4,694 authored rows own 435 co-generated rows.

The checker enforces that every declaration sharing a compiler command shares
its tier, destination, span and command hash. Where a command initially
straddled tiers, the **most restrictive** tier won: if any member had to be
source because it reached source material, the whole command moved to source.
That rule was monotone, was interleaved with the two dependency fixpoints, and
converged to **0** command groups straddling a destination.

Correcting this moved 248 declarations relative to the first manifest, of which
39 moved from a reusable tier into `Source/Higham/Chapter20` precisely because a
structure's projections forced their span up. The remaining 209 are within-tier
consolidations.

An independent cross-check confirms that every authored root has exactly the
committed `.ilean` span and that all 5,129 declarations resolve to one of those
roots. Pre mode re-hashes all 42 frozen sources and all 41 `.ilean` files. Stage
and post mode then locate every authored root in the candidate owner's `.ilean`
and hash the candidate source command. Consequently a same-kind, same-edge edit
to a declaration body or type is rejected even when the declaration and typed
dependency streams would otherwise look unchanged.

### 4.4 Frozen historical owners

All 42 pristine historical sources were copied to the external, non-repository
directory `PACKET_ROOT/runtime/frozen-owners`. The committed
`lsq-ch20-frozen-owners.tsv` records the module, repository path, Git blob
ID re-verified against the frozen base, source SHA-256, physical and non-blank
line counts, and the compiled `.ilean` SHA-256 and size. Its SHA-256 is
`1B56CB65B129D7CCA113CECFE7324A2FEB22C301037A77537BB4ECA65252A524`.

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

The 19 frozen `LS_TO_QR` and four `QR_TO_LS` direct imports are expanded into a
4,224-row machine-readable normalization contract: 4,221 exact typed
declaration edges and three import-only edges. It records the known LS
destination on every row and either the stable QR owner or an explicit
`@QR_OWNER_REQUIRED:*` token.

The QR lane's canonical owner map is not available at this base. Therefore
1,628 rows remain intentionally unresolved, representing 68 exact QR
declarations and one import-only carrier. This is a hard post-mode failure, not
a waiver. Pre and stage require every placeholder and status to remain byte-for-
byte unchanged unless the coordinator supplies both `--qr-handoff` and its
separately reviewed `--qr-handoff-sha256`.

That handoff has 69 exact identities. It records the QR delivery commit and
ownership-artifact SHA-256, maps each historical QR declaration exactly once,
and maps the import-only carrier by its complete frozen module pair. Its owner
rows must equal the generated placeholder identity set with no missing or extra
row. Post requires the handoff, requires all 1,628 rows resolved exactly as it
specifies, checks each QR declaration's actual candidate owner, requires the
normalized direct imports in both directions, and rejects all production
imports of LS or Higham19 compatibility wrappers. File existence or a matching
import is never accepted as evidence for the carrier. The four QR reverse
consumers therefore migrate to canonical LS destinations; they do not retain
their historical LS imports.

In every checker mode, the complete artifact is regenerated from the
SHA-pinned 56,898-declaration baseline plus the compiler-span route/ownership
contract. The checker requires exactly 4,224 immutable base identities, 4,221
typed edge rows, three import-only rows, and the exact LS destination on every
row. An already-canonical QR owner is immutable. An
`@QR_OWNER_REQUIRED:*` field and its status may change only to the exact owner
in the hash-pinned handoff; deleting a row, replacing an LS owner with another
valid destination, inventing a declaration owner or carrier, or changing a
stable QR owner is rejected before stage/post graph validation.

## 6. Lane ownership checker

`tools/architecture/check_lsq_ch20_ownership.py` implements the lane contract
with `--mode pre`, `--mode stage`, `--mode post` and `--self-test`.

- `pre` verifies the frozen stream digest, all source and `.ilean` hashes, all
  5,129 compiler-span routes and command fingerprints, the unchanged ownership
  manifest, the 244-edge typed destination DAG, all 46 exact wrapper/aggregate
  import contracts, the 121-module tier surface, all 23 base cross-lane imports
  and their 4,221 typed edges, and the 203 exact coordinator patch rows.
- `stage` accepts a partially migrated tree: it takes the completed
  destinations, requires reviewed private-name rewrites only for those, proves
  candidate ownership, re-hashes every candidate source command, regenerates
  and verifies the full 4,224-row cross-lane freeze, requires exact normalized
  equality for every LS declaration and every typed edge incident to one, and
  requires the exact declaration-name set in every LS historical/canonical
  owner. It also checks each completed destination's exact direct lane-DAG
  imports and each completed wrapper/aggregate's exact imports.
  Declaration/module moves whose owners and edge endpoints are wholly outside
  the LS contract are deliberately ignored.
- `post` additionally requires all destinations complete, all 151 reviewed
  private rewrites, every wrapper and aggregate, the hash-pinned 69-identity QR
  handoff, all placeholders resolved exactly from it, all coordinator
  imports/root tests/tier rows/compatibility rows, and proves that no reusable
  destination transitively reaches a `Source.*`, `Higham.*`, legacy
  least-squares, or `Analysis.HighamChapter7` module.

`--self-test` passes. It positively proves that an unrelated synthetic
declaration may move from `Other.Old` to `Other.New` while its non-LS edge is
unchanged, and rejects each of these mutations:

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
11. a lost contracted LS-incident typed edge;
12. an extra typed edge;
13. a lost declaration self-edge;
14. a baseline stream whose digest changed;
15. a reusable module importing a canonical source leaf;
16. a reusable module transitively reaching `Analysis.HighamChapter7`;
17. a missing or extra direct destination-DAG import;
18. a dropped normalized cross-lane import;
19. an unresolved QR canonical owner;
20. a final production import of a compatibility wrapper;
21. a wrapper that still owns a compiled declaration;
22. a wrapper whose exact import set drifted, contains non-import code, has an
    unsorted import list, or has no module
    docstring;
23. proposed tier rows that omit wrappers/umbrellas, contradict a destination
    role, or declare a `mixed` tier;
24. an unapplied coordinator consumer/root/tier/compatibility patch;
25. a format-1 exact route attempting to bypass compiler spans;
26. co-generated declarations split from their source command;
27. compiler coordinates differing from the frozen `.ilean`;
28. a same-kind, same-edge source-command semantic edit; and
29. a manifest digest mismatch;
30. a truncated cross-lane normalization artifact;
31. replacement of a frozen LS destination by a different destination that is
    otherwise valid for the same historical owner; and
32. replacement of an already-canonical QR owner;
33. a QR placeholder resolution without a handoff or with a mismatched handoff
    hash;
34. a false QR declaration owner or import-only carrier despite a matching
    file/import shape; and
35. an edge-free public declaration added to a selected historical/canonical
    owner.

## 7. Integrator requests

Shared edits are required. The exact request is
`docs/architecture/migrations/worker-lsq-ch20-integrator-request.md`; its
machine-readable authority is `lsq-ch20-coordinator-patches.tsv` (203 rows,
SHA-256
`75E210F086105D5E1C2E61FD974A5022BA2A51FB602C21C6FE3E2DF6AD3FAB63`).
It covers root/registration aggregates, all five non-lane/root production
consumers, 44 exact and two prefix tier registrations, all 41 new
`COMPATIBILITY.md` rows, three root-test imports, and the final layout ratchet.
The QR-owned edits remain blocked on its canonical owner map and are frozen as
rejecting placeholders rather than guessed paths.

## 8. Committed contract artifacts

| Path | Content |
| --- | --- |
| `tools/architecture/check_lsq_ch20_ownership.py` | lane checker, pre/stage/post modes plus self-test |
| `docs/architecture/declaration-ownership/lsq-ch20-routes.tsv` | 5,129 compiler-span routes; SHA-256 `4B6079A931A0986B7455F24228F68B88BDCB165234BBF3BE556E48E6412DDD0E` |
| `docs/architecture/declaration-ownership/lsq-ch20-frozen-owners.tsv` | 42 frozen source/blob rows and 41 `.ilean` hashes; SHA-256 `1B56CB65B129D7CCA113CECFE7324A2FEB22C301037A77537BB4ECA65252A524` |
| `docs/architecture/declaration-ownership/lsq-ch20-ownership.tsv` | unchanged 5,129-row ownership allocation; SHA-256 `288CA74AD3534B6B7E39D38B11BDF831738643392F4C13A4C898BA0309722D63` |
| `docs/architecture/declaration-ownership/lsq-ch20-tiers.tsv` | exact 121-module surface: 44 source, 34 reusable, 43 compatibility; SHA-256 `39EFB2528AC96A28A12DB9EDFC1E11F60695F90929F3C47EC8D19F8C8FB96CA4` |
| `docs/architecture/declaration-ownership/lsq-ch20-structural-imports.tsv` | exact 175 imports for 43 wrappers and 3 aggregates; SHA-256 `93114D5CF9B1100D9F87C8E0A8D1F4ADE574CD845DBD91C296A854DDD2B0620F` |
| `docs/architecture/declaration-ownership/lsq-ch20-destination-dag.tsv` | exact 244 typed destination edges; SHA-256 `6F1D0003429EF4C8F3327B837B811660D2875A86B87F90C75D8BC7975CFD1420` |
| `docs/architecture/declaration-ownership/lsq-ch20-cross-lane-normalization.tsv` | 4,224 base/final QR-LS normalization rows; SHA-256 `056DA202B1D8C3FC6F6ED540B6064D094D89455A43848FBEA175C06DAFE8384F` |
| `docs/architecture/declaration-ownership/lsq-ch20-coordinator-patches.tsv` | 203 exact shared-file patches; SHA-256 `75E210F086105D5E1C2E61FD974A5022BA2A51FB602C21C6FE3E2DF6AD3FAB63` |
| `docs/architecture/declaration-ownership/lsq-ch20-private-rewrites.tsv` | 151 reviewed private-name rewrites; SHA-256 `4DC6977FE8DA3DA01940FEEEBC5D79D6F3970B7CA9E75CF3362237DE3DB4FAC8` |
| `docs/architecture/migrations/worker-lsq-ch20-migration.md` | this contract |
| `docs/architecture/migrations/worker-lsq-ch20-integrator-request.md` | exact human-readable coordinator handoff |

The ownership allocation is byte-identical to `7d876bc`; only its evidence and
enforcement were repaired. All 5,129 route rows now name their compiler command
and fingerprint. Co-generated declarations cannot be routed separately, and
candidate source text cannot change while hiding behind the same declaration
kind and dependency edges.

Gate command and result:

```text
python tools/architecture/check_lsq_ch20_ownership.py --mode pre \
  --dependency-tsv <frozen base stream> \
  --routes docs/architecture/declaration-ownership/lsq-ch20-routes.tsv \
  --manifest docs/architecture/declaration-ownership/lsq-ch20-ownership.tsv \
  --tiers docs/architecture/declaration-ownership/lsq-ch20-tiers.tsv \
  --frozen-source-dir <PACKET_ROOT>/runtime/frozen-owners/source \
  --frozen-ilean-dir <PACKET_ROOT>/runtime/frozen-owners/ilean \
  --project-root .
-> pre mode passed: 5129 declarations, 4694 compiler command groups,
   72 destinations, 244 owner edges, 19 LS-to-QR and 4 QR-to-LS base imports
   (4221 typed edges), manifest sha256
   288CA74AD3534B6B7E39D38B11BDF831738643392F4C13A4C898BA0309722D63
```

There is no cross-lane skip option. Pre validates the exact base edges and,
because no authoritative QR handoff is committed, all placeholders unchanged.
Post is deliberately blocked until the QR lane supplies the 69-identity map and
the coordinator separately records its SHA-256; it then validates the fully
canonical normalization and fails on every unresolved or mismatched owner.

## 9. Remaining lane work

1. ~~Base `lake build NumStability` and the `.ilean` freeze~~ — done, see §4.5.
2. Wave group 1 — `LSQRSolve` and `LSPerturbation`.
3. Wave group 2 — the normal-equations family.
4. Wave group 3 — `LSE`, GQR and KKT, with QR-dependent Chapter 20 tails in
   separate late commits and every QR import normalized through the resolved
   hash-pinned cross-lane handoff contract.
5. Wave group 4 — every remaining Chapter 20 owner in dependency order.
6. Wrappers, canonical and source aggregates, isolated canonical-only and
   old-only tests, then the full static, focused, downstream and global gates.
7. Delivery report and `scripts/deliver_local.ps1`.

Each wave commits on `codex/org-lsq-ch20` after its own scope, ownership stage,
focused build, canonical-only/old-only test, axiom and `git diff --check` gates
pass. The branch is never pushed; the integrator reads it from the shared local
repository.

## 10. Implementation wave 1 — `LSPerturbation`

This wave consumes the committed lane contract rather than regenerating one: the
declaration-to-destination map is read straight from
`docs/architecture/declaration-ownership/lsq-ch20-ownership.tsv`. All 5,129
manifest rows map onto the authoritative `.ilean` spans with 0 unmatched rows and
0 spans straddling two destinations.

### Why this wave is `LSPerturbation` alone

Migrating owner `H` replaces it with a wrapper importing `H`'s destinations, so
every external module that imports `H` comes to depend on those destinations. If a
destination also depends on such a module, the tree cycles. Simulating the module
graph for candidate wave sets gives:

- all 41 declaration-bearing owners are migratable **alone** without a cycle;
- a greedy set of **40** owners is buildable together;
- exactly **one** owner, `LSQRSolve`, cannot join, because its destinations depend
  on `Algorithms.RandNLA.LowRankApprox`, which reaches
  `Algorithms.MatrixInversion`, which imports `LSPerturbation`.

`MatrixInversion` is not in `OWNED_PATHS.txt`, so the lane cannot retarget it. The
integrator patch set already schedules exactly that retarget, so `LSQRSolve` is
deferred until it lands. Wave composition is a lane decision, so this wave takes
the buildable part rather than blocking on a shared edit.

### Result

| Destination | Spans | Content |
| --- | --- | --- |
| `Analysis.Perturbation.LeastSquares.Basic` | 1 | structure `LSAugmentedPerturbation` and its members |
| `Analysis.Perturbation.LeastSquares.Wedin` | 216 | reusable Wedin perturbation analysis |
| `Source.Higham.Chapter20.Lemma11.Support` | 27 | Lemma 20.11/20.12 source support, including every Chapter 7 user |

`Algorithms.LeastSquares.LSPerturbation` is now an exact import-only wrapper over
those three modules, with a module docstring and sorted imports.

### Gate results

| Gate | Result |
| --- | --- |
| Every declaration span byte-identical to the frozen pristine source | pass (244 spans) |
| Import cycles in the live tree | **0** (was 7) |
| `check_scope.py` | pass |
| `git diff --check` | pass |
| Placeholder scan (`sorry`/`admit`/`axiom`/`constant`) | 0 hits |
| Focused build incl. downstream `MatrixInversion`, `RandNLA.LowRankApprox` | pass, 3102 jobs, exit 0 |
| Canonical-only and isolated old-only tests | pass, 3048 jobs, exit 0 |
| Axiom probes (5 representatives) | all exactly `[propext, Classical.choice, Quot.sound]` |

The old-only test imports only the historical path and still resolves
`LSAugmentedPerturbation` and `wedinLemma20_11_sigmaMinCol`, proving the wrapper
preserves the historical surface.

Superseded pre-contract wave output is retained outside the repository at
`PACKET_ROOT/runtime/wave1-superseded/` (50 files) rather than discarded.

## 11. Implementation wave 2 — `LSNormalEquations`

Commit `7ba0afda5`. The 38 declarations move to
`Algorithms.LinearSystems.LeastSquares.NormalEquations` (5 spans: exact
normal-equation and Cholesky specifications) and
`Analysis.Perturbation.LeastSquares.NormalEquations` (15 spans: Gram product,
vector-error and squared-condition analysis). This wave also creates the reusable
algorithm family aggregate `Algorithms.LinearSystems.LeastSquares`.

Focused build passed with 3110 jobs and exit 0, including the downstream consumer
`Algorithms.RandNLA.LeastSquaresSketch`.

## 12. Implementation wave 3 — printed Chapter 20 examples

Commit `d1447c099`. `Higham20CrossProductExample` (12 declarations) moves to
`Source.Higham.Chapter20.Examples.CrossProduct`; `Higham20GeneralWedin` (32)
splits into `Source.Higham.Chapter20.Examples.GeneralRank` (27 spans of the
printed general-rank counterexample) and
`Analysis.Perturbation.LeastSquares.Wedin` (5 spans of generic Wedin
decomposition).

### Destinations are cumulative, not per wave

Wave 3 adds 5 spans to `Analysis.Perturbation.LeastSquares.Wedin`, which already
held 216 from wave 1. Emitting only the current wave's spans would have
overwritten that module and silently dropped wave 1's content. Destinations are
therefore regenerated from the **cumulative** migrated owner set, and
byte-preservation is verified across every migrated owner on each wave, not just
the current one. `Wedin` correctly carries all 221 spans.

## 13. Measured obstructions

Wave 3 was reduced from five dependency-ready owners to two. Both reasons were
found by building, and neither is visible in the declaration graph alone.

### 13.1 Private declarations may not cross a destination boundary

Lean private names are module-scoped, so a private declaration is invisible
outside the module that defines it. The committed ownership manifest routes
**114 private-declaration uses across a destination boundary**:

| Historical owner of the private declaration | Cross-boundary uses |
| --- | --- |
| `LSQRSolve` | 62 |
| `LSE` | 31 |
| `Higham20Lemma20_11` | 11 |
| `Higham20Theorem20_4Absorption` | 4 |
| `Higham20Theorem20_10` | 2 |
| `Higham20Lemma20_12` | 2 |
| `Higham20RowSorting` | 1 |
| `Higham20Equations` | 1 |

For example private `matMulVec_zero` and `finAppend_left_right` are routed to
`Equality.Basic` while `Equality.GQR` uses them. Migrating
`Higham20Lemma20_11` and `Higham20Lemma20_12` under this manifest fails to
compile with unknown-identifier errors on their own private support
declarations (`singularValue_ne_zero_iff_le_rankIndex`,
`leadSpan_eq_gramRange_of_rankIndex`,
`higham20_lemma20_12_rangeProjection_idempotent`, and others).

No current gate detects this. The checker normalizes and re-checks private
**names** when a declaration moves, but nothing requires a private declaration to
share a destination with every declaration that uses it. Resolving it requires a
contract change: co-locate each private declaration with its users, or make the
required ones non-private, which the lane may not do because visibility is
preserved by contract.

### 13.2 An exact wrapper does not re-export a transitive import surface

Migrating `Higham20Problem20_3` breaks
`Source.Higham.Chapter14.Section05.SpectralConvergence` with 74
unknown-identifier errors (`complexMatrixOp2`, `rectRightGramEigenbasis`,
`rectRightGramProjectedColumn`, ...). That consumer relied on identifiers reaching
it transitively through the historical module's wider import surface. An exact
import-only wrapper deliberately forwards only its destinations, so the surface
narrows. `SpectralConvergence` is a non-lane file and a required
`DOWNSTREAM_BUILDS.txt` target, so this needs the consumer retarget already
scheduled in the integrator patch set.

### 13.3 Owner order is a hard constraint

A destination may only import destinations that already exist, and a reusable
destination may never import a legacy wrapper. Owner `A` must therefore migrate
after owner `B` whenever a declaration of `A` uses a declaration of `B`.
Computing that DAG shows **34 of 41 owners are transitively blocked by
`LSQRSolve`**, which is itself blocked on the `MatrixInversion` retarget.

## 14. Reachability summary

| Status | Owners | Note |
| --- | --- | --- |
| Migrated | 4 | `LSPerturbation`, `LSNormalEquations`, `Higham20CrossProductExample`, `Higham20GeneralWedin` |
| Blocked by the private-visibility defect (13.1) | 8 | needs a contract change |
| Blocked by a consumer retarget (13.2) | 1 | `Higham20Problem20_3` |
| Blocked behind `LSQRSolve` (13.3) | 28 | needs the `MatrixInversion` retarget first |

341 declarations have been relocated byte-identically. Every migrated wave holds
0 import cycles, 0 scope violations, a clean `git diff --check`, 0 placeholders,
and a passing focused build including affected downstream consumers.

All **12** axiom probes across the three waves report exactly
`[propext, Classical.choice, Quot.sound]` (build completed, 3054 jobs, exit 0).

The lane's completion definition cannot be reached from inside the lane's own
scope until 13.1 and the two scheduled consumer retargets are resolved.
