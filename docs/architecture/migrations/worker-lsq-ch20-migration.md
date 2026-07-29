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

> **Superseded by §16.2.** This diagnosis was right about the mechanism and wrong
> about the remedy. The narrowing was self-inflicted: the wrapper generator
> forwarded only destinations and dropped the historical import list, which the
> packet contract preserves. Restoring it fixes the case inside the lane, and no
> consumer retarget is required.

### 13.3 Owner order is a hard constraint

A destination may only import destinations that already exist, and a reusable
destination may never import a legacy wrapper. Owner `A` must therefore migrate
after owner `B` whenever a declaration of `A` uses a declaration of `B`.
Computing that DAG shows **34 of 41 owners are transitively blocked by
`LSQRSolve`**, which is itself blocked on the `MatrixInversion` retarget.

> **Partly superseded by §16.1.** The ordering constraint itself is real and still
> governs the wave schedule. The attribution was wrong: `LSQRSolve` was blocked by
> the private-visibility defect of §13.1, not by `MatrixInversion`.
> `MatrixInversion` is a *consumer* of this lane — it appears in the patch set only
> as an `add_import` row — and no declaration of `LSQRSolve` depends on it. With
> §13.1 fixed, `LSQRSolve` migrates and the 33 owners behind it schedule normally.

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

> **Superseded by §16.** All three obstructions turned out to be lane-owned. 13.1
> was a defect in this lane's own ownership contract, and the two "consumer
> retarget" cases were caused by this lane's wrapper generator dropping the
> historical import list. Nothing here required work outside the lane, and the
> reachability table above is void — see §16.3 for the derived schedule.

## 15. Corrected blocker partition and critical path

Section 14 assigned some owners to two categories at once. Assigning each
unmigrated owner exactly one *primary* blocker gives a clean partition of all 41:

| Primary blocker | Owners |
| --- | --- |
| Private cross-boundary defect (13.1) | 8 |
| Ordering behind a blocked owner (13.3) | 28 |
| Non-lane consumer retarget (13.2) | 1 |
| Migrated | 4 |

Owners **READY** to migrate right now: **0**.

> **Superseded by §16.3.** Correct under the defective contract, and the section's
> own conclusion — that private co-location was the critical path for 36 of 41
> owners — is what turned out to matter. With the contract corrected the count is
> **37**: every remaining owner is reachable, in 7 waves.

### The private-visibility defect is the critical path

`LSQRSolve` is itself in the private-defect set, with **62** private-declaration
uses crossing a destination boundary. It is therefore blocked by the contract
defect independently of the `MatrixInversion` retarget. Because 28 further owners
are ordered behind `LSQRSolve` and `LSE` (31 cross-boundary uses of its own), the
consequence is:

> Applying the two scheduled consumer retargets alone unblocks **no** owner.
> Fixing private-declaration co-location in the ownership contract is the
> critical path for **36** of the 41 owners.

Full per-owner counts of cross-boundary private uses:

| Owner | Uses |
| --- | --- |
| `LSQRSolve` | 62 |
| `LSE` | 31 |
| `Higham20Lemma20_11` | 11 |
| `Higham20Theorem20_4Absorption` | 4 |
| `Higham20Lemma20_12` | 2 |
| `Higham20Theorem20_10` | 2 |
| `Higham20Equations` | 1 |
| `Higham20RowSorting` | 1 |

Declaration-level evidence for the two owners that were actually attempted: the
private declarations `singularValue_ne_zero_iff_le_rankIndex`,
`pseudoinverse_output_mem_gramRange`, `leadSpan_eq_gramRange_of_rankIndex`,
`rangeProjection_complex_action_le`, `gramRange_eq_adjointRange`,
`domainProjection_fixes_adjointRange`,
`higham20_lemma20_12_rangeProjection_idempotent` and
`higham20_lemma20_12_rangeProjection_mul_complement_bound` are all routed to
`…LeastSquares.Projection` while `Source.Higham.Chapter20.Lemma11` and
`…Lemma12` use them.

### Suggested contract amendment

Add a co-location constraint to the route/ownership generator and to the lane
checker: for every private declaration `p`, every declaration that uses `p` must
share `p`'s destination. Equivalently, contract the declaration graph over
private nodes before assigning destinations, so a private declaration and its
users form one indivisible unit — the same treatment already given to a
`structure` and its co-generated projections. This is checkable statically from
the frozen format-2 stream and needs no build.

## 16. Correction: the lane was never externally blocked

Sections 13–15 concluded that the lane could not be completed from inside its own
scope. That conclusion was wrong, and the error was mine in both halves. Both
obstructions were defects in artifacts this lane owns.

### 16.1 `LSQRSolve` was blocked by §13.1, not by `MatrixInversion`

§13.3 attributed the blockage of 34 owners to `LSQRSolve` "being blocked on the
`MatrixInversion` retarget". That attribution does not survive checking:

- No declaration of `LSQRSolve` depends on any declaration of
  `NumStability.Algorithms.MatrixInversion`. `MatrixInversion` is a *consumer* of
  this lane; it appears in the patch set only as an `add_import` row.
- §15 had already established the real cause — `LSQRSolve` carried 62 of the 114
  cross-boundary private uses, so it was blocked by the contract defect
  "independently of the `MatrixInversion` retarget". §13.3 simply named the wrong
  one.

The ordering constraint of §13.3 is itself real and still governs the schedule.
Only the root attribution was wrong.

Confirmation that the fix is the operative one: the two owners that become
immediately migratable under the corrected contract are exactly
`Higham20Lemma20_11` and `Higham20Lemma20_12` — the two whose migration had
previously failed with unknown-identifier errors.

### 16.2 A compatibility wrapper must re-state its historical imports

§13.2 diagnosed the mechanism correctly — an exact import-only wrapper forwards
only its destinations, so the transitive surface narrows — and then drew the wrong
conclusion, that a non-lane consumer retarget was required.

The narrowing was self-inflicted. `generate_structural_import_contract` gave each
wrapper only its destinations and dropped the historical import list, which the
packet contract preserves alongside declarations, signatures, bodies and
visibility. `Higham20Problem20_3` has exactly one historical import,
`Higham20MPProse`; dropping it is what removed `complexMatrixOp2`,
`rectRightGramEigenbasis` and `rectRightGramProjectedColumn` from
`SpectralConvergence`'s view. Those three live in
`NumStability.Analysis.SingularValues.Basic` and
`NumStability.Algorithms.RandNLA.LowRankApprox`, both reached *through* the
historical module. Re-stating the historical import restores them.

The wrapper surface is now destinations ∪ frozen historical imports, read from the
blob-verified pristine copy rather than the worktree — after a wave the worktree
file is already the wrapper, so reading it back would preserve nothing. Two
regression cases cover it, and the wrapper emitter was reduced to a single
authority: the contract artifact.

### 16.3 Derived schedule

With no blocker hardcoded, the owner graph is acyclic and every remaining owner is
reachable:

| | |
| --- | --- |
| Owners | 41 |
| Migrated before this correction | 4 |
| Owners with a cross-boundary private use | **0** (was 8) |
| Owners with no schedulable position | **0** (was 37) |
| Waves to migrate the remaining 37 | **7** |
| Declarations still to relocate | 4,788 |

Wave 5 is `LSQRSolve` (1,485 declarations) with `Higham20Lemma20_11`,
`Higham20Lemma20_12` and `Higham20Problem20_3`; wave 6 is `LSE` (1,982) with nine
others; waves 7–11 hold the remaining 893.

### 16.4 Applying the corrected contract invalidated the applied waves

One consequence was not anticipated and is worth recording. Co-location moved some
declarations of already-migrated owners into destinations dominated by a later
wave — `LSNormalEquations` gained declarations destined for
`LinearSystems.LeastSquares.AugmentedSystem`, which `LSQRSolve` populates. Writing
the end-state wrapper contract for a migrated owner therefore produced
`bad import` for a module that did not exist yet.

`--mode pre` did not catch it because it validates the contract artifact, not the
files on disk. The rule is that a wrapper may only be written once every
destination it names exists, so the emitter now refuses to write a wrapper naming
an absent module, and each wave re-emits the cumulative migrated owner set rather
than just the new owners.

The same retarget has a second, sharper consequence: it can *empty* a destination
an earlier wave already created. `LinearSystems.LeastSquares.NormalEquations` was
created by wave 2, and the corrected contract routes **0** declarations to it — all
five of its declarations (`normalEquationsCrossProductExampleA`,
`normalEquationsCrossProductExample_gram_eq`,
`normalEquationsCrossProductExampleRoundedGram`,
`normalEquationsCrossProductExampleRoundedGram_singular`, `normalEqCholeskyXHat`)
now belong to `LinearSystems.LeastSquares.AugmentedSystem`. The old file kept its
copy, the family aggregate imported both, and Lean would have reported duplicate
declarations. Emptied destinations are now reported on every apply, checked against
their declarations' new homes, and removed.

Both hazards share one cause: a contract correction applies to the whole plan,
while the worktree holds only the waves applied so far. The invariant is that after
each wave the worktree must equal what the *current* contract prescribes for the
migrated owner set, not what an earlier contract prescribed.

## 17. Correction: dissolving `Equality.GQR` was an over-correction

§16 fixed the private co-location defect but paid far too much for it. The fix in
commit `9452c36ea` dropped `Equality.GQR` and `Equality.KKT` from the cycle
breaker's protected set, justified like this:

> Two private helper groups straddle the intended equality-constrained-LS / GQR /
> KKT split ... those groups bind the three sub-families into one module.

That inference is false. A straddling co-location group binds **its own members**,
not the sub-families those members happen to belong to. Measured on the frozen
stream: of the 708 declarations the reviewed assignment sends to
`Equality.{Basic,GQR,KKT}` there are **581** co-location components, and exactly
**2** straddle that trio. Confining just those two to the module already holding
most of each moves **9** declarations and leaves Basic = 400, GQR = 301, KKT = 7,
with **0** cross-module private uses.

The two straddlers are:

| Declarations | Private | Spans |
| --- | --- | --- |
| 20 | 8 | `Equality.GQR` 12, `Equality.Basic` 6, `Equality.KKT` 2 |
| 5 | 3 | `Equality.GQR` 3, `Analysis...Equality.Perturbation` 1, `Equality.Basic` 1 |

An earlier draft of this section described the second as "spanning Basic and GQR".
That was wrong: it also reaches the analysis-tier `Equality.Perturbation`, so it is
cross-tier. The narrow root of the first is the private theorem
`rectMatMulVec_zero`, which has 8 public users — 6 GQR-family and 2 KKT-family — so
module-scoped privacy files those 2 KKT declarations with the GQR cluster.

Both figures above are scoped to the `Equality.{Basic,GQR,KKT}` trio. Lane-wide the
reviewed assignment has **29** straddling components, which is why co-location
still has real work to do; the point is only that none of them binds the equality
sub-families together.

Removing the protection instead let the cycle breaker merge the boundaries away,
and it took four more destinations with them. Across the whole lane:

| Contract | Destinations | Cross-boundary private uses | Declarations displaced from the reviewed assignment |
| --- | --- | --- | --- |
| Reviewed (`7d876bc24`) | 72 | 114 | 0 |
| `9452c36ea` (over-merged) | 68 | 0 | 556 |
| Corrected | **72** | **0** | **161** |

The six destinations `9452c36ea` destroyed — `LinearSystems.LeastSquares.Basic`,
`Equality.GQR`, `Equality.KKT`, `MGS`, `NormalEquations` and `Projection` — were
every one of them recoverable by a component-granularity merge. This also
reframes §16.4: `LinearSystems.LeastSquares.NormalEquations` was not legitimately
emptied, it was collateral damage, and it holds declarations again.

The restored protected set adds the six boundaries the packet's semantic target
names.

A first attempt at this section also dropped `Equality.KKT`, claiming `GQR` and
`KKT` "form a genuine two-destination import cycle that relocation cannot break".
That was wrong as well. The reviewed contract has **0** declaration edges between
the two, in either direction; the cycle is manufactured by the breaker itself,
which expands every mover to its whole private group and so drags GQR material
across the boundary, then re-sights the flipped component and calls it symmetric.

`Equality.KKT` is therefore restored, but *after* the breaker rather than by
protecting it. Protecting it deadlocks the breaker — it may then neither merge the
pair nor stop relocating between them, and the graph never settles. Restoration
runs on the settled acyclic graph and returns a rule-assigned member only when its
entire co-location group is rule-assigned to that leaf, so no straddling group is
split and no foreign material follows. Six of the eight reviewed KKT members return;
the two that stay are privacy-forced, sharing the private `rectMatMulVec_zero` with
six `GeneralizedQRFactorization` users. The ninth reviewed member is private and
correctly belongs to `Source.Higham.Chapter20.Theorem10`.

All four required parts now exist as separate modules:

| Required part | Destination | Declarations |
| --- | --- | --- |
| equality-constrained LS | `Algorithms...Equality.Basic` | 388 |
| GQR | `Algorithms...Equality.GQR` | 294 |
| KKT | `Algorithms...Equality.KKT` | 6 |
| perturbation | `Analysis...Equality.{Perturbation,MixedStability,RowwiseBackwardError}` | 495 / 223 / 522 |
| source correspondence | `Source.Higham.Chapter20.Theorem08.LSE` | 59 |

Documented residual: two KKT-semantic theorems
(`LSEKKTSystem.eq_zero_of_homogeneous`,
`LSEKKTSystem.sourceResidual_of_lagrange_normal_equations`) are filed with GQR.
Promoting the one utility lemma they share would move them, but promotion is the
mechanism this lane does not use — see the note below.

The cross-lane carrier for `LSE -> QR.GramSchmidtPolar` returns to `Equality.GQR`,
where the generalized-QR material that uses the polar factorization lives.

Verified state: `pre` mode passes with 5,129 declarations, 4,694 command groups,
**72** destinations, 245 owner edges, all 19 LS-to-QR and 4 QR-to-LS base imports
(4,221 typed edges), 1,680 private declarations with 0 cross-destination uses, 0
straddling spans, 0 wrapper-induced cycles, 0 reusable-to-source and 0
algorithm-to-analysis edges, 0 mixed-tier destinations, and manifest SHA-256
`D4EF42683595A9910A3A0F9AB4A6733D8BCD0898CB33A174992BAD547B4DB9B3`.

### New gate: no orphaned canonical module

The emptied-destination hazard of §16.4 is now a lane gate rather than a lesson.
`validate_no_orphaned_destinations` requires every canonical module on disk under
the three lane roots to own at least one manifest declaration, excluding the
preserved source leaves and the structural aggregates. A destination emptied by a
retarget is reported by name, statically, instead of surfacing as a duplicate
declaration once the build reaches the family aggregate — far from the change that
caused it. It runs in stage and post mode, where the worktree is inspected, and it
has a self-test case.

### Static verification of the re-emitted wave

Because the corrected contract changes destinations for owners that were already
migrated, waves 1–3 were re-emitted together with wave 4's owners from the
cumulative migrated set. Everything checkable without a build:

| Check | Result |
| --- | --- |
| Declaration spans byte-identical to the frozen sources | 1,799 / 1,799 |
| Destinations emitted | 23 |
| Namespace balance, import sorting, duplicate imports | 23 / 23 clean |
| Public declarations defined in two modules, lane paths | **0** |
| `NumStability` imports resolving, whole tree | 4,207 / 4,207 |
| Test probes reachable from their own imports | 121 / 121 |
| Import cycles, full 1,534-module graph | 0 |
| Canonical modules owning no manifest row | 0 |
| Checker self-test, lane scope contract, `git diff --check` | pass |

The two public names that *are* defined twice in the repository —
`NumStability.infNorm_add_le` in `Algorithms/Horner.lean` and
`Algorithms/MatrixPowers.lean`, and
`FloatingPointFormat.finiteSystem_exists_int_mul_minSubnormalMagnitude` in two
Chapter 2 modules — are pre-existing at the frozen base and lie entirely outside
this lane.

### A note for the integrator on private promotions

The review branch `codex/review-lsq-contract-repair` resolves the same defect
differently, by promoting 55 authored-private declarations to public under a
frozen `lsq-ch20-private-promotions.tsv` mapping. That achieves the same split but
changes visibility, which the packet preserves. The measurement above shows the
promotions are **not** required: component-granularity co-location reaches 0
cross-boundary private uses with every private declaration still private, and with
`Equality.GQR` intact. If the two contracts are reconciled, this lane's version
needs no visibility change.
