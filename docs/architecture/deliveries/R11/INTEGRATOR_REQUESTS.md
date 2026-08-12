# R11 integration boundary

R11 edited no shared path. Every change is inside the 65 B0003 owned paths, the three
authorized production destination prefixes, `NumStabilityTest/Reorganization/R11/`, and
`docs/architecture/deliveries/R11/`. `CHECK_SCOPE.py` proves this against B0003's own
`owned_paths`, `destination_prefixes` and 2,580 `forbidden_paths` entries, and separately
proves that none of R0003's 133 paths was touched.

## R0003 is already frozen and needs nothing from this wave

R0003 is integrator-owned and complete. It carries 133 paths against C0001 preimages:

| paths | content |
| ---: | --- |
| 129 | production consumers whose imports retarget onto the R11 destinations (209 replacements; 43 paths carry more than one) |
| 1 | `NumStabilityTest.lean` — adds `import NumStabilityTest.Reorganization.R11.All` |
| 1 | `docs/architecture/tiers.json` |
| 1 | `docs/architecture/layout-exceptions.json` |
| 1 | `docs/architecture/COMPATIBILITY.md` |

`CHECK_REQUEST_REPLAY.py` validates it without applying it to this branch:

* all four request artifacts hash to their pinned values;
* all 133 preimage blob OIDs are exactly the C0001 blobs;
* forward replay reproduces all 133 pinned postimage SHA-256 values;
* reverse replay restores all 133 pinned preimage SHA-256 values;
* all 209 recorded replacements occur, with the old import gone and the new one present.

The frozen root import is `NumStabilityTest.Reorganization.R11.All`, so the R11 aggregate
is delivered at `NumStabilityTest/Reorganization/R11/All.lean` — inside the authorized
prefix. No new shared-file request is needed, and none is made.

Replaying the patch requires `core.autocrlf=false`. This machine sets `core.autocrlf=true`
at system level, and a scratch repository has none of the project's `.gitattributes`; left
alone, `git apply` writes CRLF, every postimage hash differs, and reverse replay cannot
restore the preimages byte-exactly even though the content is correct.
`CHECK_REQUEST_REPLAY.py` pins LF for exactly this reason.

## Worker-view gates: six findings, all closed by R0003

Two gates are nonzero at the worker tip. Every finding is integrator-owned, and each one
is closed by applying R0003 — verified, not assumed: `CHECK_REQUEST_REPLAY.py --full`
rebuilds the tree with the 133 postimages overlaid and none of these six reappears.

`check_layout.py` — exit 1, three errors:

| # | finding | closed by |
| ---: | --- | --- |
| 1 | `NumStabilityTest does not reach 205 test module(s)` | R0003's `NumStabilityTest.lean` postimage adds `import NumStabilityTest.Reorganization.R11.All` |
| 2 | `stale missing module docstrings baseline` listing exactly the 59 `Algorithms.QR.*` wrappers | R0003's `layout-exceptions.json` postimage removes those 59 entries |
| 3 | `stale declaration bearing umbrellas baseline` listing `Chapter19.Sensitivity` and `Chapter19.StoredLoop` | R0003's `layout-exceptions.json` postimage removes both entries |

Findings 2 and 3 are worth naming for what they are: **improvements that outran a ratchet
baseline**. Adding module documentation to 59 previously undocumented wrappers, and
emptying the two Chapter 19 umbrellas of declarations, both moved the tree in the
direction the ratchets exist to enforce. The checker asks for `--write-baseline`, which is
an integrator-owned control file, so the worker records the improvement instead of
ratcheting it. No gate was weakened and no baseline was rewritten from this branch.

`check_compatibility.py` — exit 1, three errors, one per retargeted wrapper:

```
NumStability.Algorithms.QR.HouseholderApplySupport:
  imports ('…QR.Householder.PanelApplication',) documented ('…QR.HouseholderApplySupport',)
NumStability.Algorithms.QR.HouseholderQRSupport:
  imports ('…QR.Householder.StoredQR',)        documented ('…QR.HouseholderQRSupport',)
NumStability.Algorithms.QR.HouseholderSpecSupport:
  imports ('…QR.Householder.TrailingPanels',)  documented ('…QR.HouseholderSpecSupport',)
```

These are precisely the three import retargets `B0003-module-routes.tsv` mandates. The
`COMPATIBILITY.md` rows that document them are integrator-owned, and R0003's postimage
rewrites exactly those three rows to the new destinations. The mismatch is therefore the
expected transient state of a worker branch whose shared request has not yet been applied.

`check_provenance.py` passes at the worker tip (exit 0).

## Two integrator-only findings that R0003 alone does not close

`CHECK_REQUEST_REPLAY.py --full` builds the acceptance tree — R11 worker code with the
133 R0003 postimages overlaid — and runs the shared checkers on it. `check_provenance.py`
passes (137 Apache-marked production files, 5 evidenced upstream modules). The other two
do not, and neither is fixable from this branch. Both are reported rather than worked
around; no gate was weakened.

### 1. `check_layout.py`: the two Chapter 19 wrappers are classified as aggregates but cannot import their descendants yet

```
error: NumStability.Source.Higham.Chapter19.Sensitivity misses 1 canonical descendant(s):
       NumStability.Source.Higham.Chapter19.Sensitivity.Closure
error: NumStability.Source.Higham.Chapter19.StoredLoop misses 2 canonical descendant(s):
       NumStability.Source.Higham.Chapter19.StoredLoop.AllPivots,
       NumStability.Source.Higham.Chapter19.StoredLoop.StrongModel
```

R0003's `tiers.json` reclassifies both owners as `aggregate` and its
`layout-exceptions.json` adds both as namespace-owning prefixes. An aggregate must import
every canonical descendant. B0003's module route, however, requires each relocated owner
to become an import-only wrapper importing its destination, so each currently imports
exactly one module.

The completion cannot be done on the worker branch, because on this branch it is cyclic:

| module | imports at the worker tip | imports after R0003 |
| --- | --- | --- |
| `…Chapter19.Sensitivity.Closure` | `…Chapter19.Sensitivity` | `…Sensitivity.Bounds.Results` |
| `…Chapter19.StoredLoop.AllPivots` | `…Chapter19.StoredLoop` | `…StoredLoop.Perturbation.Bridge` |
| `…Chapter19.StoredLoop.StrongModel` | `…Chapter19.StoredLoop` | `…StoredLoop.Perturbation.Bridge` |

At the worker tip all three descendants still import the wrapper, so adding
`import …Sensitivity.Closure` to `…Chapter19.Sensitivity` would close the cycle
`Sensitivity → Sensitivity.Closure → Sensitivity` and break the build. All three
descendants are integrator-owned members of the 129 protected consumers, so the worker
cannot retarget them either. Only after R0003 retargets them onto the destinations does
the aggregate completion become acyclic.

Either resolution is available to the integrator, and both are outside this wave:

* after applying R0003, add the missing descendant imports to the two wrapper files
  (`…Chapter19/Sensitivity.lean` gains `Sensitivity.Closure`; `…Chapter19/StoredLoop.lean`
  gains `StoredLoop.AllPivots` and `StoredLoop.StrongModel`), keeping both import-only; or
* leave both classified as they were rather than as `aggregate`.

The first keeps R0003 byte-frozen and is a two-line follow-up; the second changes a
frozen control artifact. Nothing about the 412 relocations or the 1,065 retained
declarations depends on which is chosen.

### 2. `check_compatibility.py`: the retained Chapter 19 outlier imports two newly registered historical paths

```
error: NumStability.Source.Higham.Chapter19.Core: production import uses historical path
       NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport
error: NumStability.Source.Higham.Chapter19.Core: production import uses historical path
       NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport
```

This is a direct collision between two frozen decisions, and it is unresolvable from the
worker branch because both sides are frozen and neither file is writable here:

* B0003 requires `Chapter19/Core.lean` to retain all 1,065 declarations **and its exact
  imports**, as a reviewed source outlier. The file is preserved byte-for-byte and does
  not appear in the changed-path ledger, so its two imports of the historical
  `*Support` owners necessarily survive.
* R0003 registers those two owners in `COMPATIBILITY.md` as forwarding modules, and
  `check_compatibility.py` rejects a production import of a registered historical path.

Retargeting Core's imports would violate the byte-for-byte retention that B0003
explicitly approved; editing `COMPATIBILITY.md` is integrator-owned and already frozen in
R0003. The integrator's options are to exempt `Chapter19.Core` from the
compatibility-import rule for as long as the retention outlier stands, or to retire the
outlier in a later wave and retarget Core's two imports then.

This finding is a property of the frozen contract, not of the implementation: it would
appear for any correct execution of B0003 combined with R0003.

## Read-only invariants held

`NumStability/Analysis/MatrixAlgebra.lean` was not modified. No phase-control record,
selector, projection, request, tool, CI file, Lake file, global aggregate, root document
or `NumStabilityTest.lean` was modified. No historical path was deleted or Git-renamed.
The formal `Rxxxx` registry resolution for R0003 remains the integrator's responsibility;
this wave records no `resolution` field and claims no checkpoint acceptance.
