# R02 integrator requests

SEVEN shared changes across seven paths are required that R02 is forbidden to make itself,
plus ONE explicit no-change decision. Requests 1-5 were anticipated from the routing;
requests 6-7 were surfaced by `check_layout` on the applied worktree, and request 7
SUPERSEDES the no-change decision originally recorded below for `Chapter15.lean` — that
earlier entry is retained deliberately so the revision is auditable rather than silently
rewritten. Each request records its exact C0000 blob, the minimal postimage and
its SHA-256, the rationale, the protected tests, the gate it unblocks, and an executable
forward/reverse replay in a disposable C0000 checkout.

R02 does not create the formal `Rxxxx` record. These are requests, not applied changes;
the worker branch contains none of them.

Base: C0000 `b1b18772d80185ec08f49c818919558645c330a1`.

## Why these five exist

R02 relocates the declaration blocks of the two endpoint owners
`Algorithms.NormEstimation.PNorm.Endpoints.{ConvergenceStatements,PNormRectangular}` to the
canonical leaves `PNorm.OneAndInfinityNorms.{Square,Rectangular}`, leaving the owners as
import-only wrappers. Five integrator-owned modules still import the historical wrappers.
Because R02's own canonical destinations import those five, every one of them acquires
**canonical-to-historical reachability** — which the brief prohibits.

The reach is carried **exclusively** by forbidden shared wiring. Measured on the applied
worktree, exactly five production modules import the endpoint owners directly, and all five
are integrator-owned. Every other direct importer is a test module (R02's own old-only
tests, which must import wrappers, and the predecessor wave's tests). **No worker-owned
module carries it**, so no worker edit can remove it. Shortest carrier path:

```
Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.ScalarCase.Iteration   (R02 destination)
  -> Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormRectangular          (integrator-owned)
  -> Algorithms.NormEstimation.PNorm.Endpoints.PNormRectangular                 (R02 wrapper)
```

## The retarget

Both postimages are a pure import substitution — no declaration, signature, proof or
namespace is touched:

| preimage import | postimage import |
| --- | --- |
| `…PNorm.Endpoints.ConvergenceStatements` | `…PNorm.OneAndInfinityNorms.Square` |
| `…PNorm.Endpoints.PNormRectangular` | `…PNorm.OneAndInfinityNorms.Rectangular` |

The import block is re-sorted and de-duplicated, because the layout checker rejects
unsorted aggregate imports.

## Requests 1–5

| # | path | C0000 blob | postimage SHA-256 | endpoint refs |
| --- | --- | --- | --- | ---: |
| 1 | `NumStability/Algorithms/NormEstimation/PNorm/All.lean` | `4eda7a200ae1` | `D28918C3A5FB…` | 2 → 0 |
| 2 | `NumStability/Algorithms/NormEstimation/PNorm/Rectangular/RectangularTermination.lean` | `4b414e0eb931` | `A44599F9371D…` | 1 → 0 |
| 3 | `NumStability/Source/Higham/Chapter15/Lemma02/PNormPowerMethod/PNormRectangular.lean` | `70f68de272fb` | `B3A6F5833A75…` | 1 → 0 |
| 4 | `NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/ConvergenceStatements.lean` | `dd968f7c9889` | `992550C29CE8…` | 1 → 0 |
| 5 | `NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/RectangularTermination.lean` | `d6d736df901b` | `040EA7580F2F…` | 2 → 0 |

**Rationale (all five).** Each imports a historical endpoint wrapper whose declarations
moved to a canonical leaf. Retargeting restores canonical-to-canonical wiring and removes
the only path by which an R02 destination reaches a historical owner. Each is a one-line
substitution against the exact C0000 blob above.

**Gate unblocked.** `destinations reaching a historical owner`, measured by `statics.py`
over the applied worktree, goes from **5 to 0** with these five applied and with nothing
else changed. Verified, not asserted:

```
before postimage: destinations reaching a historical owner = 5
after  postimage: destinations reaching a historical owner = 0
```

The same five are expected to clear any `check_layout` / `--strict-source` finding of the
same shape; see `GATE_RESULTS.tsv` for the worker-branch and with-postimage columns.

**Protected tests.** `Consumer/…` in `NumStabilityTest/Reorganization/R02/` compiles each
of these modules unedited, so the postimage can be validated without R02 touching the
file. `Canonical/AlgorithmsNormEstimationPNormOneAndInfinityNorms{Square,Rectangular}`
pins the canonical surface the retarget points at, and
`OldOnly/AlgorithmsNormEstimationPNormEndpoints{ConvergenceStatements,PNormRectangular}`
pins the historical wrappers so the retarget cannot silently break old-path resolution.

**Executable forward/reverse replay.** `replay.ps1` (delivered beside this file) creates a
disposable checkout of C0000 via `git worktree add --detach`, prints the preimage blob of
each path, applies the forward postimage, reports residual `PNorm.Endpoints` references
(expected 0), applies the reverse postimage, confirms the checkout is byte-identical to
C0000 (`git status --porcelain` empty), and removes the checkout. Run
`replay.ps1 -Mode forward`, `-Mode reverse`, or `-Mode both`. The exact forward and
`REVERSE__` file bodies are delivered alongside it, so the replay needs no regeneration.

## Explicit no-change decisions

| path | C0000 blob | decision |
| --- | --- | --- |
| `NumStability/Algorithms.lean` | `f59bed9a5a83` | **no change required** (final) |
| `NumStability/Source/Higham/Chapter15.lean` | `5b6cc8970bed` | ~~no change required~~ **SUPERSEDED by request 7** |

`NumStability/Algorithms.lean` contains **zero** references to either endpoint owner, so it
does not participate in the canonical-to-historical reach. It reaches R02 material only
through the 28 wrappers, all of which remain import-only and resolvable, so its transitive
surface is unchanged by this wave. It is listed in the brief as a candidate and is
deliberately recorded here as untouched rather than omitted.

`NumStability/Source/Higham/Chapter15.lean` **already exists** at C0000 and likewise
contains zero endpoint references. Unlike the predecessor wave — where a chapter aggregate
was absent and the layout gate reported `Source` and `Source.Higham` each *"misses N
canonical descendant(s)"* — there is no missing-aggregate problem here. If the layout gate
nonetheless requires R02's 14 new destinations to be reachable from this aggregate, that is
a sixth request of the same shape (append 14 sorted imports); `GATE_RESULTS.tsv` records
whether the gate actually asked for it, and this decision is revised only on that evidence,
not in anticipation of it.

## Accepted-consumer scope

R02 edits no shared consumer. The five requests above are the complete set of production
modules importing the endpoint owners; the remaining direct importers are test modules
outside B0002's authority in the predecessor wave's tree, plus R02's own old-only tests,
which import wrappers by design.

---

# Requests 6–7 — aggregation gaps found by `check_layout`

These two were **not** anticipated; they were surfaced by the layout gate on the applied
worktree and are recorded on that evidence. Request 7 **supersedes** the earlier no-change
decision for `Chapter15.lean`: the gate does demand the new leaves be aggregated.

With requests 6 and 7 applied to the worktree, `check_layout` was executed and returned
**exit 0 with 0 errors**, then the change was reverted; the worker branch ships none of it.
Log: `check_layout_postimage.log`.

| # | path | C0000 blob | postimage SHA-256 | change |
| --- | --- | --- | --- | --- |
| 6a | `NumStabilityTest/Reorganization/R02.lean` | **absent at C0000 (created)** | `C560026FCCD0…` | new aggregate, 63 imports |
| 6b | `NumStabilityTest.lean` | `eb23b5792e05` | `D2B53F45FF8E…` | one import line added after the W10 aggregate |
| 7 | `NumStability/Source/Higham/Chapter15.lean` | `5b6cc8970bed` | `23764C15F48D…` | import block 47 → 59 entries (+12) |

## Request 6 — reach the 63 R02 test modules

**Why.** `check_layout` reports `NumStabilityTest does not reach 63 test module(s)`. The
root test aggregate is integrator-owned, and R02's test prefix contains no aggregate of its
own. The predecessor wave solved the same shape with
`NumStabilityTest/Reorganization/W10.lean` plus a single root import, and that is the
pattern followed here.

**Minimal postimage.** Create `NumStabilityTest/Reorganization/R02.lean` containing exactly
63 sorted imports — one per module in `TEST_MATRIX.tsv` — and insert
`import NumStabilityTest.Reorganization.R02` into `NumStabilityTest.lean` immediately after
the existing `import NumStabilityTest.Reorganization.W10` line. No other edit.

**Reachability.** Neutral for the tier rules: test modules import wrappers and canonical
leaves by design and are outside the reusable/source tiering.

**Protected tests.** The 63 modules are themselves the coverage; each was built explicitly
in the four separate sets (`tests_canonical` 28 jobs, `tests_old` 45, `tests_focused` 28,
`tests_consumer` 156), all exit 0, so the aggregate cannot introduce a compile failure.

## Request 7 — aggregate the 12 new Chapter 15 leaves (supersedes a no-change decision)

**Why.** `NumStability.Source` and `NumStability.Source.Higham` each report
`misses 12 canonical descendant(s)` — the 12 new `Source/Higham/Chapter15/**` destinations
R02 creates. `Chapter15.lean` exists at C0000 and is integrator-owned, so R02 cannot add
them. I had earlier recorded this file as **no change required** on the grounds that it
contains no endpoint reference and does not participate in the canonical-to-historical
reach; that reasoning was about reachability, not aggregation, and the gate has now shown
aggregation is also required. The decision is revised on that evidence.

**Minimal postimage.** Append the 12 destination modules to the import block of
`NumStability/Source/Higham/Chapter15.lean` and re-sort the block (47 → 59 entries). The
checker rejects unsorted aggregate imports, so re-sorting is part of the minimal change.
The two reusable `NormEstimation` destinations need nothing: they are already reached.

**Gate unblocked.** `check_layout`, from 3 errors to **0**. Verified by execution, not
assertion.

**Protected tests.** `Canonical/SourceHighamChapter15…` — one per Source leaf — pin each
module's canonical surface, and `Focused/…` exercises the frozen route with the
private-normalized closure, so the aggregate is added over already-compiled modules.

**Executable forward/reverse replay.** Forward and `REVERSE__` bodies for all three files
are delivered in `postimage/`; `replay.ps1` performs the round trip in a disposable C0000
checkout and asserts byte-identical restoration. `R02.lean` has no reverse body because it
does not exist at C0000 — its reverse is deletion.
