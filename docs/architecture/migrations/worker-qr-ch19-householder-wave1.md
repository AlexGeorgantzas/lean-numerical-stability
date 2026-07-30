# QR / Chapter 19 Householder Wave 1

This wave moves the dependency-closed Householder foundation out of the
historical `NumStability.Algorithms.QR` family while preserving every public
declaration and old import.  It is based on published integration commit
`420e4f93e2a5d31b2bf5b73740ca4146de7b0921`; the immutable packet semantic
stream was captured at `6487fc33088523b8f27ecde9ad613515b78f9977`.

The earlier contract commit is
`89d8fc9d2c60bbfa08bb7292c721d5a08ce63463`.  This migration remains local on
`codex/org-qr-ch19-householder`; the worker did not push or merge it.

## Migrated surface

- Eleven source-neutral owners now live below
  `NumStability.Algorithms.LinearSystems.QR`: `HouseholderApply`,
  `HouseholderApplySupport`, `HouseholderConstruction2`,
  `HouseholderMatrixStep`, `HouseholderOneStep`, `HouseholderQApply`,
  `HouseholderQR`, `HouseholderQRSupport`, `HouseholderReflector`,
  `HouseholderSpec`, and `HouseholderSpecSupport`.
- The one numbered command,
  `NumStability.H19_Lemma19_1_construction2_backward_error`, lives in
  `NumStability.Source.Higham.Chapter19.Lemma01.Construction2` and imports the
  reusable Construction 2 API.
- All eleven historical files are exact import-only wrappers.  The
  Construction 2 wrapper imports both the reusable leaf and the numbered
  source leaf; the other wrappers import one reusable leaf each.
- Twelve canonical-only tests import one canonical destination apiece.  Eleven
  compatibility tests each import exactly one historical wrapper.  The
  allowed wave aggregate is
  `NumStabilityTest.Worker.QrCh19.HouseholderWave1`; the disallowed partial
  worker-root file `NumStabilityTest/Worker/QrCh19.lean` was not created.
- The current-main repair in `Higham19WYApplicationClosure` is preserved: it
  imports `NumStability.Analysis.FirstOrder.AsymptoticFamilies`.  The old
  `BlockLUFirstOrderFamilies` compatibility import was not reintroduced.

The materializer selected exactly 1,040 declarations in 821 compiler-backed
source-command groups across 12 destinations.  It required 15 ordinary private
owner rewrites and no public promotion.  The final materializer places module
documentation after the import block, as Lean requires, and its static text
gate re-finds every frozen command exactly once.

## Semantic evidence

Pristine source and `.ilean` copies for all 59 QR owners are retained outside
the repository at
`C:\Users\qed_s\higham-evidence\qr-householder-wave1-base`.  Their individual
hashes are frozen in `qr-ch19-frozen-owners.tsv`.

| Evidence | Result |
| --- | --- |
| Frozen format-2 stream | 115,724,349 bytes; 56,898 declarations; 649,224 typed edges; SHA-256 `32ADA469E27A971E9B0BB972F29C51E1DCBE99104A1492D4C69549C339825563` |
| Candidate format-2 stream | 115,805,153 bytes; 56,900 declarations; 649,257 typed edges; SHA-256 `42402118A39C5A66EFF55F4D056AFDF0DB9CB8539CBF7249E57AEF21271D284A` |
| Candidate location | `C:\Users\qed_s\higham-evidence\qr-householder-wave1-base\qr-householder-wave1-candidate.tsv` |
| Stage ownership | 12 destinations, 11 wrappers, all 821 command groups byte-identical |
| Normalized typed graph | 25,540 signature edges and 35,878 body/proof edges preserved exactly |
| Private rewrites | Exactly 15 rows; manifest SHA-256 `B5D95DB3E6A2203E5D37B5A9E32FD82FB56AA6AD4698579E2B18A5F106C3B01E` |

The candidate's two additional declarations and 33 additional global edges
are outside the QR incident contract and come from the later integration base.
The stage checker deliberately compares exact ownership and every signature or
body/proof edge incident to the 3,991-declaration QR contract, so unrelated
integrated work cannot conceal a QR change.  Stage mode passed once while
writing the private manifest and again read-only against the resulting file.

`check_qr_ch19_ownership.py --self-test` passed its negative tests.  The final
materialized-text gate passed with 821 command groups, 11 exact wrappers, and
12 destinations.

## Compiler-backed verification

- The pristine base `lake build NumStability` passed before edits: 4,942 jobs.
- The final focused build of all eleven reusable leaves plus the source leaf
  passed: 2,989 jobs and all 12 requested targets built.
- All eleven historical wrappers rebuilt successfully: 3,000 jobs.
- All 12 canonical-only and all 11 isolated old-only tests built as individual
  targets: 3,023 jobs.  No test relies on the test aggregate for isolation.
- Representative axiom probes for
  `fl_householderConstructApply_appError`,
  `ColumnwiseHouseholderStepErrorRect.exists_residual_matrix_columnFrob_bound`,
  and `H19_Lemma19_1_construction2_backward_error` each reported exactly
  `[propext, Classical.choice, Quot.sound]`.
- An independent integrator import-closure audit reached 30 project modules
  from the eleven reusable leaves, with zero `Source`/`Higham` hits and zero
  missing local imports.

The first focused attempt exposed only a mechanical generator error: a new
module doc command preceded imports.  The materializer was corrected to insert
the doc immediately after the last import, all eleven positions were audited,
the exact 821-command text gate was rerun, and the complete focused build then
passed.  No theorem or proof was edited in that repair.

Broad downstream, `lake test`, and full `NumStability NumStabilityTest` builds
are intentionally deferred to the integrator until the shared imports and
manifests below are applied.  Running them in the worker tree first would test
a deliberately incomplete shared registration state.

## Static gates

- Effective-parent scope against `420e4f93e2a5d31b2bf5b73740ca4146de7b0921`
  passed.  The final pre-commit measurement is 57 touched paths and 46 new
  paths, including this report; every path is in the QR allowlist and no
  forbidden/shared path was changed.  A raw packet-base comparison against
  `6487fc...` also sees inherited main, LSQ, and BlockLU integration commits and
  is therefore not an effective worker-scope measurement.
- `check_compatibility.py` passed: 119 forwarding modules and 228 canonical
  targets.
- `check_provenance.py` passed: 207 Apache-marked production files and five
  evidenced upstream modules.
- `git diff --check`, canonical-import isolation, compatibility-test isolation,
  and the no-new-`sorry`/`admit`/top-level-`axiom`/`constant` scan passed.
- The strict source audit still reports exactly 13 pre-existing reachable
  least-squares-to-`Source.Higham.Chapter06.Problem05` pairs through
  `RandNLA.LowRankApprox -> MatrixInversion -> HighamChapter8 ->
  Analysis.HighamChapter7`.  None starts in or traverses a new QR module.

`check_layout.py` reports only registrations intentionally omitted from this
worker because their files are shared: the 24 new worker test modules are not
yet root-reachable; the eleven reusable leaves are not yet classified; three
`Support` names need reviewed legacy exceptions; `LinearSystems` does not yet
reach `HouseholderConstruction2` or `HouseholderQApply`; and the `Source` and
`Source.Higham` roots do not yet reach the one Chapter 19 leaf.  There are no
new missing module docs, mixed modules, declaration-bearing umbrellas,
unsorted aggregate imports, or import cycles.

## Exact integrator patch request

Apply these shared changes after cherry-picking this wave:

1. In `NumStabilityTest.lean`, add
   `import NumStabilityTest.Worker.QrCh19.HouseholderWave1`.
2. In `NumStability/Algorithms/LinearSystems.lean`, add the two currently
   missing closure imports:
   `NumStability.Algorithms.LinearSystems.QR.HouseholderConstruction2` and
   `NumStability.Algorithms.LinearSystems.QR.HouseholderQApply`.  The other
   nine leaves are already transitively reached.  Importing all eleven
   explicitly is a valid stronger registration if the integrator chooses to
   ratchet the shared direct-import surface deliberately.
3. In `NumStability/Source/Higham.lean`, add
   `import NumStability.Source.Higham.Chapter19.Lemma01.Construction2`.
   `NumStability.Source` will then reach it through `Source.Higham`.
4. In `docs/architecture/tiers.json`, add the reusable prefix row
   `{ "prefix": "NumStability.Algorithms.LinearSystems.QR", "tier":
   "reusable" }`.
5. In the sorted `legacy.noncanonical_modules` array of
   `docs/architecture/layout-exceptions.json`, add exactly:
   `NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport`,
   `NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport`, and
   `NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport`.

No `COMPATIBILITY.md` edit is needed; its checker already accepts every
historical wrapper.  `NumStability/Algorithms/LinearSystems/QR.lean` and
`NumStability/Source/Higham/Chapter19.lean` are lane-authorized future QR
outputs, not integrator patches for this wave.  They remain absent because a
Householder-only QR family umbrella or one-leaf Chapter 19 umbrella would be a
misleading partial API before the remaining QR/Chapter 19 waves move.
