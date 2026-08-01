# Lane delivery report

> **Integration resolution:** this is historical worker-delivery evidence.
> Implementation `2d6739ee3870236cfc5342d8250ea825cf1cb026` and report
> `ce5a2e153fa2fbf8da0536842ac164741f3b3e52` are ancestors of `main`.
> The QR handoff, shared patches, candidate extraction, stage/post gates, and
> branch choice were subsequently resolved. No integrator action described
> below remains.

## Identity

- Lane: `lsq-ch20`
- Engine/subscription: `Claude subscription 3`
- Repository/remote: `https://github.com/AlexGeorgantzas/lean-numerical-stability.git`
- Frozen base SHA: `6487fc33088523b8f27ecde9ad613515b78f9977`
- Branch: `codex/org-lsq-ch20`
- Final implementation HEAD (parent of report commit): `2d6739ee3870236cfc5342d8250ea825cf1cb026`

## Ordered commits

1. `2d224437773743bf991d15874c49f3de1dd8bf8d` — freeze the baseline, the compiler-span route contract and the lane ownership checker before any declaration moves.
2. `7d876bc241d46e7192be2acaf46bb148aec76908` — rebuild the routes on authoritative `.ilean` spans, so a structure and its co-generated projections cannot be routed apart.
3. `5296ee83ede698e2f5edd9bda0f9c4efb71a945f` — harden the migration contract.
4. `f25766cc0c38434752a635764f84767391e948b0` — scope the lane graph and freeze the cross-lane rows.
5. `203ef825ede9e63ee77d5cfe963a1b4941975399` — require an authoritative QR handoff before post mode can pass.
6. `ecfb12280240ab3a9884261aa327202024f9d034` — migrate `LSPerturbation`.
7. `7ba0afda55f82531e36c08c9fd49385b0a57e34d` — migrate `LSNormalEquations`.
8. `d1447c09979b5c912a36d222dd3647f959fb26f4` — migrate the two printed Chapter 20 example owners.
9. `3c5aaac4a1281cab885c7f484f05e92c3ce52c26` — record the wave evidence and the measured obstructions.
10. `9a567bbd31cbb5389b072d2e496a611b70d09eb2` — correct the blocker partition: private co-location is the critical path.
11. `9452c36eab7c9985cc09aff4f01a82c8995de640` — add the private co-location gate and correct the manifest, 114 cross-boundary private uses to 0.
12. `568a6d22bb814e331321bc11c7520e23a0425868` — merge private groups at component rather than destination granularity, restoring six destinations.
13. `e9b61bc119e60720634b2f35d8769910d9b3e16f` — restore `Equality.KKT` and refresh 64 stale private-rewrite rows.
14. `897fb7fafdf6c539e2651e5bdd1faec500198406` — migrate `LSQRSolve` and three Chapter 20 owners.
15. `1a3004ec6461baa00a9ba21fe1a31d0f17b7fd4f` — split `LSE` into the required equality parts and migrate nine more owners.
16. `2d6739ee3870236cfc5342d8250ea825cf1cb026` — migrate the remaining 23 owners, completing the lane.

Commits 3–5 were authored by the concurrent Codex agent on this shared branch and
are preserved unchanged; the lane adopted that committed contract rather than
regenerating it.

## Scope

- Scope-check command/result: `python scripts/check_scope.py --repo <worktree> --owned OWNED_PATHS.txt --forbidden FORBIDDEN_PATHS.txt --allowed-new ALLOWED_NEW_PREFIXES.txt --base-file BASE_SHA.txt` → **Scope contract passed**, 16 commits inspected, 249 touched paths, 207 new paths.
- Changed paths: 249 in total — 41 historical owners under `NumStability/Algorithms/LeastSquares` (now wrappers), 11 `Algorithms/LinearSystems/LeastSquares`, 15 `Analysis/Perturbation/LeastSquares`, 43 under `Source/Higham/Chapter20`, 82 lane-owned tests under `NumStabilityTest/Import/**` and `NumStabilityTest/Worker/LsqCh20/**`, 9 contract artifacts under `docs/architecture/declaration-ownership`, 2 lane reports, and `tools/architecture/check_lsq_ch20_ownership.py`.
- Forbidden/shared paths changed: **none**.
- Integrator-only patch requests: recorded in `lsq-ch20-coordinator-patches.tsv` (325 rows) and described in `worker-lsq-ch20-integrator-request.md`. See “Cross-lane notes”.

## Semantic evidence

- Pristine source/blob/.ilean hashes: `PACKET_ROOT/runtime/frozen-owners/{source,ilean}`, one file per historical owner, each with a 40-hex Git blob ID and SHA-256 frozen in `docs/architecture/declaration-ownership/lsq-ch20-frozen-owners.tsv`. Every split reads those copies, never the worktree, because after a wave the worktree file is already the wrapper.
- Baseline declaration TSV: `PACKET_ROOT/runtime/baseline/phase12b-recursive-declarations-v2.tsv`, format 2, 56,898 declarations and 649,224 typed edges, 110.4 MB, digest pinned in the checker as `BASELINE_TSV_SHA256` and re-verified on every gate run.
- Candidate declaration TSV: **not extracted.** Stage and post mode require a fresh format-2 stream from the built tree; that extraction was not run, so the ownership comparison below rests on `pre` mode plus the compiler, not on a candidate stream.
- Ownership/signature comparison: `pre` mode passes — 5,129 lane declarations, 4,694 compiler command groups, 73 destinations, manifest SHA-256 `3B6B569EB76F08A9910A3A0F9AB4A6733D8BCD0898CB33A174992BAD547B4DB9B3`. Every route resolves through its `.ilean` source position into exactly one reviewed range, and every command fingerprint matches the frozen bytes.
- Signature typed-edge comparison: 4,221 typed cross-lane edges regenerated and matched, 19 LS-to-QR and 4 QR-to-LS base imports preserved.
- Body/proof typed-edge comparison: 250 typed destination-DAG edge counts regenerated and matched exactly.
- Reviewed private-owner normalization: `lsq-ch20-private-rewrites.tsv`, 151 rows, SHA-256 prefix `46009A97273F7A49`. Every private declaration keeps `private` visibility; only the module-scoped mangled prefix changes with its destination. **No declaration was promoted to public and none was duplicated.**

## Verification

- Ownership checker negative self-tests: **pass** — `--self-test` green, including new cases for private co-location, the frozen historical-import contract, and an orphaned canonical module.
- Pre/stage/post ownership gates: `pre` **passes**. `stage` and `post` **not run**: both need a candidate declaration stream, and `post` additionally requires the QR lane's 69-row handoff, which does not exist at this base. `post` is designed to fail without it.
- Canonical-only tests: 41 generated modules, each importing exactly one destination so no sibling can supply the declaration checked; all build.
- Isolated old-only tests: 41 generated modules, each importing only a historical wrapper; all build.
- Focused leaf builds: **pass** — all 73 destinations build; the three family aggregates build in 3,531 jobs with 0 errors and **0 `dupNamespace` warnings**, confirming every declaration kept its exact original fully-qualified name.
- Downstream builds: **pass** — every entry of `DOWNSTREAM_BUILDS.txt`, including `Source.Higham.Chapter14.Section05.SpectralConvergence`, `Algorithms.MatrixInversion`, `RandNLA.LeastSquaresSketch`, `Underdetermined.UnderdeterminedSolve`, `Ch14SchulzSpectralConvergence` and the four frozen QR-to-LS consumers.
- Layout/compatibility/provenance/strict-source gates: `check_layout.py` **exit 0** (0 mixed modules, 0 unsorted aggregate imports); `check_compatibility.py` **passed** (108 forwarding modules, 208 canonical targets); `check_provenance.py` **passed** (207 Apache-marked production files, 5 evidenced upstream modules); `generate_baseline.py --skip-declarations --strict-source --output-dir benchmark-results/architecture --name lsq-ch20-source` **exit 0**.
- `lake test`: **pass** — exit 0, 0 error markers across 16,868 lines of output.
- `lake build NumStability NumStabilityTest`: **pass** — `Build completed successfully (5449 jobs)`, exit 0, 0 error markers across the whole run.
- Axiom probes: **pass** — 83 probes across `Wave0{1,2,3,5,6,7}Axioms`, one per destination each wave created or extended. Every probe reports exactly `[propext, Classical.choice, Quot.sound]`; none reports anything else.
- `git diff --check`: **clean.**
- Final clean status: worktree and index clean at `2d6739ee3870236cfc5342d8250ea825cf1cb026`.

## Cross-lane notes

**Migration shape.** All 41 historical declaration-bearing owners are documented
exact import-only wrappers. 224,491 source lines became 220,876 emitted declaration
lines across 73 destinations, every authored span byte-identical to its frozen copy.
Required order item 4 is satisfied with separate modules and no visibility change:
`Equality.Basic` 388, `Equality.GQR` 294, `Equality.KKT` 6, the analysis-tier
`Equality.{Perturbation,MixedStability,RowwiseBackwardError}` 495/223/522, and
`Source.Higham.Chapter20.Theorem08.LSE` 59.

**Two contract corrections the integrator should know about.**

1. The reviewed manifest routed **114** private-declaration uses across a
   destination boundary. A Lean private name is module-scoped, so each is an
   unknown-identifier error; migrating `Higham20Lemma20_11` and
   `Higham20Lemma20_12` failed exactly that way. No existing gate detected it.
   `validate_private_colocation` now does, statically, from the frozen stream.
2. The review branch `codex/review-lsq-contract-repair` resolves the same defect by
   promoting 55 authored-private declarations to public under
   `lsq-ch20-private-promotions.tsv`. **Those promotions are not required.**
   Co-locating each private declaration with its users at component granularity
   reaches 0 cross-boundary uses with every declaration still private and
   `Equality.GQR` intact. If the two contracts are reconciled, this lane's version
   needs no visibility change.

**Gates the integrator must still run.** Only the ownership `stage` and `post` gates
remain, and neither can pass at this base: both need a fresh format-2 candidate
declaration stream extracted from the built tree, and `post` additionally requires
the QR lane's 69-row handoff, which does not exist. Every other gate in
`ACCEPTANCE_GATES.md` was run in this lane and passed — `lake test` (exit 0), the
full `lake build NumStability NumStabilityTest` (5,449 jobs, exit 0), the
strict-source baseline, layout, compatibility and provenance, alongside all 73
destinations, all 41 wrappers, all 82 isolated tests, all six axiom-probe modules
and every `DOWNSTREAM_BUILDS.txt` entry.

Note for scheduling: this lane shares one machine-wide build mutex
(`Local\LeanNumericalStabilityLargeBuild`) with three concurrent workers, and
several build windows were consumed entirely while queued. Reruns should expect the
same contention.

**QR handoff, still absent.** `lsq-ch20-cross-lane-normalization.tsv` has 4,224 rows
and SHA-256 `056DA202B1D8C3FC6F6ED540B6064D094D89455A43848FBEA175C06DAFE8384F`,
matching the value pinned in the tracked integrator request. 1,628 rows carry
`@QR_OWNER_REQUIRED:*`, covering 68 exact QR declarations plus the import-only
`Higham19Alg12MGSSourceRate` carrier. Do not resolve these by guessing one owner per
historical module — a single Higham19 module can split across several canonical
owners. Post mode requires the QR lane's separate 69-row handoff and deliberately
fails without it.

**Coordinator decision required: branch collision.** Three other worktrees carry
this packet's work: `codex/org-lsq-wave2-lse` (25 commits, has migrated `LSE`),
`codex/org-lsq-wave1-integrator` (8), and `codex/review-lsq-contract-repair` (6,
branched from this lane's `7d876bc24`). 30 of this lane's changed paths are also
changed on `codex/org-lsq-wave2-lse` and 24 of those 30 differ, including every
contract TSV, the checker, and shared production modules; that branch's own
migration report names `codex/org-lsq-ch20`. This lane neither merged nor
cherry-picked from any of them, as the contract forbids importing another worker's
unintegrated branch. Which contract integrates is a coordinator decision.

**Integrator patch set.** `lsq-ch20-coordinator-patches.tsv`, 325 rows, SHA-256
`2CF720044F4CE496CCCAD0D5132A5073402E7AFDD4C0C5B365B96E4E7BEF5FE0`. Four
QR import identities are retargeted to the canonical `LinearSystems.QR`
paths already landed by Q2A; this is the only post-Q2A contract delta. The
three preserved Chapter 20 leaves
(`Equation32`, `Lemma06`, `Theorem01`) are lane-owned and were deliberately left
importing the `LSQRSolve` wrapper: they are not manifest destinations, so the
production-import gate does not apply to them, and the wrapper resolves them.
