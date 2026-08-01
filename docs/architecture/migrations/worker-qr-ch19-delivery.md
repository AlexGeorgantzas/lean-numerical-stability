# QR / Chapter 19 Q2B worker delivery

> **Integration resolution:** implementation
> `ee1686e374d03dc8df84adf700f2025830d5b2f0` and delivery report
> `07288ac518ee399645038ea66e4fc23f2c2abe52` are ancestors of `main`.
> Shared registrations, the BlockLU handoff, QR post mode, the 69-row LSQ
> handoff check, repository gates, builds, tests, and CI all passed. The
> instructions below describe the worker's pre-integration state only.

This report records the completed Codex QR / Chapter 19 worker lane. The
packet was frozen at `6487fc33088523b8f27ecde9ad613515b78f9977`; the live
integration checkpoint used for this resumed run was
`48242807d4149210926eccf90a326d287fc0860c` (`origin/main`).

## Identity

- Lane: `codex-qr-ch19`
- Engine/subscription: `Codex subscription 2`
- Repository/remote: `https://github.com/AlexGeorgantzas/lean-numerical-stability.git`
- Frozen base SHA: `6487fc33088523b8f27ecde9ad613515b78f9977`
- Branch: `codex/org-qr-ch19`
- Final implementation HEAD (parent of report commit): `ee1686e374d03dc8df84adf700f2025830d5b2f0`

## Ordered commits

The following are the exact implementation/evidence commits after the live
checkpoint, in cherry-pick order. The final report-only commit is intentionally
not listed.

- `a46b57c5a2aee3d2b35d6cb58ce9d49810deaeee` — refresh the live Q2B ownership contract and checker.
- `e5e28016eb2712490f5235fdae1f750235bf96d1` — materialize Q2B dependency wave 1.
- `6a284b4185bb8521163d05ac7005d34c7797ed0b` — materialize Q2B dependency wave 2.
- `3eabc4b4a2e58541918dadefa06608400a07c393` — materialize Q2B dependency wave 3.
- `aaec530c3fc1449c6f4182ddb775e29aa9d2ca66` — materialize Q2B dependency wave 4.
- `35db67100effbcee824f7fa0bcf946c155951134` — materialize Q2B dependency wave 5.
- `363305157631f786c644f6d220eca77e4cb14437` — deliver the required source-rate late tail.
- `e22c2d89dedeec549968cdf42f34d6ab054b1d6b` — deliver the required Problem 19.10 late tail.
- `5fcd7978fcc90007ee6fb5650135ef6d55df5f36` — deliver the required Theorem 5 late tail.
- `7adff9c546467d43882e7dd4e86482dca25db4d9` — deliver the required Theorem 6 late tail.
- `bf69773df8b2a339d0cc40a5f5bb616ff83934b1` — materialize the post-tail nonbreakdown wave.
- `eaaf3c888b14882f519bacfd70baebd2f82f8b4c` — deliver the late WY application closure and preserve its BlockLU handoff.
- `8fea6f167c3658af8b6195cf3dee2028e6070d11` — materialize the Sun–Bischof wave.
- `07a4484e5d532f5d0d93261be8ec7d3fb657ced8` — materialize Cox–Higham concrete.
- `c316fe1d3bdd285e0f1e00c2c06e7928da6ca0dd` — materialize Cox–Higham full.
- `04df84ac38fa1c7a8ba0accf3f85c2fdbe2ee453` — materialize Cox–Higham assembly.
- `ffc2ef4c66f2d297dda417e476963461d3ac8715` — materialize column pivot.
- `2d6ec310aa56ecbe9fbfac30366e1363ea26d564` — retain the canonical column-pivot source omitted by the preceding wave commit.
- `bb56491e639fc7c13b0084d12b909d90de7fa202` — materialize column-pivot full.
- `6b72202534a6b20cae81d07f36e562575c1101f9` — materialize the final Theorem 19.6 wave.
- `77690a941e87d0f978c0c9d05a5b34d080d8bcc1` — materialize the strong-model wave.
- `ee1686e374d03dc8df84adf700f2025830d5b2f0` — record the exact 69-row QR/LSQ handoff.

## Scope

- Scope-check command/result: `check_scope.py` against `evidence/LIVE_BASE_SHA.txt` (`48242807d4149210926eccf90a326d287fc0860c`) passed; 22 commits inspected, 192 touched paths, and 148 new paths. The frozen packet base was not used as the effective scope base because its later mainline work is inherited by the live checkpoint.
- Changed paths: complete effective-live-base list is the output of `git diff --name-status 48242807d4149210926eccf90a326d287fc0860c..ee1686e374d03dc8df84adf700f2025830d5b2f0`; it consists of the 59 historical QR wrappers, 60 canonical Chapter 19/reusable destinations, 120 isolated/aggregate worker-test files, the QR checker/ownership evidence, and the lane delivery evidence.
- Forbidden/shared paths changed: none. No least-squares, Chapter 20, BlockLU, Chapter 13, Chapter 9, Chapter 11, global aggregate, root test, CI, manifest, package, or toolchain path was changed by this lane.
- Integrator-only patch requests: wire the canonical reusable QR umbrella, the numbered Chapter 19 source umbrella, and `NumStabilityTest.Worker.QrCh19` into their shared roots; register the new reusable/source/test modules in the shared manifests and layout/tier metadata; preserve the exact late `Higham19WYApplicationClosure -> BlockLUFirstOrderFamilies` handoff until the BlockLU checkpoint is available; then rerun the repository-level layout, compatibility, and strict-source gates.

## Semantic evidence

- Pristine source/blob/.ilean hashes: the 59-owner pristine source and compiled `.ilean` snapshots are in `/home/mymel/lean/reorg/codex-qr-ch19/evidence/frozen-source-420-flat` and `/home/mymel/lean/reorg/codex-qr-ch19/evidence/frozen-ilean-420-flat`; the checker verified all 59 source/.ilean pairs against the frozen evidence. The base-420 pristine library build passed in 4,942 jobs.
- Baseline declaration TSV: 706,123 lines, 115,724,349 bytes, SHA-256 `32ADA469E27A971E9B0BB972F29C51E1DCBE99104A1492D4C69549C339825563`; the immutable QR contract contains 3,991 declarations across 59 owners.
- Candidate declaration TSV: final clean candidate at `/home/mymel/lean/reorg/codex-qr-ch19/evidence/candidate/final-qr-ch19-declarations.tsv`, 706,163 lines, 115,930,299 bytes, SHA-256 `8C0FF3FDFC5F8E8E0C229FEE3125CA7D91AC551A55FA457D47AC32BF21DBA999`, generated at implementation HEAD `ee1686e374d03dc8df84adf700f2025830d5b2f0`.
- Ownership/signature comparison: post mode passed with all 60 canonical destinations and 59 exact historical wrappers; all 3,991 QR declarations remained owned by their reviewed destinations.
- Signature typed-edge comparison: exact after the reviewed normalization, with 25,540 incident signature edges preserved.
- Body/proof typed-edge comparison: exact after the reviewed normalization, with 35,878 incident body/proof edges preserved.
- Reviewed private-owner normalization: 98 rows in `docs/architecture/declaration-ownership/qr-ch19-private-rewrites.tsv` (99 lines including its header), SHA-256 `7CD7D367775AFE7CD92ABC01FA1E48591101AB3C947BD7E0811E87565CBF85EE`; the only non-private graph exception is the three-row live-main LSQ endpoint map in `qr-ch19-live-graph-rewrites.tsv` (SHA-256 `BE262D0C3147D2F9CFADBF40071CEED1A29EBBE50F87420E7877C8159EBC79B6`).

The exact QR/LSQ handoff is tracked in
`docs/architecture/declaration-ownership/qr-ch19-lsq-handoff.tsv`: 69 owner
rows across 14 owner/carrier lanes. Its SHA-256 is
`247DA93CE7A68D3325FD6C5C13A2E665E58213FC59B029E02B8E5B0DB9157195`.

## Verification

- Ownership checker negative self-tests: passed before edits and after the final candidate.
- Pre/stage/post ownership gates: pre passed for 59 owners and 3,991 declarations with the inherited 22-row manifest; every wave and late tail passed its stage gate; final post passed with 60 destinations, 59 wrappers, 3,331 byte-identical command groups, 98 private rewrites, 25,540 signature edges, and 35,878 body/proof edges.
- Canonical-only tests: every canonical leaf was built in its dependency wave; final per-wave canonical/compatibility/aggregate builds passed through 3,049 jobs, and the complete worker set was included in the full test build.
- Isolated old-only tests: every historical wrapper was tested in its own compatibility target alongside its wave; all compatibility targets passed.
- Focused leaf builds: serialized `lake build NumStability` passed at each wave, ending at 5,053 jobs; focused worker counts were 3,133, 3,237, 3,258, 3,271, 3,281, 3,108, 3,060, 3,110, 3,129, 3,142, 3,042, 3,042, 3,044, 3,045, 3,047, 3,047, 3,048, and 3,049 jobs across the implementation waves/tails.
- Downstream builds: the complete worker downstream set passed; `lake test` reached 5,947/5,947 targets, and the combined build passed 5,949 jobs.
- Layout/compatibility/provenance/strict-source gates: provenance passed with 207 Apache-marked production files and 5 evidenced upstream modules; layout and strict-source remain integrator-pending because shared umbrellas/root registrations were intentionally not edited; compatibility is integrator-pending only for the explicitly preserved WY -> BlockLU handoff.
- `lake test`: passed; final target `NumStabilityTest` built at 5,947/5,947.
- `lake build NumStability NumStabilityTest`: passed; 5,949 jobs.
- Axiom probes: four representative Chapter 19 endpoints (`H19_Theorem19_6_strongModel`, `H19_Theorem19_6_final`, `fl_householderQRColPivot_Q`, and `theorem19_6_coxHigham_concrete_full`) each reported exactly `[propext, Classical.choice, Quot.sound]`.
- `git diff --check`: passed after every wave, tail, evidence commit, and final report preparation.
- Final clean status: clean at implementation HEAD `ee1686e374d03dc8df84adf700f2025830d5b2f0`; the final delivery commit changes only this report and leaves the worktree clean.

## Cross-lane notes

- Required late-tail order is source-rate, Problem 19.10, Theorem 5 source closure, and Theorem 6 actual source; these are separate commits `3633051`, `e22c2d8`, `5fcd797`, and `7adff9c`, respectively.
- The WY closure is a separate late commit `eaaf3c888b14882f519bacfd70baebd2f82f8b4c`. Its source file preserves imports of `NumStability.Algorithms.LU.BlockLUFirstOrderFamilies` and canonical `NumStability.Algorithms.LinearSystems.QR.GramSchmidtPolar`; do not move or erase that edge before the BlockLU integrator checkpoint.
- The required integration order is: cherry-pick the contract/checker commit; Q2B waves 1--5; the four one-tail commits in the order above; post-tail wave 6; WY late handoff; Sun–Bischof; Cox concrete, full, and assembly; column-pivot, corrective canonical-source, and column-pivot-full; final; strong-model; then the 69-row handoff evidence commit. Wire the shared umbrellas/manifests only after all worker commits are present.
- After integration, regenerate a clean format-2 candidate from the integrated root registrations, rerun QR post mode, rerun the 69-row handoff/hash checks, and rerun layout, compatibility, strict-source, `lake test`, the combined build, axiom probes, final scope, and clean-status checks.
