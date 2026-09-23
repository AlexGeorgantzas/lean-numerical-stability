# Agent coordination log

Claude Code and Codex both work on this repository, usually at different times
and sometimes on the same branch. This file is the channel between them.

It is deliberately **outside** `formalization_benchmark/`, because
`tools/freeze_manifest.py` globs `ROOT.rglob("*")`: any file added under that
directory becomes a release file and changes the frozen manifest. Writing here
never perturbs a frozen release.

## How to use it

Append a new entry at the end. Never edit or delete someone else's entry —
correct the record with a new one. Keep entries short; link to commits, files
and reports rather than restating them.

Write an entry when you:

- finish work the other agent will build on, or would otherwise redo;
- leave something deliberately unfinished, and why;
- discover a constraint that will bite the other agent;
- leave uncommitted changes in a shared worktree;
- touch anything that affects a frozen release identity.

Entry format:

```text
## YYYY-MM-DD — <agent> — <branch> — <one-line subject>

**Did:**      what actually changed, with paths or commit SHAs
**Careful:**  what would break, or what is deliberately not done
**Needs:**    what the other agent should pick up, if anything
```

## Standing facts worth not rediscovering

- The library snapshot the pilot mounts is `45813a95dacf577461bae13f033af0dbc985a225`,
  **not** `higham_v01` (`045daf280`). They differ sharply: 63 vs 287 `Problem`
  modules. Screening against the wrong one gives wrong answers.
- Any file added anywhere under `formalization_benchmark/` changes
  `manifest.json`. `paper_bencmark/AGENTS.md` and this file are outside it and
  are not in `repository_dependencies`, so both are safe to edit.
- The five pilot-6 task IDs are frozen in `PROTOCOL.md` (line 37) and bound to
  release identity (line 17). Changing the task list mints a new pilot; it is
  not an amendment. `manifest_control.py` and `run_benchmark.py` enforce this.
- Benchmark run evidence lives only on Titan under
  `/hdd/alexgeorgantzas/highambench/` and is never committed. An agent reading
  only the repository cannot see run results.

---

## 2026-09-19 — Claude — formalization_benchmark — Higham exercise corpus screened; 13 packets drafted

**Did:**
- Screened all 240 end-of-chapter problems in Higham against the pinned library
  snapshot. 152 label-leaked, 27 research/empirical, 61 judged by hand. Method
  and full results: `numstability-thesis` repo, commit `9e072c5`,
  `sources/benchmark/higham_exercise_screening.md`.
- Thirteen tasks survive, across nine chapters and all six admissible
  conclusion types. Draft packets are in that same repo at
  `sources/benchmark/packets/` (`H5-5` … `H23-6`), schema-valid apart from the
  `task_id` pattern, with every `paper_pdf.sha256` recomputed and every printed
  page read from the page header.
- Governing criterion the screen forced: a task is valid only where the library
  holds **building blocks but not the result**. Result present reduces
  condition L to retrieval; no support at all predicts a null.

**Careful:**
- I trial-installed the packets here and **reverted it**. It works technically
  (schemas widened, 18 packets valid, manifest re-frozen to 72 files, all
  hashes verifying) but it touches six files including `manifest_control.py`
  and `run_benchmark.py` on the measurement path, and it changes the frozen
  task list. That is pilot-7, not a pilot-6 amendment. The exact file set is in
  `sources/benchmark/packets/README.md`.
- I did not re-freeze anything. `manifest.json` here is untouched at payload
  `024d5035e757bb3f2a615838d629374e005230ba6c342da2411ead1bf166bb4d`.

**Needs:**
- Whoever mints pilot-7: the packets are ready to copy in. Five carry a
  `SOURCE-ADMISSIBILITY FLAG` naming an underdetermined target that
  `PROTOCOL.md` requires resolving before scoring — H23-6, H5-5, H12-4, H7-14,
  H15-3. The other eight take their target verbatim from the source.

---

## 2026-09-19 — Claude — formalization_benchmark — observed uncommitted config change (not mine)

**Did:** nothing to it. Recording only.

**Careful:**
- `paper_bencmark/formalization_benchmark/config.json` is modified in the
  shared worktree at `~/.codex/worktrees/formalization_benchmark/`:
  `formalizer_reasoning_effort` `"ultra"` -> `"xhigh"`, mtime 2026-09-19 22:33.
  Not committed, and not made by me.
- `config.json` is a manifest release file, so this change invalidates the
  frozen manifest until `tools/freeze_manifest.py` is re-run. A `doctor` or
  `verify-release` will fail against it meanwhile.
- It also changes the formalizer's reasoning effort, which is part of the
  frozen protocol and of the environment identity for any scored pair. Pilot-6
  results already recorded used `ultra`.

**Needs:** whoever made it — commit it with a re-freeze, or revert it. Leaving
it uncommitted in a shared worktree means the next agent inherits a release
that does not verify.

---

## 2026-09-20 — Codex — formalization_benchmark — Pilot-8 authentication-repaired successor prepared

**Did:**
- Minted `formalization-benchmark-pilot-8` with the same 18-task experimental
  design, model policy, prompts, audit depth, condition ordering, and resource
  envelope as Pilot-7. The frozen manifest payload is
  `9b958df6de4c2724e1b91cd4e3e56df60d0cc4dc8630f841919e505b92169b7f`.
- Added direct, hash-verified lineage to Pilot-7's successful installation,
  clean build, and failed one-shot qualification. The failure completed zero
  roles after a stale/reused ChatGPT refresh token error; no official Pilot-7
  pair or account-global reservation exists.
- Shifted and retained the complete Pilot-5/4/3/2/1 evidence chain and campaign
  locks, updated the Titan launcher/deployment identity and operator skill to
  Pilot-8, and added regression coverage. All 161 unit tests, release
  verification, and skill validation pass.

**Careful:**
- Pilot-7 remains immutable at deployment SHA-256
  `8258440ac97ec55a4775839fa2e5cd25e1e90d62005c4e9de2b29a037be9ec8e`;
  do not retry or rewrite its failed qualification. Pilot-8 must use a distinct
  deployment, launcher, qualification, and official task namespace.
- Preparing, installing, or qualifying Pilot-8 does not authorize an official
  benchmark pair.

**Needs:** Install Pilot-8 beside Pilot-7 on Titan using the newly refreshed
device authorization, then run verify-release, doctor, all-task status checks,
and the one-shot provider qualification. Start no task without a new explicit
user request naming it.

### Titan completion

- Installed from commit `c3c07630bc961675ed22c0e39b247242ed8539ff` at
  `/hdd/alexgeorgantzas/highambench/deployment-pilot-8-r1`; deployment record
  SHA-256 is
  `3c680b39563e3e7c66e2892a16d7cb72f541ed04631d4b134cee101acda04588`.
- The fresh clean build passed in `1295.406857829` seconds under eight logical
  CPUs, 32 GiB RAM, 512 tasks, and no swap. Build-record SHA-256 is
  `94a3cec672a8c67ef1f5ffeb842320b56b68f49df2d5bfc7daaa96e545b31584`;
  it produced 879 OLean files totaling 1,015,839,912 bytes.
- Verify-release and doctor passed; condition N's 9,692,398,312-byte / 127,166-
  file treatment-absence scan passed. All 18 task slots remain `NOT_STARTED`.
- The one-shot off-benchmark qualification passed with record SHA-256
  `e8e90208a08dfcf60ca336fab3e82edc1b240701df4ab0ff6e1ec31ce6165a2e`.
  It used six isolated role turns, 14 raw provider responses, 141,042 total
  tokens, and 117.452 aggregate role wall-seconds; it consumed no official slot
  and charged no contestant budget.

**Current need:** Pilot-8 is ready. Start exactly one official task only after
a new explicit user request naming that task.

---

## 2026-09-21 — Codex — formalization_benchmark — Pilot-9 audit-interface repair prepared

**Did:**
- Preserved Pilot-8 H22-11 as an immutable `PAIR_INCIDENT`; no semantic verdict
  was inferred and no Pilot-8 evidence was rewritten or resumed.
- Fixed the blind/direct dependency-record interface: ordered `Dxxx` IDs remain
  mandatory identities, every dependency still requires a record, but `name`
  is now explicitly a human-readable semantic label rather than a hidden exact-
  equality field. The 16 semantic checks, two implication directions, fresh
  roles, and adjudication policy are unchanged.
- Minted `formalization-benchmark-pilot-9`, added hash-verified lineage to the
  Pilot-8 release, qualification, build, registry, pair, condition, and audit-
  incident evidence, and retained Pilot-7/5/4/3/2/1 locks and provenance.
- Updated the operator skill and Titan paths for Pilot-9. All 163 unit tests,
  Python compilation, release freeze, and skill validation pass. Manifest
  payload SHA-256 is
  `7de3b3ad11a96f7b0e5afa1f0f33c1d05a59e095cc4710656b0db638d7785d49`.

**Careful:**
- Pilot-8 deployment SHA-256
  `3c680b39563e3e7c66e2892a16d7cb72f541ed04631d4b134cee101acda04588`
  and H22-11 audit-incident SHA-256
  `4363f8fde6b0121ab33372364bb0806967e43ff814b010b5fcc89f1e16195469`
  are predecessor evidence only.
- Installing and qualifying Pilot-9 does not authorize H22-11 or any other
  official pair. A new explicit task request is required after readiness.

**Needs:** Commit and push the frozen Pilot-9 release, install it beside Pilot-8
on Titan, then pass verify-release, doctor, all-task status checks, and the
one-shot provider qualification without starting an official task.

### Titan completion

- Installed from commit `16172f249084b517b8069859760517297e4fb4cf` at
  `/hdd/alexgeorgantzas/highambench/deployment-pilot-9-r1`; deployment-record
  SHA-256 is
  `cf84e8cfeb47447be38055cb8cd2758c50ccb7ff98d6afe8bdf531e9ab480863`.
- The fresh clean build passed in `1296.309068256` seconds under eight logical
  CPUs, 32 GiB RAM, 512 tasks, and no swap. Build-record SHA-256 is
  `7f12698294c2e10f68431d86a959bccf34698bda1dbf3fd236a7993349ae80fa`;
  GNU time recorded 6,514.09 user CPU seconds, 392.15 system CPU seconds,
  532% CPU, and 8,453,357,568 bytes peak RSS. It produced 879 OLean files
  totaling 1,015,839,912 bytes; no memory, PID, or swap limit event occurred.
- Verify-release and doctor passed. Condition N's 9,692,673,818-byte / 127,166-
  file treatment-absence scan passed, and all 18 Pilot-9 task slots were
  `NOT_STARTED`.
- The one-shot off-benchmark qualification passed with record SHA-256
  `54efe6d01d9ef0a50235c905298779876a338e1f12806432a0f4f6b16ea2ca2a`
  and roles-tree SHA-256
  `44abda6f8a174740bc65ace23dc21f92aa5c71c6385e37e855954d4c0ba8072c`.
  Six isolated role turns made 15 raw provider calls, used 151,430 total tokens,
  and took 121.319530234 aggregate role wall-seconds. It charged no contestant
  budget and consumed no official slot. H22-11 remained `NOT_STARTED` afterward.

**Current need:** Pilot-9 is ready. Start H22-11 or another allowlisted task
only after a new explicit user request naming that task.

---

## 2026-09-21 — Codex — formalization_benchmark — Pilot-10 warm-root successor prepared

**Did:**
- Preserved all Pilot-9 results as the cold-library-discovery predecessor and
  minted `formalization-benchmark-pilot-10` for the new primary warm-start
  experiment.
- Added one task-neutral, one-shot NumStability scouting turn per release. Its
  persistent Codex checkpoint, source thread/turn IDs, cumulative usage,
  timing, prompt, environment, and tree hashes are sealed separately from task
  results. Every condition-L task copies that frozen checkpoint and uses the
  app-server `thread/fork` method; condition N still starts from a fresh thread.
- Made the N/L task prompt bytes identical. The task clock begins only with the
  task turn. Raw usage remains recorded, while the headline task usage removes
  cached/cache-write input so the inherited scouting prefix is not counted as
  newly generated task work.
- Tightened binary adjudication so a final adjudicator can return only faithful
  or unfaithful, cannot retain uncertainty, and must attach a concrete mismatch
  to an unfaithful verdict.
- Added Pilot-9 release/build/qualification/pair/condition/audit-incident
  lineage and shifted the complete predecessor chain. All 166 unit tests,
  Python compilation, release freeze, and skill structure checks pass. The
  frozen manifest payload is
  `753396d3d41ee5fae0ac488afb76b0ecf67a2c9c677a7ee91bffd7caf7e9b60a`.

**Careful:**
- The warm-root command may run exactly once for this release. Failure is
  fail-closed; it must not silently create a replacement root.
- Preparing the warm root is off the task clock and consumes no official task
  slot. It does not authorize any benchmark pair.
- Pilot-9 and its cold-start results remain immutable predecessor evidence.

**Needs:** Commit and push Pilot-10, install it beside Pilot-9 on Titan, pass
verify-release, doctor, provider qualification, and the one-shot warm-root
preparation. Do not start an official task without a separate explicit request.

### Titan completion and sealed scout failure

- Pilot-10 was committed and pushed as
  `c75840169037df96af3e4b946c8a6372e33f7377`, then installed at
  `/hdd/alexgeorgantzas/highambench/deployment-pilot-10-r1`. Deployment-record
  SHA-256 is
  `18c67fd64df4ee5ef1c3802ab6399869fda273064be37de917243757eb8b876a`.
- Its clean full NumStability build passed in `1297.901876704` seconds under
  eight logical CPUs, 32 GiB RAM, 512 tasks, and no swap. GNU time recorded
  6,537.4 user CPU seconds, 428.18 system CPU seconds, 536% CPU, and
  8,440,983,552 bytes peak RSS. Build-record SHA-256 is
  `3d9a00ac37216feaab03010538b992b9738d19b6ec3de53db35b32b62a0e6794`;
  it produced 879 OLean files totaling 1,015,839,912 bytes, with no memory,
  PID, or swap-limit event.
- Verify-release, doctor, and the off-benchmark provider qualification passed.
  Qualification SHA-256 is
  `ba26624b9e4dba410c1d133667656967afe7508302a02168e8b3ca87709ed711`;
  roles-tree SHA-256 is
  `a54d41a8bad20547b3092966c91c3e58f3eadb6ba624190efaab8834c7129b4e`.
- The one permitted scout completed its model turn, but the controller failed
  closed at telemetry reconciliation. Codex emitted an automatic
  `contextCompaction`; exact raw-response usage included that call while
  thread-cumulative usage omitted it. The difference exactly equals the
  compaction response: 248,955 input, 234,880 cached input, 4,500 output, and
  253,455 total tokens. The sealed failed warm-root record SHA-256 is
  `1f532db6810812309a8f36f6963fadd038851d95daa8a80cfa6540ede4399e08`.
  Its checkpoint and scout artifacts remain immutable evidence. No official
  Pilot-10 task started; all 18 task slots remain `NOT_STARTED`.

**Current need:** Never retry or rewrite Pilot-10's one-shot scout. Use a new
pilot identity for the telemetry repair.

---

## 2026-09-21 — Codex — formalization_benchmark — Pilot-11 compaction-aware warm-root successor in progress

**Did:**
- Preserved Pilot-10's failed scout and added exact hash-bound lineage for its
  deployment, release, build, qualification, warm-root record, scout turn,
  checkpoint tree, scout-artifact tree, and untouched official task namespace.
- Corrected usage reconciliation narrowly: exact raw usage still includes and
  reports every automatic context-compaction response, while the app-server
  thread-cumulative cross-check subtracts only raw responses explicitly
  bracketed by `contextCompaction` item events. Fork baselines use the actual
  thread-cumulative usage; the separately reported scout cost remains full raw
  usage.
- Minted `formalization-benchmark-pilot-11`, shifted and retained all nine
  predecessor locks, and added regression coverage for compaction telemetry.

**Careful:**
- Pilot-11 must create a fresh scout exactly once. Pilot-10's checkpoint is
  evidence only and must not be used as the new root.
- Installation, qualification, and scouting consume no official task slot and
  do not authorize an official benchmark pair.

**Needs:** Finish release validation, commit and push Pilot-11, install it
beside Pilot-10 on Titan, then pass verify-release, doctor, qualification, and
the one-shot warm-root preparation. Start no official task.

### Titan completion

- Pilot-11 was committed and pushed as
  `6fe44e8836d55c3f7885b026a5d22cdd5bf3dd56`, then installed at
  `/hdd/alexgeorgantzas/highambench/deployment-pilot-11-r1`. Deployment-record
  SHA-256 is
  `de9a9252a641272224c180f12036fc315b483cc4828e1b3ae882b3bb5f0b8d8d`;
  manifest-file SHA-256 is
  `a4edfb6ee6d1c13b586f20dd53900580ff54dacae3f6d7df24042db444c26cd7`;
  manifest payload is
  `14783783fe5d63fb492462bf46fbaffd65e28993fd858f291c7c7d73c0df87b5`.
- The fresh clean build passed in `1315.179208196` seconds under eight logical
  CPUs, 32 GiB RAM, 512 tasks, and no swap. GNU time recorded 6,499.55 user
  CPU seconds, 440.06 system CPU seconds, 527% CPU, and 8,406,028,288 bytes
  peak RSS. Build-record SHA-256 is
  `6f4581380982e51fd52a342cc380db5c8bae5d427d32be9c8f2aa9d136de8058`.
  It produced 879 OLean files / 1,015,839,912 bytes and 4,425 complete output
  files / 1,234,721,915 bytes. Memory, PID, and swap event deltas were zero.
- Verify-release and doctor passed. N's treatment-absence scan covered
  9,698,590,812 bytes in 127,166 files. The one-shot provider qualification
  passed with record SHA-256
  `ed0a3691c1cd2951b8e2ffdd0c9f4693f72f3d20f8c9d84ef7cce2097f49030b`
  and roles-tree SHA-256
  `36e52751a7bd768b9f515cf4cde886d13b36e61846e3f45356858ec22a4adc9d`.
- The one-shot task-neutral scout completed successfully. Warm-root-record
  SHA-256 is
  `bf30ecb9c23108cb1b1b1aa39140247d7cd175454ec903753a07c07997142031`;
  scout-turn SHA-256 is
  `b5c1c80e0023554f51cc69cd9c734d442baa708a30a2abab6ea7cccaca29303b`;
  checkpoint-tree SHA-256 is
  `17ff4f5421b1ffcd4ca083251c00087a97d802cac8c2a9238876ba742a9d1cb7`;
  and scout-artifacts-tree SHA-256 is
  `81effa1e61245ed59c25f9442df5b9bbeadce785a1396e08c7f2ff4a59f5cc6d`.
  It used 420.164831505 active seconds and 4,840,334 exact raw tokens. One
  explicitly bracketed context-compaction response used 259,829 tokens; after
  subtracting only that response, the expected and observed thread-cumulative
  baselines both equal 4,580,505 tokens. Telemetry is complete.
- A provider-free H22-11 dry run passed with zero contestant time and no model
  call. All 18 Pilot-11 task slots were checked and remain `NOT_STARTED`; no
  official pair has been created.

**Current need:** Pilot-11 is ready. An explicit user request naming one task
is required before starting an official pair.

### Sealed H22-11 incident and Pilot-12 controller successor

- Pilot-11 H22-11 is now sealed as
  `H22-11-20260921T104855Z-31f586ee` with `PAIR_INCIDENT`. Condition L
  failed before task `turn/start`; active time and task usage are zero, N never
  started, and no candidate, compilation, or audit exists. App-server emitted
  the forked child's inherited cumulative-usage notification after
  `thread/fork`; it named the Pilot-11 scout's final turn and exactly matched
  its 4,580,505-token cumulative baseline. The Pilot-11 controller incorrectly
  classified that provenance event as premature model activity. Pair-report
  SHA-256 is
  `b55af582e935bbd655b8d9dca3376a4dd3d48aeb0c526539fabbde4798c2e801`.
- Pilot-12 was committed and pushed as
  `e886cfbff3f58498f41bea3f36759588f26c5597`, then installed at
  `/hdd/alexgeorgantzas/highambench/deployment-pilot-12-r1`. Deployment-record
  SHA-256 is
  `d6e2d93daaaa409b8d42545969d851966e9a8340d6152ee075f7e1fb78ca7074`;
  manifest-file SHA-256 is
  `89a6681427d25dff5e0a3d335d42ebeb1fa67d5a199eed6234427794534ad8fc`;
  manifest payload is
  `0ed3c7e090efd8f3f580215afd1a469b6431571a50e1103ff697820996831499`.
- The fix admits exactly one pre-turn fork-baseline event only when child
  thread, frozen source turn, and all cumulative usage fields match. It logs
  the event as excluded provenance, does not assign it to the child task turn,
  and still fails closed on a wrong turn, total, foreign thread, malformed
  payload, or duplicate. Regression coverage includes the exact event order
  and mismatch rejection.
- Pilot-12 directly reuses Pilot-11's authenticated Lean/Mathlib runtime,
  NumStability source/OLean tree, and measured build record
  `6f4581380982e51fd52a342cc380db5c8bae5d427d32be9c8f2aa9d136de8058`.
  Its deployment records `new_library_build_invocations = 0` and
  `new_scout_turns = 0`. It inherits the exact Pilot-11 scout checkpoint;
  missing inherited state fails closed and cannot trigger a replacement scout.
- A provider-free real `thread/fork` installation canary passed against a copy
  of that inherited checkpoint. It observed the exact 4,580,505-token source
  baseline, charged zero task time/tokens, and sent no `turn/start`.
  Canary-record SHA-256 is
  `f1a0e810f14cef23cf4814f3e6de53e3464997188670f3773d8d3b094a57d806`;
  inherited Pilot-12 warm-root-record SHA-256 is
  `c6fb31a2728e778f6f25b12cea7ccdff4dc87cc82ecd6311fd3cbc964a3ecc5d`.
- Verify-release and doctor passed on the exact eight-CPU/32-GiB/no-swap
  envelope. The separate live formalizer/auditor/schema qualification passed;
  record SHA-256 is
  `eb825b64d270b50fb5c05ea203ecda56d8c61a264368bef499c7d0ec33f83f19`
  and roles-tree SHA-256 is
  `cd6313d0e26ef3985f7e158aeccfc0b3fce1d9a2a6d16d1de450ba5776aaf8f0`.
  All 18 Pilot-12 task slots were checked and remain `NOT_STARTED`.

**Current need:** Pilot-12 is ready. Do not rerun Pilot-11 and do not rebuild or
rescout. Start no Pilot-12 task until the user explicitly names it again.

## 2026-09-21 — Codex — formalization_benchmark — Pilot-13 exact warm-fork telemetry successor

**Did:**
- Preserved Pilot-12 H22-11 as the immutable incident
  `H22-11-20260921T113537Z-ac4c93f2`. Its L task completed in
  308.111706846 active seconds, but app-server emitted no
  `rawResponse/completed` usage. The controller therefore sealed L as
  `TELEMETRY_FAILURE`; N never started. Pair-report SHA-256 is
  `7d17491487b94243340466e243dfe2594137a72f30692678dcccac0c32298d6c`.
- Added a narrow exact fallback for inherited warm forks only. Each ordered,
  pre-`turn/completed` `thread/tokenUsage/updated` notification must contain an
  exact `last` record equal field-by-field to its cumulative delta from the
  authenticated fork baseline. Missing, late, duplicated, regressing, or
  mismatched notifications fail closed. A context-compaction item without raw
  response usage also fails closed. Fresh threads still require raw-response
  usage.
- Extended the one-shot provider qualification with a real task-neutral fork
  from the frozen warm root, the exact formalizer model/effort, NumStability
  mounts, and checked workspace read/write tools. Updated the deployment
  lineage and campaign locks to authenticate Pilot-12 plus all eleven older
  run roots.
- Committed and pushed Pilot-13 as
  `9296649b69bdac2b0d6722c1099a2f13a9ebedf6`. Manifest payload SHA-256 is
  `1f2e2753e78c6a7d612a1958eb1293d0e4a82ab9bd1d87d21fc28253d2823b1b`;
  manifest-file SHA-256 is
  `3d927b34d5abd85fec7335ab149b3f6e1331311dbc5fb7a5d38109c88286a505`.
  The complete formalization benchmark suite passed all 174 tests, and the
  installed operator skill passed its validator.

### Titan completion

- Installed Pilot-13 at
  `/hdd/alexgeorgantzas/highambench/deployment-pilot-13-r1`; deployment-record
  SHA-256 is
  `7e0fac28705562b1603b7f26dbf6bce2640de8116fbc5502b98cfde470372c84`.
  Verify-release and doctor passed on eight logical CPUs, 32 GiB RAM, 512
  tasks, and no swap.
- Reused Pilot-11's authenticated build record
  `6f4581380982e51fd52a342cc380db5c8bae5d427d32be9c8f2aa9d136de8058`
  and the inherited task-neutral scout. The deployment records zero new
  library builds and zero new scout turns. Pilot-13 warm-root-record SHA-256 is
  `8a1df612f64b31ff4e8507fd5eda051cc51e4e9a8148a058fde491a5e0aa5c29`.
- The seven-turn off-benchmark qualification passed. Record SHA-256 is
  `7f42ca772f18b52b2ae430bdb855666879bbfbff57de6086cc21d1e9d05664b7`;
  roles-tree SHA-256 is
  `7389fc863e9ed6be718c2b9fb8ce4e641f7d5e08a1e2e29a1776d84d88276d77`.
  The new live warm-fork probe reproduced the production provider surface:
  zero raw-response usage events and four exact cumulative notifications. It
  passed in `fork_cumulative_notifications` mode with 112,472 exact tokens.
  Qualification is uncharged and consumed no official task slot.
- All 18 Pilot-13 task statuses were checked and remain `NOT_STARTED`, including
  H22-11.

**Current need:** Pilot-13 is ready. Do not rebuild, rescout, reinterpret the
Pilot-12 incident, or start an official pair without a new explicit task-run
request.

## 2026-09-21 — Codex — formalization_benchmark — Pilot-13 H22-11 official pair

**Did:**
- Ran exactly one user-authorized official Pilot-13 pair for H22-11. Run ID is
  `H22-11-20260921T124400Z-b9314206`; frozen condition order was L then N.
  The pair completed at `2026-09-21T13:21:50.152617+00:00` with status
  `COMPLETE`, `measurement_admissible = true`, and strict hardware enforcement.
- Both conditions compiled, passed proof-integrity checks, and were accepted
  faithful on their first submission. Both audits classified the candidate
  `faithful-equivalent`, judged both implication directions `yes`, reported no
  mismatches or remaining uncertainties, and did not require adjudication.
- L used 436.405785288 contestant-active seconds and 147,099 exact net-new
  contestant tokens (131,536 uncached input plus 15,563 output; 934,299 total
  provider tokens including cached input). Its candidate is 106 lines,
  Candidate.lean SHA-256 is
  `5a14030502aea74d1ebdb97d178146338ad3b781a57d8212c742eb43529e3464`,
  and semantic SHA-256 is
  `874b195088342b759d0c6fcb9e898dc1829925a82661fe5a6b9450b7e33fb089`.
- N used 207.567803626 contestant-active seconds and 39,499 exact net-new
  contestant tokens (29,818 uncached input plus 9,681 output; 226,891 total
  provider tokens including cached input). Its candidate is 92 lines,
  Candidate.lean SHA-256 is
  `683782798008ae10b916be4d7de10366e91535638095f828b3d2229bd581fe04`,
  and semantic SHA-256 is
  `37c9870cba6c12a995cff2e4f50cc29c84be48f0ef5408f1baa9a5754934d312`.
- L's audit consumed 776.757844736 excluded wall seconds and 264,415 auditor
  tokens across blind translation, direct judgment, and round-trip judgment;
  its decision SHA-256 is
  `36c6869a46224b01e43516e73a15b48dad61779b8a816dcc782b19ad99419c2f`.
  N's audit consumed 786.521991498 excluded wall seconds and 308,682 auditor
  tokens across the same three roles; its decision SHA-256 is
  `65ca67bcc15f4effdba1d9a43ba457187a06c78be84606c0335f610c591d971c`.
  Auditor usage was recorded and excluded from benchmark scores.
- Total contestant-active time was 643.973588914 seconds. Total end-to-end wall
  time was 2269.825632396 seconds, of which 1625.852043482 seconds were
  excluded overhead. The reused frozen library build and inherited scout were
  not rebuilt or rerun. No network violations or credential-scan failures were
  recorded.
- Pair-report SHA-256 is
  `bcc10950f86b99dd934206e1828bdb03898b171994964e81309a5c63843eb958`;
  pair root is
  `/hdd/alexgeorgantzas/highambench/deployment-pilot-13-r1/runs/pairs/H22-11-20260921T124400Z-b9314206`.

**Result:** H22-11 is a valid completed Pilot-13 observation. On this single
pair, N was 228.837981662 contestant seconds faster and used 107,600 fewer
net-new contestant tokens than L. Preserve the raw sealed artifacts; do not
rerun H22-11 as another official Pilot-13 observation.

---

## 2026-09-21 — Codex — codex/pilot-14-retrieval-proof — proof-required retrieval-indexed Pilot-14 prepared

**Did:** Minted `formalization-benchmark-pilot-14` in commit
`65049ebed42b6cc3ebf1417d503535921250caf1`, manifest payload
`07a7cbbf10cec79fa2f6900ff15fabf2d6a47e3f2f891bf9e829d82e74aa5fdd`.
Candidates now require complete kernel-checked proofs. L receives a deterministic
ranked declaration atlas and reuse-first guide; every attempt records private
uptake/code/search telemetry. Added excluded synthetic canary H00-00 and froze
the scientific gate to H5-5, H7-12, H10-7, H23-6. All 177 controller tests,
release verification, skill validation, and an actual Titan-source atlas smoke
test pass; the atlas builds in 2.6 seconds, is 39 MiB, and returns bounded ranked
queries in about 0.33 seconds.

**Careful:** Pilot-13 evidence and task slots remain immutable. Pilot-14 setup
must reuse `/hdd/alexgeorgantzas/highambench/deployment-pilot-13-r1`; it must not
rebuild NumStability or run another scout. H00-00 is not scientific evidence.

**Needs:** Push the branch, install Pilot-14 beside Pilot-13, qualify once, run
H00-00, then run the four predeclared primary pairs and evaluate the frozen gate.

---

## 2026-09-21 — Codex — Pilot-14 execution and Pilot-15 successor

**Pilot-14 evidence preserved:**
- Installed and qualified Pilot-14 at
  `/hdd/alexgeorgantzas/highambench/deployment-pilot-14-r1` without a new
  NumStability build or scout turn. H00-00 completed with both conditions
  faithful and validated the end-to-end proof/audit/telemetry path.
- H5-5 run `H5-5-20260921T154540Z-9a55852a` completed with both conditions
  faithful. N used 409.356090076 active seconds, 77,755 net-new tokens, and 251
  final lines. L used NumStability, used 537.723999656 active seconds, 102,606
  net-new tokens, and 149 lines. L therefore reduced code size by about 41%
  but lost on time and task-local tokens. Its trace found the exact Horner
  declarations by 33 seconds; most remaining cost was semantic adaptation.
- H7-12 run `H7-12-20260921T164426Z-d75c302c` is a sealed `PAIR_INCIDENT`.
  N accumulated 1135.529578188 active seconds and 155,470 observed net-new
  tokens before the driver rejected an exact duplicate token-usage
  notification. The provider repeated an identical cumulative and last-usage
  payload after 57 seconds without a new raw response. The old driver treated
  that idempotent replay as a delta mismatch, aborted the live turn, and then
  rejected one late shutdown message. L never ran. Pair-report SHA-256 is
  `7f095fcac73bd26f0ab1066cac1d24b909e9af0b7a4d67846e350dc9b7a7a93b`.
  Do not rerun either Pilot-14 slot.

**Pilot-15 prepared:**
- Created branch `codex/pilot-15-adaptation-runtime-fix` and pilot identity
  `formalization-benchmark-pilot-15` with manifest payload SHA-256
  `0b54fc94945f993ac59aa76f239a7e09aef6a2f1f2d6f73abeb31ed225552228`.
- Exact duplicate cumulative/last-usage notifications are now recorded as
  idempotent replays and not counted twice. Changed duplicates, regressions,
  and raw/cumulative disagreements still fail closed.
- The deterministic atlas is version 2 and adds bounded `show.py` declaration
  inspection. The L-only guide now stops broad discovery after a plausible
  hit, asks for a minimal direct wrapper compile first, and only then adds
  paper-specific bridges. No new scout turn is allowed.
- All 178 controller tests, release verification, focused atlas/telemetry
  tests, `git diff --check`, and the operator-skill validator pass.

**Needs:** Commit and push Pilot-15, install it beside all predecessors using
the same frozen Pilot-13 runtime/build/scout lineage, qualify once, run H00-00,
then run the four predeclared primary tasks and evaluate the unchanged gate.

---

## 2026-09-22 — Codex — codex/pilot-16-composition-packets — matched exploratory runner

**Did:** Added `tools/design16_matched.py` and focused tests for sequential R0
(Mathlib-only) versus R1 (Mathlib plus NumStability) engineering pairs. Both
conditions use the same bounded retriever and prompt, fresh stateless
formalizers, compile-only preflight, separate retrieval/formalizer timing, and
condition-specific OLean visibility. Added the exact CLI/setup note at
`design16/MATCHED_RUNNER.md`.

**Careful:** Every output is labelled `UNSCORED_ENGINEERING_EXPLORATORY` and
`NOT_AUDITED`. A successful run is only `COMPILED_UNAUDITED`; it is not a
scientific observation until an independent faithfulness audit is bound to it.
The Pilot-15 manifest was deliberately not refreshed or edited.

**Needs:** Build one frozen Mathlib atlas on Titan, then invoke the runner with
an explicit counterbalanced `--condition-order`. Do not run timed conditions
concurrently on the eight-core host.

---

## 2026-09-22 — Codex — codex/pilot-16-composition-packets — proof-completion feasibility screen

**Did:** Added the provider-free, repository-only machine-readable screen at
`formalization_benchmark/design16/proof_completion_feasibility.json`. It finds
zero immediately usable common Lean statements: the repository has source
packets but no exact proof-free Lean statement plus independent audit binding
for any of the thirteen tasks. H22-11 and H5-5 have faithful-run signals but
their candidate sources are Titan-only. Nine tasks are potentially
constructible; H20-8, H20-9, and H23-6 are excluded for direct result-family
leakage, and H15-3 needs a collision review.

**Careful:** This is a feasibility report, not a benchmark result. It did not
access Titan or a provider, did not alter a router or frozen Pilot-15 file, and
does not treat prose run summaries as substitutes for exact candidate bytes.

**Needs:** Before using the fallback, construct and independently audit one
Mathlib-only common statement per admitted task, freeze its bytes, cross-compile
it in R0/R1, and keep proof-completion results separate from end-to-end
formalization results.

---

## 2026-09-22 — Codex — codex/pilot-16-composition-packets — authenticated campaign reporter

**Did:** Added the provider-free Design-16/17 campaign reporter at
`formalization_benchmark/tools/design16_campaign_report.py`. It authenticates
the nonce-bound campaign manifest, frozen-input identity, state/summary journal
chains, pair attestations and artifact closures, condition reports, internal
statement audits, and an optional external proof-audit batch. JSON and Markdown
keep the 2/6/5 strata separate and report the five diagnostic per-task R1/R0
ratios without a pooled estimate. Focused reporter tests cover proof and
statement modes,
external audits, tampering, missing audits, and overwrite refusal.

**Careful:** A proof pair with status `FORMALIZATION_FROZEN_PENDING_AUDIT` is
never counted as an effect result, even when an external audit batch is shown.
Only a primary `AUDITED_FAITHFUL_PAIR` is marked effect-analysis eligible;
negative controls and excluded diagnostics remain separate. The Pilot-15
manifest was deliberately not refreshed.

**Needs:** Run the reporter only after the campaign journal is quiescent. Pass
`--audit-batch-root` for proof-mode audit results; statement-only audits are
read from each condition's sealed internal audit tree.

**2026-09-22 hardening update:** The reporter now authenticates the three-way
statement condition classification (`FAITHFUL`, `UNFAITHFUL_OR_FAILED`, and
`NOT_DECIDED_INFRASTRUCTURE`) and the attested campaign outcome
`PAIR_INFRASTRUCTURE_INCIDENT`. Contestant-active seconds are checked against
the attempt sum and exposed as the primary timer. Its R1/R0 effect ratio is
published only for `AUDITED_FAITHFUL_PAIR`; ineligible and infrastructure
outcomes retain authenticated raw diagnostics but no effect ratio.

---

## 2026-09-22 — Codex — codex/pilot-16-composition-packets — Design17 13-task campaign complete

**Did:** Completed all 13 Design17 statement-only pairs on Titan at controller
commit `c5c279d3dff674f9b91c5a774f8db76eac487431`: 12 audited-faithful
pairs, one audited-ineligible pair (H12-4), and zero incidents. The authenticated
offline report is summarized in `paper_bencmark/DESIGN17_CAMPAIGN_2026-09-22.md`;
Titan report SHA-256 values are recorded there.

**Careful:** The campaign is `UNSCORED_ENGINEERING_EXPLORATORY`. Only H5-5 and
H10-7 are primary-engineering tasks; negative controls and excluded collision/
router diagnostics must not be pooled with them. H23-6 exposed a component-
router false negative, while H12-4 exposed an incomplete semantic source
contract.

**Needs:** Implement component-level composition packets and a semantic
source-contract gate, then validate H23-6 and H10-7 as canaries before launching
another large campaign. Do not rewrite or resume the completed Titan campaign.

---

## 2026-09-22 — Codex — next-campaign formalizer model decision

**Decision:** The next benchmark campaign must use `gpt-6-sol` at `xhigh` for
both matched formalizer conditions. Keep the audit model/effort independent and
unchanged unless separately approved. Freeze the exact model and effort in the
new campaign protocol, config, manifest, and provider qualification; verify
the model/effort combination on Titan before any paid task.

**Boundary:** Completed Design-17 and earlier campaigns retain their original
`gpt-5.6-sol` identity and evidence. Do not edit their frozen schedules,
manifests, or results or pool their measurements with the successor campaign.
No new run is authorized by this model decision alone.

---

## 2026-09-23 — Codex — codex/pilot-18-probabilistic — model admission blocked

**Did:** Created a draft twelve-task probabilistic successor corpus with
hash-frozen HM19/HALL21/CASTRO24 PDFs, initial source and NumStability
component screens, and a draft staged protocol under
`formalization_benchmark/design18/`. The screen flags HM19 Theorem 3.4's
printed column-index inconsistency and CASTRO24 Theorem 4.1's printed
pairwise-tree-height concern; neither has been silently corrected.

**Gate:** An off-benchmark Titan CLI probe of `gpt-6-sol` at `xhigh` returned
HTTP 400: the model is not supported when using Codex with that ChatGPT
account. No measured successor task, canary, or provider qualification has
started. A user choice between waiting for Sol access and authorizing a
separately identified Astra pilot was requested asynchronously. Do not fall
back to GPT-5.6 or replace Sol inside a frozen pilot.

**Needs:** Resolve model access; independently validate each full source
contract and target-collision absence; implement and test the successor
component router/controller/deployment before any measured call. The design18
documents are explicit drafts, not an admitted or completed benchmark.

---

## 2026-09-23 — Codex — codex/pilot-20-integrity-interface — open-snapshot retrieval prepared

**Did:** Commit `90f74086b` adds a prospective open-snapshot statement mode:
the composition packet is a suggestion rather than a whitelist; L can read
the full pinned NumStability source/index and import any compiled declaration;
N can read Mathlib source/index. Direct library uses remain logged. A separate
Pilot-20 task-neutral warm-root prompt asks for exact foundational FP/gamma
interfaces once, off the per-task clock. Focused tests pass.

**Careful:** Historical packet-only mode and Pilot-19 evidence are unchanged.
This is not an admitted/frozen Pilot-20 release: no new warm root, task runner,
or measured pair has been launched. Files added under
`formalization_benchmark/` change manifest identity; do not attempt to use
this checkout as an older frozen release. The new source-first corpus and
target-collision gate are still required before measured tasks.

**Needs:** Wire `library_access_policy="open-snapshot"`, the Pilot-20 prompts,
and `warm_root_schema_version="pilot-20-warm-root-1"` into a new frozen runner;
perform a non-contestant Titan mount/search/import smoke test and review the
new one-time scout dossier before launching any measured task.

---

## 2026-09-23 — Codex — Pilot 22 first-pair incident and prospective fix

**Did:** Pilot 22 stopped at its mandatory first-pair gate with an unscored
`PAIR_INCIDENT`: a warm-fork tool sandbox created an empty top-level `.codex`
mount point, which the workspace safety scan rejected before freezing/auditing
R1. R0's single candidate passed the full audit. The frozen Titan campaign and
pair hashes and exact evidence are in
`formalization_benchmark/design20/PILOT22_INCIDENT.md`; do not resume or edit
Pilot 22.

**Prospective fix:** The next controller permits only an empty top-level
`.codex` directory. Populated or nested `.codex`, symlinks, and protected
control files remain prohibited. The development campaign requires an explicit
new pilot ID. Relevant unit tests pass. A new Pilot 23 must use a fresh output
root and controller commit; no Pilot 22 outcome may be scored as a pair.

---

## 2026-09-23 — Codex — Pilot 24 preserved; Pilot 25 running

**Did:** Admitted twelve prospectively screened development tasks, each with a
source-only review, target-collision screen, direct-component preflight, and
private Lean statement compilation. Pilot 24 ran the first pair only and is
frozen at `PAUSED_FIRST_REVIEW`. Both RUMP12-THM3.4 statements were audited
faithful on one submission; L directly used NumStability but was 1.390× slower
and used 1.808× net-new tokens. Full immutable hashes and diagnosis are in
`formalization_benchmark/design20/PILOT24_EARLY_REVIEW.md`. Do not resume it.

**Prospective fix:** The task-neutral router now exposes public finite-format
and nearest-rounding interfaces for positive titles calling for that model;
Pilot 24's L trace showed it searching for and ultimately using those exact
declarations without any initial card. The new Pilot 25 corpus/admission and
12-task preflight are frozen at controller commit `9a27c4e44`. Active Titan
campaign: `/hdd/alexgeorgantzas/highambench/pilot25-development-12-20260923-a`.
It runs RUMP12-THM3.4 first and pauses for early review; if eligible, resume
the **same** campaign with `--resume-after-review`, then three 8-CPU/24-GiB
lanes run the other eleven tasks. Do not overlap campaigns or alter frozen
inputs. Preserve all negative and no-use results.

**Account boundary:** The user explicitly said not to redeem the available
Codex reset credit. At about 3% weekly usage remaining, provide a complete
fresh-chat handoff prompt for their second account and stop or coordinate
without overlapping the still-running campaign. Codex sign-in, not API
billing, is used for GPT-6 Sol/high formalizers and Astra/high auditors.

---

## 2026-09-23 — Codex — Pilot 25 paused; Pilot 26 prepared

Pilot 25 is frozen at `PAUSED_CONCURRENT_INCIDENT` after seven of twelve
scheduled tasks. Four pairs were audited faithful, two were ineligible, and
one had an audit-system pair incident. Its final journal hash and all outcomes
are in `formalization_benchmark/design20/PILOT25_PARTIAL_REVIEW.md`; do not
resume or silently rerun any Pilot 25 measured task. The controller process
and its active lane exited before Pilot 26 setup proceeded.

Pilot 26 is a separate adaptive exploratory run with the same twelve source
tasks and frozen library. Its prospective changes are condition-neutral safe
exploration guidance, clearer audit output-field semantics with the strict
validator retained, and three fixed 8-CPU/24-GiB lanes refilled on task
completion. The corpus puts RUMP12-THM3.5 first as an incident canary. A fresh
static preflight and hash-bound admission are required before its first pair.
No result from Pilot 25 may be pooled into Pilot 26.

Pilot 26's static preflight and admission passed all twelve tasks. Its first
RUMP12-THM3.5 pair was audited faithful on both sides in one submission and
is documented in `formalization_benchmark/design20/PILOT26_FIRST_REVIEW.md`.
L was 1.061× slower in contestant-system time, 1.238× higher in net-new
tokens, and 0.784× the candidate lines; no interface or audit-system incident
recurred. The same frozen campaign was resumed for its remaining eleven tasks
in refilled three-lane mode. Monitor only the existing campaign at
`/hdd/alexgeorgantzas/highambench/pilot26-development-12-20260923-a`;
never launch an overlapping one or restart a measured task silently.
