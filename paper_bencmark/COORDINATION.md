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
