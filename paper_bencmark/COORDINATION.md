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
