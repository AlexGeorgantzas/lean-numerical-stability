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
