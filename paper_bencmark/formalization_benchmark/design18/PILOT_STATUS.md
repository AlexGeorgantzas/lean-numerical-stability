# Pilot 18 status — preflight, not a measured campaign

As of 2026-09-23 (Europe/Athens), **zero R0/R1 task pairs have been run**.
No result from this design should be reported as a benchmark effect. The draft
release is deliberately fail-closed while the gates below remain unresolved.

## Completed provider-free checks

- The twelve draft source packets match the declared task IDs, and the three
  PDF SHA-256 hashes match on both the development machine and Titan.
- The frozen schema-v3 Mathlib and NumStability declaration atlases were used
  with the same `component-roles-1` policy in R0 and R1. All twelve routes
  completed without a target probabilistic theorem selected.
- R0 receives Mathlib's `Measure` and `iIndepFun` foundations. R1 receives
  those same foundations plus matching NumStability FP and algorithm components.
  The initial selector's unrelated theorem matches were removed before any
  timed formalization. The exact catalog has 32 verified declaration anchors.
- The condition prompts have an exact common-byte prefix; only R1 appends
  encouragement to use NumStability.
- A full packet build on the nine-root `CASTRO24-4-1` treatment route produced
  9,411 bytes, safely below the frozen 64-KiB cap. Its R0 route produced 2,518
  bytes. Both use ten-root/two-dependency limits and identical routing code.
- The provider-free preflight ran successfully on Titan from an isolated,
  detached worktree at commit `30c57b7cfa3f9bb8f27f4afac9de2879461affc1`.
  It reported `NOT_ADMITTED_SOURCE_FLAGS`, twelve packets, and an exact prompt
  prefix match. It did not run a formalizer or auditor.
- One independent, fresh `gpt-6-astra`/`high` paper-side review of
  `HM19-3-4` completed off benchmark. It judged the **draft packet** faithful
  to the printed PDF while explicitly identifying the `j=1:n`/`p`-column
  inconsistency; it did **not** resolve or admit the theorem. The immutable
  artifact is at
  `/hdd/alexgeorgantzas/highambench/pilot18-source-contracts/HM19-3-4-v1/source-contract-review.json`
  on Titan (SHA-256 `973fc0ebd2a7c827059bd84e7a0f397e61637cefabe5c3545d3e335cfae4f877`).
  This single check cost 95,803 total tokens and 86.98 seconds of reviewer wall
  time, excluded from benchmark metrics. Because independent source-contract
  calls were previously deemed optional, this high cost argues against
  repeating the same check for every static source packet without a specific
  source uncertainty.

Reproduce the local/Titan preflight with:

```bash
PYTHONPATH=paper_bencmark/formalization_benchmark/tools \
  python3 paper_bencmark/formalization_benchmark/tools/design18_preflight.py \
  --mathlib-atlas /path/to/mathlib/declarations.jsonl \
  --numstability-atlas /path/to/numstability/declarations.jsonl
```

## Admission blockers

1. A real off-benchmark Titan probe of `gpt-6-sol`/`xhigh` returned HTTP 400:
   the model is not supported for Codex with the currently signed-in ChatGPT
   account. No API credential is configured on Titan. Do not silently use
   another model, pricing route, or account.
2. `HM19-3-4` prints `j=1:n` for a matrix with `p` columns. A documented
   correction to `j=1:p` is mathematically indicated by the proof but must be
   decided before freezing the packet.
3. `CASTRO24-4-1` prints `h=floor(log₂ n)` for a recursively ceiling-split
   pairwise tree. That height can be `ceil(log₂ n)`; no source correction has
   been found. Restricting the task to powers of two would be partial-domain
   coverage and is not permitted by the current audit policy.
4. A draft Pilot-18 wrapper now binds the Design-17 compiler/audit/repair
   machinery to the new packet paths, task-neutral component policy, exact
   condition prompts, and a verified one-time warm fork. The campaign runner
   has provider-free tests for the frozen twelve-task schedule and first-pair
   slowdown/uptake stops; it has not run a measured pair. It still needs a
   successful provider capability check and end-to-end canary on Titan before
   measurement. The mere presence of wrapper code is not a runnable release.

The source alternatives under investigation, **not admitted replacements**, are
to select equation (3.12) alone from Higham–Mary Theorem 3.4 (thus avoiding its
misindexed (3.11)) and replace Castro Theorem 4.1 with a separately screened
result such as Hallman Theorem 5.2. Either decision must be made before the
source manifest is frozen, with the superseded task and reason retained in the
release record. No outcome data exist for any proposed replacement.

The present branch is preparation only. A successful routing preflight is
not evidence of faster or more faithful formalization. Preserve all
preflight/model-gate incidents and do not pool later Pilot-18 outcomes with
the prior Design-17 campaign.
