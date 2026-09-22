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
- A later compile preflight uncovered an indexer defect: `mutual … end`, dotted
  namespace names, and relative dotted declaration names had produced bad
  qualified names in the old discovery atlas. This is an infrastructure
  incident, not a benchmark outcome. The corrected task-neutral Mathlib and
  NumStability atlases were rebuilt from the **same** frozen source closures;
  their file hashes are pinned in `ATLAS_RELEASE.json`. The old deployment and
  its compiled OLean trees were not modified. The corrected catalogs passed
  a fresh full twelve-task routing preflight on Titan. This does not clear the
  source or model gates.
- The condition prompts have an exact common-byte prefix; only R1 appends
  encouragement to use NumStability.
- A full packet build on the nine-root `CASTRO24-4-1` treatment route produced
  9,411 bytes, safely below the frozen 64-KiB cap. Its R0 route produced 2,518
  bytes. Both use ten-root/two-dependency limits and identical routing code.
- The provider-free preflight ran successfully on Titan from an isolated,
  detached worktree, updated through commit
  `420ce225125a8e8b4a0e0088bc65eaef065e81a8`.
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
   account. The exact Pilot-18 qualification repeated this under the fixed
   8-CPU/32-GiB envelope at 2026-09-22 22:44 UTC and failed after 3.36 seconds
   with **zero** model tokens; its immutable record is at
   `/hdd/alexgeorgantzas/highambench/pilot18-model-gate-v1/qualification.json`
   on Titan (SHA-256
   `a684c5ff00aaa413d8ededb4af67e3b1eb7ebe28ad1a4100fc53e7465c88ee7e`).
   No API credential is configured on Titan. Do not silently use another
   model, pricing route, or account.
   The deployed tool is Codex CLI `0.154.0`. Official OpenAI documentation
   [lists `gpt-6-sol` at `xhigh` as an API model](https://developers.openai.com/api/docs/models),
   but that does not grant it to Titan's current ChatGPT-account login. An
   API-key route would be a separate billing/authentication choice, not an
   automatic retry or a reason to rewrite the requested model.
   A second one-shot qualification after the continuation request, at
   2026-09-23 UTC, again returned the same ChatGPT-account HTTP 400 with zero
   model tokens. The immutable report is
   `/hdd/alexgeorgantzas/highambench/pilot18-model-gate-v2/qualification.json`
   (SHA-256 `7f3a3aafcd6370bc0bdd35026cc162922e422215de8c2f4668ed9f1e0c6f0f4a`);
   this is not a timed task. An initial invocation with an incompatible
   deployment manifest stopped before making an output root or a model call.
   The recorded v2 uses the Pilot-15 authentication deployment. Its Codex
   binary and authentication-file hashes equal those in the frozen Design-17
   deployment used for library compilation, so this probes the same model
   access without changing the library snapshot.
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

The Titan campaign entry point was also dry-gated under the enforced envelope:
it stopped on source flags before creating an output directory. A separate
provider-free `design18_compile_preflight.py` can check the first three
controller-generated packets, signature interfaces, OLean closure, and one-sorry
templates without invoking a formalizer or judge. This is an infrastructure
check only; any output is excluded from benchmark metrics.
The `HM19-3-2` compile preflight passed for both conditions using the old
atlas. `HALL21-3-3` passed both conditions, but `CASTRO24-4-2` failed while
rendering Horner signatures because old catalog names lacked the namespace.
These are retained as off-benchmark diagnostics and are **not** timed task
results. The corrected catalog is the proposed fix; its preflight outcome is
recorded below.

With the corrected catalogs, all three early tasks passed signature rendering,
packet OLean closure, and controller-template compilation in both conditions
under Titan's fixed envelope. The immutable off-benchmark artifact is
`/hdd/alexgeorgantzas/highambench/pilot18-compile-preflight-corrected-v1/compile-preflight.json`
on Titan (SHA-256
`c2a142e251f2682ff38b7dd66949cd95a62f81e14b9a02cf04c9fac24387a0c5`).
The observed per-condition preflight wall times were R0/R1 19.35/32.33 s for
`HM19-3-2`, 18.63/29.07 s for `HALL21-3-3`, and 18.95/32.44 s for
`CASTRO24-4-2`. These include packet/signature/template checks and are **not**
contestant-active time or benchmark outcomes. The measured runner now records
retrieval-phase and template-validation times separately.

The other seven source-clean tasks also passed the same two-condition static
compile preflight under Titan's fixed envelope. The immutable reports are
`/hdd/alexgeorgantzas/highambench/pilot18-compile-preflight-clean-a-v1/compile-preflight.json`
(SHA-256 `36b3629eada005c532a4a3bae8e5154e72f840c03d6c97cabe2457b0a28de780`;
`HM19-2-4`, `HM19-3-1`, `HM19-3-3`, `HM19-3-5`) and
`/hdd/alexgeorgantzas/highambench/pilot18-compile-preflight-clean-b-v1/compile-preflight.json`
(SHA-256 `2d9651cf0066434692e4e2389b9bc152197f3a837a0425471db2065a6b7742ab`;
`HM19-3-6`, `HM19-3-7`, `HM19-3-8`). Thus **all ten unflagged tasks** have
passed static controller packet, signature, OLean, and one-`sorry` template
checks for both conditions. The two source-flagged tasks are intentionally
excluded until their source contracts are resolved. No formalizer, candidate,
or faithfulness audit was run in these preflights.

The source alternatives under investigation, **not admitted replacements**, are
documented correction of `j=1:n` to `j=1:p` while retaining both conclusions
of Higham–Mary Theorem 3.4, and prospective replacement of Castro Theorem 4.1
with a separately screened result. The preferred candidate is now Hallman and
Ipsen Theorem 2.6, which explicitly defines computational-tree height. The
source rationale, full-domain constraints, and rejected alternative are in
`SOURCE_RESOLUTION_PROPOSAL.md`. This proposal changes neither frozen source
packet nor task manifest. Any adoption must mint a new pilot identity, retain
the superseded task and reason, and redo the admission checks. No outcome data
exist for any proposed replacement.

The unadopted Hallman–Ipsen proposal packet revealed another off-benchmark
router defect: its negative scope sentence forbidding sequential specialization
had activated the recursive-summation API. The selector now activates algorithm
families only from the positive selected-result title; the full packet remains
in lexical ranking and all contestant/auditor input. It also recognizes
general summation trees and can expose a task-neutral SumTree statistical RMS
bridge. Unit tests cover negated-scope exclusion. This routing revision is
still **not** admitted for measurement despite the later static checks: source
and model gates remain. Any measured release would use a new pilot identity;
no Pilot-18 contestant outcome exists to pool or overwrite.
The first twelve-task reroute caught an additional orthographic gap before
measurement: `Gaussian-elimination` in the selected title did not match the
generic `gaussian elimination` family alias, leaving `HM19-3-7` without its
algorithm component. Hyphen/dash normalization has been added to both title
and alias matching, with a regression test; the first reroute remains an
off-benchmark diagnostic, not a passed release check.

After hyphen normalization, the full twelve-task Titan routing check passed
with an exact common prompt prefix, no control exposure to NumStability, and
the correct Doolittle family for `HM19-3-7`. It still reports
`NOT_ADMITTED_SOURCE_FLAGS`. All ten source-clean tasks then passed the
revised-router signature, OLean, and one-`sorry` compile preflight in both
conditions under the fixed Titan envelope. The three immutable reports and
SHA-256 hashes are:

- `/hdd/alexgeorgantzas/highambench/pilot18-compile-preflight-router-v2-early/compile-preflight.json`
  — `e00a0544787a32e90555167ed6734068350cc3aac4b201d930a68db87108ca8c`
  (`HM19-3-2`, `HALL21-3-3`, `CASTRO24-4-2`);
- `/hdd/alexgeorgantzas/highambench/pilot18-compile-preflight-router-v2-a/compile-preflight.json`
  — `39e3ee95eb16931ed08099c1df32517c7215216fd16db6be6708898671e037be`
  (`HM19-2-4`, `HM19-3-1`, `HM19-3-3`, `HM19-3-5`);
- `/hdd/alexgeorgantzas/highambench/pilot18-compile-preflight-router-v2-b/compile-preflight.json`
  — `aaa47160a3af92fcd1ad1dca647f8250a147750c5140a5e10421d0004eccd42a`
  (`HM19-3-6`, `HM19-3-7`, `HM19-3-8`).

These are still infrastructure checks, not formalizer attempts, audits, or
benchmark outcomes. The two source-flagged tasks and the GPT-6 Sol gate remain.

The present branch is preparation only. A successful routing preflight is
not evidence of faster or more faithful formalization. Preserve all
preflight/model-gate incidents and do not pool later Pilot-18 outcomes with
the prior Design-17 campaign.
