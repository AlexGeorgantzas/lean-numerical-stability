# Pilot-14 operations

## Identity and paths

- Pilot: `formalization-benchmark-pilot-14`
- Launcher: `~/.local/bin/run-highambench-formalization-pilot-14-r1`
- Deployment: `/hdd/alexgeorgantzas/highambench/deployment-pilot-14-r1`
- Predecessor: `/hdd/alexgeorgantzas/highambench/deployment-pilot-13-r1`
- Formalizer: `gpt-5.6-sol`, `xhigh`
- Auditors: `gpt-6-astra`, `high`
- Candidate: one final `HighamBenchCandidate.target`, complete proof, no holes

The release files under `paper_bencmark/formalization_benchmark/` are
authoritative. Pilot-13 and earlier run roots are read-only.

## Install once

From a clean release checkout:

```bash
python3 paper_bencmark/formalization_benchmark/tools/setup_titan.py \
  --pdf-source-dir /ABSOLUTE/PATH/TO/FROZEN/PDFS \
  --predecessor-deployment-root /hdd/alexgeorgantzas/highambench/deployment-pilot-13-r1 \
  --deployment-root /hdd/alexgeorgantzas/highambench/deployment-pilot-14-r1 \
  --launcher ~/.local/bin/run-highambench-formalization-pilot-14-r1
```

Setup must authenticate Pilot 13 and reuse its toolchain, packages, library
source/OLean, build record, and warm checkpoint. It generates only the
deterministic task-neutral atlas, records its full tree hash, runs provider-free
runtime/sandbox/app-server/fork canaries, and publishes atomically. No `lake
build`, package update, cache download, or model scout is permitted.

## Readiness

```bash
~/.local/bin/run-highambench-formalization-pilot-14-r1 verify-release
~/.local/bin/run-highambench-formalization-pilot-14-r1 doctor --task-id H00-00
~/.local/bin/run-highambench-formalization-pilot-14-r1 qualify-provider --task-id H00-00
```

Qualification is one-shot and off-benchmark. A previous PASSED record is reused
only after full hash verification. Doctor must prove:

- exact release, deployment, Codex/host, Lean, Mathlib, PDFs, packets, prompts;
- frozen NumStability source/OLean/build and generated atlas identity;
- N treatment absence and L-only source/OLean/atlas/guide exposure;
- inherited warm-root/checkpoint identity and real-fork compatibility;
- eight-CPU/32-GiB/no-swap outer envelope and generated-command cgroup;
- account registry and predecessor locks; and
- no existing official slot for a new task.

## Canary

Run the synthetic end-to-end pair exactly once:

```bash
~/.local/bin/run-highambench-formalization-pilot-14-r1 run --task-id H00-00
~/.local/bin/run-highambench-formalization-pilot-14-r1 status --task-id H00-00
```

Require `COMPLETE`, both N and L `ACCEPTED_FAITHFUL`, complete exact active-time
and usage telemetry, a compiled proof with zero holes, private semantic dossiers,
uptake records, and graceful conversation shutdown. H00-00 is excluded from all
scientific summaries regardless of performance.

## One official task

Normalize case and hyphens, check the allowlist, then:

```bash
~/.local/bin/run-highambench-formalization-pilot-14-r1 doctor --task-id H5-5
~/.local/bin/run-highambench-formalization-pilot-14-r1 run --task-id H5-5
~/.local/bin/run-highambench-formalization-pilot-14-r1 status --task-id H5-5
```

The controller owns ordering, prompt delivery, warm fork, metering, command
quiescence, freeze/hash, validation, dossier extraction, audit, repair feedback,
state transitions, and sealing. Do not manually create or edit run evidence.

Reissuing `run` is permitted only when the task index points to the same
nonterminal pair and the controller authenticates a safe boundary (before the
first turn or between sealed conditions). A submitted condition is never
cold-resumed without its live usage stream.

## Primary campaign

After the canary succeeds, and only under explicit campaign authorization, run
these frozen slots once each:

```bash
~/.local/bin/run-highambench-formalization-pilot-14-r1 run --task-id H5-5
~/.local/bin/run-highambench-formalization-pilot-14-r1 run --task-id H7-12
~/.local/bin/run-highambench-formalization-pilot-14-r1 run --task-id H10-7
~/.local/bin/run-highambench-formalization-pilot-14-r1 run --task-id H23-6
~/.local/bin/run-highambench-formalization-pilot-14-r1 evaluate-gate
```

Never substitute a task, rerun a slot, or weaken the gate after observing data.

## Candidate and retrieval checks

For every frozen attempt, require:

- exactly one final theorem named `HighamBenchCandidate.target`;
- zero `sorry`, `admit`, new axiom/constant, `opaque`, `unsafe`, `partial`,
  metaprogramming, extern, or compiler command;
- successful compilation of a fresh immutable copy and a trusted `#check`;
- raw/nonblank code lines, declarations, and imports recorded;
- in L, atlas queries and reached NumStability declarations/modules recorded;
- in N, zero treatment import/path/closure/trace evidence.

The atlas is a discovery surface, not a gold mapping. L should run the ranked,
bounded `/usr/bin/python3 /library-index/query.py <terms>` command, inspect only
plausible source locations, and confirm exact types with Lean. Whole-library
recursive scans are fallback.

## Audit checks

Every distinct semantic hash gets a fresh candidate audit. Require independent
blind, direct, and round-trip roles; one ordered record for every Dxxx
dependency in blind/direct outputs; S01-S16; both implication directions; and
fresh adjudication of every trigger. Auditors see the PDF, packet, and
pseudonymized dossier, never candidate provenance, proof, condition, attempt,
or uptake telemetry.

Final valid verdicts are only `faithful` and `unfaithful`. Full-domain genuine
strengthening may pass. Proper-subdomain or partial case-split coverage fails.
Feedback must be condition-neutral and must not reveal Lean/library names.

## Measurement and reporting

Charge each formalizer task/repair turn through process quiescence and candidate
freeze/hash. Exclude installation/scout, validation, dossier, audit, and
controller overhead while recording each separately. Preserve raw provider
usage plus task-local net-new tokens. Do not infer hidden reasoning.

For terminal reports include pair/run IDs, release/manifest/deployment hashes,
condition order and statuses, submission counts, active seconds, exact token
components, net-new tokens, raw/nonblank lines, declaration count, treatment
uptake/modules, atlas/source-search counts, audit usage/time, and authenticated
artifact paths.
