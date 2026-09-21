# Pilot-14 Titan deployment

Pilot 14 installs beside Pilot 13. It reuses Pilot 13's authenticated frozen
Lean/Mathlib/NumStability runtime, clean build record, and inherited warm scout
root. It does not rebuild NumStability and does not run a new scout.

## Install

Run from a clean checkout of `codex/pilot-14-retrieval-proof` (or the eventual
`formalization_benchmark` release branch):

```bash
python3 paper_bencmark/formalization_benchmark/tools/setup_titan.py \
  --pdf-source-dir /ABSOLUTE/PATH/TO/FROZEN/PDFS \
  --predecessor-deployment-root /hdd/alexgeorgantzas/highambench/deployment-pilot-13-r1 \
  --deployment-root /hdd/alexgeorgantzas/highambench/deployment-pilot-14-r1 \
  --launcher ~/.local/bin/run-highambench-formalization-pilot-14-r1
```

H00-00's synthetic PDF is embedded in the frozen release. The remaining 18 PDF
basenames must be present under `--pdf-source-dir` with the packet hashes.

Setup fails closed unless it can authenticate the exact Pilot-13 deployment,
manifest, build, warm root, full predecessor chain, Codex executable/host,
hardware envelope, treatment-free N runtime, and all PDFs. It then:

1. clones the clean release without Git metadata;
2. copies private auth/PDFs into mode-restricted deployment paths;
3. reuses the frozen toolchain, packages, source, OLean, and build record;
4. generates and hashes `/runtime/library-index` from frozen source;
5. copies and rebinds the one inherited warm root to Pilot 14;
6. runs provider-free compiler, sandbox, Codex, and real-fork preflights;
7. installs the digest-bound launcher and operator skill atomically.

## Qualification and canary

```bash
~/.local/bin/run-highambench-formalization-pilot-14-r1 verify-release
~/.local/bin/run-highambench-formalization-pilot-14-r1 doctor --task-id H00-00
~/.local/bin/run-highambench-formalization-pilot-14-r1 qualify-provider --task-id H00-00
~/.local/bin/run-highambench-formalization-pilot-14-r1 run --task-id H00-00
~/.local/bin/run-highambench-formalization-pilot-14-r1 status --task-id H00-00
```

Qualification is off-benchmark and one-shot. H00-00 is the official synthetic
infrastructure pair; it consumes only its own canary slot and is excluded from
scientific results.

## Primary experiment

After H00-00 completes faithfully with valid proof, audit, usage, and uptake
records, run exactly once each:

```bash
~/.local/bin/run-highambench-formalization-pilot-14-r1 run --task-id H5-5
~/.local/bin/run-highambench-formalization-pilot-14-r1 run --task-id H7-12
~/.local/bin/run-highambench-formalization-pilot-14-r1 run --task-id H10-7
~/.local/bin/run-highambench-formalization-pilot-14-r1 run --task-id H23-6
~/.local/bin/run-highambench-formalization-pilot-14-r1 evaluate-gate
```

Do not rerun a consumed task, rewrite an incident, or substitute another task
after observing results. A failed gate requires a separately frozen successor
pilot.
