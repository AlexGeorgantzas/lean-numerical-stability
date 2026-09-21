# Formalization benchmark architecture

Pilot-12 is a side-by-side warm-start successor. Earlier deployments and
results are read-only provenance, not Pilot-12 observations. The direct
predecessor is Pilot-11. Its task-neutral scout and frozen build are valid and
reused unchanged; its H22-11 pair is sealed as a pre-turn controller incident.
Pilot-10's failed scout and Pilot-9's cold-start H22-11 pair also remain sealed.

## Operator path

```text
"Run benchmark for H22-11"
        |
        v
installed run-highambench-experiments skill
        |
        +--> verify frozen release closure
        +--> Titan doctor: PDFs/runtime/build/hardware
        +--> one-shot off-benchmark provider/schema/tool qualification
        |
        v
8 CPUs / 32 GiB / 512 tasks / no swap
        |
        +--> trusted control child with 8-GiB memory.low
        `--> generated-command child: 24 GiB / 384 tasks / no swap
        |
        v
one campaign-level scout inherited from Pilot-11 (no new scout turn)
        |
        `--> frozen NumStability orientation root
                    |
                    `--> independent thread/fork for each L task
        |
        v
one pair controller
        |
        +--> N: PDF + packet + Lean/Mathlib
        `--> L: identical task prompt + frozen NumStability + forked familiarity
```

The controller pre-stages and compares both condition inputs before the first
contestant call. An account-global registry reserves each
`(formalization-benchmark-pilot-12, task_id)` once. A shared campaign lock and
predecessor locks prevent concurrent measured use of Titan. Reissuing a command
returns the terminal pair or continues only at a safe boundary between sealed
conditions.

## Per-condition loop

```text
persistent formalizer conversation
        |
        | contestant time ON; provider usage metered
        v
Candidate.lean -> terminal cleanup -> bounded workspace
        |
        | model interval OFF
        v
telemetry settle and bookkeeping (off-clock)
        |
        v
stable Candidate.lean copy/hash (timed and charged)
        |
        | contestant charging OFF
        v
sandboxed compilation and integrity checks
        |
        v
recursive pseudonymized dependency dossier
        |
        +--> fresh blind translator: every Dxxx dependency
        +--> fresh direct judge: every Dxxx + S01--S16 + two implications
        `--> fresh round-trip judge: S01--S16 + two implications
                    |
                    +--> conclusive agreement: derive binary verdict
                    `--> trigger: fresh evidence-based adjudicator
                                  |
                                  +--> faithful: accept
                                  `--> unfaithful: neutral repair feedback
                                                     |
                                                     `--> same conversation
```

At most four immutable submissions are permitted. Compilation and auditing are
off-clock. Auditor usage is stored in a separate overhead ledger. The same
formalizer app-server remains alive so a repair continues the exact conversation
and exact raw-response metering.

## Audit data flow

`prepare_candidate_audit.py` asks Lean for the elaborated root type and its
dependency graph. Candidate-local and reached NumStability declarations are
followed recursively through types and bodies. Lean/Mathlib declarations form a
one-level external semantic frontier. Stable `Dxxx` IDs and semantic hashes
are assigned before local names and module provenance are pseudonymized. The
ordered `Dxxx` ID is the dependency identity. Each role must preserve every ID
and its order, while its required `name` field is a descriptive semantic label.

The blind role sees only this dossier. The direct role sees the PDF, source
packet, and dossier. The round-trip role sees the PDF, packet, and blind
translation but no Lean. The adjudicator sees all evidence only when triggered.
No role receives the benchmark condition or submission number.

Judges classify explicit implication directions as equivalent, stronger,
weaker, different, or provisionally undetermined. The final controller outcome
is binary. Partial source-domain coverage is unfaithful even if split across
multiple declarations.

## Isolation

N has no NumStability sources, objects, caches, names, documentation, Git
history, or prior artifacts. L adds the frozen source and compiled trees and
forks the single task-neutral scout history. The library encouragement and
practical discovery guidance occur in that scout history, not in the task
prompt. Each task gets a private copy of the authenticated root checkpoint and
a new child thread, so L tasks cannot contaminate one another.

N has fresh Codex state. Each L child has a private copy of the same frozen
scout checkpoint and a fresh workspace inside a minimal Bubblewrap filesystem.
The exact same-package Code Mode host is hash-pinned and
mounted read-only. Model-selected commands pass through a frozen offline
Landlock/seccomp launcher and a bounded command cgroup. Untrusted Lean is
compiled only in a separate no-network namespace with a fresh candidate
scratch directory and frozen dependencies.

Agent delegation is disabled globally and per thread. Collaboration events,
foreign-thread activity, missing Code Mode, malformed structured output, or
incomplete telemetry fail closed as infrastructure incidents.

## Trusted scripts

| Script | Responsibility |
| --- | --- |
| `tools/setup_titan.py` | Authenticate Pilot-11 reuse, run a provider-free real-fork canary, and atomically install Pilot-12. |
| `tools/measure_library_build.py` | Record the clean full NumStability build and resources. |
| `tools/runtime_canary.py` | Prove the N/L import boundary without provider calls. |
| `tools/provider_capability_canary.py` | Exercise exact models, schemas, tools, and isolation off-benchmark. |
| `tools/titan_envelope.py` | Enter the fixed systemd/cgroup hardware envelope. |
| `tools/run_benchmark.py` | Expose verify, doctor, qualify, prepare-warm-root, run, and status. |
| `tools/pair_controller.py` | Own uniqueness, ordering, state, clocks, freeze, and repair. |
| `tools/codex_driver.py` | Own persistent/fresh conversations and raw usage. |
| `tools/formalization_validator.py` | Enforce the one-root/one-hole contract. |
| `tools/lean_sandbox.py` | Compile untrusted Lean without network access. |
| `tools/prepare_candidate_audit.py` | Build and pseudonymize the semantic closure. |
| `tools/audit_controller.py` | Validate deep audit records, adjudicate, and render feedback. |
| `tools/freeze_manifest.py` | Author the release manifest; never called during scoring. |

## Artifact layout

```text
runtime/library/
  snapshot.json
  source/
  olean/
  build/
    build-record.json
    build-output.log
    gnu-time.txt
runs/
  qualifications/<manifest-sha256>/
  warm-roots/<manifest-payload-sha256>/
    warm-root.json
    checkpoint/
    scout-artifacts/
  index/H22-11.json
  pairs/<run-id>/
    admission.json
    pair_state.json
    pair_report.json
    conditions/N|L/
      prompt.txt
      condition_state.json
      workspace/Candidate.lean
      attempts/01..04/
        Candidate.lean
        hardware.json
        formalizer/
        validation.json
        dossier/
        repair_feedback.json
    audits/<semantic-sha256>/
      blind_translation.json
      direct_judgment.json
      roundtrip_judgment.json
      adjudication.json             # conditional
      decision.json
~/.local/share/highambench-formalization-registry/
  locks/campaign.lock
  index/formalization-benchmark-pilot-12/H22-11.json
```

Records bind prompts, candidates, source packets, semantic dossiers, role
outputs, exact token fields, charged/excluded timing, hardware, executables,
build evidence, and terminal hashes. Hidden chain-of-thought is not represented.
