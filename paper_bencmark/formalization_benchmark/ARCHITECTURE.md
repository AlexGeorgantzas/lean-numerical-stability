# Formalization benchmark architecture

## Operator path

```text
"Run benchmark for P01-T2"
        |
        v
installed run-highambench-experiments skill
        |
        +--> verify-release (complete frozen-file closure)
        +--> Titan doctor (PDF/runtime/executable/hardware identities)
        |
        v
transient systemd user service: fixed 8 CPUs / 32 GiB / 512 tasks / no swap
        |
        +--> trusted-control child: 8-GiB memory.low reservation
        `--> generated-command child: 24 GiB / 384 tasks / no swap
        |
        v
one authenticated pair controller
        |
        +--> condition N: paper + packet + Lean/Mathlib
        `--> condition L: identical base + frozen NumStability + L appendix
```

The pair controller pre-stages and byte-compares both condition inputs before
the first provider call. It then follows the condition order frozen per task in
`config.json`. A task index permits one official pair only. Reissuing the same
run command returns a terminal pair or continues before the first turn or
between sealed conditions. An interruption after a condition has submitted is
not cold-resumed, because that would lose its exact raw-event stream; it fails
closed as an incident. A deployment-wide lock admits only one pilot pair at a
time, preventing concurrent pilot tasks from contending for Titan's fixed CPU
and memory allocation.

## Per-condition loop

```text
persistent formalizer conversation
        |
        | model-active clock ON; formalizer response tokens metered
        v
Candidate.lean produced --> clean/list background terminals --> workspace bounded
        | model-active interval OFF
        v
ordered telemetry settle + trusted bookkeeping (off-clock)
        |
        v
stable Candidate.lean copy + SHA-256 (separately timed and charged)
        | all contestant charging OFF
        v
no-network Lean compilation + integrity checks
        |
        v
pseudonymized semantic dependency dossier
        |
        v
fresh blind translator + direct judge + round-trip judge
        |
        +--> faithful: accept and stop
        +--> unclear: unscored audit-system incident
        `--> unfaithful: fixed neutral feedback
                              |
                              `--> same conversation; next turn restarts metering
```

There are at most four immutable submissions: one initial submission and three
repairs. One app-server process remains alive through the condition, including
the validation/audit pauses, so repairs use the same conversation and raw
per-response metering remains enabled. The model-active interval through
background-terminal quiescence and the separately timed candidate copy/hash are
charged. Ordered telemetry settling, trusted bookkeeping, validation, and
auditing are outside contestant measurement. Auditor usage is retained in a
separate overhead ledger.

## Isolation boundary

Each formalizer gets a fresh Codex state and workspace inside a minimal
Bubblewrap filesystem. The provider control process may reach the model
provider; model-selected shell descendants are forced through the frozen
Landlock/seccomp launcher, cannot read `/proc` or the Codex control tree, and
cannot create or use sockets. Security-sensitive Codex configuration generated
during provider-free startup is hash-sealed, then mounted read-only for the
complete measured app-server session. Refreshable authentication remains only
inside the private tmpfs-backed control state used by that live app-server; it
is inaccessible to generated commands, excluded from the control manifest, and
redacted from persisted artifacts. Refresh rotations are synchronized under a
lock to the deployment-private auth store, and the tmpfs copy is destroyed when
the driver closes. Host `/usr/local`, home trees, and documentation trees are
absent; the narrow common system-runtime mounts are treatment-scanned, hashed,
and rechecked by the doctor. The N filesystem has no NumStability source,
objects, cache, index, documentation, Git history, or prior outputs. The L
filesystem adds only the frozen read-only source and compiled tree. Its L-only
prompt appendix points to `/library/NumStability` and
`/library/NumStability.lean`, notes that compiled declarations are on
`LEAN_PATH`, and gives concrete `find`, `rg`, and `import NumStability`
discovery/import examples.

The waited, piped transient systemd user service applies the frozen eight-CPU
affinity and limits the whole benchmark process tree to 32 GiB, 512 tasks, and
zero swap. A service-wide syscall filter prevents the controller, Codex, build
tools, auditors, and all descendants from changing their inherited CPU
affinity; each strict snapshot proves the denial with a no-op syscall canary.
It delegates separate cgroup-v2 children for the trusted controller and
model-generated commands. The generated-command seccomp policy repeats the
affinity denial. Commands are migrated
into a 24-GiB, 384-task, zero-swap child with CPU weight 100; the control child
uses CPU weight 10000 and an 8-GiB `memory.low` reservation. The controller
checks resource identities and command-child limit events at every attempt.
Workspace traversal is capped at 10,000 entries and 1 GiB total, with a 256-MiB
per-written-file limit. Protocol lines, event traces, event counts, and stderr
archives are also bounded; a limit breach is a recorded fail-closed outcome.

Untrusted `Candidate.lean` is never compiled directly on the host. Validation
and semantic extraction run in a separate no-network Bubblewrap namespace that
mounts only a fresh candidate scratch directory, the frozen Lean toolchain,
the frozen package closure, and—only for L—the frozen library objects.

## Trusted scripts

| Script | Responsibility |
| --- | --- |
| `tools/setup_titan.py` | Build and hash the private Titan deployment in a resumable, atomically published transaction without paid model calls. |
| `tools/measure_library_build.py` | Clean and measure the full NumStability build under the fixed outer resource envelope, retaining authenticated build output and resource evidence. |
| `tools/runtime_canary.py` | Prove the N/L import boundary with provider-free sandboxed compilations. |
| `tools/titan_envelope.py` | Enter the exact CPU, RAM, and swap cgroup. |
| `tools/run_benchmark.py` | Expose `verify-release`, `doctor`, `run`, and `status`. |
| `tools/pair_controller.py` | Own pair uniqueness, ordering, state transitions, clocks, freezing, and repair continuation. |
| `tools/codex_driver.py` | Own fresh/persistent Codex conversations, tool isolation, raw events, and provider usage. |
| `tools/formalization_validator.py` | Enforce the one-root/one-`sorry` source contract. |
| `tools/lean_sandbox.py` | Compile untrusted Lean in the no-network filesystem. |
| `tools/prepare_candidate_audit.py` | Extract and pseudonymize the generated/NumStability recursive closure and frozen Lean/Mathlib frontier. |
| `tools/audit_controller.py` | Run fresh condition-blind audit roles and emit neutral feedback. |
| `tools/freeze_manifest.py` | Release-authoring only: regenerate the frozen manifest before commit. |

The historical `paper_bencmark/highambench/tools/runner.py` and
`run_matrix.py` are not part of this architecture.

## Artifact layout

```text
runtime/library/
  snapshot.json
  source/...
  olean/...
  build/
    build-record.json
    build-output.log
    gnu-time.txt
runs/
  index/P01-T2.json
  pairs/<run-id>/
    admission.json
    pair_staging.json
    pair_state.json
    pair_report.json
    conditions/N|L/
      prompt.txt
      condition_state.json
      codex-state/
      workspace/Candidate.lean
      attempts/01..04/
        Candidate.lean
        hardware.json
        hardware_after.json
        formalizer/{prompt.md,events.jsonl,last_message.txt,turn.json,network_violations.bin}
        validation.json
        dossier/{blind_semantic_dossier.json,private_semantic_manifest.json}
        repair_feedback.json
    audits/<semantic-sha256>/
      roles/... fresh auditor transcripts and usage
      decision.json
```

The library build record is provisioning evidence and is never added to either
condition's contestant clock. It identifies the clean project build after a
workspace clean, off-clock dependency-cache rehydration, and proof that the
root build tree remains empty, together with the exact toolchain and source commits,
all dependency commits and compiled OLean cache digests, clean source and
project-configuration digests before and after, and the complete sanitized
subprocess environment. It also records the enforced
eight-CPU/32-GiB/512-task/no-swap service, monotonic and UTC time, GNU `time`
resource metrics, strict cgroup counter deltas, source/object size counts, and
hashes of the retained raw outputs. The library snapshot and deployment record
bind the complete build-evidence tree so a later doctor detects any change.

The records contain exact prompt and candidate hashes, source line counts,
observable messages/reasoning summaries, tool events and commands, exact
deduplicated provider input/cached/cache-write/output/reasoning/total token
counts, active, excluded, and end-to-end wall durations, executable/runtime
identities, and start/end hardware observations. Terminal condition hashes bind
the attempt telemetry into the pair report. Hidden chain-of-thought is neither
available nor requested; it is never represented as a benchmark artifact.
