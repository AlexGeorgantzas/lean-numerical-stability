# Pilot-15 architecture

Pilot 15 keeps all Pilot-14 and earlier evidence read-only and creates a new deployment,
manifest, registry namespace, run root, warm-root record, qualification, and
task slots.

```text
sealed Pilot-13 build + scout root
              |
              +--> deterministic declaration atlas (once, installation)
              |
hash-frozen PDF + neutral packet + identical task prompt
              |
       +------+------+
       |             |
   N: fresh       L: warm fork + NumStability + atlas
       |             |
       +--> complete Candidate.lean proof --> freeze/hash
                        |
             compile + integrity validation
                        |
              private semantic dossier
                        |
 blind translation + direct judge + round trip
                        |
             adjudicator when triggered
                        |
     faithful => terminal   unfaithful => same-chat repair
```

## Retrieval surface

`tools/library_atlas.py` deterministically indexes every named declaration in
the frozen source by module, file, line, signature, documentation, and combined
search text. Setup records the complete atlas tree manifest in `deployment.json`.
The L app-server sandbox mounts it read-only at `/library-index`; N has no atlas,
source, OLean, guide, warm state, or filesystem path to them. L's workspace
contains a protected byte copy of `GUIDE.md`; N's does not.

The atlas is intentionally not a task-to-declaration oracle. It replaces a
1.47-million-line recursive scan with a compact lexical lookup, after which the
formalizer uses a ranked, bounded top-N query before `show.py` returns one
exact declaration, a small source window, and nearby API signatures. The guide
then requires a minimal wrapper compile before paper-specific bridges. This
reduces broad source reading without making the atlas task-specific.

The usage meter accepts an exact repeated cumulative/last-usage notification
as an idempotent provider replay and records it separately. Any repeat that
changes either payload, any regression, or any raw/cumulative disagreement
still makes the turn unscoreable.

## Trust boundaries

- The release manifest hashes every controller, prompt, schema, packet, canary,
  and repository-level dependency.
- Titan setup authenticates Pilot 13 and its predecessor chain, reuses the
  frozen runtime/build/warm state, and atomically publishes a distinct Pilot-15
  deployment.
- Bubblewrap removes network access and exposes only condition-appropriate
  read-only mounts. Generated commands run inside a subordinate cgroup.
- Source PDF, packet, environment note, and L guide are protected read-only
  workspace paths. `Candidate.lean` is the only submission file.
- Each candidate is copied to a new validation workspace. The semantic
  extractor follows the target type but excludes the proof.
- Private provenance maps and uptake telemetry remain controller-side. Auditors
  receive pseudonymized semantic dossiers and cannot see condition or attempt.
- Per-task and account-global locks enforce one official pair per pilot/task.

## Principal components

| Component | Responsibility |
| --- | --- |
| `tools/setup_titan.py` | Authenticate Pilot 13, reuse runtime/build/scout, build the atlas, run provider-free canaries, and publish atomically. |
| `tools/library_atlas.py` | Build the deterministic task-neutral declaration index. |
| `tools/pair_controller.py` | Stage N/L, fork L, meter turns, freeze submissions, validate, audit, repair, record uptake, and seal pairs. |
| `tools/formalization_validator.py` | Reject holes/trust escapes, require one final target theorem, compile a fresh copy, and record source metrics. |
| `tools/prepare_candidate_audit.py` | Extract complete target-type dependency semantics and pseudonymize treatment provenance. |
| `tools/audit_controller.py` | Run fresh blind/direct/round-trip roles and conditional binary adjudication. |
| `tools/evaluation_gate.py` | Evaluate the frozen four-task time/token/faithfulness criterion. |
| `tools/run_benchmark.py` | Expose verify, doctor, qualification, run, status, and gate commands. |

## Evidence layout

```text
runs/
  warm-roots/<manifest-payload>/
  qualifications/<manifest-file-sha>/
  pairs/<run-id>/
    admission.json
    pair_state.json
    pair_report.json
    conditions/{N,L}/
      staging.json
      condition_state.json
      attempts/NN/
        Candidate.lean
        validation.json
        library_uptake.json
        dossier/{blind_semantic_dossier.json,private_semantic_manifest.json}
        formalizer/{prompt.md,events.jsonl,turn.json,last_message.txt,...}
    audits/<semantic-sha>/
  index/<task-id>.json
```

The pair report includes condition summaries and final uptake metrics. H00-00 is
tagged by the frozen evaluation policy as non-scientific.
