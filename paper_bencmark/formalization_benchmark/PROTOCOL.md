# Pilot-14 protocol

Pilot 14 is a new frozen release. Pilot 13 and every earlier release, build,
qualification, run, incident, and audit remain immutable predecessor evidence.

## Frozen identity

- Pilot: `formalization-benchmark-pilot-14`.
- Formalizer: `gpt-5.6-sol`, `xhigh`.
- Auditors: `gpt-6-astra`, `high`.
- Lean: `leanprover/lean4:v4.29.0-rc3`.
- Mathlib: `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.
- NumStability: `45813a95dacf577461bae13f033af0dbc985a225`.
- Hardware: eight logical CPUs, 32 GiB RAM, 512-task outer ceiling, no
  swap; generated commands receive 24 GiB and 384 tasks.
- One pair per task, four submissions per condition, five cumulative
  contestant-active hours, no token cap.

The existing clean NumStability build and task-neutral warm root are reused by
hash. Installation generates only a deterministic declaration atlas; it does
not call `lake build` and does not run another scouting model turn.

## Input and treatment

Both conditions receive byte-identical hash-frozen source PDFs, neutral task
packets, and task prompts. The PDF is authoritative. Packets locate and
disambiguate the selected result but contain no Lean target, proof plan, or
library declaration name.

N sees only Lean and Mathlib and begins from a fresh conversation. L additionally
sees the frozen NumStability source/OLean closure, forks the single inherited
task-neutral scout conversation, and receives:

- `/library-index/declarations.jsonl`, mapping declaration names to modules,
  source lines, compact signatures, documentation, and searchable text;
- `/library-index/modules.tsv` and `atlas.json`;
- a protected `LIBRARY_GUIDE.md` prescribing atlas-first, reuse-first discovery.

The task prompt remains byte-identical. Treatment awareness is carried by L's
frozen prior conversation and environment guide. The atlas is task-neutral and
contains no source-packet or gold-target mapping.

## Candidate contract

`Candidate.lean` is the only writable submission. It must contain exactly one
final theorem named `HighamBenchCandidate.target`, formalizing the exact source
result, with a complete kernel-checked proof. All helpers precede the target.
No proof holes, new unchecked assumptions, opaque/unsafe escapes,
metaprogramming, or interactive compiler commands are permitted.

The controller freezes and hashes each submission before stopping the charged
boundary. It then validates a fresh immutable copy and checks the root theorem.
Compilation and integrity work are excluded from contestant measurements. A
compilation or integrity failure receives condition-neutral feedback and, if a
submission remains, resumes the same formalizer conversation.

## Faithfulness loop

Every distinct validated target type receives a fresh candidate audit. Audit
roles are fresh, stateless, independent of the formalizer, condition-blind, and
attempt-blind. The candidate proof is excluded from the semantic dossier; the
auditors judge the target type and every reached generated/treatment-library
dependency.

The audit retains the paper method's depth:

1. Blind translation returns one record for every dependency.
2. The direct judge returns one record for every dependency.
3. Both complete the mandatory S01-S16 semantic checklist and explicitly judge
   source-to-candidate and candidate-to-source implication.
4. The round-trip judge independently reconstructs the mathematical claim.
5. Any conflict, missing coverage, or substantive uncertainty triggers a fresh
   adjudicator, which must resolve to exactly `faithful` or `unfaithful`.

An independently generated source-contract call is omitted because the frozen
source packet supplies the stable paper-side contract; this omission is part of
the protocol. Explicit two-direction judgments remain mandatory.

A genuine strengthening may be faithful when it still establishes the complete
paper claim on the full source domain. Multiple declarations covering only a
proper subset of that domain are unfaithful; the method paper's partial
case-split score exception is not used. Feedback contains only the missing
paper requirement and candidate mismatch—never gold Lean, proof code, condition,
attempt number, or NumStability names.

## Measurement and telemetry

Charged time starts when the task turn begins and stops after model completion,
background-command quiescence, and candidate freeze/hash. It resumes only for a
repair turn. PDF staging, validation, dossier extraction, audits, and controller
work are measured separately and excluded.

Raw exact provider usage is retained. The primary token measure is task-local
net-new tokens (uncached input plus output); inherited scout/cache tokens are
not charged. Every attempt also records raw lines, nonblank code lines,
declarations, imports, reached NumStability declarations/modules, and
atlas/source-search activity.

Private treatment uptake is never supplied to auditors. Hidden chain-of-thought
is neither requested nor available; provider-visible messages, tool calls,
usage events, and final responses are retained instead.

## Canary and scientific gate

H00-00 exercises the complete N/L, proof, audit, telemetry, and sealing path but
is synthetic and excluded from results. The scientific set is frozen as H5-5,
H7-12, H10-7, and H23-6. Pilot 14 passes its predeclared effect gate only if:

- all four pairs complete without incidents and both conditions are faithful;
- L is faster on at least three pairs;
- median active-time reduction is at least 20%; and
- median net-new-token reduction is at least 20%.

Failure mints a successor pilot with a changed, predeclared design. It never
authorizes rerunning a consumed Pilot-14 slot or selecting tasks after results.
