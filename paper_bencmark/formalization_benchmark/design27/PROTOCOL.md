# Pilot 27: proof-required, full-library development canary

Status: prospective exploratory development, not held-out or confirmatory.
The three canary tasks were chosen after seeing Pilot 26 outcomes. Unfavorable
outcomes and all failed proof attempts remain part of the record. A change to
the inputs, task list, prompt, clock, or proof policy requires a new pilot ID;
never silently rerun a measured pair.

## Scientific question

Compare Mathlib-only N against the same environment plus the frozen
NumStability snapshot L. Primary outcome is net-new Lean lines in the final
kernel-checked, source-faithful statement *and proof*, when both conditions
complete one. Also report the faithful statement-only line comparison and all
proof failures; never condition on success without showing attrition. Direct
use of a relevant NumStability algorithm/error declaration is a separate
treatment-uptake requirement. Time and net-new tokens, including task-time
library search, are secondary outcomes. Search time is also broken out as a
descriptive diagnostic, not subtracted from the headline result or treated as
evidence of a hypothetical fine-tuned model's performance.

## Frozen materials and conditions

- Both conditions get the same hashed paper PDF, source packet, task
  clarification, common prompt, model (`gpt-6-sol`, high), four-statement
  submission limit, and cumulative five-hour task-active cap.
- L gets the complete read-only NumStability source/compiled snapshot and a
  condition-specific appendix encouraging use. N has Mathlib only. There is
  no task-specific automatic retriever, ranked declaration packet, or hidden
  target-specific guidance in either condition. Ordinary file search and Lean
  type probes are allowed, metered, and logged.
- L forks one task-neutral GPT-6 Sol high orientation conversation made
  once, before tasks are known to the scout. Its one-time time/tokens and
  inherited cached prefix are reported separately. The raw scout transcript
  is preserved and its hash is pinned. N starts fresh.
- Initial canary tasks and admission evidence are pinned in
  `CORPUS_CANARY.json` and `ADMISSION_CANARY.json`. The Pilot 26 outcome-aware
  selection is disclosed. The old private compile smoke probe is *not* the
  faithfulness evidence: a prior independently audited, source-faithful,
  compiled L candidate is. Neither private candidate nor its proof is given
  to a contestant.
- First pair runs alone and pauses for review. Remaining canary pairs use
  separate fixed 8-CPU/24-GiB lanes. Per-turn CPU/RAM peaks, hardware
  snapshots, prompt hashes, usage, candidate hashes, compiler output,
  semantic dossiers, and audit decisions are retained.

## Two-stage attempt

1. Each contestant writes a single theorem statement with only its target
   proof `sorry`. Every submission is frozen and hashed before off-clock
   compilation, proof-integrity validation, and fresh blinded faithfulness
   audit. Rejected submissions receive neutral mismatch feedback in the same
   conversation. The verdict is faithful or unfaithful; no partial-domain
   acceptance. A stronger bound must cover every source case.
2. Only after an audited faithful statement, the *same conversation* is asked
   to prove the exact frozen proposition. Proof turns are timed; validation
   happens off-clock. Up to four proof submissions and one cumulative
   one-hour proof-active cap apply, also subordinate to the five-hour total.
   Any changed statement/dependency semantic hash is rejected. A final proof
   requires compilation and no `sorry`, new axiom, unsafe/trust escape, or
   other integrity violation. Proof failures remain recorded.
3. Blind/direct/round-trip/adjudicator roles retain their frozen Pilot 26
   prompts and are metered separately from the contestant clock. Their
   candidate-specific audit artifacts and dependency records are preserved.

## Interpretation and next release

Pilot 27's three tasks are engineering canaries. A later 10–15-task campaign
requires a separately frozen corpus and admission record, including 2–4
genuinely hard but in-scope tasks. Source overlap must be verified before
measurement: the library must supply relevant building blocks, especially
an actual algorithm/error interface compatible with the paper's FP model,
without containing the target result. The admission gate uses private
compile-checked faithful skeletons; these are never delivered to formalizers.
Prior outcomes may guide exploratory selection but must be disclosed. Do not
claim confirmatory generalization from an outcome-selected corpus.
