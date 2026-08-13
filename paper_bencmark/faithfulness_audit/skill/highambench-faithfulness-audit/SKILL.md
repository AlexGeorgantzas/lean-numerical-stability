---
name: highambench-faithfulness-audit
description: Run a reproducible, multi-agent faithfulness audit of HighamBench Lean targets against reference-paper statements. Use when the user asks to audit, check, verify, review, or assess paper faithfulness for one task such as P11-T1 or a paper batch such as P03, including blind translation, imported-definition coverage, paper-level source extraction, direct and round-trip judgments, hash-verified dependency reuse, conditional adjudication, and per-task artifacts.
---

# Run a HighamBench Faithfulness Audit

Audit propositions only. Do not edit targets, shared Lean files, task metadata,
contexts, PDFs, benchmark snapshots, or proofs.

## Load the protocol

Work in the `lean-fp-analysis` repository containing
`paper_bencmark/highambench/`. The spelling `paper_bencmark` is intentional.

Read before running roles:

- `paper_bencmark/faithfulness_audit/METHODOLOGY.md`;
- all role prompts under `paper_bencmark/faithfulness_audit/prompts/`;
- all role schemas under `paper_bencmark/faithfulness_audit/schemas/`.

The methodology is canonical. This skill supplies orchestration.

Normalize task references such as `P11 T1`, `P11/T1`, or `P11-T1` to
`P11-T1`. Use paper-batch mode for a request covering T1, T2, and T3 from one
paper. Use single-task mode for an isolated task.

Do not create user-visible Codex tasks. Use internal agents. The audit workflow
authorizes these subagents.

## Preserve existing work

Inspect every requested `faithfulness/manifest.json` first. Reuse a valid
`prepared` bundle and validate existing partial role outputs before continuing.
For a `completed` audit, report the existing result unless the user explicitly
requests a fresh run.

Never use `--force` merely to simplify orchestration. Use it only for an
explicit fresh run or an intentional input invalidation. Preparation archives
old artifacts, but avoid invalidating them unnecessarily.

Preparation must compile untouched targets and writes only under each task's
`faithfulness/` folder.

## Enforce agent isolation

For every role, call `multi_agent_v1__spawn_agent` with `fork_context: false`.
Do not override model or reasoning effort. Do not use `send_input` to repair a
role. Retry malformed or invalid output with a new fresh agent. Close completed
or failed agents promptly.

Only the orchestrator writes files. Agents return bare JSON in final messages
and never modify the workspace. Parse and validate every output before another
role consumes it.

### Blind rule

A blind translator receives inline only:

1. `prompts/blind_translation.md`;
2. `schemas/blind_translation.schema.json`;
3. the manifest hash for `inputs/blind_review_packet.md`;
4. the complete text of that packet.

Explicitly prohibit tool calls and filesystem inspection. Do not pass a skill,
path, task ID, paper, theorem name, target source, context, conversation history,
or prior output. `fork_context: false` is necessary but does not itself remove
filesystem capability, so the no-tool instruction is part of validity.

## Run a paper batch

Use this path when all three tasks of one paper are pending.

### 1. Prepare T1, T2, and T3

```bash
python3 paper_bencmark/faithfulness_audit/scripts/prepare_paper_audit.py P03
```

This compiles the three targets concurrently and adds one hash-identical
`paper_source_locator.json` to every task. Validate all three prepared bundles.

### 2. Run paper extraction and blind translations concurrently

Spawn four fresh agents before waiting:

- one paper source-contract agent;
- one blind translator for each of T1, T2, and T3.

The paper source agent receives the paper-level prompt and schema,
`paper_source_locator.json` plus its SHA-256, and the absolute reference-PDF
path. Permit inspection only of that PDF and surrounding pages needed for
definitions and cross-references. Do not supply Lean, dossiers, context, or task
paraphrases.

Each blind agent follows the blind rule and remains independent of the other
three roles.

After validating the paper-agent JSON shape, write it to a temporary local path
and split it:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/split_paper_source_contract.py \
  /path/to/paper_source_contract.json
```

The splitter writes and validates a hash-bound paper contract plus each task's
`source_contract.json`. Write each blind result to its task-local
`agent_outputs/blind_translation.json`, then validate it:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/validate_agent_output.py \
  P03-T1 blind-translation
```

Repeat validation for T2 and T3. Never show source output to a blind agent.

### 3. Run T1 direct and all round-trip judges concurrently

Spawn four fresh agents:

- the T1 direct judge;
- T1, T2, and T3 round-trip judges.

The T1 direct judge receives the direct prompt/schema, PDF source packet,
task-local source contract, manifest semantic checks, and complete
`inputs/direct_review_packet.md`. Require every `Dxxx` and `Sxx` in order.

Each round-trip judge receives only its prompt/schema, PDF source packet,
task-local source contract, blind translation plus hash, and semantic-check
list. Do not supply Lean, dossiers, dependency inventory, context, or direct
judgment.

Write and validate all four outputs immediately.

### 4. Compact T2 and T3 direct packets

Only after P03-T1's direct output validates, run:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/apply_dependency_reuse.py \
  P03-T2 --source P03-T1 --role direct
python3 paper_bencmark/faithfulness_audit/scripts/apply_dependency_reuse.py \
  P03-T3 --source P03-T1 --role direct
```

The command rewrites no blind input. It includes only exact semantic-hash
matches whose source dependency status is `pass` or `not-applicable`.

For a full dependency section, a direct output includes `interpretation`. For a
reuse section, it includes the exact `reuse_sha256` instead. In both cases, the
new judge must independently write `effect_on_target`, `paper_match`, and
`status`. Reuse never supplies those task-specific decisions.

### 5. Run T2 and T3 direct judges concurrently

Spawn both fresh judges with their now-final direct review packets. Write and
validate each `direct_judge.json`.

## Run one task

For an isolated task, prepare and validate:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/prepare_audit.py P11-T1
python3 paper_bencmark/faithfulness_audit/scripts/validate_audit.py \
  P11-T1 --phase prepared
```

Phase one runs a fresh single-task source-contract agent and blind translator in
parallel. The source role receives `source_locator.json`, source prompt/schema,
and the PDF. The blind role follows the blind rule. Validate both outputs.

Phase two runs fresh direct and round-trip judges in parallel. Supply the direct
judge `direct_review_packet.md`, not the larger complete dossier. Supply the
round-trip judge no Lean material. Validate both outputs.

## Adjudicate only when triggered

For every task, run:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/finalize_audit.py \
  P03-T1 --check-adjudication
```

Exit `0` means no adjudicator is required. Exit `3` means the printed reasons
require one and is not a command failure. Source or translation ambiguity alone
does not trigger adjudication; an unresolved judge status, request,
`undetermined` result, or classification disagreement does.

When required, spawn one fresh adjudicator. Inline the adjudicator prompt and
schema, PDF source packet, complete direct and blind dossiers, any reuse records,
all four outputs, and exact trigger reasons. Require primary-evidence resolution
for every reason. Write and validate `agent_outputs/adjudicator.json`.

Independent task adjudicators may run concurrently. Never spawn one when the
check reports no trigger.

## Finalize and verify

For each task:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/finalize_audit.py P03-T1
python3 paper_bencmark/faithfulness_audit/scripts/validate_audit.py \
  P03-T1 --phase complete
```

Sanity-check `decision.json` and `report.md`:

- every dependency and semantic ID occurs exactly once;
- reused records carry the manifest-bound hash;
- implication verdicts imply the recorded classification;
- `accepted` is true only for `faithful-equivalent` or `faithful-stronger`;
- stronger means genuine nonvacuous strength, not restricted applicability;
- claims use paper and declaration evidence;
- all current hashes match.

When the user requires one commit per task, finalize, validate, stage only that
task's faithfulness artifacts, commit, and push in T1, T2, T3 order. Agents for
later tasks may already have run concurrently; commits remain task-local and
ordered. Never stage unrelated dirty files.

Report each classification, acceptance, consequential findings, and absolute
result-folder path. State that no benchmark input changed. Do not commit or push
unless the user requested it.
