---
name: highambench-faithfulness-audit
description: Run a reproducible, multi-agent faithfulness audit of a HighamBench Lean target against its reference-paper statement. Use when the user asks to audit, check, verify, review, or assess the paper faithfulness of a task such as P11-T1, including blind target translation, detailed imported-definition coverage, direct and round-trip judgments, conditional adjudication, and per-task audit artifacts.
---

# Run a HighamBench Faithfulness Audit

Audit the proposition only. Do not edit the target, shared Lean files, task
metadata, context, reference PDF, benchmark snapshots, or proofs.

## Locate the canonical protocol

Work from the `lean-fp-analysis` repository containing
`paper_bencmark/highambench/`. The existing directory is intentionally spelled
`paper_bencmark`; do not create a parallel `paper_benchmark` directory.

Read these files before running agents:

- `paper_bencmark/faithfulness_audit/METHODOLOGY.md`
- all five role prompts under `paper_bencmark/faithfulness_audit/prompts/`
- the corresponding JSON schemas under
  `paper_bencmark/faithfulness_audit/schemas/`

Treat the methodology as canonical. The installed skill is orchestration glue,
while the repository owns the reproducible method.

## Interpret the request

Normalize a task reference such as `P11 T1`, `P11/T1`, or `P11-T1` to
`P11-T1`. Audit one task per requested audit unless the user explicitly asks for
a batch.

Do not create user-visible Codex tasks. Use internal multi-agent tools. The user
has explicitly authorized the audit workflow's subagents.

## Prepare the inputs

If the task has no `faithfulness/manifest.json`, run from the repository root:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/prepare_audit.py P11-T1
python3 paper_bencmark/faithfulness_audit/scripts/validate_audit.py P11-T1 --phase prepared
```

If a manifest already exists, inspect its status and run the prepared validator
instead of calling preparation again. Reuse a valid `prepared` bundle. For a
partial run, validate every existing agent output before continuing; do not
silently mix valid and invalid artifacts. For a `completed` audit, report the
existing result unless the user explicitly requests a fresh independent run.

Do not use `--force` if completed or partial results exist. Explain the existing
state and inspect it first. Use `--force` only when the user requests a fresh run
or when current inputs intentionally invalidate prior results.

Preparation must compile the untouched target and succeed. It writes only under
the task's `faithfulness/` result folder.

## Enforce fresh-agent isolation

For every role, call `multi_agent_v1__spawn_agent` with `fork_context: false`.
Do not override the model or reasoning effort. Do not reuse an agent with
`send_input`; a malformed or incomplete answer gets a newly spawned retry.
Close every completed or failed agent promptly because open completed agents
consume concurrency.

Only the orchestrator writes files. Agents return JSON in their final messages
and must not modify the workspace.

### Blind-agent rule

The blind translator's message must inline only:

1. `prompts/blind_translation.md`;
2. `schemas/blind_translation.schema.json`;
3. the blind dossier SHA-256 from the manifest;
4. the complete `inputs/blind_dossier.md` text.

Explicitly prohibit all tool calls and filesystem inspection. Do not pass a
skill item, local path, task ID, paper path, theorem name, source text,
conversation history, or any prior output. `fork_context: false` is mandatory
but does not itself remove filesystem capability, so the no-tool condition is
part of run validity.

## Run phase one in parallel

Spawn both fresh agents before waiting.

### Source-contract agent

Inline the source-contract prompt, its schema, and `source_locator.json`. Supply
the reference PDF's absolute path and page anchors from the locator. Permit the
agent to inspect only the PDF and surrounding pages needed to resolve definitions
and cross-references. Do not supply the target, dossiers, context, or task
paraphrases.

### Blind-translation agent

Use the blind-agent rule above.

Wait for both agents. Require bare JSON with no Markdown fence. Parse it before
writing:

```text
faithfulness/agent_outputs/source_contract.json
faithfulness/agent_outputs/blind_translation.json
```

If parsing or required coverage fails, close that agent and retry the role with
a new fresh agent. Never show one phase-one agent the other's output.

Validate both files immediately:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/validate_agent_output.py P11-T1 source-contract
python3 paper_bencmark/faithfulness_audit/scripts/validate_agent_output.py P11-T1 blind-translation
```

## Run phase two in parallel

Spawn both judges fresh before waiting.

### Direct judge

Inline:

- the direct-judge prompt and schema;
- `source_locator.json` and the exact PDF path/pages;
- `source_contract.json`;
- `manifest.json`;
- the complete `inputs/declaration_dossier.md`.

Require one dependency record for every manifest `Dxxx` ID and one semantic
record for every `Sxx` ID. The judge must inspect the original source and every
imported semantic dependency rather than trusting names or the source contract.

### Round-trip judge

Inline:

- the round-trip prompt and schema;
- `source_locator.json` and the exact PDF path/pages;
- `source_contract.json`;
- `blind_translation.json` and its SHA-256;
- only the manifest's `semantic_checks` list.

Do not supply Lean, either dossier, dependency inventory, context, task
paraphrases, or direct judgment.

Write valid bare JSON to:

```text
faithfulness/agent_outputs/direct_judge.json
faithfulness/agent_outputs/roundtrip_judge.json
```

Validate both files immediately:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/validate_agent_output.py P11-T1 direct-judge
python3 paper_bencmark/faithfulness_audit/scripts/validate_agent_output.py P11-T1 roundtrip-judge
```

## Decide whether to adjudicate

Run:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/finalize_audit.py P11-T1 --check-adjudication
```

Exit code `0` means no adjudicator is required. Exit code `3` means the printed
reasons require one; it is not a command failure.

When required, spawn one fresh adjudicator with `fork_context: false`. Inline the
adjudicator prompt and schema, source locator and PDF, both dossiers, all four
agent outputs, and the printed trigger reasons. Require primary-evidence
resolution of each reason. Write its bare JSON to:

```text
faithfulness/agent_outputs/adjudicator.json
```

Validate it immediately with `validate_agent_output.py P11-T1 adjudicator`.

Do not spawn an adjudicator when the check says none is needed.

## Finalize and verify

Run:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/finalize_audit.py P11-T1
python3 paper_bencmark/faithfulness_audit/scripts/validate_audit.py P11-T1 --phase complete
```

Read `decision.json` and `report.md`. Sanity-check that:

- all dependency and semantic IDs are covered exactly once;
- implication verdicts agree with the classification;
- `accepted` is true only for `faithful-equivalent` or
  `faithful-stronger`;
- any stronger classification is genuine, nonvacuous strength;
- every final claim cites the paper and declaration evidence;
- hashes still match current inputs.

Report the classification, whether it is accepted, the most consequential
findings, and the result-folder path. State explicitly that no benchmark input
was changed.

Do not commit or push audit files unless the user separately asks after reviewing
the local results.
