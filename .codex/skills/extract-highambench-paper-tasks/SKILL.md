---
name: extract-highambench-paper-tasks
description: Independently extract or revise one HighamBench P0X paper into T1-T3 selected Lean tasks or a T4 whole-paper corpus, with paper-local semantics, metadata, private N/L solvability proofs, T4 faithfulness review, validation, and registration. Use under paper_bencmark/reference_papers.
---

# Extract HighamBench Paper Tasks

## Scope

Work on exactly one paper and one `P0X` ID per invocation. Do not read or
process other reference papers. Different `P0X` invocations may run
concurrently. Write only the selected paper's owned paths; treat every other
paper, corpus-wide configuration or aggregate, shared tool or schema, and
`HighamBench.Core` or `HighamBench.SemanticCore` as read-only. Never use another
paper as mathematical or semantic input. If the request does not identify one
paper unambiguously, ask which paper to use.

## Route the work progressively

Read only the references required by the selected mode and current stage, but
read every selected reference completely before acting on it.

For T4, enforce this order: construct the controlled placeholder corpus,
validate separate proof-complete private N and L solutions on the exact same
semantic bytes, run source-faithfulness review, pass the final gates, and only
then run explicitly authorized measurements. Never begin a later stage using
provisional hashes or incomplete evidence from an earlier stage.

Use the least machinery needed for the current stage. During construction,
direct pinned Lean compilation of the exact current private N and L files,
together with the statement, dependency, and placeholder checks in the routed
private-solvability reference, establishes mathematical solvability and is
enough to begin faithfulness review. Do not require a locked measurement
workspace, Bubblewrap, a special result recorder, or final registry receipt for
that transition. If optional release hardening cannot run on the current host,
leave only measurement-ready registration pending; do not freeze the paper,
change its mathematics, invent a wrapper stack, or edit shared tools to force
it. Hashing a current snapshot never prohibits later construction edits; every
semantic edit simply requires fresh direct N/L checks and review evidence.

- For any T1--T3 selection, construction, revision, tier review, metadata
  review, or private N/L proof work, read
  [T1--T3 selected-result workflow](references/t1-t3-workflow.md).
- Before the first write in either mode, and before paper registration, read
  [paper-local independence](references/paper-local-independence.md).
- For any T4 inventory, source mapping, schema work, statement or definition
  construction, revision, or controlled-surface audit, read
  [T4 corpus construction](references/t4-construction.md). Before creating or
  revising T4 metadata or construction-input hashes, then read and use the
  frozen assets in
  [T4 metadata contract](references/t4-metadata-contract.md).
- For T4 private N/L proof construction or solvability validation on the exact
  current controlled surface, read
  [T4 private solvability](references/t4-private-solvability.md). Also read the
  construction reference only if statements, mappings, imports, or controlled
  semantic definitions may change.
- For T4 review-unit or packet preparation, or verdict-driven semantic
  revision, read the construction reference and then
  [T4 source-faithfulness review](references/t4-faithfulness-review.md).
- For launching or auditing a campaign over frozen packets, or orchestrating
  judges, translators, or adjudicators, read only the faithfulness and
  paper-local-independence references and verify the recorded exact-byte N/L
  gate. Do not load or transmit private proof procedure or artifacts. Treat
  the round trip as directional: sanitized Lean target → locked
  natural-language reconstruction of that Lean target → comparison with the
  paper source claim. Never ask the Blind Translator to reconstruct the source
  excerpt; that role must not receive it. Treat
  fresh conversation context, role-visible data, packet-local tool access, and
  bounded delegation as separate sealed controls. Fresh context does not
  itself prohibit tools; permit only the separately sealed packet-local
  capabilities. A semantic change returns the workflow to construction,
  private N/L revalidation, and fresh packet review; a packet-only repair stays
  in the faithfulness stage and uses fresh reviewers.
- Before final T1--T3 validation or acceptance, read its workflow and then
  [completion and registration gates](references/completion-registration.md).
- Before final T4 validation, acceptance, registration, or reporting overall
  completion, read the construction, private-solvability, and faithfulness
  references, then read the completion and registration gates.

Do not load T4 references for a T1--T3-only request or the T1--T3 reference for
a T4-only request. When the user requests T4, do not reselect or revise T1--T3
unless explicitly asked, and never apply T1--T3 selection filters or tier
classifications to T4. T4 is a whole-paper corpus, not a harder single result.

## Common preparation

1. For T4, claim the paper-local writer lease specified by
   [paper-local independence](references/paper-local-independence.md) before
   the first write. Keep its bearer only in the owner-only ephemeral credential
   file created by the lease tool; never put it in argv, output, metadata, or
   durable artifacts. Pass that credential file to every workspace init or
   scaffold. Initialize and check the generic workspace, and use its scaffold
   only for a new shard whose starter destinations are all absent. Hold or
   renew the lease through every write and release it when the invocation is
   terminal; successful release removes the credential file.
2. Read `paper_bencmark/AGENTS.md`, `paper_bencmark/TASK_SOURCE_TAGS.md`,
   `paper_bencmark/scratch_pad/HighamBench_Simple_Two_Condition_Specification.pdf`,
   and the versioned paper-neutral schemas or templates used by the generic
   validator. Do not use another paper or a mutable corpus aggregate as a
   schema source.
3. Read the selected PDF completely and sequentially, including appendices and
   mathematically substantive footnotes. Use extracted text for search, but
   inspect page images for formulas, typography, indices, and scoped
   assumptions. Record the PDF hash, bibliographic data, PDF and printed pages,
   section, and exact source anchor.
4. Keep `classification_frozen_before_runs` false throughout construction.
   Paraphrase source material in public metadata instead of copying long
   passages.
5. Put every custom statement-facing type, model, algorithm, notation, and
   semantic definition needed by the paper in
   `shared/HighamBench/P0XDefinitions.lean`. It imports only the minimal frozen
   upstream `Std` or `Mathlib` modules directly, never `HighamBench.Core`,
   `HighamBench.SemanticCore`, or another paper's definitions. Every target for
   the paper imports exactly `HighamBench.P0XDefinitions`.

## Core invariants

- Preserve the source's objects, domains, quantifiers, assumptions, constants,
  indices, epistemic status, approximation semantics, and conclusions. Never
  alter them for easier formalization or proof.
- Keep the controlled target and paper-owned bundle condition-neutral,
  minimal, and byte-identical between N and L. N has no NumStability artifact;
  L alone additionally has the frozen evaluated library.
- Keep proof-oriented helpers, certificates, tactics, and solutions outside the
  controlled task and trusted bundle. Never hide a conclusion in an axiom,
  structure field, typeclass assumption, definition, or imported helper.
- Every proof-bearing benchmark declaration requires separate proof-complete
  private N and L solutions. Retain the designated public placeholders required
  by the selected mode. The controlled declarations differ only in their proof
  bodies; private solutions may contain proved, unexposed proof-local helpers.
  Their controlled statements, imports, and semantic dependencies must match
  exactly. Private solutions must never reach measured agents or faithfulness
  reviewers.
- A statement, import, or semantic-definition change invalidates all dependent
  private-solvability and applicable source-faithfulness evidence within that
  paper. Rebuild and rereview the exact revised semantic bytes. Paper-local
  ownership must make cross-paper invalidation impossible.
- Persist the reusable workflow as authenticated, paper-local artifacts using
  the routed versioned templates: exact prompts and packets, manifests, plans,
  checkpoints, validated final role JSON, provenance, hashes, and audit
  ledgers. Never make hidden reasoning or ephemeral chat transcripts a
  dependency of a later paper or fresh session.

## Source tags

Record source presentation separately from mathematical result form.

- `THM`, `LEM`, `PROP`, `COR`: use only for that exact author label and copy it
  to `author_label`.
- `EQN`: numbered equation or formula.
- `TXT`: claim stated materially in prose.
- `UNL`: displayed but unnumbered and unlabeled result.

Set `author_label` to `null` without an explicit named label. Combine `EQN` and
`TXT` only when prose materially completes the numbered formula. Do not tag a
claim from the presentation of a supporting result.

## Authorization boundary

Before launching T4 external-model reviewer sessions, disclose the
provider/model, reasoning and speed modes, transmitted packet contents, tools,
freshness/blindness controls, exact manifest and plan hashes, and worst-case
session counts. Require either explicit authorization or a valid recorded
standing authorization whose exact scope covers the launch. If such standing
authorization already covers a similar or replacement campaign, bind it to the
new paper-local plan, make the disclosure, and launch without asking again.
Never activate Fast mode when the recorded profile requires Standard, and use
literal Ultra for every covered semantic role, canary, and adjudicator. A scope
change requires new authorization. Review authorization does not authorize
measurements.

In either mode, pass the applicable completion gates before measurements;
explicit user authorization is additionally required.

Do not expand this invocation to another paper. User-started invocations for
distinct paper IDs may proceed concurrently. Do not run measurements, mark the
corpus measurement-ready, commit, or push unless the user explicitly asks.
