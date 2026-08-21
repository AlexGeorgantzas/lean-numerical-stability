# Source-validity records

This directory records source defects discovered while reviewing HighamBench
tasks. These records are standalone research notes. They are not generated audit
outputs and are not part of the audit protocol.

The reference paper remains primary evidence. A source-validity record documents
the project's analysis and benchmark decision; it does not override the paper,
alter an audit classification, or replace independent source inspection.

## File naming

Use one record per affected benchmark task:

```text
P17-T1.md
```

Use a paper-level record only when the issue affects the paper independently of
any selected task.

## Status vocabulary

- `published-statement-contradicted`: a concrete counterexample satisfies the
  printed hypotheses and violates the printed conclusion.
- `published-statement-incomplete`: the claim may be correct, but necessary
  conditions are absent and no counterexample has yet been established.
- `published-statement-ambiguous`: the source does not determine one proposition
  without an interpretive choice.
- `author-corrected`: an author-issued erratum or corrected version resolves the
  issue; the correction must be identified exactly.

Record the benchmark treatment separately from the source status. A project may
retain a task for an independently documented reason while declaring that its
ordinary audit classification is not used because the printed source is itself
contradicted.

## Required contents

Every record must state:

1. the paper version, local PDF path, and SHA-256;
2. the affected result and exact source location;
3. the source-validity status;
4. the defect and the proof step that needs the missing condition;
5. a complete counterexample or other primary evidence;
6. sufficient repair conditions, clearly distinguished from printed hypotheses;
7. the benchmark treatment and its rationale;
8. implications for faithfulness classification;
9. provenance links to the relevant audit artifacts; and
10. a concise thesis-ready summary using appropriately qualified language.

Do not describe a source as author-corrected without an identifiable correction.
When the project itself finds a defect, prefer language such as "the published
statement as written admits the following counterexample."

## Audit independence

These notes do not modify the audit skill, methodology, prompts, schemas,
classifications, or generated decisions. Any audit continues to run normally and
its output remains available as provenance. When a source defect makes the
ordinary classification non-decisive for project purposes, that fact is stated
only in the affected source-validity note and in the resulting thesis discussion.
