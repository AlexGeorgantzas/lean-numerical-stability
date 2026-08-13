# HighamBench faithfulness audit

## Purpose

This audit determines whether a fixed Lean target represents the result selected
from its reference paper. Kernel acceptance is necessary but does not answer
this question: a provable theorem can still formalize the wrong statement.

The audit accepts either:

- `faithful-equivalent`: Lean and the paper have the same mathematical content,
  allowing definitional reformulation and harmless presentation changes;
- `faithful-stronger`: Lean genuinely proves a more general domain or stronger
  conclusion while retaining the selected paper result.

Adding hypotheses, restricting dimensions, deleting conclusions, replacing an
algorithmic claim by an unrelated analytic fact, or making a theorem vacuous is
not a stronger result.

Protocol v0.2 reduces repeated work across a paper's T1, T2, and T3 audits. It
does not remove stateless roles, primary-PDF evidence, dependency coverage,
round-trip judgment, conditional adjudication, or task-local final decisions.

## Repository layout

All reusable audit material lives here:

```text
paper_bencmark/faithfulness_audit/
  METHODOLOGY.md
  prompts/
  schemas/
  scripts/
  templates/
  skill/highambench-faithfulness-audit/
```

One task audit uses a dedicated result folder:

```text
paper_bencmark/highambench/tasks/P03/T1/faithfulness/
  manifest.json
  inputs/
    source_locator.json
    paper_source_locator.json
    declaration_dossier.md
    blind_dossier.md
    direct_review_packet.md
    blind_review_packet.md
    dependency_inventory.json
    blind_dependency_inventory.json
    dependency_reuse_direct.json     # only when reuse applies
  agent_outputs/
    paper_source_contract.json       # paper-batch mode
    source_contract.json
    blind_translation.json
    direct_judge.json
    roundtrip_judge.json
    adjudicator.json                 # only when required
  decision.json
  report.md
  history/                           # prior runs archived by intentional refresh
```

No audit agent may edit `Target.lean`, `context.md`, `task.json`, shared Lean
sources, or the reference PDF. Only the orchestrator writes audit artifacts.

## Sources of authority

The reference PDF and exact Lean environment are authoritative. `task.json` may
locate the PDF, source pages, and theorem declaration, but its informal
paraphrases are not evidence. `context.md` is an object being audited, not
evidence for the verdict. The target proof is excluded because faithfulness
concerns the proposition, not how it is proved.

Before any model call, preparation must:

1. validate task IDs and required files;
2. verify the reference PDF against the SHA-256 recorded in `task.json`;
3. hash the target, metadata, context, local imports, and audit setup;
4. compile the unchanged targets and local imports;
5. inspect each elaborated theorem type through Lean's environment API;
6. generate complete evidence dossiers and role-specific review packets;
7. write and validate `prepared` manifests.

`prepare_paper_audit.py` runs those independent preparations concurrently for
T1, T2, and T3, then verifies that all three identify exactly one paper file,
version, and hash. If any preparation fails, no role runs.

## Declaration coverage

A role must never infer the meaning of a symbol from its name. For example, a
name ending in `Norm` is not evidence that the declaration is a Euclidean norm.

The complete declaration dossier has four layers:

1. **Exact declaration source.** The theorem text appears without its doc
   comment or proof.
2. **Elaborated type.** Lean prints readable and fully explicit types exposing
   implicit arguments, instances, coercions, and notation.
3. **Recursive local closure.** Traversal follows types and bodies of every
   declaration owned by the target's local HighamBench modules. Constructors of
   local structures and inductives are included.
4. **External semantic frontier.** Directly reached Lean/mathlib declarations
   are listed with owner, kind, type, and one-level body. Traversal stops there.

The complete direct dossier also contains the hashed source of every local
import, including imports not reached by the target type. It remains available
for human review and adjudication. Normal judges receive a compact review packet
that omits this duplicated module text because every reached declaration is
already represented in the semantic inventory.

The blind dossier replaces benchmark-local names and modules with neutral IDs
without changing types, bodies, dependency IDs, or mathematical content. The
blind translator receives only its review packet inline and has no tools.

Every dependency has a task-local `Dxxx` ID and a semantic SHA-256. The semantic
hash covers its role, actual declaration name, owner module, kind, readable and
explicit types, and readable body. It excludes task-local ID and graph distance.
Both the blind translator and direct judge must return exactly one record for
every `Dxxx` ID, in order. Missing or duplicate IDs invalidate the output.

The external frontier is the trust boundary. If one-level external evidence is
insufficient, the role must return `unclear`; unresolved items trigger an
adjudicator with access to the complete dossiers.

## Hash-verified reuse

A declaration interpretation may be reused only when all of these hold:

- its semantic SHA-256 exactly matches a dependency in a validated earlier role;
- the earlier blind status is `understood`, or the earlier direct status is
  `pass`/`not-applicable`, for the role being reused;
- the source role output and reuse payload are SHA-256 bound;
- the target role receives the cached text and exact `reuse_sha256`.

Reuse covers **declaration meaning only**. The new role must still explain the
dependency's effect on the current target. A direct judge must also decide its
match to the current paper result. Those task-specific fields cannot be copied.
Dependencies without an eligible exact match remain fully expanded.

The default fast paper schedule uses direct reuse for T2 and T3 after validating
T1's direct dependency ledger. Blind meanings can also be reused in a sequential
or resumed audit, but all three blind translations normally run concurrently,
so their packets remain complete and independent.

## Stateless roles

Every role is a fresh subagent started with inherited conversation disabled. A
role receives only its declared bundle. Invalid output is retried with another
fresh agent, not repaired in the old conversation.

### Paper source-contract agent

In paper-batch mode, one fresh source agent receives
`paper_source_contract.md`, `paper_source_locator.json`, and the reference PDF.
It reads the paper context once and returns separate contracts for T1, T2, and
T3. It receives no Lean, dossiers, `context.md`, or informal task paraphrases.
The splitter hash-binds the batch output and writes one validated task-local
`source_contract.json` per task.

`source_contract.md` remains the single-task fallback when only one task exists
or a paper batch was not requested.

### Blind translator

Each task gets its own fresh blind agent. It receives only
`blind_translation.md`, its schema, the packet hash, and the complete inline
`blind_review_packet.md`. It receives no task identity, paper, theorem name,
proof, prior output, filesystem access, or tools.

### Direct judge

Each task gets its own fresh direct judge. It receives the PDF source packet,
task source contract, manifest checklist, and `direct_review_packet.md`. It
checks the PDF independently rather than treating the source contract as
authoritative. It must complete every dependency and semantic-check record.

### Round-trip judge

Each task gets its own fresh round-trip judge. It receives the PDF source
packet, task source contract, blind translation, and semantic-check list. It
does not see Lean, either declaration dossier, or the direct judgment.

### Adjudicator

A fresh adjudicator is mandatory when:

- direct and round-trip classifications differ;
- either judge requests adjudication or returns `undetermined`;
- a dependency or semantic check remains `unclear`;
- implication directions conflict with the stated classification.

Source or translation ambiguities are evidence the judges must resolve; their
mere presence does not automatically create a fifth model call. If a judge
cannot resolve one, its `unclear` status or adjudication request triggers the
adjudicator. The adjudicator receives primary PDF evidence, complete dossiers,
reuse records, and all role outputs. It resolves evidence item by item rather
than voting.

## Fast paper schedule

For one paper with T1, T2, and T3:

1. Prepare all three tasks concurrently with `prepare_paper_audit.py`.
2. Spawn one paper source-contract agent and three task-local blind translators
   concurrently.
3. Validate and split the paper source contract; validate all blind outputs.
4. Spawn the T1 direct judge and all three round-trip judges concurrently.
5. Validate T1's direct ledger. Apply direct-only semantic-hash reuse to the T2
   and T3 review packets before either direct judge starts.
6. Spawn the T2 and T3 direct judges concurrently.
7. Run only the adjudicators actually triggered. Independent adjudicators may
   run concurrently.
8. Finalize, validate, commit, and push task results in T1, T2, T3 order when
   per-task commits are required.

Thus all judgments remain task-local, while the repeated PDF read and repeated
definition interpretation are reduced. Running tasks concurrently does not make
one task's verdict depend on another task's verdict.

## Implication decisions

Every judge answers both directions separately:

1. Does the Lean proposition imply the selected paper result under the paper's
   context?
2. Does the selected paper result imply the Lean proposition?

| Lean implies paper | Paper implies Lean | Classification |
|---|---|---|
| yes | yes | `faithful-equivalent` |
| yes | no | `faithful-stronger` only when the extra strength is genuine |
| no | yes | `not-faithful-weaker` |
| no | no | `not-faithful-different` |
| unclear | any | `undetermined` |

Logical implication alone does not excuse vacuity. Added assumptions, restricted
types, or impossible premises must be analyzed as reduced applicability.

## Numerical semantic checks

Every manifest fixes 16 required checks (`S01`-`S16`): source selection; binders
and types; quantifier scope; hypotheses; conclusion completeness; operators and
imported definitions; exact versus computed values; algorithm linkage; norm
semantics; constants and indexing; floating-point model and exceptional values;
relation strength; error notion; higher-order terms;
specialization/generalization; and nonvacuity.

Each judge records `pass`, `fail`, `unclear`, or `not-applicable`, with concrete
paper and Lean/translation evidence. `not-applicable` requires an explanation.

## Finalization and repair

Only the orchestrator writes outputs. It validates JSON, hashes every artifact,
invokes adjudication when required, writes `decision.json`, renders `report.md`,
and marks the manifest `completed` only after complete validation passes.

An audit does not repair a target. A later repair agent may consume the report
and retry formalization. Any changed target requires a new audit because its
hash no longer matches.

Completed v0.1 audits retain their original setup fingerprints as historical
provenance and remain validatable. New preparation always uses v0.2.

## Commands

Prepare a complete paper batch:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/prepare_paper_audit.py P03
```

Split a valid paper-level source-agent response:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/split_paper_source_contract.py \
  /path/to/paper_source_contract.json
```

Apply direct dependency reuse after validating P03-T1's direct output:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/apply_dependency_reuse.py \
  P03-T2 --source P03-T1 --role direct
```

Prepare or validate one task:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/prepare_audit.py P11-T1
python3 paper_bencmark/faithfulness_audit/scripts/validate_audit.py \
  P11-T1 --phase prepared
```

Validate each role immediately after writing its JSON:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/validate_agent_output.py \
  P11-T1 direct-judge
```

Refresh only when intentionally invalidating prior results:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/prepare_audit.py P11-T1 --force
```

Install the repository skill copy locally:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/install_skill.py
```
