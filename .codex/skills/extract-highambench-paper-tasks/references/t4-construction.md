# T4 corpus construction

Read this reference completely before constructing, revising, or preparing
faithfulness packets for a T4 corpus. The common preparation and invariants in
`../SKILL.md` still apply.

T4 construction covers the source inventory, controlled placeholder corpus,
minimal semantic surface, and corpus-aware metadata. It is not solvability or
review acceptance: those later stages use their separately routed references.

## Keep construction simple

Finish the paper's inventory, semantic definitions, statements, and private
proofs before doing release hardening. The pre-review solvability check is the
direct exact-byte N/L procedure in
[T4 private solvability](t4-private-solvability.md); it does not require the
measurement runner, the final registry, Bubblewrap, seccomp, a socket filter,
or a special recorder. Do not build paper-specific wrappers, modify shared
tools, or change the mathematics because an optional hardened runner cannot
start on the current host. Record that release/measurement registration remains
pending and continue the paper-local construction and faithfulness work.

Commands or prose that say `freeze` in this workflow mean “hash this exact
current snapshot.” They do not set `classification_frozen_before_runs: true`,
make the files read-only, or forbid continued extraction. After any semantic
edit, refresh the hashes and rerun the direct private N/L checks before review.

## Claim and initialize the paper-local T4 shard

Before the first T4 write, create a private temporary credential directory,
then let the claim command generate a fresh invocation UUID and high-entropy
bearer directly into its owner-only credential file. The public command result
never contains the bearer:

```bash
lease_credential_dir="$(mktemp -d /tmp/highambench-P0X-lease.XXXXXXXX)"
lease_credential_file="$lease_credential_dir/credential.json"
python3 paper_bencmark/highambench/tools/t4_writer_lease.py claim \
  --scratch-root paper_bencmark/scratch_pad --paper-id P0X \
  --credential-out "$lease_credential_file" --ttl-seconds TTL
```

Keep the credential file out of the repository, metadata, prompts, logs, and
durable hand-off artifacts. Do not read its bearer into argv or model context.
With that lease active, initialize and retain the generic paper-local workspace
descriptor:

```bash
python3 paper_bencmark/highambench/tools/t4_workspace.py init \
  --benchmark-root paper_bencmark/highambench \
  --reference-root paper_bencmark/reference_papers \
  --scratch-root paper_bencmark/scratch_pad --paper-id P0X \
  --lease-credential-file "$lease_credential_file"
```

For an entirely new shard, after `write-set` confirms the paper-local scope,
run `scaffold` with the same lease credentials. It creates exactly the seven
explicitly incomplete paper-owned starters—definitions, target, context,
inventory, task record, and private N/L files—and binds the versioned generic
schemas, role prompts, authorization template, and durable-artifact policy.
It preflights every destination and refuses to overwrite anything. If any
starter already exists, do not delete or replace it to force scaffolding;
validate and continue the existing shard instead.

```bash
python3 paper_bencmark/highambench/tools/t4_workspace.py scaffold \
  --benchmark-root paper_bencmark/highambench \
  --reference-root paper_bencmark/reference_papers \
  --scratch-root paper_bencmark/scratch_pad --paper-id P0X \
  --lease-credential-file "$lease_credential_file"
```

This binds exactly one source PDF and the selected paper’s controlled, private,
packet, evidence, and campaign roots, plus hashes of the shared read-only
schemas and templates. Run `write-set` before publication. Workspace `check`
authenticates descriptor bindings only; run it together with the routed
metadata and stage-specific gates before a hand-off. Renew the writer lease
before it expires:

```bash
python3 paper_bencmark/highambench/tools/t4_writer_lease.py renew \
  --scratch-root paper_bencmark/scratch_pad --paper-id P0X \
  --credential-file "$lease_credential_file" --ttl-seconds TTL
```

After the invocation's final write, release the lease and remove the now-empty
private directory. A successful release removes the credential file; if
release fails, retain it and retry rather than losing the active credentials:

```bash
python3 paper_bencmark/highambench/tools/t4_writer_lease.py release \
  --scratch-root paper_bencmark/scratch_pad --paper-id P0X \
  --credential-file "$lease_credential_file"
rmdir "$lease_credential_dir"
```

An expired hand-off requires an explicit archived takeover rather than silent
reuse. After constructing metadata, use the `t4_metadata.py freeze` and `check`
commands routed in the metadata contract; that helper may write only the
selected paper's `T4/task.json`.
Never copy a P01-specific campaign script or path layout to another paper;
historical P01 tooling audits only its own immutable artifacts. Distinct paper
descriptors have disjoint write scopes.

## Build a coverage ledger first

Make a source-order ledger before writing Lean. Inventory all of the following,
including every clause or case and all appendix occurrences:

- explicitly named theorems, lemmas, propositions, and corollaries;
- every numbered mathematical equation, distinguishing definitions,
  hypotheses/model equations, and asserted consequences;
- precise unnumbered prose claims and unlabeled displays, including precise
  claims inside proofs, remarks, or discussions;
- central algorithms, with their inputs, outputs, state transitions, stopping
  conditions, and nondeterminism where stated;
- symbolic or exact mathematical examples; and
- precise problem formulations, objectives, constraints, and solution
  specifications.

Also inventory precise asymptotic, probabilistic, empirical, or externally
cited claims when the paper states enough semantics to formalize them. Do not
exclude an item merely because it is difficult, already known, proved
elsewhere, approximate, or not suitable for T1--T3. Preserve its stated status:
a conjecture, question, heuristic, or empirical observation must not silently
become a universally asserted theorem.

Make each ledger item one atomic source claim: split independently falsifiable
clauses, cases, observations, or epistemic statuses even when the paper puts
them in one sentence or paragraph. For every item, record a stable ID, source
kind, exact locations and scope, all assumptions and notation it inherits, and
either its Lean declaration mapping or a specific exclusion reason. Distinguish
mapping roles explicitly:

- `primary_carrier`: the smallest declaration or declaration group whose
  semantics directly states the source claim;
- `semantic_context`: a definition or result needed to interpret the carrier
  but not itself a statement of this source claim; and
- `duplicate_anchor`: a genuine restatement whose additional source location
  is attached to an already reviewed carrier.

Only primary carriers determine the declaration group submitted to judges;
semantic context belongs in its dependency closure. The default is inclusion.
Exclude only content with no determinate mathematical proposition or
specification after inspecting its context. Map a true duplicate or verbatim
restatement to one declaration with every anchor; use separate declarations
when a restatement changes assumptions, domain, constants, or conclusion.
Reconcile equation numbering, cross-references, named-result lists, and the
appendices so text extraction cannot silently omit an item.

## Keep controlled statements placeholder-bearing

Create `tasks/P0X/T4/Target.lean` in paper order. Prefer one named primary Lean
declaration per atomic source claim. If one source claim genuinely needs a
small group of declarations, record the group explicitly; do not bundle
unrelated claims into one conjunction or split away a material clause.

- Preserve the paper's objects, domains, quantifiers, assumptions, constants,
  indices, edge conditions, approximation/asymptotic semantics, and full
  conclusion. Do not replace an approximate relation by equality, drop higher
  order terms without source authorization, strengthen premises, or narrow the
  domain for convenience. The sole permitted non-equivalent relation is a
  same-domain `faithful-stronger` statement accepted under the review contract;
  extra assumptions, narrower domains, altered constants, and weaker
  conclusions never qualify.
- Encode a purely definitional equation as a transparent definition. Encode
  every assertive proposition, including theorem-like equations and symbolic
  example claims, as a named declaration with exactly one designated benchmark
  proof placeholder using the repository's `PROOF_START` convention and
  `sorry`. Do not discharge even an easy result in the controlled T4 target.
- Formalize a central algorithm with a faithful transparent function, relation,
  transition system, or trace specification. Do not replace it with an
  unconstrained opaque symbol. Put its asserted invariants, correctness, or
  error properties in separate placeholder-bearing declarations.
- Represent a precise problem or conjecture as data plus a predicate or
  proposition specification. Add a proof hole for existence, correctness, or a
  solution only when the paper asserts that claim.
- If a source assertion is inconsistent, ill-typed, or demonstrably false
  under its own stated model, do not silently repair it, add premises, or leave
  an impossible benchmark proof hole. Record the source issue and evidence in
  the ledger, preserve the assertion and its attributed status in a transparent
  report object when that is determinate, and mark it as non-proof-bearing.
  Formalize a correction or counterexample only when the paper itself states
  one. Require the completeness audit and faithfulness packets to expose this
  disposition explicitly.
- Never make a target vacuously provable or hide its conclusion in an `axiom`,
  a structure field, a typeclass assumption, a definition, or an imported
  helper.

## Keep the paper-owned N/L surface minimal

The complete custom semantic closure is the paper's `Target.lean` and
`P0XDefinitions.lean`. Supply those bytes identically to N and L. The paper
definitions module imports only the minimal frozen upstream `Std` or `Mathlib`
modules needed to elaborate its declarations. It never imports
`HighamBench.Core`, `HighamBench.SemanticCore`, or another paper module.

- Audit the target and paper definitions together. Every custom declaration
  exposed to agents must be a transparent type, structure, constant, notation,
  model, algorithm, or semantic definition directly or transitively needed by
  at least one primary declaration in this paper. Remove unused imports and
  custom declarations.
- If two papers need mathematically similar semantics, each paper owns its own
  namespaced definition. Do not promote it to a shared HighamBench module.
- Add no proof helper lemma, derived convenience theorem, tactic support used
  only by a proof, NumStability adapter, hidden certificate, or unused API.
  `P0XDefinitions.lean` contains no `sorry`, `admit`, new axioms, or `unsafe`
  bypasses.
- No NumStability name may occur in the target, `P0XDefinitions.lean`, or their
  transitive custom definitions. N and L receive the byte-identical target and
  paper-owned definitions; L alone additionally has the frozen evaluated
  library.

## Use a corpus-aware metadata schema

Before writing the coverage ledger or task metadata, read
[`t4-metadata-contract.md`](t4-metadata-contract.md). Start from the exact
paper-neutral schemas and pending templates routed there; never reverse-engineer
another paper's metadata. The external inventory is canonical, and its complete
normalized `items` array must remain synchronized with the embedded task view.

Use the frozen generic T4 schema and validators. A paper extraction invocation
must not edit shared schemas or tools. If the frozen schema cannot represent a
source object faithfully, report that bootstrap infrastructure gap instead of
mutating shared infrastructure mid-extraction. Store a claim-scoped coverage
ledger, declaration records, and review-unit records; do not squeeze a
multi-declaration T4 into singular fields such as `theorem_name` or
`required_declaration`. Use a plural `required_declarations` list and
per-declaration IDs, source mappings, semantic dependency hashes, placeholder
locations, and review status.

Validators must check the complete mapping in both directions: every included
atomic inventory item occurs in exactly one review unit and maps to a primary
declaration or recorded smallest group, every primary declaration maps back to
source, and every required declaration and placeholder is covered by accepted
review records. Review-unit declarations must be exactly the declaration-order
union of their items' primary carriers. A declaration may occur in more than
one review unit only when it is genuinely reused in two distinct atomic claims;
record the reuse and smallest-group reason explicitly, require every containing
unit to pass, and invalidate all containing and dependent units if it changes.
Do not merge a large connected component merely to force declaration groups to
form a partition.

Existing source-presentation and result-form tags are per declaration in T4.
Apply a result-form tag to a proposition only where that taxonomy is accurate;
do not force algorithms, problems, or other claim forms into it. Add a separate
`source_kind` for algorithms, examples, problems, definitions, and other source
objects. Extend the schema deliberately rather than inventing an inaccurate
existing tag or a single aggregate result form.
