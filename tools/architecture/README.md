# Architecture baseline tooling

This directory contains the reproducible measurements used during the
book-formalization migration. The generator has two layers:

- `generate_baseline.py` scans Lean sources and the direct-import graph using
  only the Python standard library.
- `declaration_dependencies.lean` loads the compiled `NumStability`
  environment, separates signature references from body/proof references, and
  contracts Lean-reserved or compiler-generated declarations onto the authored
  project declarations reachable through them. Authored private declarations
  remain in the graph; unstable `_proof_*`, `_simp_*`, `match_*`, flat
  constructors, unfold helpers, and similar implementation details do not.
- `check_compatibility.py` verifies that every old path documented in the
  compatibility table is an import-only wrapper around exactly its stated
  canonical targets, that the table agrees exactly with the `compatibility`
  tier in `docs/architecture/tiers.json`, that every historical path and
  every canonical target carries a direct test import, and that production
  code contains zero imports of historical paths outright. The former
  retained-boundary exception mechanism was retired with R0015; the checker
  carries no exception list.
- `check_layout.py` enforces the naming, classification, aggregate, generated-
  artifact, and documentation ratchet recorded in
  `docs/architecture/layout-exceptions.json`.
- `check_norms_phase11b_ownership.py` enforces the immutable Phase 11B1
  declaration-ownership manifest, owner DAG, direct-import allowlist, and
  normalized declaration/signature/body graph preservation contract.
- `check_chapter06_phase11b2_ownership.py` checks the frozen 69-constant
  Chapter 6 source-tail ownership partition and its incident dependency graph.
- `check_blocklu_phase12_ownership.py` enforces the frozen 1,990-declaration
  Block LU semantic route map, staged destination ownership, private-name
  rewrites, structural aggregates, destination DAG, and exactly normalized
  contracted graph.
- `check_phase.py` validates the tracked repository-reorganization operating
  contract: phase, milestone, branch, request, projection, and checkpoint
  records, using only the Python standard library and read-only Git commands.
  By default it checks the phase directory named by
  `docs/architecture/phases/active-phase.json`; `--phase-dir` targets another
  phase directory, and `--all-phases` validates every retained phase
  directory plus the supersession fleet invariants: exactly one effectively
  active phase, active-phase pointer agreement, every other retained phase
  effectively terminal, supersession records whose successor chains name
  existing phases, stay acyclic, and reach the active phase, and a
  preserved-phase hash matching each superseded phase's live `phase.json`.
- `check_completion_phase.py` is the dedicated validator for the 2026-08
  completion phase, rooted at the predecessor reorganization phase's final
  C0008 checkpoint. It is deliberately independent of `check_phase.py` and
  enforces the phase's exact one-off contract, including pinned commits,
  frozen inventories, request/branch/projection lifecycles, reviewed-union
  postimages, and checkpoint acceptance evidence, using disposable Git
  indexes rooted at the applicable checkpoint.
- `check_phase_projection.py` compares a frozen format-2 declaration
  projection with a candidate dependency graph: selected declaration names,
  kinds, visibility, and the exact signature/body incident edge sets must be
  preserved, and only the owning module may change, to owners matching the
  exact modules or namespace prefixes given on the command line.
- `check_completion_phase_projection.py` is the completion-phase variant of
  the projection comparison. It additionally accepts a hash-pinned private
  normalization map, total over the projection's private declarations, that
  permits selected private names to change while pinning each normalized
  declaration's destination owner.
- `check_provenance.py` validates license pointers and exact upstream evidence.
- `check_warnings.py` enforces the warning contract in
  `docs/architecture/warnings.json` against a build or test log. It normalizes
  ANSI sequences, CRLF, GitHub timestamp prefixes, runner path prefixes, and
  multiline diagnostics, then identifies each diagnostic by path, kind,
  normalized message, a stable nearby-source anchor hash, and occurrence, so
  line and column stay evidence rather than identity. `--check` fails on a new
  fingerprint, an unclassifiable diagnostic, an exceeded global, per-kind,
  per-role, or per-file ceiling, a warning in a file with no reviewed
  allowance, a path or kind mutation, an unlisted or expired suppression, or a
  capture-environment change; a diagnostic that no longer fires fails as an
  improvement requiring a reviewed reduction. `--write-baseline` is review-only
  and byte-reproducible from a given log. `--self-test` exercises every failure
  class against synthetic fixtures.
- `sort_aggregate_imports.py` mechanically normalizes import-only umbrellas.

Run the complete capture from the repository root:

```text
python tools/architecture/generate_baseline.py --name YYYY-MM-DD
```

Check the compatibility contract independently:

```text
python tools/architecture/check_compatibility.py
```

Check a retained dependency stream against the frozen Phase 11B1 ownership
manifest. Pre-migration mode validates the Phase 11A Core input; post-migration
mode validates the 24 semantic owners. Supplying the retained Phase 11A stream
as `--baseline-tsv` additionally requires an exact normalized full-graph
comparison:

```text
python tools/architecture/check_norms_phase11b_ownership.py \
  --mode pre --dependency-tsv <phase11a-dependencies.tsv>
python tools/architecture/check_norms_phase11b_ownership.py \
  --mode post --dependency-tsv <phase11b1-dependencies.tsv> \
  --baseline-tsv <phase11a-dependencies.tsv>
```

Run `--mode pre` from the Phase 11A checkout, or pass `--source` a retained copy
of the frozen Phase 11A `Analysis/Norms/Core.lean`; the live Phase 11B1 Core is
the declaration-free aggregate and intentionally fails the frozen pre-split
source hash.

Check the frozen Phase 11B2 input against its tracked ownership manifest:

```text
python tools/architecture/check_chapter06_phase11b2_ownership.py \
  --mode pre \
  --dependency-tsv benchmark-results/architecture/phase11b1-declarations.tsv
```

After the migration, compare the fresh stream with the complete retained
Phase 11B1 graph:

```text
python tools/architecture/check_chapter06_phase11b2_ownership.py \
  --mode post \
  --dependency-tsv benchmark-results/architecture/phase11b2-declarations.tsv \
  --baseline-tsv benchmark-results/architecture/phase11b1-declarations.tsv
```

Check the immutable Phase 12 Block LU input and reviewed route map:

```text
python tools/architecture/check_blocklu_phase12_ownership.py --self-test
python tools/architecture/check_blocklu_phase12_ownership.py \
  --mode pre \
  --dependency-tsv benchmark-results/architecture/phase11b2-declarations-v2.tsv \
  --routes docs/architecture/declaration-ownership/blocklu-phase12-v2-routes.tsv \
  --manifest docs/architecture/declaration-ownership/blocklu-phase12-v2.tsv \
  --expected-manifest-sha256 \
    90F28D568A611035DE20839F2C30CB2800B75F2FC1DF2CE1373E9FFDD3D11287
```

During an incremental extraction, use `--mode stage` with the fresh dependency
TSV, the frozen Phase 11B2 format-2 TSV as `--baseline-tsv`, the current sorted
private-rewrite file, one `--completed-destination` per fully moved owner, and
one `--structural-module` per completed wrapper or aggregate. Phase 12A moves
no authored private declaration, so its rewrite file is header-only. Final
`--mode post` requires all destinations and all 19 reviewed authored-private
name rewrites.

Route-map validation normally belongs to pre mode. Stage and post invocations
omit `--routes` because live `.ilean` files no longer preserve historical
source ranges after extraction. If route validation is deliberately repeated
later, every routed historical module must be supplied through a frozen
pre-migration `.ilean` override with `--ilean HISTORICAL_MODULE=PATH`.

Sort and deduplicate an import-only aggregate mechanically:

```text
python tools/architecture/sort_aggregate_imports.py NumStability/Algorithms.lean --write
```

Check that no architectural debt has increased:

```text
python tools/architecture/check_layout.py
```

In `layout-exceptions.json`, a complete-aggregate contract may use a descendant
prefix string or a nonempty explicit module list. Explicit lists cover curated
umbrellas whose canonical leaves are siblings rather than descendants of the
umbrella module name, and they enforce the aggregate's exact direct-import set.

Check license pointers and evidenced upstream attribution:

```text
python tools/architecture/check_provenance.py
```

The reviewed one-time normalizer for legacy Apache notices is dry-run by
default. `--write` adds the canonical SPDX identifier and license path while
preserving copyright and author lines:

```text
python tools/architecture/normalize_apache_notices.py
python tools/architecture/normalize_apache_notices.py --write
```

`--write-baseline` is a review-only bootstrap/update operation. It records the
exact current legacy exception sets; ordinary CI requires equality so a debt
reduction must update the reviewed baseline and cannot silently regress at the
same path later. Never use it to make an unexplained regression pass.

The layout check also rejects production or test modules containing `sorry`,
`admit`, or top-level `axiom`/`constant` commands. This is a zero-debt gate, not
a grandfathered warning count.

The command builds `NumStability`, then writes matching JSON and Markdown files
under `docs/architecture/baselines/`. The JSON is the machine-readable source
of truth. The Markdown is generated for review.

Useful options:

```text
# Fast source/import-only capture
python tools/architecture/generate_baseline.py --skip-declarations --name source-only

# CI/release guard for unresolved imports, cycles, and classified forbidden edges
python tools/architecture/generate_baseline.py --skip-declarations --strict-source \
  --output-dir benchmark-results/architecture --name source-check

# Reuse already-current .olean files
python tools/architecture/generate_baseline.py --no-build --name YYYY-MM-DD

# Verify that a committed capture is reproducible
python tools/architecture/generate_baseline.py --check --name YYYY-MM-DD

# Retain the large raw dependency stream for separate analysis
python tools/architecture/generate_baseline.py \
  --keep-dependency-tsv benchmark-results/architecture/dependencies.tsv \
  --name YYYY-MM-DD

# Re-render from a previously retained raw stream
python tools/architecture/generate_baseline.py \
  --dependency-tsv benchmark-results/architecture/dependencies.tsv \
  --name YYYY-MM-DD
```

The raw TSV is kept below the ignored `benchmark-results/` tree by default. It
can contain hundreds of thousands of edges and is an intermediate
representation, not a stable data format.

Check mode compares the production-source SHA-256, source/import metrics,
compiled declaration metrics, Lean toolchain, and Mathlib revision. The digest
normalizes UTF-8 BOMs and CRLF/CR line endings so Windows and Linux checkouts
agree. Check mode ignores
capture-time Git fields such as `HEAD`, branch, and dirty-path provenance,
which necessarily change when a generated report is committed. It separately
requires the committed Markdown to be the exact rendering of the committed
JSON.

## Metric definitions

The import graph contains an edge `A -> B` when module `A` directly imports
module `B`.

The semantic declaration graph contains an edge `A -> B` when the elaborated
signature, body, or proof of authored declaration `A` reaches authored project
declaration `B` through zero or more excluded compiler-generated project
details. Signature and body/proof edges are retained separately. An edge
appearing in both sets is counted once in the union graph.

- An **apparent leaf** has no incoming project declaration edge.
- A **project-foundational declaration** has no outgoing project declaration
  edge.
- A **project-isolated declaration** has neither incoming nor outgoing project
  declaration edges.
- **Cross-module utilization** is the fraction of public declarations that at
  least one project declaration in another module directly references.
- **Weak-component coverage** forgets edge direction and measures undirected
  connectedness. It does not measure reuse.

For the report, a declaration is classified as public when its Lean name is
neither private nor an internal-detail name. Generated recursors and
constructors remain visible in the raw population and are reported by kind.

These diagnostics identify review candidates. They are not dead-code tests,
and their percentages are not optimization targets.

## Tier audit

The generator also reads
[`docs/architecture/tiers.json`](../../docs/architecture/tiers.json). It reports
classification coverage, a tier-to-tier import matrix, and direct/transitive
`reusable -> source` / `reusable -> mixed` violations. The manifest is
complete: every production module is classified, coverage is 100%, and no
`mixed` modules remain, so the physical-target gate's precondition holds and
a zero violation count is conclusive; see
[`docs/architecture/TIERS.md`](../../docs/architecture/TIERS.md).
