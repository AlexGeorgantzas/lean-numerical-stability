# Chapter 9 format-2 migration contract (preparation only)

**Implementation status: `BLOCKED_ON_BLOCKLU_INTEGRATION`.**

This directory prepares the Chapter 9 semantic split. It creates no canonical
production module, moves no declaration, rewrites no proof, edits no import, and
adds no wrapper. Everything here is frozen at base
`6487fc33088523b8f27ecde9ad613515b78f9977` and derived from the packaged
immutable format-2 stream `baseline/parallel-base-declarations-v2.zip`.

## What "format 2" means here

The packaged baseline is a tab-separated stream that begins `format 2` and whose
rows are

```text
declaration   <logical_name>   <module>   <kind>   <visibility>
edge          signature|body   <source>   <target>
```

Signature edges and body/proof edges are loaded, compared, and hashed
separately at every step, because they answer different questions: signature
edges are conceptual API coupling, body edges are implementation coupling.
"Format 2" is that stream contract — it is *not* an instruction to rename the
route or ownership TSV headers, which keep the repository's existing
`docs/architecture/declaration-ownership/` schema.

## Artifacts

| File | Rows | Content |
| --- | --- | --- |
| `routes.tsv` | 36 range routes | complete, non-overlapping line routing of all 11 candidate files |
| `ownership.tsv` | 4,420 | every baseline declaration mapped to exactly one destination |
| `owner-dag.tsv` | 453 | the expected destination graph, signature and body edges kept distinct |
| `direct-imports.tsv` | 252 | the planned exact direct imports per destination |
| `private-rewrites.tsv` | 28 | one reviewed private-name rewrite per private declaration |
| `downstream-consumers.tsv` | 29 | every direct production, test, and example consumer of the 11 historical modules |
| `acceptance.json` | — | frozen counts, normalized hashes, required gates, blocked status |

Frozen totals: 11 candidate modules, 35 declaration-bearing destinations,
4,420 declarations (28 private), 20,081 signature edges, 26,737 body edges,
and 4,108 authored declaration groups across the candidates (3,745 of them in
`HighamChapter9.lean` alone).

## Mathematical seams

`HighamChapter9.lean` is 113,809 lines and already declares its own seams: 53
`/-! ## ... -/` section blocks that follow the book. The contract routes along
exactly those seams rather than inventing new ones, merging only adjacent
blocks that belong to the same numbered result:

- §9.1–§9.5, §9.8, §9.10, §9.11 → `Section01`…`Section11`, with §9.6 split into
  `Section06.SpecialClasses` and `Section06.Tridiagonal` because the file itself
  separates the special tridiagonal classes from the general tridiagonal
  development;
- the displayed growth-factor witnesses → `Equation12`, `Equation13`, and
  `Equation14` (the Hadamard determinant foundation plus its Hadamard-matrix
  growth application, which are adjacent and inseparable);
- the rook-pivoting/Foster development → `Equation16`;
- Bohte's tridiagonal growth analysis → `Theorem11.BohteBandOne` (the `p = 1`
  case) and `Theorem11.BohteGeneral` (general bandwidth plus the comparison
  matrix);
- Appendix A and in-chapter problems → `Problem02`, `Problem05`–`Problem08`,
  `Problem11`, `Problem13`, and `Problem14.RowReversal`, with `Problem14.FirstMethod` for the
  §9.9 first-method development the file gives its own subsection.

The ten satellite closure modules are routed whole-file, each to the numbered
result it closes: `Theorem03.DoolittleClosure`, `Theorem05.ComputedCorrection`,
`Theorem07.Classification`, `Theorem09.Closure`, `Theorem09.ComplexClosure`,
`Theorem14.Actual`, `Theorem14.CompletePivotSharp`,
`Theorem14.DiagonallyDominant`, `Theorem14.Primitive`, and `ComplexDomain` for
the Theorems 9.8–9.11 complex-domain closure, which spans several numbered
results and therefore takes a plain semantic leaf name.

Every destination owns **one contiguous region of one historical module**. That
is not cosmetic: because Lean requires a declaration to precede its uses inside
a file, contiguity makes the destination dependency graph acyclic by
construction, and the checker proves acyclicity independently for the signature
graph, the body graph, and their union.

`Section11` (1,109 declarations) and `Problem06` (667) are the two largest
destinations. They are the natural candidates for a second-level split in a
later wave; this contract deliberately routes at the granularity of the seams
the source itself declares rather than guessing finer ones.

## Compatibility policy

- All 11 historical paths survive as **exact import-only compatibility
  wrappers**. `routes.tsv` keeps lines 1–37 of `HighamChapter9.lean` — its
  imports and module docstring — routed to the historical module itself, so the
  facade retains its historical import surface.
- Public names, namespaces, signatures, bodies, proofs, visibility, licences,
  and historical import paths are preserved. No proof cleanup, rename,
  visibility change, or shim removal is proposed.
- Lean private names encode their owning module and therefore *must* change.
  `private-rewrites.tsv` records all 28 rewrites explicitly as
  `logical → historical actual → candidate actual`; only those reviewed
  rewrites may be normalized during the post-migration full-graph comparison.
- 29 direct consumer rows cover the 11 historical modules: the
  `NumStability.Algorithms` aggregate, `HighamChapters1To9SourceClosure`, the
  Chapter 10/11/14/15 consumers, and `examples/LibraryLookup.lean`. No
  pre-existing test module imports a Chapter 9 candidate directly; the
  historical test surface reaches them through the `NumStability.Algorithms`
  aggregate. This lane's own isolated smoke modules under
  `NumStabilityTest/Worker/ClassificationAudit/` are deliberately **excluded**
  from the consumer table: it records the impact surface the integrator must keep
  working, not this lane's evidence. The integrator wires global root tests.

## Dependency order

1. **BlockLU/Chapter 13 must land first.** `HighamChapter9.lean` imports
   `NumStability.Algorithms.LU.BlockLU` and `NumStability.Algorithms.LU.GrowthFactor`,
   both owned by the integrator's BlockLU wave
   (`KNOWN_CROSS_LANE_EDGES.tsv`, `CH9_TO_BLOCKLU`). Chapter 9 may not be
   released before BlockLU/Chapter 13 is merged and globally verified.
2. **The import contract is provisional until that refresh.** Evidence: the
   declaration-level references of the Chapter 9 candidates resolve into the
   *already canonical* BlockLU leaves
   (`…LinearSystems.LU.BlockLU.BlockMatrices`, `…BlockLU.PositiveDefinite`) and
   never into the historical `Algorithms.LU.BlockLU` module. So the BlockLU wave
   changes Chapter 9's **imports** while leaving its declaration bodies and its
   26 referenced external owners unchanged. `direct-imports.tsv` is therefore
   correct in semantic content and provisional in spelling until the integrator
   refreshes `HighamChapter9.lean` against the accepted checkpoint. See
   `../REFRESH-APPENDIX.md`.
3. **Then Chapter 9, then Chapter 11.** Chapter 11 has real Chapter 9
   dependencies and is marked `BLOCKED_ON_CH09_INTEGRATION` in `../ch11/`.
   Chapter 9 and Chapter 11 must never be scheduled as parallel waves.
4. Within Chapter 9, implement destinations in `owner-dag.tsv` topological
   order; `direct-imports.tsv` gives each destination's exact import list, and
   the checker requires that list to equal the set of owners its declarations
   actually reference — no more and no less.

## Gates

```console
python tools/architecture/lane_claude_classification/check_ch09_contract.py --self-test
python tools/architecture/lane_claude_classification/check_ch09_contract.py --mode pre \
    --baseline-zip <packet>/baseline/parallel-base-declarations-v2.zip
```

`--mode pre` proves: exact route coverage with no gap or overlap; every command
group inside exactly one route; ownership complete, unique, and exactly equal to
the baseline declaration set; kind and visibility preserved against the
baseline; one reviewed rewrite per private declaration with a changed candidate
name; the signature, body, and combined destination graphs acyclic; planned
imports exactly equal to referenced owners and never a historical facade; the
tracked artifacts byte-identical to their deterministic derivation; and the
frozen `acceptance.json` still exact.

`--mode stage` and `--mode post` are documented and deliberately refuse to run
in this lane: they require a freshly generated candidate format-2 stream for a
migrated tree. Stage mode compares the candidate stream against
`normalized_hashes` with routes applied but wrappers not yet removed; post mode
requires exact declaration ownership, signatures, and typed-graph equality after
only the reviewed private-owner normalization in `private-rewrites.tsv`. The
integrator runs both after the BlockLU checkpoint lands and the wave is
implemented. This lane must not fabricate that evidence.

## Reconciliation note

`origin/main` has since advanced past the frozen base and already contains a
completed Chapter 9 physical split (20 canonical destinations, 4,420
declarations, 4,108 command groups, 28 private declarations, 11
declaration-free historical facades). The declaration, command-group, and
private-declaration totals in this contract match that landed wave exactly,
which cross-validates the extraction; the destination granularity does not (35
finer destinations here versus 20 there). This contract is the frozen-base
proposal it was scoped to be — the integrator reconciles it against integrated
`main`. See `../REFRESH-APPENDIX.md`.
