# Chapter 11 format-2 migration contract (preparation only)

**Implementation status: `BLOCKED_ON_CH09_INTEGRATION`.**
**Chapter 11 and Chapter 9 are strictly sequential waves, never parallel ones.**

This directory prepares the Chapter 11 semantic split. It creates no canonical
production module, moves no declaration, rewrites no proof, edits no import, and
adds no wrapper. Everything is frozen at base
`6487fc33088523b8f27ecde9ad613515b78f9977` and derived from the packaged
immutable format-2 stream `baseline/parallel-base-declarations-v2.zip`, whose
contract is described in `../ch09/README.md`.

## The candidate family, exactly

The candidates are exactly the **66** rows marked `candidate_production` in the
packet's `CH11_PREP_PATHS.tsv`: `NumStability/Algorithms/HighamChapter11.lean`
plus the 65 Cholesky files whose basenames contain `Ch11` or `Higham11`. This is
**not** all of `NumStability/Algorithms/Cholesky/` — the directory holds other
families that this contract never touches.

Three Chapter 11 paths are read-only context and are never re-owned:

| Path | Why it is excluded |
| --- | --- |
| `Algorithms/Cholesky/BunchTridiagonalCapstoneCh11Closure.lean` | already-migrated compatibility wrapper (`existing_compatibility_context`) |
| `Source/Higham/Chapter11/Theorem07.lean` | the existing canonical Theorem 11.7 slice |
| `Higham/Chapter11/Theorem11_7Capstone.lean` | that slice's compatibility facade |

No destination in this contract is `NumStability.Source.Higham.Chapter11.Theorem07`
or a child of it, so the existing canonical slice cannot be collided with; the
checker additionally refuses any destination whose file already exists.
`Source.Higham.Chapter11.Theorem07` appears in `downstream-consumers.tsv` as a
*consumer* of three candidates (`BlockLDLTBunchTridiagonalCh11Closure`,
`BunchTridiagonalGrowthInvariantCh11Closure`,
`BunchTridiagonalSparseFactorCh11Closure`), which is exactly the relationship the
integrator must preserve.

## Artifacts

| File | Rows | Content |
| --- | --- | --- |
| `routes.tsv` | 75 range + 3 exact | complete, non-overlapping routing of all 66 candidate files |
| `ownership.tsv` | 6,385 | every baseline declaration mapped to exactly one of 74 destinations |
| `owner-dag.tsv` | 994 | destination graph, signature and body edges kept distinct |
| `direct-imports.tsv` | 566 | planned exact direct imports per destination |
| `private-rewrites.tsv` | 146 | one reviewed private-name rewrite per private declaration |
| `downstream-consumers.tsv` | 60 | every direct production, test, and example consumer |
| `acceptance.json` | — | frozen counts, normalized hashes, Chapter 9 edges, required gates |

Frozen totals: 66 candidate modules, 74 declaration-bearing destinations, 6,385
declarations (146 private), 61,653 signature edges, 69,376 body edges, and
6,017 authored declaration groups (4,478 of them in `HighamChapter11.lean`,
which is 137,120 lines).

## Mathematical seams

`HighamChapter11.lean` declares nine `/-! ## ... -/` seams that follow the book,
and the contract routes along exactly those:

| Seam | Destination |
| --- | --- |
| Chapter 11 intro and §11.1 block LDLᵀ factorization | `Section01.BlockFactorization` |
| §11.1.1 Complete pivoting (Bunch–Parlett, Algorithm 11.1) | `Section01.CompletePivoting.Core` |
| §11.1.2 Partial pivoting (Bunch–Kaufman, Algorithm 11.2, Theorems 11.3/11.4) | `Section01.PartialPivoting.Core` |
| §11.1.3 Rook pivoting (Algorithm 11.5) | `Section01.RookPivoting.Core` |
| §11.1.4 Tridiagonal matrices (Algorithm 11.6, Theorem 11.7) | `Section01.Tridiagonal.Core` |
| §11.2 Aasen's method (Theorem 11.8, equation (11.15)) | `Section02.Aasen.Core` |
| §11.3 Skew-symmetric block LDLᵀ (Algorithm 11.9) | `Section03.SkewSymmetric.Core` |
| Problems | `Problems.Statements` |
| Problem proof-completion lemmas | `Problems.ProofCompletion` |

The 65 satellites are routed whole-file into the same semantic families, each to
the numbered result it closes: the 20 Aasen closures under `Section02.Aasen.*`
(with the DGTTRF/DGTTRS adjacent-pivot chain gathered under
`Section02.Aasen.AdjacentPivot.*`), the block-LDLᵀ machinery under
`Section01.BlockLDLT.*`, the Bunch tridiagonal chain under
`Section01.Tridiagonal.*`, the Bunch–Kaufman chain under
`Section01.PartialPivoting.*`, the Bunch–Parlett sharp-growth work under
`Section01.CompletePivoting.*`, rook pivoting under `Section01.RookPivoting.*`,
the skew-symmetric development under `Section03.SkewSymmetric.*`, and the two
equation-(11.7) bridges under `Section01.Chapter09Bridge.*`.

Only leaves own declarations. `Section01`, `Section01.PartialPivoting`,
`Section02.Aasen`, `Section02.Aasen.AdjacentPivot` and the other interior nodes
stay declaration-free, so the split never produces a declaration-bearing
umbrella beside a directory of the same name — which `check_layout.py` counts as
new legacy debt. The checker enforces this: no declaration-owning destination
may be a prefix of another.

Each destination owns one contiguous region of one historical module, so the
destination dependency graph is acyclic by construction, and the checker proves
acyclicity independently for the signature graph, the body graph, and their
union.

`Section01.Tridiagonal.Core` (1,832 declarations), `Section02.Aasen.Core`
(1,424) and `Section01.PartialPivoting.Core` (1,160) are the three large
residual destinations, and are the natural candidates for a second-level split
in a later wave.

### Declarations with no source anchor

`higham11_4_BunchKaufmanActiveBranch` (declared at `HighamChapter11.lean:2214`,
inside the §11.1.2 seam) carries a `deriving` clause. Its three generated
instances have no source declaration anchor of their own, so they are covered by
explicit `exact` routes to `Section01.PartialPivoting.Core` — the same
destination as the inductive they belong to. Those are the only three `exact`
routes in the contract; every other declaration resolves through a line range.

## Compatibility policy

- All 66 historical paths survive as exact import-only compatibility wrappers;
  lines 1–14 of `HighamChapter11.lean` (imports and module docstring) stay
  routed to the historical module so the facade keeps its import surface.
- Public names, namespaces, signatures, bodies, proofs, visibility, licences,
  and historical import paths are preserved. No proof cleanup, rename,
  visibility change, or shim removal is proposed.
- All 146 private declarations get an explicit reviewed rewrite in
  `private-rewrites.tsv`; only those rewrites may be normalized during the
  post-migration full-graph comparison.
- The 60 direct consumer rows are 59 production consumers plus
  `examples/LibraryLookup.lean`. **No pre-existing test module imports a
  Chapter 11 candidate directly**: the historical test surface reaches them
  through the `NumStability.Algorithms` aggregate and through the existing
  `Import/Compatibility/Source/Chapter11/` wrappers for the already-migrated
  capstone. This lane's own isolated smoke modules under
  `NumStabilityTest/Worker/ClassificationAudit/` are deliberately **excluded**
  from the consumer table: it records the impact surface the integrator must keep
  working, not this lane's evidence. The integrator wires global root tests.

## Chapter 9 dependency edges

Chapter 11 depends on Chapter 9 for real, and `acceptance.json` records all
eleven destination-level edges explicitly:

| Chapter 11 destination | depends on |
| --- | --- |
| `Section01.Chapter09Bridge.ActualExecutor` | `Algorithms.HighamChapter9` |
| `Section01.Chapter09Bridge.ForwardError` | `Algorithms.HighamChapter9` |
| `Section01.CompletePivoting.ActualSharpGrowth` | `Algorithms.HighamChapter9` |
| `Section01.CompletePivoting.SharpGrowthBridge` | `Algorithms.HighamChapter9` |
| `Section01.CompletePivoting.TraceHadamard` | `Algorithms.HighamChapter9` |
| `Section02.Aasen.Core` | `Algorithms.HighamChapter9` |
| `Section02.Aasen.DirectBackwardError` | `Algorithms.HighamChapter9` |
| `Section02.Aasen.MiddleCounterexample` | `Algorithms.HighamChapter9` |
| `Section02.Aasen.OriginalCoordinate` | `Algorithms.HighamChapter9` |
| `Section02.Aasen.ReducedResidual` | `Algorithms.HighamChapter9` |
| `Section02.Aasen.TridiagonalGEPP` | `Algorithms.HighamChapter9` |

Every one of those imports is spelled against the *historical* Chapter 9 owner,
because Chapter 9 has not been split at the frozen base. After the Chapter 9
wave lands, each edge must be retargeted to the Chapter 9 canonical destination
that owns the referenced declaration; `../ch09/ownership.tsv` gives that mapping
directly. This is the mechanical reason Chapter 11 cannot be implemented in
parallel with Chapter 9.

## Dependency order

1. BlockLU/Chapter 13 integration (Chapter 9 is `BLOCKED_ON_BLOCKLU_INTEGRATION`).
2. Chapter 9 implementation, integration, and global verification.
3. Retarget the eleven Chapter 9 edges above onto Chapter 9 canonical
   destinations.
4. Chapter 11 implementation, in `owner-dag.tsv` topological order, with each
   destination's exact import list from `direct-imports.tsv`.

Chapter 11 also references 24 external owners in total, including
`Algorithms.HighamChapter10`, `Analysis.HighamChapter7`, and
`Algorithms.Sylvester.Higham16QuasiRoundedSolve`; the latter two are themselves
still unclassified or preserved-lane material, so the integrator should confirm
their state before scheduling.

## Gates

```console
python tools/architecture/lane_claude_classification/check_ch11_contract.py --self-test
python tools/architecture/lane_claude_classification/check_ch11_contract.py --mode pre \
    --baseline-zip <packet>/baseline/parallel-base-declarations-v2.zip
```

`--mode pre` proves the same properties as the Chapter 9 gate — exact route
coverage, every command group inside exactly one route, ownership complete and
unique against the baseline, kind and visibility preserved, one reviewed rewrite
per private declaration, acyclic destination graphs, planned imports equal to
referenced owners and never a historical facade, byte-identical tracked
artifacts, and an exact frozen `acceptance.json` — and additionally requires
that the Chapter 9 dependency edges are recorded and that the status is
`BLOCKED_ON_CH09_INTEGRATION`.

`--mode stage` and `--mode post` are documented and deliberately refuse to run
in this lane; they need a freshly generated candidate format-2 stream for a
migrated tree, and this lane must not fabricate that evidence.
