# R07 projection replay

P0010 is active against C0005. Its deterministic gzip graph has SHA-256
`BFAF298CE8BFB295552D48C04DF8D74DD717A2EBAA701E396C9651C798671F97`
and size 8,718 bytes. The decompressed format-2 payload has SHA-256
`27313A98B70A8BFEC7F6DF1F2CBE796D4B420A03EE91D7BF136E8AF4F93E8A90`
and size 158,181 bytes.

The projection selects 194 declarations and freezes 243 signature edges and 752
body edges (775 distinct union edges). Its checker contract permits exactly 75
modules, no prefix allowance, and a total 44-row private-normalization map.
`CHECK_PROJECTION.py` substitutes only the generated candidate format-2 graph,
hash-pins that candidate during the replay, and requires the exact expected
counts from the official checker. It also requires the full graph census of
56,903 declarations in 1,713 declaration-bearing modules, with exactly 266,387
signature, 382,872 body, and 424,082 union edges.

The normal public root intentionally does not import R07's three private-only
internal notation leaves. A `NumStability`-only extraction therefore reports
56,900 declarations even though all 649,259 typed edges are already present.
The missing declarations are exactly the zero-project-edge private definitions
owned by:

- `NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Internal.HermitianEuclideanSpaceNotation`;
- `NumStability.Analysis.LinearOperators.NumericalRadius.Core.Internal.EuclideanSpaceNotation`;
- `NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal.ScalarNotation`.

They remain absent from public umbrellas, compatibility rows, and historical
wrappers. For analysis only, the delivery checker copies the official extractor
to a temporary directory outside the checkout and replaces its single loader
array with exactly `NumStability` plus those three modules. The official source
is immutable and hash-pinned at
`04AE8E46F66A0B8D2FED1FDB83904D8A60398F9B61A3EC4A10ADB3DF2352D771`;
the official baseline generator is hash-pinned at
`AD1B19090B75936C874E6762989E4F06C0C1434C7DC7078E13499570BA3B6A63`.
The exact temporary four-root extractor bytes are independently pinned at
`A13D69B60F899E39D75DF050518E57C1A05406CE18718ED7D84381D56EAC53BD`.
No production source, import, root aggregate, shared tool, or supported API is
changed by this analysis-only loader closure.

The final candidate is materialized only after the worker tree and all four
compiled roots are final:

```text
python -B docs/architecture/deliveries/R07/CHECK_PROJECTION.py --control-root <activated-control-checkout> --materialize-candidate
```

Materialization is accepted only while the worker remains at exact base
`ad92bbfae62d538f3e52829a269a846688a8e213`. After the immutable delivery
commit, the same checker is replay-only and accepts only that base's sole child;
it cannot rewrite the capture metadata or candidate hashes.

The candidate is fixed to `benchmark-results/R07-candidate.tsv` in the R07
worker checkout. The adjacent generated `R07-candidate.json` and
`R07-candidate.md` are part of its provenance evidence. All three artifacts
must be nonempty, ignored, untracked, unstaged regular files. The delivery
checker rejects another path or checkout, verifies the JSON reports format 2
with the exact declaration/module/edge census, verifies the three additional
private definitions have no incident project edges, and regenerates the same
four-root TSV in a temporary directory on every replay. That Lean-emitted TSV
must match the fixed candidate byte-for-byte. The adjacent JSON and Markdown
are checked with the official baseline generator rather than byte-compared to a
fresh capture, because their informational Git metadata legitimately changes
when the immutable delivery commit is created. It then performs this official
source-tree/declaration regeneration check:

```text
python -B tools/architecture/generate_baseline.py --no-build --dependency-tsv benchmark-results/R07-candidate.tsv --output-dir benchmark-results --name R07-candidate --check
```

That replay recomputes the current worker source graph and requires
`source.source_tree_sha256` to equal the final reviewed R07 source-tree digest
`0F1DD883F3157535D059D3E7F60D80DDDC27638C0C34D926ADA5F0DFD6F5417A`
before the exact P0010 checker contract is executed. The extraction roots,
extractor and generator hashes, TSV/JSON/Markdown paths, sizes and hashes,
source-tree hash, and exact declaration/module/edge totals are printed on
success for transfer to `GATE_RESULTS.tsv`.

The final four-root candidate generated from the worker tree has this exact
evidence:

- TSV: 117,168,449 bytes, SHA-256
  `07A3213243A770AE68C1DB76C7A9F120E65FDCDD00ADBFDCB354B785E5171376`;
- JSON: 100,858 bytes, SHA-256
  `0C8D7E653CD6EEAE7768AE7D6AE2DB97DCC593EF64E1D7C82CA37BD56B19D181`;
- Markdown: 20,413 bytes, SHA-256
  `5954EF0D2EC443788316FACC74FE4CEE96E846503C4B75BC62D7741BEB59DB8D`;
- source tree:
  `0F1DD883F3157535D059D3E7F60D80DDDC27638C0C34D926ADA5F0DFD6F5417A`;
- census: 56,903 declarations in 1,713 modules, 266,387 signature edges,
  382,872 body edges, and 424,082 union edges.

The base-only materialization transcript has SHA-256
`A5B346057844216FF9F1F0DC19BBE86BCF4AA370326ECE906CF5115462AAD88D`.
The independent deterministic replay transcript has SHA-256
`71936608D60B62C3084ED4BFA881D3C58A384AD1321C161428A5306024607AA7`.
