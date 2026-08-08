# W11 private-declaration reverse closure

W11 contains exactly three private declarations.  They remain in their
historical modules under their original private names; none is moved or
renamed:

1. `_private.NumStability.Algorithms.RandNLA.HitCountConcentration.0.NumStability.sqMagTraceProbMass_two_point_factor`
2. `_private.NumStability.Algorithms.RandNLA.RowSamplingGram.0.NumStability.rowSqNormTraceProbMass_two_point_factor`
3. `_private.NumStability.Algorithms.RandNLA.UniformRowSampling.0.NumStability.uniformRowTraceProbMass_two_point_factor`

The deterministic command graph contains 3,086 whole source commands.  Reverse
closure from those three seeds retains 225 commands and leaves 2,861 command
move candidates.  Because each retained command has one selected declaration,
the closure also accounts for exactly 225 selected declarations.

| Private seed family | Historical owners in closure | Retained commands / declarations |
| --- | --- | ---: |
| Hit-count | `HitCountConcentration` (3), `ElementwiseSpectral` (17) | 20 |
| Row-Gram | `RowSamplingGram` (23), `RowSamplingLeverage` (2), `LeastSquaresSketch` (8) | 33 |
| Uniform-row | `UniformRowSampling` (10), `UniformRowSamplingComposition` (1), `Preconditioning` (66), `UniformRowSamplingFP` (95) | 172 |
| **Total** | nine declaration-bearing historical owners | **225** |

`PRIVATE_CLOSURE.tsv` records every command span, decision, closure depth, and
typed witness edge.  Its retained payload (ordered by historical owner and
source span, with a trailing newline) has SHA-256:

`FAD5DC5D7CD80112157031E012D32593FBF33ACED6C1B9F94D60DEC55D1EA7F9`

`CHECK_STATIC.py` independently requires the exact three seed roots, 3,086 /
225 / 2,861 command counts, per-owner agreement with `RETENTION.tsv`, and this
payload hash.  The generated historical facades are then compiled directly by
the 18 old-path-only tests and by three focused private-closure tests.
