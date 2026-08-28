# NumStability

NumStability is a Lean 4 library for machine-checked floating-point error
analysis and numerical stability. It provides reusable foundations for rounding
error, summation, perturbation analysis, matrix computations, and numerical
algorithms, together with source-facing formalizations from Nicholas J.
Higham's *Accuracy and Stability of Numerical Algorithms* (2nd ed.).

The core model is abstract: an `FPModel` supplies rounded arithmetic operations,
a nonnegative unit roundoff, and the operation laws used by each theorem. This
supports reusable mathematical analysis without claiming that every result is a
bit-level IEEE-754 verification.

## Install as a Lake dependency

Add the package to a downstream `lakefile.toml`:

```toml
[[require]]
name = "numStability"
git = "https://github.com/AlexGeorgantzas/lean-numerical-stability"
rev = "higham_v01"
```

For a reproducible project, replace the branch name with the immutable release
tag or commit recorded for the benchmark snapshot.

NumStability currently pins Lean `4.29.0-rc3` in [`lean-toolchain`](lean-toolchain)
and Mathlib commit `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` in
[`lakefile.toml`](lakefile.toml). A downstream project must use a compatible Lean
and Mathlib environment.

Start with a narrow import:

```lean
import NumStability.FloatingPoint.Model

open NumStability

#check FPModel
#check FPModel.exactWithUnitRoundoff
```

`import NumStability` remains available as a compatibility entry point, but it
loads the complete supported tree. Narrow imports are preferable for discovery
and compilation.

## Entry points

| Import | Purpose |
|---|---|
| `NumStability.Core` | Small foundation for floating-point models and error analysis |
| `NumStability.FloatingPoint` | Floating-point foundations and IEEE-facing utilities |
| `NumStability.Analysis` | Analysis, perturbation, norms, probability, and error bounds |
| `NumStability.Algorithms` | Numerical algorithm families |
| `NumStability.Source` | Source-specific theorem and equation correspondence |
| `NumStability.Source.Higham` | Higham chapter correspondence |
| `NumStability.All` | Complete supported library surface |
| `NumStability` | Compatibility entry point forwarding to `NumStability.All` |

Historical import paths retained for compatibility remain available through
forwarding modules. New code should use the narrow semantic imports above.

## Build locally

Install Git and [elan](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get
lake build NumStability
lake env lean docs/LibraryLookupChecks.lean
```

The final command keeps the lookup guide's representative imports and public
declaration names compiler-checked.

## Documentation

- [`docs/LIBRARY_LOOKUP.md`](docs/LIBRARY_LOOKUP.md) is the detailed declaration
  and module lookup guide.
- [`docs/LibraryLookupChecks.lean`](docs/LibraryLookupChecks.lean) checks the
  representative imports and public declarations used by the lookup guide.

## Repository layout

```text
NumStability.lean                   complete-tree compatibility entry point
NumStability/
  Core.lean                        small reusable foundation
  All.lean                         complete supported surface
  FloatingPoint/                   floating-point models and operation laws
  Analysis/                        reusable analysis and error bounds
  Algorithms/                      numerical algorithms
  Source/                          source-facing correspondence
  Upstream/                        attributed adapted or backported code
docs/
  LIBRARY_LOOKUP.md                human-readable module and declaration guide
  LibraryLookupChecks.lean         executable checks for documented API paths
```

## License

The repository-level license is MIT. Files carrying an explicit Apache-2.0
notice remain governed by that license; see [`LICENSES/`](LICENSES/) and
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).
