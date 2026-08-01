# Chapter 19 compatibility-metadata closure

Date: 2026-08-01

Base: `298f57e88d4d83ace07151587dffebd1ac0637df`

Status: **LOCAL_POST_PASS; remote CI pending at the delivery commit**.

## Scope

The completed QR/Chapter 19 declaration migration left 42 historical
`NumStability.Algorithms.QR.Higham19*` files as declaration-free, one-import
forwarders, but those files were still unclassified. This checkpoint closes
that metadata gap without moving or changing any declaration.

The exact 42-row old-to-canonical map is
`docs/architecture/declaration-ownership/qr-ch19-compatibility-closure.tsv`.
Including its header, the LF-terminated artifact has 43 lines and SHA-256
`183FDADB38C07931840561B459A9576476D02FFE39E1CFA255E81CFDA5B583C5`.

For each row:

- the historical file contains exactly one canonical import and no Lean code;
- the old and canonical paths already have direct smoke-test imports;
- `tiers.json` now classifies the old path as `compatibility`;
- `COMPATIBILITY.md` records the exact imported target; and
- production consumers use the canonical target, never the historical path.

The production-import normalization removed the 42 historical imports from
the broad `NumStability.Algorithms` aggregate and replaced seven imports in six
source-facing consumers with their identical canonical targets. Declaration
bodies and public names are unchanged.

## Ratchet improvement

| Metric | Before | After |
|---|---:|---:|
| Classified modules | 933 (67.122%) | 975 (70.144%) |
| Unclassified modules | 457 | 415 |
| Compatibility modules | 254 | 296 |
| Documented compatibility targets | 524 | 566 |
| Legacy naming exceptions | 318 | 276 |
| Missing module documentation | 206 | 206 |
| Mixed modules | 0 | 0 |
| Forbidden reusable-to-source/mixed reachable pairs | 0 | 0 |

This is a compatibility and dependency-metadata closure, not a new physical
declaration migration and not repository-wide completion.

## Validation

The following passed on the resulting local tree:

- `python tools/architecture/check_layout.py`;
- `python tools/architecture/check_compatibility.py` (296 wrappers, 566 direct
  targets, no production use of a historical path);
- `python tools/architecture/check_provenance.py`;
- `python tools/architecture/generate_baseline.py --skip-declarations
  --strict-source --output-dir benchmark-results/ci-architecture --name source`
  (zero import cycles and zero forbidden reachable pairs);
- `lake build NumStability NumStabilityTest` (5,540 build targets); and
- `lake test` (5,719 test targets).

Existing linter warnings were non-fatal. The delivery commit must pass the
tracked GitHub Lean CI workflow before it is accepted as the next phase base.
