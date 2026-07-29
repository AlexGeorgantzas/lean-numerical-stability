# Integrator request: least squares / Chapter 20

Frozen base: `6487fc33088523b8f27ecde9ad613515b78f9977`

Contract repair base: `7d876bc241d46e7192be2acaf46bb148aec76908`

Repair branch: `codex/review-lsq-contract-repair` (local only; never push)

This request supersedes the packet's earlier `INTEGRATOR_REQUEST.md`.  The
authoritative patch set is the machine-readable file
`docs/architecture/declaration-ownership/lsq-ch20-coordinator-patches.tsv`:

- 203 exact rows;
- 94 `COMPATIBILITY.md` mapping edges for the 41 declaration-bearing legacy
  wrappers;
- 44 exact global-tier registrations and 2 prefix registrations;
- 40 historical-import removals and 19 canonical-import additions;
- 1 new aggregate; and
- 3 root-test imports.

Its SHA-256 is
`75E210F086105D5E1C2E61FD974A5022BA2A51FB602C21C6FE3E2DF6AD3FAB63`.
The LSQ post gate reads this file and rejects an integration tree on which any
import, root-test, tier, or compatibility mapping is missing or inexact.

## Required packet replacement

The packet's original `INTEGRATOR_REQUEST.md` is stale and
`scripts/deliver_local.ps1` packages that external file. Before running the
delivery script, replace the packet file byte-for-byte with this tracked file:

```powershell
$lsqRepo = 'C:\Users\qed_s\higham-worktrees\lsq-contract-repair'
$lsqPacket = 'C:\Users\qed_s\OneDrive\Documents\QED 94\.codex\handoffs\four-subscriptions-6487fc33088523b8f27ecde9ad613515b78f9977\03-claude-lsq-ch20'
$trackedRequest = Join-Path $lsqRepo 'docs\architecture\migrations\worker-lsq-ch20-integrator-request.md'
$packetRequest = Join-Path $lsqPacket 'INTEGRATOR_REQUEST.md'
Copy-Item -LiteralPath $trackedRequest -Destination $packetRequest -Force
if ((Get-FileHash -Algorithm SHA256 $trackedRequest).Hash -ne
    (Get-FileHash -Algorithm SHA256 $packetRequest).Hash) {
  throw 'LSQ integrator-request replacement did not verify byte-for-byte'
}
```

The coordinator should perform that external copy only after the follow-up
contract commit is present. This repository commit intentionally does not edit
the packet directory.

## Shared aggregate edits

Apply these exact import changes after the corresponding lane modules exist:

| Module | Action | Import |
| --- | --- | --- |
| `NumStability.Algorithms.LinearSystems` | add | `NumStability.Algorithms.LinearSystems.LeastSquares` |
| `NumStability.Analysis` | add | `NumStability.Analysis.Perturbation` |
| `NumStability.Analysis.Perturbation` | create declaration-free aggregate | `NumStability.Analysis.Perturbation.LeastSquares` |

In `NumStability.Algorithms`, remove its 35 direct
`NumStability.Algorithms.LeastSquares.*` imports and add exactly:

```lean
import NumStability.Algorithms.LinearSystems.LeastSquares
import NumStability.Analysis.Perturbation.LeastSquares
import NumStability.Source.Higham.Chapter20
```

This preserves the historical aggregate's algorithm, analysis, and source
surface without making it import compatibility wrappers.

## Non-lane production consumers

Remove every listed legacy import and add the complete canonical set shown.
The machine-readable patch artifact records each removal and addition
separately.

| Consumer | Remove | Add |
| --- | --- | --- |
| `NumStability.Algorithms.MatrixInversion` | `NumStability.Algorithms.LeastSquares.LSPerturbation` | `NumStability.Analysis.Perturbation.LeastSquares.Wedin` |
| `NumStability.Source.Higham.Chapter14.Section05.SpectralConvergence` | `NumStability.Algorithms.LeastSquares.Higham20Problem20_3` | `NumStability.Source.Higham.Chapter20.Problem03` |
| `NumStability.Algorithms.Underdetermined.UnderdeterminedSolve` | `NumStability.Algorithms.LeastSquares.LSQRSolve` | `NumStability.Algorithms.LinearSystems.LeastSquares.Basic`, `NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry`, `NumStability.Analysis.Perturbation.LeastSquares.Normwise`, `NumStability.Analysis.Perturbation.LeastSquares.Wedin`, `NumStability.Source.Higham.Chapter20.Theorem03.QRSolve` |
| `NumStability.Algorithms.RandNLA.LeastSquaresSketch` | `NumStability.Algorithms.LeastSquares.LSNormalEquations`, `NumStability.Algorithms.LeastSquares.LSQRSolve` | `NumStability.Algorithms.LinearSystems.LeastSquares.Basic`, `NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations`, `NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR`, `NumStability.Analysis.Perturbation.LeastSquares.BackwardError`, `NumStability.Analysis.Perturbation.LeastSquares.Basic`, `NumStability.Analysis.Perturbation.LeastSquares.NormalEquations`, `NumStability.Source.Higham.Chapter20.Theorem03.QRSolve` |

The three preserved Chapter 20 leaves are lane-owned, not coordinator edits.
Their exact final imports are also enforced by the post gate:

| Lane module | Exact canonical LS/Chapter 20 imports |
| --- | --- |
| `NumStability.Source.Higham.Chapter20.Equation32` | `NumStability.Analysis.Perturbation.LeastSquares.Wedin` |
| `NumStability.Source.Higham.Chapter20.Lemma06` | `NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem`, `NumStability.Algorithms.LinearSystems.LeastSquares.Basic`, `NumStability.Source.Higham.Chapter20.Theorem03.QRSolve` |
| `NumStability.Source.Higham.Chapter20.Theorem01` | `NumStability.Analysis.Perturbation.LeastSquares.Wedin`, `NumStability.Source.Higham.Chapter20.Lemma11.Support` |

## Global tiers and compatibility map

Add these prefix rules to `docs/architecture/tiers.json`:

```text
NumStability.Algorithms.LinearSystems.LeastSquares. -> reusable
NumStability.Analysis.Perturbation.LeastSquares.    -> reusable
```

Add exact `aggregate` rows for both reusable umbrellas and for
`NumStability.Analysis.Perturbation`. Add exact `compatibility` rows for all
41 declaration-bearing historical modules. The exact 44 rows are in the patch
artifact. The existing source prefix already classifies all new Chapter 20
leaves, and the existing exact row already classifies the Chapter 20 source
aggregate.

Add one `docs/architecture/COMPATIBILITY.md` table row per historical wrapper.
Group the 94 `compatibility_map` edges by historical module; the resulting 41
rows must name exactly the canonical imports frozen in
`lsq-ch20-structural-imports.tsv`, with no omissions or extras. The post gate
parses the Markdown table and compares those sets exactly.

After the final files and tier rules land, regenerate
`docs/architecture/layout-exceptions.json` with the reviewed layout bootstrap.
Expected lane deltas are 41 fewer unclassified historical modules, 37 fewer
noncanonical-module exceptions, and 10 fewer missing-module-docstring
exceptions; new canonical modules must add no debt.

## Root tests

Add these three direct imports to `NumStabilityTest.lean` in sorted position:

```lean
import NumStabilityTest.Import.Algorithms.LinearSystems.LeastSquares
import NumStabilityTest.Import.Analysis.Perturbation.LeastSquares
import NumStabilityTest.Import.Compatibility.Algorithms.LeastSquares
```

The source aggregate test `NumStabilityTest.Import.Source.Chapter20` is already
root-imported and remains the lane-owned source test umbrella.

## QR cross-lane normalization (mandatory unresolved gate)

`lsq-ch20-cross-lane-normalization.tsv` freezes all 19 LS-to-QR and 4 QR-to-LS
base imports, 4,221 typed declaration edges, and 3 import-only edges. It has
4,224 rows and SHA-256
`056DA202B1D8C3FC6F6ED540B6064D094D89455A43848FBEA175C06DAFE8384F`.

Pre, stage, and post deterministically regenerate all 4,224 base rows from the
hash-pinned semantic stream and compiler-span route/ownership data. They
require the exact row identities and LS destinations. Only an unresolved
`qr_owner`/`status` pair may be replaced by a reviewed canonical QR owner;
truncation, LS-owner substitution, or mutation of an already-stable QR owner
fails before the final import checks.

The QR lane's canonical declaration-owner map is not present at this base.
Therefore 1,628 rows intentionally contain `@QR_OWNER_REQUIRED:*`, covering
68 exact QR declarations plus the import-only
`Higham19Alg12MGSSourceRate` carrier. Do not replace these by guessing one
owner per historical module: a single Higham19 module can split across several
canonical owners. The integrator must fill every row from the QR lane's
machine-readable ownership result. Post mode deliberately fails while even one
placeholder remains.

The four reverse consumers normalize to these known LS targets after their QR
source owners are supplied:

| Historical QR consumer | Required canonical LS imports |
| --- | --- |
| `Higham19Alg12MGSSourceRate` | `NumStability.Source.Higham.Chapter20.Prose.MoorePenrose` (import-only preservation) |
| `Higham19Problem19_10` | `NumStability.Source.Higham.Chapter20.Examples.CrossProduct` |
| `Higham19Theorem5SourceClosure` | `NumStability.Source.Higham.Chapter20.Theorem03.ZeroDeltaB` |
| `Higham19Theorem6ActualSource` | `NumStability.Source.Higham.Chapter20.Theorem07.ActualAssembly`, `NumStability.Source.Higham.Chapter20.Theorem07.ActualClosure`, `NumStability.Source.Higham.Chapter20.Theorem07.ActualTrace` |

Once resolved, the checker verifies each referenced QR declaration actually
lives in the supplied canonical owner, requires every normalized direct import,
and rejects production imports of either LS compatibility wrappers or the
future Higham19 compatibility wrappers.
