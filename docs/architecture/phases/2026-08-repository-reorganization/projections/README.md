# Lane baseline projections

Each live branch references one active projection tied to the current accepted
checkpoint's combined format-2 baseline. A projection freezes the exact
historical declarations and typed edges selected for that wave, together with
its checker and expected counts. It is superseded whenever the checkpoint or
selected ownership contract changes.

[`P0001`](P0001.json) is active for W01 at checkpoint C0001. Its deterministic
gzip freezes 3,697 declarations and all 48,076 incident union edges across the
four selected owners. Workers compare a fresh full format-2 candidate against
that hash-pinned graph with the recorded checker arguments.

From a clean `main` control checkout, this PowerShell sequence creates the
recorded worker branch and runs the exact projection gate. Acquire the shared
Lean lock first: the extractor performs `lake build NumStability` so a fresh
machine has the complete olean closure, even if focused worker builds passed:

```powershell
$controlRoot = (Resolve-Path .).Path
$workerRoot = Join-Path (Split-Path $controlRoot -Parent) 'reorg-w01-worker'
git fetch origin main
git worktree add -b codex/reorg-2026-08-w01-fp-boundary $workerRoot d6e643adf0f20b33f7faebce7e1b9b1f87122c58

$leanMutex = [System.Threading.Mutex]::new($false, 'Local\lean-reorganization-2026-08')
$lockHeld = $false
try {
  try {
    $lockHeld = $leanMutex.WaitOne([TimeSpan]::FromHours(3))
  } catch [System.Threading.AbandonedMutexException] {
    $lockHeld = $true
  }
  if (-not $lockHeld) { throw 'Timed out waiting for the Lean build lock.' }
  Push-Location $workerRoot
  try {
    python tools/architecture/generate_baseline.py --output-dir benchmark-results/W01-candidate-summary --name W01-candidate --keep-dependency-tsv benchmark-results/W01-candidate.tsv
    if ($LASTEXITCODE -ne 0) { throw "Candidate extraction failed with exit code $LASTEXITCODE." }
  } finally {
    Pop-Location
  }
} finally {
  if ($lockHeld) { $leanMutex.ReleaseMutex() }
  $leanMutex.Dispose()
}

python (Join-Path $controlRoot 'tools/architecture/check_phase_projection.py') `
  --projection (Join-Path $controlRoot 'docs/architecture/phases/2026-08-repository-reorganization/projections/P0001.tsv.gz') `
  --projection-sha256 6278CE1673465F9069A01A9D7FF5005223209E28533BC0F13DB4B90E82042352 `
  --candidate (Join-Path $workerRoot 'benchmark-results/W01-candidate.tsv') `
  --allow-module NumStability.Analysis.CancellationOfRoundingErrors `
  --allow-module NumStability.Analysis.FloatingPointArithmetic `
  --allow-module NumStability.Analysis.IncreasingPrecision `
  --allow-module NumStability.Analysis.InstabilityWithoutCancellation `
  --allow-prefix NumStability.Analysis.FloatingPointArithmetic. `
  --allow-prefix NumStability.Source.Higham.Chapter01.FloatingPointArithmetic. `
  --allow-prefix NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.
```

If the branch already exists locally or remotely, do not create an auxiliary
branch: fetch it into the recorded worktree after verifying that it descends
from the recorded base SHA.
