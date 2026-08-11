# Executable forward/reverse replay of the R02 integrator request in a DISPOSABLE
# C0000 checkout. Creates the checkout, applies the postimage, verifies, reverses,
# verifies restoration, then removes the checkout. Nothing outside it is touched.
param([string]$Mode = 'both')
$ErrorActionPreference = 'Stop'
$BASE = 'b1b18772d80185ec08f49c818919558645c330a1'
$REPO = 'C:\Users\qed_s\OneDrive\Documents\QED 94'
$SP   = 'C:\Users\qed_s\AppData\Local\Temp\claude\C--Users-qed-s-OneDrive-Documents-QED-94\a3d8791c-13d8-4c40-b7e4-93d35467467d\scratchpad\r02'
$DISP = Join-Path $env:TEMP "r02-c0000-replay"
$paths = @(
 'NumStability/Algorithms/NormEstimation/PNorm/All.lean',
 'NumStability/Algorithms/NormEstimation/PNorm/Rectangular/RectangularTermination.lean',
 'NumStability/Source/Higham/Chapter15/Lemma02/PNormPowerMethod/PNormRectangular.lean',
 'NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/ConvergenceStatements.lean',
 'NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/RectangularTermination.lean')

if (Test-Path $DISP) { git -C $REPO worktree remove --force $DISP 2>$null; cmd /c "rd /s /q `"$DISP`"" 2>$null }
git -C $REPO worktree add --detach $DISP $BASE | Out-Null
Write-Output "disposable C0000 checkout: $DISP at $(git -C $DISP rev-parse HEAD)"

function Hashes { foreach ($p in $paths) { "{0}  {1}" -f (git -C $DISP hash-object $p), $p } }
Write-Output "`n-- preimage blobs --"; Hashes

if ($Mode -in @('forward','both')) {
  foreach ($p in $paths) { Copy-Item (Join-Path $SP ("postimage\" + ($p -replace '/','__'))) (Join-Path $DISP ($p -replace '/','\')) -Force }
  Write-Output "`n-- FORWARD applied; postimage blobs --"; Hashes
  $refs = 0; foreach ($p in $paths) { $refs += (Select-String -Path (Join-Path $DISP ($p -replace '/','\')) -Pattern 'PNorm\.Endpoints\.' -AllMatches | Measure-Object).Count }
  Write-Output "residual PNorm.Endpoints references after forward: $refs   (expect 0)"
}
if ($Mode -in @('reverse','both')) {
  foreach ($p in $paths) { Copy-Item (Join-Path $SP ("postimage\REVERSE__" + ($p -replace '/','__'))) (Join-Path $DISP ($p -replace '/','\')) -Force }
  Write-Output "`n-- REVERSE applied; restored blobs --"; Hashes
  $dirty = (git -C $DISP status --porcelain | Measure-Object).Count
  Write-Output "disposable checkout dirty entries after reverse: $dirty   (expect 0 = exact C0000 restoration)"
}
git -C $REPO worktree remove --force $DISP 2>$null
Write-Output "`ndisposable checkout removed"
