Write-Host "====================================================" -ForegroundColor Cyan
Write-Host "  THETA0PHOTON: LEAN 4 COMPILATION AUDIT          " -ForegroundColor Cyan
Write-Host "====================================================" -ForegroundColor Cyan

Write-Host "[1/2] Compiling Lean 4 targets with pinned toolchain..." -ForegroundColor Yellow
lake build

if ($LASTEXITCODE -eq 0) {
    Write-Host "`n[2/2] Build SUCCESSFUL: zero compilation errors." -ForegroundColor Green
} else {
    Write-Host "`n[ERROR] Lean 4 build failed with exit code $LASTEXITCODE" -ForegroundColor Red
    exit 1
}
