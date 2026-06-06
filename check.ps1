# AI Assurance Category-Theoretic Core — Lean verification
# Run from the repository root.

Write-Host "Checking AIAssurance.lean ..." -ForegroundColor Cyan
lake env lean AIAssurance.lean

if ($LASTEXITCODE -eq 0) {
    Write-Host "OK — all theorems verified." -ForegroundColor Green
} else {
    Write-Host "FAILED — see errors above." -ForegroundColor Red
    exit 1
}
