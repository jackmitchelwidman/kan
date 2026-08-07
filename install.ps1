# Kan installer for Windows — downloads a prebuilt kan.exe. No OCaml required.
#
#   irm https://raw.githubusercontent.com/jackmitchelwidman/kan/main/install.ps1 | iex
#
# Environment overrides:
#   $env:KAN_VERSION     install a specific tag (default: latest release)
#   $env:KAN_INSTALL_DIR install location (default: %LOCALAPPDATA%\Kan\bin)

$ErrorActionPreference = 'Stop'
$repo = 'jackmitchelwidman/kan'

$asset = 'kan-windows-x86_64.exe'
$installDir = if ($env:KAN_INSTALL_DIR) { $env:KAN_INSTALL_DIR } else { Join-Path $env:LOCALAPPDATA 'Kan\bin' }

if ($env:KAN_VERSION) {
  $url = "https://github.com/$repo/releases/download/$($env:KAN_VERSION)/$asset"
} else {
  $url = "https://github.com/$repo/releases/latest/download/$asset"
}

New-Item -ItemType Directory -Force -Path $installDir | Out-Null
$dest = Join-Path $installDir 'kan.exe'

Write-Host "Downloading $asset ..."
try {
  Invoke-WebRequest -Uri $url -OutFile $dest -UseBasicParsing
} catch {
  Write-Error "Download failed: $url`n(If no release exists yet, ask the maintainer to push a tag, or build from source.)"
  exit 1
}

Write-Host ""
Write-Host "Installed kan -> $dest"

# Add the install dir to the user PATH if it isn't already there.
$userPath = [Environment]::GetEnvironmentVariable('Path', 'User')
if (($userPath -split ';') -notcontains $installDir) {
  [Environment]::SetEnvironmentVariable('Path', "$userPath;$installDir", 'User')
  Write-Host ""
  Write-Host "Added $installDir to your PATH. Open a NEW terminal, then try:"
} else {
  Write-Host ""
  Write-Host "You're ready. Try:"
}
Write-Host "  kan run examples\tutorial.kan"
