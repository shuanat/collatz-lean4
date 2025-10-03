# Installing Z3 and CVC5 SMT Solvers

## Windows

### Option 1: Chocolatey (Recommended)

```powershell
# Install Chocolatey if not installed
Set-ExecutionPolicy Bypass -Scope Process -Force
[System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072
iex ((New-Object System.Net.WebClient).DownloadString('https://community.chocolatey.org/install.ps1'))

# Install Z3
choco install z3

# Verify installation
z3 --version
```

### Option 2: Manual Download

1. Go to https://github.com/Z3Prover/z3/releases
2. Download `z3-<version>-x64-win.zip`
3. Extract to `C:\Program Files\z3\`
4. Add `C:\Program Files\z3\bin` to PATH

### Option 3: Python Package

```bash
pip install z3-solver
python -c "import z3; print(z3.get_version_string())"
```

## macOS

```bash
# Using Homebrew
brew install z3

# Verify
z3 --version
```

## Linux

```bash
# Ubuntu/Debian
sudo apt-get update
sudo apt-get install z3

# Fedora
sudo dnf install z3

# Verify
z3 --version
```

## CVC5 (Optional, for cross-validation)

### All Platforms

Download from: https://github.com/cvc5/cvc5/releases

```bash
# Linux/macOS
wget https://github.com/cvc5/cvc5/releases/latest/download/cvc5-Linux
chmod +x cvc5-Linux
sudo mv cvc5-Linux /usr/local/bin/cvc5

# Windows: Download cvc5-Win64.exe and add to PATH
```

## Python Dependencies

```bash
pip install pysmt z3-solver
```

## Verification

```bash
# Test Z3
z3 --version

# Test Python binding
python -c "from z3 import *; print('Z3 Python OK')"

# Test CVC5 (if installed)
cvc5 --version
```

## Troubleshooting

### Z3 not found in PATH

**Windows:**
```powershell
$env:Path += ";C:\Program Files\z3\bin"
```

**Linux/macOS:**
```bash
export PATH=$PATH:/usr/local/bin
```

### Python import error

```bash
pip install --upgrade z3-solver pysmt
```

---

## Next Steps

After installation:

```bash
cd scripts/smt
python verify_z3.py
```

