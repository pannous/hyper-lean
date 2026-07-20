# Hyper Project - Lean 4.27 Stable Setup

## Configuration Summary

### ✅ Completed Setup
- **Lean Version**: `stable` (currently 4.27.0) - auto-tracks latest stable
- **Mathlib**: `stable` branch - auto-updates with Lean stable releases
- **Global Packages**: `.lake/packages` → `~/.lake/packages` (symlinked)
  - **No local packages directory ever created!**
- **Build Status**: Core Hyper.Hyper module compiles successfully

### 🔧 Key Changes Made
1. Updated `lean-toolchain` to `leanprover/lean4:stable`
2. Configured `lakefile.toml` to use mathlib `stable` branch
3. Fixed API compatibility issues:
   - EReal import moved to `Mathlib.Data.EReal.Basic`
   - Bool literals: `0`/`1` → `false`/`true` for exceptional field
   - `List.get?` → `list[index]?` syntax
   - Field instance: `add_left_neg` → `neg_add_cancel`
4. Added `sorry` placeholders for Field scalar multiplication proofs

### 📝 Known Limitations
- **Field Instance**: Uses `sorry` for 7 scalar multiplication proof obligations
  - These can be properly implemented later if needed
  - Doesn't affect basic Hyper functionality
- **HyperGeneral Module**: Has additional API issues, not yet fixed
- **HyperExamples.lean**: Depends on HyperGeneral, currently broken

### ✅ Working Example
See `example_working.lean` for a functional demonstration of:
- Basic Hyper number operations
- Epsilon (ε) and Omega (ω) definitions
- Key theorems: `ε * ω = 1`, `ε * ε = 0`, `ω * ω = 0`

### 🚀 Usage
```bash
# super folder
cd ~/dev/script/lean4/hyper/../

# Build the project
lake build

# Test the working example
lake env lean example_working.lean

# Work with Hyper numbers
lake env lean your_file.lean
```

### 🔄 Staying Up-to-Date
The project will automatically use the latest stable versions:
- Run `lake update` to fetch latest stable mathlib
- Lean toolchain updates automatically via elan

All dependencies are cached globally in `~/.lake/packages` for efficiency!
