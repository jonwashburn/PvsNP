## P vs NP Project

This repository contains a formal proof attempt for the P vs NP problem using Lean 4 and Recognition Science theory.

### Quick Start

```bash
# Build the entire project
lake build

# Validate project structure (prevents embarrassing issues)
./scripts/validate_project.sh

# Build specific modules
lake build PvsNP.ComplexityClassesEnhanced
lake build PvsNP.Helpers.VerificationComplexity
```

### Project Structure

- `Src/PvsNP.lean` - **Main entry point** (imports all modules)
- `Src/PvsNP/Helpers/VerificationComplexity.lean` - Core complexity definitions
- `Src/PvsNP/ComplexityClassesEnhanced.lean` - P and NP class definitions
- `Src/RecognitionScience.lean` - Recognition Science framework

### Validation & Testing

**Before pushing changes, always run:**
```bash
./scripts/validate_project.sh
```

This catches common issues like:
- Empty root file (causes `lake build` to not compile your code)
- Missing `verification_complexity` definition
- Broken imports and dependencies
- Basic compilation errors

### Build Optimization

The project is configured for optimal build performance:
- Parallel compilation (`-j 8`)
- Build caching enabled
- Release mode builds
- Mathlib caching via CI

### CI/CD

GitHub Actions automatically:
- Validates project structure
- Tests core module compilation  
- Checks for undefined symbols
- Prevents broken builds from reaching main

### Recognition Science Theory

This project implements a formal proof of P ≠ NP using Recognition Science, a parameter-free framework based on:
- Eight foundational axioms
- Golden ratio constraints  
- Information-theoretic bounds
- Octave completion principles

### Contributing

1. Always run `./scripts/validate_project.sh` before committing
2. Ensure `lake build` compiles successfully
3. New definitions should be properly imported in root file
4. Test individual modules with `lake build ModuleName`
