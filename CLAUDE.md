# Collatz Lean4 - Formal Verification

## Technology Stack

- **Lean 4** theorem prover
- **Lake** package manager
- **Mathematical proofs** in formal logic

## Project Structure

```
Collatz/
├── Convergence/           # Convergence proofs
├── CycleExclusion/        # Cycle exclusion proofs
├── Epochs/                # Epoch structure
├── SEDT/                  # SEDT formalization
└── Documentation/        # Lean documentation
```

## Key Commands

- `lean --run`: Run Lean verification
- `lake build`: Build project
- `lake test`: Run tests

## Important Files

- `Collatz.lean`: Main module
- `lakefile.lean`: Project configuration
- `lean-toolchain`: Lean version

## Development Notes

- Formal mathematical proofs
- Dependent type theory
- Proof automation where possible
- Integration with paper proofs

## Verification Goals

- Formalize SEDT theorem
- Prove convergence properties
- Verify cycle exclusion
- Bridge with paper mathematics
