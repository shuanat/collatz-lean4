/-
Proof roadmap for collatz-lean4.
-/

namespace Collatz.Documentation

/-!
## Closed Chain

`D.1 -> {E.2, F.6/F.7, G.5} -> H.main -> I.1`

## Module Order

1. Foundations core
2. Epoch D-level modules
3. SEDT E-level modules
4. Mixing F-level modules
5. Long-epochs G-level module
6. Cycle exclusion H-level modules
7. Convergence I-level modules

## Acceptance

- `lake build Collatz` passes.
- CI chain gate rejects `sorry`/`axiom` in theorem-chain files.
-/

end Collatz.Documentation
