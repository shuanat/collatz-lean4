/-
Paper-Code Mapping for collatz-lean4 proof-closure chain.
-/

namespace Collatz.Documentation

/-!
## Canonical Theorem Chain

`D.1 -> {E.2, F.6/F.7, G.5} -> H.main -> I.1`

## Lean Modules Used In Chain

- D.1 support:
  - `Collatz/Epochs/APStructure.lean`
  - `Collatz/Epochs/Homogenization.lean`
  - `Collatz/Epochs/NumeratorCarry.lean`
- E.2 support:
  - `Collatz/SEDT/Core.lean`
  - `Collatz/SEDT/Theorems.lean`
- F.6/F.7 support:
  - `Collatz/Mixing/PhaseMixing.lean`
  - `Collatz/Mixing/TouchFrequency.lean`
  - `Collatz/Mixing/Semigroup.lean`
- G.5 support:
  - `Collatz/Epochs/LongEpochs.lean`
- H.main support:
  - `Collatz/CycleExclusion/Main.lean`
- I.1 support:
  - `Collatz/Convergence/MainTheorem.lean`

## CI Guardrails

The workflow checks that chain modules contain neither `sorry` nor `axiom`.
-/

end Collatz.Documentation
