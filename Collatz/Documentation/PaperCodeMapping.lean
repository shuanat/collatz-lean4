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
  - `Collatz/Epochs/Core.lean` (touch residue, AP-step period `Q_t`, finite-window touch bounds)
- E.2 support:
  - `Collatz/SEDT/Core.lean`
  - `Collatz/SEDT/Theorems.lean`
  - W3 hardened interface: explicit envelope/negativity inequalities and
    threshold-driven period-sum contracts (no vacuous `: True` statements)
- F.6/F.7 support:
  - `Collatz/Mixing/PhaseMixing.lean`
  - `Collatz/Mixing/TouchFrequency.lean`
  - `Collatz/Mixing/Semigroup.lean`
  - W4 hardened interface: explicit semigroup closure/generation,
    phase-periodicity recurrence, finite-window touch discrepancy bounds,
    and mixing-to-SEDT envelope bridge (no vacuous `: True` statements)
- G.5 support:
  - `Collatz/Epochs/LongEpochs.lean`
- H.main support:
  - `Collatz/CycleExclusion/Main.lean`
- I.1 support:
  - `Collatz/Convergence/MainTheorem.lean`

## CI Guardrails

The workflow checks that chain modules contain neither `sorry` nor `axiom`.
W2 hardening additionally enforces non-vacuous D-level statements in epoch semantics modules
(`Epochs/Core`, `Epochs/APStructure`, `Epochs/Homogenization`, `Epochs/NumeratorCarry`, `Epochs/LongEpochs`).
W4 hardening extends this with non-vacuous F-level contracts in
`Mixing/Semigroup`, `Mixing/PhaseMixing`, and `Mixing/TouchFrequency`.
-/

end Collatz.Documentation
