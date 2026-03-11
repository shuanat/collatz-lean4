# Semantic Hardening Plan (D.1 -> I.1)

## Goal

Replace compile-safe placeholders with mathematically meaningful Lean proofs across the production chain:

- no `axiom`
- no `sorry`
- no proxy theorem statements of the form `: True`

## Scope

Production proof chain files:

- `Collatz/Foundations/Core.lean`
- `Collatz/Epochs/Core.lean`
- `Collatz/Epochs/APStructure.lean`
- `Collatz/Epochs/Homogenization.lean`
- `Collatz/Epochs/NumeratorCarry.lean`
- `Collatz/Epochs/LongEpochs.lean`
- `Collatz/SEDT/Core.lean`
- `Collatz/SEDT/Theorems.lean`
- `Collatz/Mixing/Semigroup.lean`
- `Collatz/Mixing/PhaseMixing.lean`
- `Collatz/Mixing/TouchFrequency.lean`
- `Collatz/CycleExclusion/CycleDefinition.lean`
- `Collatz/CycleExclusion/PeriodSum.lean`
- `Collatz/CycleExclusion/PureE1Cycles.lean`
- `Collatz/CycleExclusion/MixedCycles.lean`
- `Collatz/CycleExclusion/RepeatTrick.lean`
- `Collatz/CycleExclusion/Main.lean`
- `Collatz/Convergence/Coercivity.lean`
- `Collatz/Convergence/FixedPoints.lean`
- `Collatz/Convergence/NoAttractors.lean`
- `Collatz/Convergence/MainTheorem.lean`

## Workstreams

### W1. Foundations Hardening

Target:

- Replace proxy definitions (`OddPred`, simplified `collatz_step`, etc.) with canonical forms.
- Prove foundational arithmetic and parity lemmas needed by all downstream modules.

Done criteria:

- Core definitions match paper-level intent.
- No theorem/lemma in this file uses `: True`.
- Downstream files can import these lemmas without introducing local stubs.

### W2. Epoch Semantics (D.1 + G.5 prerequisites)

Target:

- Replace synthetic epoch quantities (`p_touch`, `long_epoch_density`, etc.) with derivable definitions.
- Formalize AP structure, homogenization, and numerator carry lemmas with exact hypotheses.

Done criteria:

- D-level lemmas are real statements with executable hypotheses/conclusions.
- Long-epoch machinery has a mathematically interpretable statement that can feed SEDT/mixing.

### W3. SEDT Core (E.2)

Target:

- Remove proxy numeric constants and bind them to explicit assumptions/derived bounds.
- Replace placeholder bounds and witness-only proofs with inequalities used in subsequent modules.

Done criteria:

- `SEDT/Core` and `SEDT/Theorems` expose theorem statements that correspond to paper E.2 objects.
- No placeholder existential witnesses (`⟨-1, by norm_num⟩` style) remain unless mathematically intended.

### W4. Mixing Layer (F.6/F.7)

Target:

- Formalize semigroup and phase-mixing statements as actual measure/frequency bounds.
- Connect touch-frequency and mixing conclusions to SEDT inputs.

Done criteria:

- F.6/F.7 equivalent statements are explicit and consumed by H-level modules.
- No vacuous proofs.

### W5. Cycle Exclusion (H.main)

Target:

- Replace `False`-based proxy predicates for cycle properties with real definitions.
- Prove exclusion via period-sum and repeat-trick arguments over those real predicates.

Done criteria:

- `Cycle.is_pure_e1`, `Cycle.is_nontrivial`, and related notions are semantically meaningful.
- `Main.lean` excludes nontrivial cycles from proven premises, not from definitional falsity.

### W6. Convergence Closure (I.1)

Target:

- Strengthen coercivity/fixed-point/no-attractor modules to formal implications.
- Derive global convergence theorem from hardened D/E/F/G/H stack.

Done criteria:

- `Convergence/MainTheorem.lean` theorem statement corresponds to I.1 and depends only on proven lemmas.

### W7. CI and Acceptance

Target:

- Keep existing no-`sorry`/no-`axiom` gate.
- Add semantic gate that rejects vacuous theorem signatures in production chain.

Done criteria:

- CI fails on new `: True` theorem declarations in production files.
- `lake build Collatz` passes in CI and locally.

## Execution Order

1. W1 Foundations
2. W2 Epoch semantics
3. W3 SEDT core
4. W4 Mixing
5. W5 Cycle exclusion
6. W6 Convergence
7. W7 CI hardening

## Risk Notes

- Tight coupling between W2, W3, and W4 can cause theorem churn; stabilize interfaces early.
- Avoid introducing new broad axiomatizations; prefer local assumptions and explicit parameter records.
- Keep theorem names stable where possible to reduce cross-file rewrite overhead.
