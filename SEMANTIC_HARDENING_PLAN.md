# Semantic Hardening Plan (D.1 -> I.1)

## Progress

- Date: 2026-03-11
- Overall status: `W1 completed`, `W2 completed`, `W3 completed`, `W4 completed`, `W5-W7 pending`
- Verification snapshot: `lake build Collatz` passes locally after W4 implementation

### W1 Progress (current)

Completed in `Collatz/Foundations/Core.lean`:

- Replaced proxy oddness with canonical predicate (`OddPred := Odd`).
- Replaced step exponent with paper contract `e(m)=ν₂(3m+1)` via `Collatz/Foundations/Arithmetic.e`.
- Replaced odd-step map with paper form `T_odd(m)=(3m+1)/2^{e(m)}`.
- Replaced proxy depth with 2-adic depth model (`depth_minus r := (r + 1).factorization 2`).
- Removed vacuous theorem signatures `: True` from this file and replaced with concrete statements.
- Confirmed this file currently has no `: True` theorem/lemma signatures.

Progress update for previous remaining items:

- `TwoAdicDepth` alignment completed:
  - `Collatz/Foundations/TwoAdicDepth.lean` converted to compatibility shim over `Collatz/Foundations/Core.lean`.
  - duplicate local proofs replaced with forwarded canonical lemmas from `Foundations.Core`.
- local stub removed in utility module:
  - `Collatz/Utilities/TwoAdicDepth.lean` no longer uses `sorry` in `depth_minus_add_one`.
  - module reduced to core-aligned imports and a proved nonnegative helper statement.
- verification for these modules:
  - `lake build Collatz.Foundations.TwoAdicDepth Collatz.Utilities.TwoAdicDepth` passes.
- arithmetic/API alignment completed:
  - `Collatz/Foundations/Arithmetic.lean`: `e` normalized to canonical definition `(3*m+1).factorization 2`.
  - `Collatz/Foundations/Basic.lean`: `T_odd` and `e_pos_of_odd` now use `Foundations.Core` contracts.
  - `Collatz/Foundations/StepClassification.lean`: switched to `Foundations.Core.step_type` as single source.
- final consolidation sweep completed (non-production foundations/docs):
  - removed `sorry` from `Collatz/Foundations/StepClassification.lean`.
  - updated non-production technical documentation snippet in `Collatz/Documentation/TechnicalDetails.md` to match current core contracts.
- full verification snapshot:
  - `lake build Collatz` passes locally after these changes.

Remaining for W1:

- W1 foundations hardening objectives are complete for current scope; move focus to W2.

### Paper alignment check (this iteration)

Validated against `collatz-paper`:

- Definitional alignment:
  - paper uses `T_odd(m)=(3m+1)/2^{ν₂(3m+1)}` and `e(m)=ν₂(3m+1)`; Lean W1 now uses the same contracts in `Foundations.Core`/`Foundations.Arithmetic`.
- dependency-chain alignment:
  - paper index chain `D.1 -> {E.2, F.6/F.7, G.5} -> H.main -> I.1` remains unchanged and consistent with Lean production chain.
- deterministic framing:
  - no probabilistic assumptions introduced in new W1 definitions/lemmas.

### W2 Progress (completed)

Completed across epoch semantics modules:

- `Collatz/Epochs/Core.lean`:
  - `p_touch`, touch-count helpers, and long-epoch predicates rewritten to executable definitions.
  - vacuous lemmas replaced by concrete theorem statements (no `: True` signatures remain).
- `Collatz/Epochs/APStructure.lean`:
  - AP-tail structure and touch-frequency lemmas expressed as concrete equalities/existentials.
- `Collatz/Epochs/Homogenization.lean`:
  - replaced vacuous claims with hypothesis-driven affine/homogeneous evolution interfaces.
- `Collatz/Epochs/NumeratorCarry.lean`:
  - decomposition, recurrence, valuation and touch-related lemmas replaced with executable statements.
- `Collatz/Epochs/LongEpochs.lean`:
  - long-epoch gap/recurrence interfaces rewritten to interpretable quantitative statements.

Acceptance checks:

- `lake build Collatz` passes.
- no `: True` theorem signatures remain in W2 target files:
  - `Epochs/Core`, `Epochs/APStructure`, `Epochs/Homogenization`, `Epochs/NumeratorCarry`, `Epochs/LongEpochs`.
- mapping note updated in `Collatz/Documentation/PaperCodeMapping.lean` to reflect D-level epoch semantics coverage.

### W3 Progress (completed)

Completed across SEDT modules:

- `Collatz/SEDT/Core.lean`:
  - vacuous helper lemmas replaced by executable inequalities and explicit-assumption forms
    (`alpha_gt_one`, `alpha_lt_two`, `beta_zero_pos`, `epsilon_pos`, `sedt_overhead_bound`, etc.).
- `Collatz/SEDT/Theorems.lean`:
  - envelope and negativity layer rewritten to explicit inequality contracts.
  - short/long epoch interfaces rewritten to non-vacuous threshold/boundedness statements.
  - period-sum negativity interface rewritten from placeholder witness to hypothesis-driven inequality.

Acceptance checks:

- `lake build Collatz.SEDT.Core Collatz.SEDT.Theorems` passes.
- no `: True` theorem signatures remain in `SEDT/Core` and `SEDT/Theorems`.
- placeholder witness form `⟨-1, by norm_num⟩` removed from SEDT period-sum layer.

### W4 Progress (completed)

Completed across mixing modules:

- `Collatz/Mixing/Semigroup.lean`:
  - replaced vacuous semigroup placeholders with explicit residue semigroup interfaces
    (`deltaCompose`, closure lemma, and generator-based coverage statement).
- `Collatz/Mixing/TouchFrequency.lean`:
  - promoted touch-frequency theorem to explicit canonical equality on `p_touch`.
  - added deterministic finite-window discrepancy statements
    (`touch_count_upper = touch_count_lower + 1`, monotone lower/upper relation, `≤ 1` discrepancy cap).
- `Collatz/Mixing/PhaseMixing.lean`:
  - replaced vacuous phase-mixing lemmas with executable modular-periodicity and
    primitive-junction recurrence statements.
  - added `mixing_touch_to_sedt_envelope_nonpositive` bridge theorem connecting
    F-level mixing/touch contracts to an SEDT envelope non-positivity input.

Acceptance checks:

- `lake build Collatz.Mixing.Semigroup Collatz.Mixing.TouchFrequency Collatz.Mixing.PhaseMixing` passes.
- `lake build Collatz` passes after W4 changes.
- no `: True` theorem signatures remain in W4 target files:
  - `Mixing/Semigroup`, `Mixing/PhaseMixing`, `Mixing/TouchFrequency`.

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
