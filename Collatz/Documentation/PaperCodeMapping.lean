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
  - W5 hardened interface: semantic cycle predicates (`is_valid_cycle`,
    `is_trivial`, `is_nontrivial`, `is_pure_e1`, `is_mixed`) and
    explicit `main_cycle_exclusion` / `no_nontrivial_cycles`
    period-repeat exclusion layer (no `False`-based proxies)
- I.1 support:
  - `Collatz/Convergence/MainTheorem.lean`
  - W6 unconditional-closure pass (in progress): orbitwise stream/cofinal
    coercivity interfaces are strengthened and wired into the periodic/aperiodic
    split; the epoch-side `A.REC/A.LONG` phase-return-to-long-gap bridge is now
    internalized canonically, and periodic-tail handling is refactored to a
    structured orbit witness (`period = 1` fixed-point branch vs `period > 1`
    H-level bridge). The remaining scientific risk is now localized below the
    canonical-gap level: one real `E.2` lemma for a single aligned phase-return
    pair with SEDT-long separation, plus drift control on the filler segment up
    to the next canonical left index. Even that single-gap lemma is now split
    into an `SEDT`-native orbit-segment drift theorem and a separate
    normalization-correction control. The old arbitrary-segment formulations
    (`sedt_potential_change_of_phase_return_segment` and
    `sedt_potential_change_of_gap_long_multiple_segment`) are now understood as
    arithmetic idealizations rather than the honest local paper target. Lean now
    exposes the paper-faithful assembly theorem
    `potential_change_le_sedt_envelope_of_local_bounds`, the canonical
    selected-segment witness `phase_return_epoch_accounting_witness`, and now an
    explicit epoch-semantic bridge object
    `Epochs.SelectedLongEpochBridge`. Lean now also exposes the constructor
    `Epochs.selected_long_epoch_bridge_of_semantics`, so the selected-epoch
    bridge itself is reduced to exact lower semantic witnesses. In the current
    Lean state, modulo-`Q_t` phase data, local log compression, and
    finite-window touch-count packaging are already internalized below the
    bridge. Lean now also exposes a theorem-driven carry chain below that
    bridge: a paper-faithful D.1/E.1 package
    `Epochs.SelectedPaperCarryArguments` produces
    `Epochs.SelectedDepthBookkeepingBridgeSemantics`, which collapses to
    `Epochs.SelectedCarryDepthSemantics`, then canonically to
    `Epochs.SelectedMultibitCarryWitness`, which `LongEpochs` consumes
    internally. So the bridge no longer asks for a prebuilt carry/depth object;
    it asks only for explicit paper-side portrait/carry arguments. Lean now also
    exposes the direct local theorem
    `Epochs.selected_depth_from_bonus_bound_canonical_of_paper_arguments`, so
    those same paper-faithful arguments already imply the canonical
    `selected_multibit_gain_budget - length` depth inequality before any higher
    aperiodic packaging. The same normal form is now also exposed directly from
    `Epochs.SelectedCarryDepthSemantics` via
    `Epochs.selected_depth_from_bonus_bound_canonical_of_depth_semantics`, so
    the final carry-side residual can now be attacked at the smallest stable
    selected-pair depth interface rather than only through full paper carry
    aperiodic packaging. On the
    coercivity side, Lean now also exposes an honest normalization chain:
    `Convergence.phase_return_endpoint_nonincrease` feeds
    `Convergence.phase_return_potential_correction_nonpositive` via the local
    arithmetic lemma
    `Convergence.potential_change_correction_nonpositive_of_end_le_start`.
    The filler side is likewise repaired so that
    `Convergence.phase_return_gap_fill_step_drift` is witness-indexed and only
    the wrapper `Convergence.phase_return_gap_fill_bridge` quantifies over all
    phase-return witnesses. The weak index-only skeleton
    `Convergence.aperiodic_orbit_has_cofinal_gap_long_phase_returns` is now
    treated explicitly as only that: a phase-aligned return skeleton, not yet an
    honest canonical aperiodic witness. Lean therefore now exposes a repaired
    semantic witness object
    `Convergence.CanonicalAperiodicPhaseReturnWitness`, together with the
    localized bridge
    `Epochs.SelectedLongEpochBridgeOn` and its constructor
    `Epochs.selected_long_epoch_bridge_on_of_semantics`, so the actual selected
    segments are carried on one fixed witness rather than through broad
    `∀ hphase` interfaces. The endpoint side is now repaired to the honest
    correction-level target
    `Convergence.phase_return_potential_correction_nonpositive_on`, while the
    filler side is pushed up to the already reassembled canonical-gap theorem
    `Convergence.canonical_phase_return_gap_step_sedt_on`. Lean now also
    exposes the actual aperiodic semantic package
    `Convergence.CanonicalAperiodicPhaseReturnSemantics`, the constructor
    `Convergence.canonical_aperiodic_phase_return_witness_of_semantics`, and the
    actual-skeleton carry constructor
    `Convergence.canonical_aperiodic_carry_paper_of_depth_semantics`, so the
    repaired witness can be produced theorem-first from semantics on the
    concrete aperiodic skeleton itself. This repaired semantic package/witness
    now also carries the witness-level filler endpoint-order content required by
    the stream normalization branch, rather than leaving it only as an external
    wrapper. Lean now also exposes the exact
    actual-skeleton theorem sources
    `Convergence.canonical_aperiodic_selected_long_epoch_bridge_on`,
    `Convergence.canonical_aperiodic_selected_carry_depth_semantics`,
    `Convergence.canonical_aperiodic_phase_return_correction_nonpositive_on`,
    and
    `Convergence.canonical_aperiodic_phase_return_gap_step_sedt_on`, together
    with the constructor
    `Convergence.canonical_aperiodic_phase_return_semantics_of_theorem_sources`.
    Moreover, the residual content is now pushed one layer lower in theorem
    form: `Convergence.selected_carry_depth_semantics_of_selected_long_epoch_witness`
    and
    `Convergence.canonical_aperiodic_selected_long_epoch_bridge_on_of_selected_long_epoch_bridge`,
    `Convergence.canonical_aperiodic_selected_long_epoch_bridge_on_of_carry_paper`
    and
    `Convergence.canonical_aperiodic_selected_long_epoch_bridge_on_of_depth_semantics`
    and
    `Convergence.canonical_aperiodic_selected_long_epoch_bridge_on_of_phase_return_semantics`
    produce the actual-skeleton selected-long-epoch bridge from honest
    selected-pair semantics. Lean now also exposes
    `Convergence.canonical_aperiodic_carry_paper_of_selected_long_epoch_bridge_on`
    and
    `Convergence.canonical_aperiodic_phase_return_epoch_accounting_witness_of_selected_long_epoch_bridge_on`,
    so the actual selected-long-epoch bridge can be pushed back down to
    paper-faithful `carryPaper` data and forward to local E.1/E.2 accounting on
    the same canonical aperiodic skeleton. Lean now also exposes the still lower
    actual-skeleton target
    `Convergence.canonical_aperiodic_selected_portrait_enumeration_semantics`,
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_semantics`,
    `Convergence.canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics`
    and the constructors
    `Convergence.canonical_aperiodic_selected_portrait_enumeration_semantics_of_depth_bookkeeping_bridge`,
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_semantics_of_depth_bookkeeping_bridge`,
    `Convergence.canonical_aperiodic_selected_portrait_enumeration_semantics_of_carry_paper`,
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_semantics_of_carry_paper`,
    `Convergence.canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_carry_paper`,
    `Convergence.canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_return_semantics`,
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_semantics_of_phase_return_semantics`,
    `Convergence.canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_phase_return_semantics`,
    `Convergence.canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry`,
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_budget_source`,
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_semantics_canonical_of_budget_source`,
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_semantics_of_depth_semantics`,
    `Convergence.canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_phase_geometry_and_depth_semantics`,
    `Convergence.canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_portrait_and_depth_from_bonus`
    and
    `Convergence.canonical_aperiodic_selected_carry_depth_semantics_of_depth_bookkeeping_bridge_semantics`,
    so the carry side is now reduced all the way to the selected-segment
    portrait/depth bridge layer. In particular, portrait enumeration on the
    canonical aperiodic skeleton is now already forced by the built-in
    modulo-`Q_t` phase geometry, leaving only the canonical dependent
    depth-from-bonus target
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_semantics_canonical`
    as the last genuinely semantic lower carry target. Thus
    `Convergence.canonical_aperiodic_selected_carry_depth_semantics_of_selected_long_epoch_bridge_on`
    and
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_semantics_canonical_of_selected_long_epoch_bridge_on`
    as well as the more local
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_semantics_canonical_of_carry_paper`,
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_budget_source_of_carry_paper`,
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_budget_source_of_phase_return_semantics`,
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_budget_source_of_selected_long_epoch_bridge_on`,
    and
    `Convergence.canonical_aperiodic_selected_depth_from_bonus_semantics_canonical_of_phase_return_semantics`
    reduces the carry-depth source to that actual selected-long-epoch bridge on
    the concrete aperiodic skeleton. On the `E.2` side,
    `Convergence.canonical_aperiodic_orbit_epoch_sedt_envelope`,
    `Convergence.canonical_aperiodic_orbit_long_epoch_stream`,
    `Convergence.canonical_aperiodic_orbit_epoch_local_accounting_semantics`,
    `Convergence.canonical_aperiodic_orbit_epoch_native_sedt_semantics`,
    `Convergence.canonical_aperiodic_orbit_epoch_correction_nonpositive`,
    `Convergence.canonical_aperiodic_orbit_epoch_endpoint_nonincrease`,
    `Convergence.canonical_aperiodic_phase_return_fill_endpoint_nonincrease`,
    `Convergence.canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_witness`,
    `Convergence.canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_phase_return_semantics`,
    `Convergence.canonical_aperiodic_phase_return_fill_stepwise_nonincrease`,
    `Convergence.canonical_aperiodic_phase_return_fill_stepwise_bridge`,
    `Convergence.canonical_aperiodic_phase_return_fill_candidate_promotion_semantics`,
    `Convergence.canonical_aperiodic_phase_return_fill_next_left_minimality_semantics`,
    `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_promotion_semantics`,
    `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_semantics`,
    `Convergence.canonical_aperiodic_phase_return_fill_candidate_selection_semantics_of_canonical_next_left_phase_compatibility_and_minimality`,
    `Convergence.canonical_aperiodic_phase_return_fill_candidate_selection_semantics_of_promotion_and_minimality`,
    `Convergence.canonical_aperiodic_phase_return_fill_candidate_selection_semantics`,
    `Convergence.canonical_aperiodic_phase_return_fill_candidate_exclusion_bridge`,
    `Convergence.canonical_aperiodic_phase_return_fill_candidate_exclusion_bridge_of_selection_semantics`,
    `Convergence.canonical_aperiodic_phase_return_fill_no_simple_step_bridge`,
    `Convergence.canonical_aperiodic_phase_return_fill_no_simple_step_bridge_of_candidate_exclusion_bridge`,
    `Convergence.canonical_aperiodic_phase_return_fill_complex_step_bridge`,
    `Convergence.canonical_aperiodic_phase_return_fill_complex_step_bridge_of_no_simple_step_bridge`,
    `Convergence.canonical_aperiodic_phase_return_fill_step_type_two_bridge`,
    `Convergence.canonical_aperiodic_phase_return_fill_step_type_two_bridge_of_complex_step_bridge`,
    `Convergence.canonical_aperiodic_phase_return_fill_stepwise_bridge_of_step_type_two_bridge`,
    `Convergence.canonical_aperiodic_phase_return_fill_stepwise_nonincrease_of_step_type_two_bridge`,
    `Convergence.canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_step_type_two_bridge`,
    `Convergence.canonical_aperiodic_phase_return_fill_stepwise_nonincrease_of_lower_bridge`,
    `Convergence.CanonicalAperiodicPhaseReturnCandidateSelectionSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnCandidateExclusionSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnNoSimpleStepSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnStepTypeTwoSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnStepwiseSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnCandidateSelectionSemantics.toCandidateExclusionSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnCandidateSelectionSemantics.toPhaseReturnSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnCandidateExclusionSemantics.toNoSimpleStepSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnCandidateExclusionSemantics.toPhaseReturnSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnNoSimpleStepSemantics.toStepTypeTwoSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnNoSimpleStepSemantics.toPhaseReturnSemantics`,
    `Convergence.canonical_aperiodic_phase_return_candidate_selection_semantics_of_canonical_next_left_phase_compatibility_and_minimality_theorem_sources`,
    `Convergence.canonical_aperiodic_phase_return_candidate_selection_semantics_of_promotion_and_minimality_theorem_sources`,
    `Convergence.canonical_aperiodic_phase_return_candidate_selection_semantics_of_theorem_sources`,
    `Convergence.canonical_aperiodic_phase_return_candidate_exclusion_semantics_of_theorem_sources`,
    `Convergence.canonical_aperiodic_phase_return_no_simple_step_semantics_of_theorem_sources`,
    `Convergence.canonical_aperiodic_phase_return_fill_stepwise_nonincrease_of_phase_return_stepwise_semantics`,
    `Convergence.canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_phase_return_stepwise_semantics`,
    `Convergence.CanonicalAperiodicPhaseReturnStepTypeTwoSemantics.toStepwiseSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnStepTypeTwoSemantics.toPhaseReturnSemantics`,
    `Convergence.CanonicalAperiodicPhaseReturnStepwiseSemantics.toPhaseReturnSemantics`,
    `Convergence.canonical_aperiodic_orbit_epoch_endpoint_nonincrease_of_phase_return_endpoint_and_fill`,
    `Convergence.canonical_aperiodic_orbit_epoch_endpoint_nonincrease_of_phase_return_semantics_and_endpoint`,
    `Convergence.canonical_aperiodic_orbit_epoch_sedt_envelope_of_canonical_gap_step`,
    `Convergence.canonical_aperiodic_orbit_epoch_native_sedt_semantics_of_local_accounting`,
    `Convergence.canonical_aperiodic_orbit_epoch_correction_nonpositive_of_endpoint_nonincrease`,
    `Convergence.canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_semantics_and_correction`,
    `Convergence.canonical_aperiodic_orbit_epoch_sedt_envelope_of_local_accounting_and_correction`,
    `Convergence.canonical_aperiodic_orbit_epoch_sedt_envelope_of_local_accounting_and_endpoint_nonincrease`,
    `Convergence.canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_semantics_and_endpoint_nonincrease`,
    `Convergence.canonical_aperiodic_orbit_epoch_native_endpoint_package`,
    `Convergence.canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_endpoint_package`,
    `Convergence.canonical_aperiodic_orbit_epoch_native_endpoint_package_of_native_semantics_and_phase_return_semantics`,
    `Convergence.canonical_aperiodic_orbit_epoch_native_endpoint_package_of_native_semantics_and_fill_stepwise`,
    `Convergence.collatz_convergence_from_aperiodic_lower_selected_segment_and_stream_local_semantics`,
    `Convergence.collatz_convergence_from_aperiodic_lower_selected_segment_and_stream_native_semantics`,
    `Convergence.collatz_convergence_from_aperiodic_canonical_depth_from_bonus_and_stream_local_semantics`,
    `Convergence.collatz_convergence_from_aperiodic_canonical_depth_from_bonus_and_stream_native_semantics`,
    `Convergence.canonical_aperiodic_phase_return_pair_step_sedt_on_of_accounting_witness_and_correction`,
    `Convergence.canonical_aperiodic_phase_return_pair_step_sedt_on_of_selected_long_epoch_bridge_on_and_correction`,
    `Convergence.canonical_aperiodic_phase_return_gap_step_sedt_on_of_selected_long_epoch_bridge_on_correction_and_fill`,
    `Convergence.canonical_aperiodic_orbit_epoch_sedt_envelope_of_selected_long_epoch_bridge_on_correction_and_fill`,
    `Convergence.canonical_aperiodic_orbit_epoch_sedt_envelope_of_phase_return_bridge`,
    `Convergence.canonical_aperiodic_orbit_epoch_sedt_envelope_of_phase_return_semantics`,
    `Convergence.canonical_aperiodic_phase_return_gap_step_sedt_on_of_orbit_epoch_sedt_envelope`
    and
    `Coercivity.canonical_phase_return_gap_step_sedt_on_of_orbit_epoch_sedt_envelope`
    identify the canonical-gap source with the orbitwise `E.2` envelope on the
    induced canonical long-gap stream. The resulting direct actual-skeleton
    convergence entrypoint is
    `Convergence.collatz_convergence_from_aperiodic_selected_long_epoch_and_orbit_epoch_semantics`,
    which isolates the remaining scientific work to those two honest lower
    theorem targets together with the already separated correction theorem.
    The direct theorem-level entrypoints are now the honest generic forms
    `Convergence.collatz_convergence_from_semantic_canonical_witness_semantics`
    and
    `Convergence.collatz_convergence_from_aperiodic_phase_return_semantics`,
    the exclusion-style semantic-package variant
    `Convergence.collatz_convergence_from_aperiodic_no_simple_step_semantics`,
    the narrower semantic-package variant
    `Convergence.collatz_convergence_from_aperiodic_step_type_two_semantics`,
    plus the even more explicit theorem-source entrypoint
    `Convergence.collatz_convergence_from_aperiodic_theorem_sources`
    and the stronger filler-aware variant
    `Convergence.collatz_convergence_from_aperiodic_stepwise_theorem_sources`,
    together with the current narrowest arithmetic stream-side entrypoint
    `Convergence.collatz_convergence_from_aperiodic_step_type_two_theorem_sources`
    and the residue-level precursor
    `Convergence.collatz_convergence_from_aperiodic_complex_step_theorem_sources`,
    with the new lowest candidate-exclusion semantic/theorem-source pair
    `Convergence.collatz_convergence_from_aperiodic_candidate_exclusion_semantics`
    and
    `Convergence.collatz_convergence_from_aperiodic_candidate_exclusion_theorem_sources`,
    and one layer below that the honest candidate-selection semantic/theorem-source pair
    `Convergence.collatz_convergence_from_aperiodic_candidate_selection_semantics`
    and
    `Convergence.collatz_convergence_from_aperiodic_candidate_selection_theorem_sources`,
    and now the explicit split theorem-source layer beneath it
    `Convergence.collatz_convergence_from_aperiodic_candidate_promotion_and_minimality_theorem_sources`,
    with the even more concrete next-left phase-compatibility theorem-source layer beneath that
    `Convergence.collatz_convergence_from_aperiodic_canonical_next_left_phase_compatibility_and_minimality_theorem_sources`,
    with the current narrowest exclusion-style variant
    `Convergence.collatz_convergence_from_aperiodic_no_simple_step_theorem_sources`,
    with the older segment/gap-multiple names retained only as compatibility
    wrappers. Thus the remaining aperiodic closure task is no longer to prove
    endpoint/fill theorems on the weak `choose`-based witness, but to produce
    correction-level and canonical-gap semantics for the repaired canonical
    witness from actual orbit/epoch semantics. This bridge then packages into
    the accounting witness and into
    `Convergence.Coercivity.phase_return_pair_step_sedt`. Whole-stream and
    canonical-gap packaging are already internalized.

## CI Guardrails

The workflow checks that chain modules contain neither `sorry` nor `axiom`.
W2 hardening additionally enforces non-vacuous D-level statements in epoch semantics modules
(`Epochs/Core`, `Epochs/APStructure`, `Epochs/Homogenization`, `Epochs/NumeratorCarry`, `Epochs/LongEpochs`).
W4 hardening extends this with non-vacuous F-level contracts in
`Mixing/Semigroup`, `Mixing/PhaseMixing`, and `Mixing/TouchFrequency`.
W5 hardening extends this with non-vacuous H-level cycle semantics in
`CycleExclusion/CycleDefinition`, `CycleExclusion/PureE1Cycles`,
`CycleExclusion/MixedCycles`, `CycleExclusion/PeriodSum`,
`CycleExclusion/RepeatTrick`, and `CycleExclusion/Main`.
W6 currently hardens the convergence bridge layer in
`Convergence/Coercivity`, `Convergence/FixedPoints`,
`Convergence/NoAttractors`, and `Convergence/MainTheorem` by replacing
external bridge placeholders with theorem-driven orbitwise contracts.
The strict unconditional `I.1` endpoint remains tied to completing
the selected-long-epoch semantic bridge, correction control, and filler drift
closure without artificial assumptions.
-/

end Collatz.Documentation
