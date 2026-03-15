# Semantic Hardening Plan (D.1 -> I.1)

## Progress

- Date: 2026-03-11
- Overall status: `W1 completed`, `W2 completed`, `W3 completed`, `W4 completed`, `W5 completed`, `W6 in progress`, `W7 pending`
- Verification snapshot: `lake build Collatz` passes locally after W6 bridge-layer strengthening

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

### W5 Progress (completed)

Completed across cycle-exclusion modules:

- `Collatz/CycleExclusion/CycleDefinition.lean`:
  - replaced proxy cycle validity with semantic closed-orbit contracts
    (`cycle_node`, `cycle_edge_valid`, `is_valid_cycle`) and helper lemmas.
- `Collatz/CycleExclusion/PureE1Cycles.lean`:
  - replaced `False`-based pure-e1 proxy with quantified step-type definition over cycle nodes.
  - replaced vacuous lemmas with explicit pure-e1 implications on step-type bounds.
- `Collatz/CycleExclusion/MixedCycles.lean`:
  - replaced `False`-based mixed-cycle proxy with existential split (`e=1` and `e>=2` witnesses).
  - added executable mixed-branch drift witness contract.
- `Collatz/CycleExclusion/PeriodSum.lean` and `Collatz/CycleExclusion/RepeatTrick.lean`:
  - replaced constant/placeholder models with quantitative period-term and repeat-gap interfaces.
  - removed placeholder existential negativity witness disconnected from cycle expressions.
- `Collatz/CycleExclusion/Main.lean`:
  - replaced proxy trivial/nontrivial/detection predicates with semantic definitions.
  - `main_cycle_exclusion` / `no_nontrivial_cycles` now exclude nontrivial cycles through explicit period/repeat premises rather than definitional falsity.

Acceptance checks:

- `lake build Collatz.CycleExclusion.CycleDefinition Collatz.CycleExclusion.PeriodSum Collatz.CycleExclusion.PureE1Cycles Collatz.CycleExclusion.MixedCycles Collatz.CycleExclusion.RepeatTrick Collatz.CycleExclusion.Main` passes.
- `lake build Collatz` passes after W5 changes.
- no `: True` theorem signatures remain in W5 target files.
- no `: Prop := False` / `: Prop := True` proxy cycle predicates remain in `CycleExclusion/*`.

### W6 Progress (in progress)

Current convergence-layer hardening completed:

- `Collatz/CycleExclusion/Main.lean`:
  - strengthened the `H.main` interface so that `Cycle.is_nontrivial` no longer carries
    exclusion premises by definition.
  - introduced explicit theorem-level cycle exclusion via `main_cycle_exclusion`
    and premise-driven `no_nontrivial_cycles`, making the `H.main -> I.2` bridge honest.
- `Collatz/Convergence/Coercivity.lean`:
  - replaced the vacuous coercivity marker with explicit potential, bounded-orbit,
    concatenation, and absorption bridge lemmas aligned with the structure of Appendix I / Lemma I.2.
  - normalized the odd-state potential so that `potential β 1 = 0`.
  - added cofinal prefix-growth / cofinal absorption lemmas
    (`prefix_total`, `prefix_total_lower_bound`, `prefix_total_cofinal_of_uniform_long`,
    `coercivity_absorption_cofinal`, `long_epoch_supply`) to move from finite-prefix
    negativity toward the orbitwise/cofinal form of Lemma I.2.
- `Collatz/Convergence/FixedPoints.lean`:
  - replaced the vacuous fixed-point marker with semantic fixed-point definitions
    and uniqueness contracts centered at the odd fixed point `1`.
- `Collatz/Convergence/NoAttractors.lean`:
  - replaced proxy attractor definitions with semantic closure/nonempty predicates
    and explicit contradiction interfaces back to `CycleExclusion.Main`.
- `Collatz/Convergence/MainTheorem.lean`:
  - removed tautological `k = 0` convergence proofs.
  - introduced an honest bridge theorem `collatz_convergence_from_entry` and compatibility
    aliases `main_convergence` / `global_convergence` phrased through entry into `{1}`.

Current status / remaining gap:

- DONE: `lake build Collatz` passes after these W6 bridge-layer changes.
- DONE: no `: True` theorem signatures remain in `Convergence/*`.
- DONE: no `: Prop := True/False` proxy convergence predicates remain in `Convergence/*`.
- DONE: no `: True` / `: Prop := False` proxy artifacts remain in the strengthened
  `CycleExclusion/Main` interface used by convergence.
- DONE: the orbitwise/cofinal `I.2` bridge layer is now explicit in Lean:
  strengthened `OrbitLongEpochStream` / `OrbitLongEpochSupply` in
  `Epochs/LongEpochs`, strong orbitwise prefix-drift packaging in
  `Convergence/Coercivity`, and periodic/aperiodic split wiring in
  `Convergence/MainTheorem`.
- DONE: `Convergence/MainTheorem` no longer depends on the previous external placeholders
  `hperiodic_extract`, `haperiodic_stream`, `hupper`; these are replaced by
  theorem-level contracts (`periodic_tail_cycle_extractor`, `OrbitLongEpochSupply`,
  `orbit_epoch_step_drift`, `orbit_epoch_margin`).
- DONE: `Convergence/MainTheorem` now derives positivity of
  `ε(t,U,β)` from SEDT assumptions (`ht`, `hU`, `hβgt`) instead of taking
  `hε` as an external bridge placeholder.
- DONE: `Convergence/MainTheorem` also internalizes `0 ≤ β`
  from SEDT-side assumptions (`hβgt`, `beta_zero_pos`), removing
  another bridge-level numeric assumption from strict-I.1-facing theorems.
- DONE: `SEDT/Core` now exports `alpha_lt_two_of_ht_hU`, and
  `Convergence/MainTheorem` derives `α(t,U)<2` internally from (`ht`,`hU`)
  rather than receiving it as a bridge input.
- DONE: `Convergence/MainTheorem` now proves oddness of all iterates
  from the odd start via `Foundations.Basic.T_odd_odd_of_odd`, removing the
  external `hoddIter` bridge assumption from the strict-I.1-facing interface.
- DONE: the aperiodic branch is now expressed in a more paper-aligned
  `E.2` form: `Convergence/MainTheorem` consumes `orbit_epoch_sedt_envelope`
  instead of the already-expanded drift inequality, and derives
  `orbit_epoch_step_drift` internally inside `Convergence/Coercivity`.
- DONE: the previous per-stream margin contract
  `orbit_epoch_margin` is no longer required at the strict-I.1 interface;
  the absorbed orbitwise bound is now routed through a paper-aligned
  dominance condition rather than the older half-margin shortcut.
- DONE: the coercivity packaging is now closer to the paper’s Part 2/3
  logic: `Convergence/Coercivity` exposes a raw inequality
  `-ε * ΣL + β*C*J`, and the final absorbed orbitwise bound is obtained from the
  paper-aligned dominance criterion `sedt_dominance_condition`
  (`β*C(t,U) < ε(t,U,β) * L₀(t,U)`), using `J ≤ ΣL / L₀`.
- DONE: the remaining residual aperiodic bridge has been consolidated into
  paper-shaped witness objects: `Convergence/MainTheorem` now consumes an
  `OrbitLongEpochE2Witness` (`G.5/G.Super-SEDT` long-epoch supply together with
  the `E.2` envelope on selected epochs). The former external parameter bridge
  `sedt_dominant_parameters` is now discharged internally from `t ≥ 3`, `U ≥ 1`
  via the canonical existence theorem
  `Convergence/Coercivity.exists_sedt_dominant_parameters` (implemented with the
  explicit admissible choice `β = 4` in the current SEDT model).
- IN_PROGRESS: the final strict unconditional I.1 endpoint
  `∀ m, Odd m → ∃ k, (collatz_step^[k]) m = 1`
  is not yet formally derived in Lean.
- IN_PROGRESS: the remaining scientific task is to complete the paper-level bridge
  `H.main -> Lemma I.2 (coercivity/absorption) -> I.1`
  without introducing artificial hypotheses or definitional shortcuts.
- IN_PROGRESS: the remaining closure gap for strict unconditional I.1 is now concentrated in
  proving the remaining theorem-level orbit-semantic extraction bridge from the
  upstream proven stack (`E.2`, `G.5/G.Super-SEDT`, `H.main`) without adding new
  assumptions. The numeric SEDT parameter-choice bridge is already internalized;
  the unresolved content now lies on the aperiodic orbit-semantic side.
- DONE: the strict-I.1-facing interface has now been further normalized to
  paper shape: `Convergence/MainTheorem` exposes
  `collatz_convergence_from_upstream_contracts` /
  `strict_i1_from_upstream_contracts`, where the residual aperiodic input is no
  longer a preassembled `OrbitLongEpochE2Witness`, but two separate upstream
  contracts:
  `OrbitLongEpochSupply` (the `G.5/G.Super-SEDT` stream supply) and the
  `orbit_epoch_sedt_envelope` on the induced canonical stream (the `E.2`
  envelope). So the remaining scientific gap is now an honest extraction task,
  not witness packaging.
- DONE: the `G.5` side has now been further decomposed into a genuinely
  orbit-semantic intermediate contract:
  `Epochs.LongEpochs.OrbitHasCofinalLongEpochGaps`. Lean now proves that this
  semantic predicate packages canonically into
  `Epochs.LongEpochs.OrbitLongEpochSupply`, and `Convergence/MainTheorem`
  exposes `collatz_convergence_from_gap_semantics` /
  `strict_i1_from_gap_semantics` accordingly. Thus the next real theorem target
  is to derive `OrbitHasCofinalLongEpochGaps` from
  `¬ orbit_eventually_periodic`, rather than merely constructing a supply object.
- DONE: the first honest orbit-semantic consequence of aperiodicity is now
  formalized: `Convergence/MainTheorem` proves that any bounded odd-step orbit is
  eventually periodic (finite pigeonhole + determinism), hence
  `¬ orbit_eventually_periodic` implies `¬ orbit_bounded`. This does not yet
  produce long epochs, but it removes the finite-state obstruction and isolates
  the remaining gap to extracting cofinal long gaps from genuinely unbounded
  aperiodic dynamics.
- DONE: that same orbit-semantic bridge has now been sharpened to a
  cofinal form: `Convergence/MainTheorem` defines
  `orbit_cofinally_unbounded` and proves that
  `¬ orbit_bounded` implies this stronger statement, hence every aperiodic orbit
  is formally shown to exceed every finite bound arbitrarily far out. The
  remaining scientific gap is therefore no longer mere unboundedness, but the
  extraction of SEDT-long epoch gaps from this cofinal unbounded behaviour.
- DONE: the orbit-semantic aperiodic bridge has now been pushed one layer
  closer to the `A.REC/A.LONG` shape: `Convergence/MainTheorem` proves that
  cofinally unbounded orbits admit arbitrarily long sequences of large hits with
  prescribed spacing (`cofinally_unbounded_orbit_has_spaced_hits`) and, for any
  fixed period `q > 0`, arbitrarily far-out large same-residue return pairs
  (`orbit_has_cofinal_phase_returns`). The remaining scientific gap is now to
  connect these phase-return witnesses to the actual long-epoch/gap semantics
  needed for `Epochs.LongEpochs.OrbitHasCofinalLongEpochGaps`.
- DONE: the remaining `A.REC/A.LONG`-side gap was isolated at the epoch layer
  and then canonically closed in the current Lean interface.
  `Epochs.LongEpochs` now distinguishes
  `RawCofinalGapLongPhaseReturns` (raw cofinal witnesses),
  `OrbitHasCofinalGapLongPhaseReturns` (structured cofinal alignment data with
  explicit sequences), and the canonical bridge
  `canonical_gap_long_phase_returns_bridge`.
  `Convergence/MainTheorem` has been rebased onto this strengthened contract via
  `aperiodic_orbit_has_cofinal_gap_long_phase_returns`,
  `collatz_convergence_from_phase_return_bridge` /
  `strict_i1_from_phase_return_bridge`, and the further-internalized wrappers
  `collatz_convergence_from_canonical_phase_return_bridge` /
  `strict_i1_from_canonical_phase_return_bridge`.
  The older weak phase-return formulation is superseded, and this epoch-side
  `A.REC/A.LONG` bridge is no longer an external hypothesis.
- IN_PROGRESS: after canonical closure of the phase-return/long-gap bridge and
  periodic-tail refactoring, the remaining strict-I.1 external input on the
  aperiodic side is now localized further. `Convergence/Coercivity` packages
  the old whole-stream bridge as `phase_return_sedt_envelope_bridge`, but also
  exposes the smaller residual target
  `canonical_phase_return_gap_step_sedt`: a per-gap `E.2` inequality on the
  canonical long gaps extracted from the structured phase-return witness. This
  has now been decomposed once more into the more atomic contracts
  `sedt_single_gap_of_phase_return` (real `E.2` bound on one aligned return
  pair with SEDT-long separation) and `phase_return_gap_fill_step_drift`
  (drift control on the filler segment up to the next canonical left index).
  `Convergence/MainTheorem` now exposes
  `collatz_convergence_from_single_gap_and_fill_bridges` /
  `strict_i1_from_single_gap_and_fill_bridges`, so the external aperiodic input
  is no longer a raw stream-level envelope hypothesis, nor a whole
  canonical-stream theorem, nor even directly a canonical-gap theorem, but a
  smallest single-gap `E.2` lemma plus one explicit filler-drift contract.
  The single-gap target itself is now further decomposed into an `SEDT`-native
  local segment theorem
  `SEDT.sedt_potential_change_of_phase_return_segment` and a separate
  normalization-side correction control
  `phase_return_potential_correction_nonpositive`, so the remaining scientific
  gap is visible as:
  `SEDT` local orbit-segment drift
  - potential-normalization correction
  - filler-drift control.
    The `SEDT` local orbit-segment drift theorem was then repackaged as the
    more arithmetic contract
    `SEDT.sedt_potential_change_of_gap_long_multiple_segment`, and Lean now
    proves the reverse arithmetic reduction as well. Hence
    `SEDT.sedt_potential_change_of_phase_return_segment` and
    `SEDT.sedt_potential_change_of_gap_long_multiple_segment` are equivalent
    arithmetic interfaces only; they are not the honest final local paper
    target on their own.
- DONE: `Collatz/SEDT/Theorems.lean` now contains a paper-faithful local
  assembly theorem
  `potential_change_le_sedt_envelope_of_local_bounds`, splitting the native
  `SEDT.potential_change ≤ sedt_envelope` claim into explicit logarithmic and
  depth-side bounds on one realized long segment.
- DONE: the honest canonical selected-segment local witness is now exposed as
  `SEDT.phase_return_epoch_accounting_witness`, and
  `Convergence/Coercivity.lean` proves that this witness, together with the
  already-separated normalization correction, yields the downstream
  `phase_return_pair_step_sedt` contract used in the aperiodic closure chain.
- DONE: the local witness has now been pushed one honest semantic layer lower.
  `Epochs/LongEpochs.lean` defines the paper-faithful object
  `Epochs.SelectedLongEpochWitness` and the bridge type
  `Epochs.SelectedLongEpochBridge`; `SEDT/Theorems.lean` proves that such a
  bridge yields `phase_return_epoch_accounting_witness`, and
  `Convergence/Coercivity.lean` packages it directly into
  `phase_return_pair_step_sedt` once normalization correction is provided.
- DONE: `Epochs.SelectedLongEpochBridge` is now reduced to theorem-driven lower
  semantic inputs; the selected-segment carry layer is internalized below
  `LongEpochs`, and the bridge itself is no longer the residual aperiodic gap.
- IN_PROGRESS: the remaining aperiodic closure content has been repaired to more
  honest local targets in `Convergence/Coercivity.lean`. The normalization side
  is now factored through `phase_return_endpoint_nonincrease ->
phase_return_potential_correction_nonpositive`, and the filler side is no
  longer a single over-broad global Prop: `phase_return_gap_fill_step_drift` is
  witness-indexed, with only the wrapper `phase_return_gap_fill_bridge`
  quantifying over all selected phase-return witnesses. The previous weak
  `choose`-based skeleton
  `aperiodic_orbit_has_cofinal_gap_long_phase_returns` has now been recognized
  as only an index-level alignment witness, not an honest canonical aperiodic
  witness. Lean therefore now exposes the repaired semantic object
  `Convergence.CanonicalAperiodicPhaseReturnWitness`, together with the local
  bridge `Epochs.SelectedLongEpochBridgeOn` and its constructor
  `Epochs.selected_long_epoch_bridge_on_of_semantics`. Lean now also exposes
  the actual theorem-producing aperiodic semantic package
  `Convergence.CanonicalAperiodicPhaseReturnSemantics` and the constructor
  `Convergence.canonical_aperiodic_phase_return_witness_of_semantics`, so the
  repaired witness is built internally from semantics on the concrete aperiodic
  skeleton. The endpoint branch is now repaired to the honest correction-level
  target `phase_return_potential_correction_nonpositive_on`, and the filler
  branch is pushed up to the already reassembled canonical-gap theorem
  `canonical_phase_return_gap_step_sedt_on`. Lean also now exposes the
  actual-skeleton carry constructor
  `canonical_aperiodic_carry_paper_of_depth_semantics`. Lean now also exposes
  the exact actual-skeleton theorem sources
  `canonical_aperiodic_selected_carry_depth_semantics`,
  `canonical_aperiodic_phase_return_correction_nonpositive_on`, and
  `canonical_aperiodic_phase_return_gap_step_sedt_on`, together with the
  constructor `canonical_aperiodic_phase_return_semantics_of_theorem_sources`.
  The honest direct entrypoints are now
  `collatz_convergence_from_semantic_canonical_witness_semantics`,
  `collatz_convergence_from_aperiodic_phase_return_semantics`, and the even
  more explicit theorem-source form
  `collatz_convergence_from_aperiodic_theorem_sources`, while the older
  segment/gap-multiple names remain only as compatibility wrappers. The residual
  content is now pushed one layer lower in theorem form:
  `selected_carry_depth_semantics_of_selected_long_epoch_witness` and
  `canonical_aperiodic_selected_carry_depth_semantics_of_selected_long_epoch_bridge_on`
  reduce the carry-depth source to an actual selected-long-epoch bridge on the
  concrete aperiodic skeleton, now exposed directly as the theorem target
  `canonical_aperiodic_selected_long_epoch_bridge_on`; Lean now also exposes the
  direct constructors
  `canonical_aperiodic_selected_long_epoch_bridge_on_of_selected_long_epoch_bridge`,
  `canonical_aperiodic_selected_long_epoch_bridge_on_of_carry_paper` and
  `canonical_aperiodic_selected_long_epoch_bridge_on_of_depth_semantics` and
  `canonical_aperiodic_selected_long_epoch_bridge_on_of_phase_return_semantics`
  to produce that bridge from honest selected-pair semantics on the actual
  skeleton. Lean now also exposes
  `canonical_aperiodic_carry_paper_of_selected_long_epoch_bridge_on` and
  `canonical_aperiodic_phase_return_epoch_accounting_witness_of_selected_long_epoch_bridge_on`,
  so this actual selected-long-epoch bridge can be pushed back down to
  paper-faithful `carryPaper` data and forward to local E.1/E.2 accounting on
  the same canonical skeleton. Lean now also exposes the still lower actual
  selected-segment target
  `canonical_aperiodic_selected_portrait_enumeration_semantics`,
  `canonical_aperiodic_selected_depth_from_bonus_semantics`,
  `canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics` and the
  constructors
  `canonical_aperiodic_selected_portrait_enumeration_semantics_of_depth_bookkeeping_bridge`,
  `canonical_aperiodic_selected_depth_from_bonus_semantics_of_depth_bookkeeping_bridge`,
  `canonical_aperiodic_selected_portrait_enumeration_semantics_of_carry_paper`,
  `canonical_aperiodic_selected_depth_from_bonus_semantics_of_carry_paper`,
  `canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_carry_paper`,
  `canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_return_semantics`,
  `canonical_aperiodic_selected_depth_from_bonus_semantics_of_phase_return_semantics`,
  `canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_phase_return_semantics`,
  `canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry`,
  `canonical_aperiodic_selected_depth_from_bonus_semantics_of_depth_semantics`,
  `canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_phase_geometry_and_depth_semantics`,
  `canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_portrait_and_depth_from_bonus`
  and
  `canonical_aperiodic_selected_carry_depth_semantics_of_depth_bookkeeping_bridge_semantics`,
  so the carry side is now reduced all the way to the selected-segment
  portrait/depth bridge layer. In particular, portrait enumeration on the
  canonical aperiodic skeleton is now already forced by the built-in
  modulo-`Q_t` phase geometry, leaving only the canonical dependent
  depth-from-bonus target
  `canonical_aperiodic_selected_depth_from_bonus_semantics_canonical`
  as the last genuinely semantic lower carry target. Meanwhile,
  `canonical_aperiodic_phase_return_gap_step_sedt_on_of_orbit_epoch_sedt_envelope`
  reduces the canonical-gap source to the orbitwise `E.2` envelope on the
  induced canonical long-gap stream, now exposed directly as
  `canonical_aperiodic_orbit_epoch_sedt_envelope`; Lean now also exposes the
  direct constructors
  `canonical_aperiodic_orbit_long_epoch_stream`,
  `canonical_aperiodic_orbit_epoch_local_accounting_semantics`,
  `canonical_aperiodic_orbit_epoch_native_sedt_semantics`,
  `canonical_aperiodic_orbit_epoch_correction_nonpositive`,
  `canonical_aperiodic_orbit_epoch_endpoint_nonincrease`,
  `canonical_aperiodic_orbit_epoch_sedt_envelope_of_canonical_gap_step`,
  `canonical_aperiodic_orbit_epoch_native_sedt_semantics_of_local_accounting`,
  `canonical_aperiodic_orbit_epoch_correction_nonpositive_of_endpoint_nonincrease`,
  `canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_semantics_and_correction`,
  `canonical_aperiodic_orbit_epoch_sedt_envelope_of_local_accounting_and_correction`,
  `canonical_aperiodic_orbit_epoch_sedt_envelope_of_local_accounting_and_endpoint_nonincrease`,
  `canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_semantics_and_endpoint_nonincrease`,
  `collatz_convergence_from_aperiodic_lower_selected_segment_and_stream_local_semantics`,
  `collatz_convergence_from_aperiodic_lower_selected_segment_and_stream_native_semantics`,
  `collatz_convergence_from_aperiodic_canonical_depth_from_bonus_and_stream_local_semantics`,
  `collatz_convergence_from_aperiodic_canonical_depth_from_bonus_and_stream_native_semantics`,
  `canonical_aperiodic_phase_return_pair_step_sedt_on_of_accounting_witness_and_correction`,
  `canonical_aperiodic_phase_return_pair_step_sedt_on_of_selected_long_epoch_bridge_on_and_correction`,
  `canonical_aperiodic_phase_return_gap_step_sedt_on_of_selected_long_epoch_bridge_on_correction_and_fill`,
  `canonical_aperiodic_orbit_epoch_sedt_envelope_of_selected_long_epoch_bridge_on_correction_and_fill`,
  `canonical_aperiodic_orbit_epoch_sedt_envelope_of_phase_return_bridge` and
  `canonical_aperiodic_orbit_epoch_sedt_envelope_of_phase_return_semantics` for
  producing that stream-level target from honest `E.2` semantics on the actual
  skeleton. Lean also now exposes the direct actual-skeleton convergence entrypoint
  `collatz_convergence_from_aperiodic_selected_long_epoch_and_orbit_epoch_semantics`,
  so the remaining scientific target is no longer to prove endpoint/fill on the
  weak skeleton, but precisely to produce the theorem-level selected-long-epoch
  bridge and the stream-level `E.2` envelope on the repaired actual aperiodic
  skeleton.

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
