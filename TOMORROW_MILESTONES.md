# Tomorrow Milestones

Date: 2026-03-14
Focus: formal-first closure of the filler-side residual on the canonical aperiodic skeleton

## Goal

Tomorrow's goal is not to "close the whole bridge", but to reduce the stream-side residual by one more honest theorem-producing layer.

### Current Overall Progress

- DONE: Milestone 1
- DONE: Milestone 2
- ACTIVATED: Milestone 3
- MILESTONE 4 RESULT: current proxy-level promotion target failed under a formal sample counterexample
- Current state summary:
  - the old admissibility target is retired
  - proxy-level minimality now has an explicit theorem-producing local source
  - the current proxy-level promotion target is now known to be too strong/misaligned for direct population from a raw filler `simpleStep` candidate
  - a new witness-based concrete next-left layer has now been introduced locally, separating the admissibility language from the retired phase-only proxy
  - the next scientifically correct move is to populate this repaired witness-based layer from honest lower semantics rather than add stronger wrappers

Primary target:

- treat the old admissibility audit as completed
- decide whether the current phase-compatibility proxy is sufficient as a temporary concrete target
- then attack `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_semantics`

Secondary target:

- only after minimality stabilizes, move to `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_promotion_semantics`
- if the proxy remains too weak or too misleading, replace it with a more honest event-level admissibility object before any further proof effort

## Milestone 1: Record the Audit Result and Freeze the Decision

### Objective

Start from the already completed audit result and ensure tomorrow's work does not drift back to the superseded target.

### Progress

- DONE: the old `Epochs.CanonicalNextLeftAdmissibleOn` remains retired
- DONE: the concrete layer is frozen as a phase/order proxy, not event-level admissibility
- DONE: the generic chain above it stayed structurally unchanged
- Decision memo:
  - decision = `replace`
  - replaced target = old concrete admissibility predicate
  - current proxy layer = `CanonicalNextLeftPhaseCompatibleOn` plus its promotion/minimality wrappers
  - explicitly deferred = any genuine event-level admissibility redesign unless later proof evidence forces Milestone 3

### Files

- `Collatz/Epochs/LongEpochs.lean`
- `Collatz/Convergence/MainTheorem.lean`
- optionally `Collatz/Documentation/PaperCodeMapping.lean` only if the public interface changes

### Tasks

1. Reconfirm the completed decision: the old `Epochs.CanonicalNextLeftAdmissibleOn` was replaced.
2. Treat the current concrete layer explicitly as a **phase/order proxy**, not as genuine selected-event admissibility.
3. Keep in mind the current concrete symbols:
   - `Epochs.CanonicalNextLeftPhaseCompatibleOn`
   - `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotionOn`
   - `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimalityOn`
4. Preserve the generic chain above this layer:
   - `FillerSimpleStepPromotionOn`
   - `FillerNextLeftMinimalityOn`
   - `FillerCandidateSelectionSemanticsOn`

### Success Criteria

- no accidental return to the superseded admissibility target
- tomorrow's work starts from the already accepted `replace` decision
- the distinction "phase-compatible proxy vs event-level admissibility" stays explicit

### Failure Mode

If tomorrow's proof attempt starts depending on the old predicate or silently reinterprets the proxy as a genuine selected-event notion, stop and re-open target design before proving anything.

## Milestone 2: Make Phase-Compatible Minimality Theorem-Producing

### Objective

Turn the current abstract slot
`Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimalityOn`
into something produced by a more explicit local semantics object.

### Progress

- DONE: introduced `Epochs.CanonicalNextLeftPhaseCompatibleMinimalitySemanticsOn`
- DONE: introduced global wrapper `Epochs.CanonicalNextLeftPhaseCompatibleMinimalitySemantics`
- DONE: proved
  `Epochs.gap_long_phase_returns_filler_canonical_next_left_phase_compatible_minimality_on_of_semantics`
- DONE: proved
  `Epochs.gap_long_phase_returns_filler_canonical_next_left_phase_compatible_minimality_of_semantics`
- DONE: introduced
  `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_local_semantics`
- DONE: proved
  `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_semantics_of_local_semantics`
- DONE: `lake build` passed for the edited Lean modules
- Result: phase-compatible minimality is no longer only a bare assumption slot; there is now one explicit theorem-producing source below the current wrapper
- Boundary: this still proves only proxy-level minimality, not genuine event-level admissibility

### Files

- `Collatz/Epochs/LongEpochs.lean`
- `Collatz/Convergence/MainTheorem.lean`

### Tasks

1. Decide whether the current phase-compatibility proxy is good enough to support one more theorem-producing layer.
2. If yes, introduce or isolate a local semantics object for next-left choice/minimality under the proxy interpretation.
3. Prove a local theorem:
   - `idx` has the required phase compatibility,
   - `idx < hphase.leftIdx (j + 1)`,
   - therefore `False`.
4. Package that theorem into
   `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimalityOn`.
5. Lift it to the actual aperiodic skeleton as
   `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_semantics`.

### Success Criteria

- phase-compatible minimality is no longer a bare assumption slot
- at least one theorem-producing source exists below the current wrapper
- `lake build` passes for edited Lean modules

### Failure Mode

If even the phase-compatible minimality target still cannot be justified from any honest lower semantics, stop and treat that as evidence that the proxy itself should be replaced by an event-level admissibility object.

## Milestone 3: If Needed, Replace the Proxy With Event-Level Admissibility

### Objective

If the phase-compatible proxy still proves too weak, too strong, or too disconnected from `simpleStep`, replace it with a more honest event-level admissibility notion before further proof work.

### Progress

- ACTIVATED: Milestone 4 produced formal evidence that the current proxy-level promotion target does not follow from a raw filler `simpleStep` candidate
- DONE: `Collatz/Epochs/LongEpochs.lean` now contains a sample counterexample theorem
  `sample_gap_long_phase_returns_15_0_0_not_filler_canonical_next_left_phase_compatible_promotion`
- DONE: the corresponding global impossibility corollary
  `not_all_gap_long_phase_returns_have_filler_canonical_next_left_phase_compatible_promotion`
  records that this promotion target is not forced by the raw structured phase-return interface alone
- DONE: introduced the repaired witness-based lower object
  `Epochs.CanonicalNextLeftSelectionWitnessOn`
  together with witness-relative promotion/minimality wrappers
  `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionOn`
  and
  `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessMinimalityOn`
- DONE: added the local bridge
  `Epochs.filler_candidate_selection_semantics_on_of_canonical_next_left_witness`
  so the redesign still collapses directly into the unchanged generic candidate-selection seam
- DONE: added actual-skeleton witness-based wrappers in `Collatz/Convergence/MainTheorem.lean`
  and the theorem-source constructor
  `Convergence.canonical_aperiodic_phase_return_candidate_selection_semantics_of_canonical_next_left_witness_theorem_sources`
- DONE: `lake build` passed for `Collatz.Epochs.LongEpochs` and `Collatz.Convergence.MainTheorem`
- DONE: the repaired witness-based layer is now partially populated:
  - unconditional self-witness via
    `Epochs.canonical_next_left_selection_witness_on_of_phase_compatibility`
  - witness-relative minimality via
    `Epochs.filler_next_left_minimality_on_of_phase_compatible_witness_and_minimality`
  - actual-skeleton lift via
    `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_witness`
    and
    `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_witness_minimality_of_phase_compatible_minimality`
- DONE: the existing external phase-compatible theorem-source route now passes
  through the repaired witness-based constructor internally, so the new path is
  reachable without changing the current top-level API
- DONE: the still-missing promotion gap is now expressed explicitly as an
  event-level source:
  `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionEventSourceOn`
  together with its actual-skeleton wrapper
  `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_event_source_semantics`
- DONE: this explicit event-level promotion source is now further decomposed into
  two sharper local residuals:
  - `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessInteriorAdmissibilityOn`
  - `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSourceOn`
    together with actual-skeleton wrappers in `Collatz/Convergence/MainTheorem.lean`
- DONE: the sample witness now already refutes the sharpened right-boundary case
  for the old phase-compatible witness, so the obstruction has been localized
  even more precisely to the genuinely new event-level source rather than the
  older bundled proxy statement
- DONE: the remaining boundary residual has now been sharpened once more to a
  canonical simple-step-at-`rightIdx j` source:
  `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSourceOn`
  together with a direct bridge back into
  `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSourceOn`
  and the corresponding actual-skeleton wrapper
  `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_witness_right_boundary_simple_step_event_source_semantics`
- DONE: a stronger structural obstruction is now formalized as well:
  even the sharpened target
  `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSourceOn`
  is not uniformly derivable for arbitrary witness-relative admissibility notions,
  via
  `Epochs.canonical_next_left_selection_witness_on_of_only_next_left`,
  the sample refutation
  `sample_gap_long_phase_returns_15_0_0_not_only_next_left_right_boundary_simple_step_event_source`,
  and the corresponding global impossibility corollary
  `not_all_gap_long_phase_returns_have_only_next_left_right_boundary_simple_step_event_source`
- DONE: the remaining boundary target has now been refactored into a concrete
  event layer plus a separate admissibility bridge:
  - `Epochs.BoundaryPromotedSelectedEventOn`
  - `Epochs.GapLongPhaseReturnsBoundaryPromotedSelectedEventSourceOn`
  - `Epochs.GapLongPhaseReturnsBoundaryPromotedSelectedAdmissibilityBridgeOn`
    together with the bridge
    `Epochs.gap_long_phase_returns_filler_canonical_next_left_witness_right_boundary_simple_step_event_source_on_of_boundary_event_source_and_admissibility`
    and the corresponding actual-skeleton wrappers in
    `Collatz/Convergence/MainTheorem.lean`
- DONE: the new concrete boundary-event source is now formally reduced to the
  exact one-step geometry statement
  `rightIdx j + 1 < leftIdx (j + 1)` via:
  - `Epochs.boundary_promoted_selected_event_on_has_successor_room`
  - `Epochs.boundary_promoted_selected_event_on_of_successor_room`
  - `Epochs.gap_long_phase_returns_boundary_promoted_selected_event_source_on_of_successor_room`
  - `Epochs.not_gap_long_phase_returns_boundary_promoted_selected_event_source_on_of_no_successor_room`
    and the actual-skeleton wrapper
    `Convergence.canonical_aperiodic_phase_return_fill_boundary_promoted_selected_event_source_semantics_of_successor_room`
- DONE: the now-minimal geometric theorem on the canonical aperiodic skeleton is
  proved theorem-driven by strengthening cofinal phase returns to a strict
  threshold form and routing the actual constructor through it:
  - `Convergence.orbit_has_strictly_cofinal_phase_returns`
  - `Convergence.cofinally_unbounded_orbit_has_strictly_cofinal_phase_returns`
  - `Convergence.aperiodic_orbit_has_strictly_cofinal_phase_returns`
  - `Epochs.RawStrictCofinalGapLongPhaseReturns`
  - `Epochs.orbit_has_cofinal_gap_long_phase_returns_of_raw_strict`
  - `Epochs.successor_room_orbit_has_cofinal_gap_long_phase_returns_of_raw_strict`
  - `Convergence.aperiodic_orbit_has_cofinal_gap_long_phase_returns_successor_room`
  - `Convergence.canonical_aperiodic_phase_return_fill_boundary_promoted_selected_event_source_semantics_of_aperiodic_successor_room`
- DONE: the remaining obstruction has now been localized one step further, from
  the boundary event source to the witness-relative admissibility bridge itself:
  the sample witness carries a genuine concrete boundary interior event, but that
  event is not admitted by the current phase-compatible language, via
  - `Epochs.sample_gap_long_phase_returns_15_0_0_not_phase_compatible_boundary_promoted_selected_admissibility_bridge`
  - `Epochs.not_all_gap_long_phase_returns_have_phase_compatible_boundary_promoted_selected_admissibility_bridge`
- DONE: the attempted next step exposed a stronger seam-level obstruction:
  on the current interface, any witness language that admits the concrete
  boundary successor event is immediately incompatible with the present
  next-left minimality slot, via
  - `Epochs.not_gap_long_phase_returns_boundary_promoted_selected_admissibility_bridge_on_of_successor_room_and_minimality`
  - `Convergence.canonical_aperiodic_phase_return_fill_not_boundary_admissibility_bridge_and_witness_minimality`
- DONE: the split replacement seam is now implemented locally:
  - `Epochs.CanonicalNextLeftSplitWitnessOn`
  - `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftSplitPromotionEventSourceOn`
  - `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftSplitNormalizationOn`
  - `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftSplitMinimalityOn`
  - `Epochs.gap_long_phase_returns_filler_candidate_exclusion_on_of_split_event_source_normalization_and_minimality`
    together with the corresponding actual-skeleton wrappers in
    `Collatz/Convergence/MainTheorem.lean`
- DONE: the stronger structured replacement seam is now also implemented:
  - `Epochs.PromotedFillerSelectedComparisonWitnessOn`
  - `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftStructuredNormalizationOn`
  - `Epochs.FillerNextLeftStructuredMinimalityOn`
  - `Epochs.gap_long_phase_returns_filler_candidate_exclusion_on_of_structured_event_source_normalization_and_minimality`
    together with the corresponding actual-skeleton wrappers in
    `Collatz/Convergence/MainTheorem.lean`
- DONE: the stronger no-go theorem is now proved for the whole class of
  index/order-only structured comparison outputs:
  once a concrete boundary event is admitted on the event side, the forgetful
  passage to such a comparison witness is automatic, so any structured
  minimality theorem already yields contradiction, via
  - `Epochs.not_gap_long_phase_returns_boundary_event_admissibility_bridge_on_of_successor_room_simple_step_and_structured_minimality`
  - `Convergence.canonical_aperiodic_phase_return_fill_not_boundary_event_admissibility_bridge_and_structured_minimality`
- DONE: the strongest consumer-driven route is now formalized too:
  direct `event witness -> contradiction` theorem sources already conflict with
  boundary-event admission, via
  - `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftSplitEventConflictOn`
  - `Epochs.not_gap_long_phase_returns_boundary_event_admissibility_bridge_on_of_successor_room_simple_step_and_event_conflict`
  - `Convergence.canonical_aperiodic_phase_return_fill_not_boundary_event_admissibility_bridge_and_event_conflict`
- DONE: the most obvious split normalization target is now formally refuted on
  the sample witness as well:
  even if every genuine event is admitted on the promotion side, one still
  cannot normalize the concrete boundary event into the old phase-compatible
  comparison language, via
  - `Epochs.sample_gap_long_phase_returns_15_0_0_not_trivial_event_phase_compatible_split_normalization`
  - `Epochs.not_all_gap_long_phase_returns_have_trivial_event_phase_compatible_split_normalization`
- DONE: the boundary branch is now further refined below `eventAdmissible`
  itself, into a certificate-level seam:
  - `Epochs.BoundaryPromotedSelectedCertificateOn`
  - `Epochs.GapLongPhaseReturnsBoundaryPromotedSelectedCertificateSourceOn`
  - `Epochs.GapLongPhaseReturnsBoundaryPromotedSelectedCertificateComparisonAdapterOn`
  - `Epochs.GapLongPhaseReturnsBoundaryPromotedSelectedCertificateEventWitnessAdapterOn`
    together with actual-skeleton wrappers in
    `Collatz/Convergence/MainTheorem.lean`
- DONE: the canonical successor-room route now theorem-produces the stronger
  boundary certificate directly, without first committing to any event-language
  admission predicate, via
  - `Epochs.gap_long_phase_returns_boundary_promoted_selected_certificate_source_on_of_successor_room`
  - `Convergence.canonical_aperiodic_phase_return_fill_boundary_promoted_selected_certificate_source_semantics_of_aperiodic_successor_room`
- DONE: the certificate seam now carries its own guard theorems:
  - the forgetful route from certificate to index/order-only comparison data is
    already ruled out by structured minimality, via
    `Epochs.not_gap_long_phase_returns_boundary_certificate_source_on_of_simple_step_and_structured_minimality`
    and
    `Convergence.canonical_aperiodic_phase_return_fill_not_boundary_certificate_source_and_structured_minimality`
  - if one can already turn the certificate into the exact promotion-side event
    witness consumed by direct event-conflict, contradiction now occurs strictly
    at that certificate-to-consumer adapter seam, via
    `Epochs.not_gap_long_phase_returns_boundary_certificate_source_on_of_simple_step_and_event_witness_adapter_and_event_conflict`
    and
    `Convergence.canonical_aperiodic_phase_return_fill_not_boundary_certificate_source_and_event_witness_adapter_and_event_conflict`
- ACTIVE NEXT STEP: populate the new certificate-to-consumer seam below
  `eventAdmissible`.
  The comparison-side forgetful path is now formally sealed off, and the active
  question is no longer whether to admit the concrete boundary event. The new
  local residual is:
  - which minimal extra semantic data, beyond the concrete boundary certificate,
    theorem-produces the specific promotion-side event witness expected by the
    canonical direct event-conflict consumer,
  - without collapsing back to an index/order-only forgetful object,
  - and without smuggling the downstream contradiction into the certificate
    definition itself.

### Files

- `Collatz/Epochs/LongEpochs.lean`
- `Collatz/Convergence/MainTheorem.lean`
- `Collatz/Documentation/PaperCodeMapping.lean` only if public names stabilize

### Tasks

1. Keep the new certificate source fixed as the lower theorem-producing object
   for the boundary branch.
2. Identify the weakest honest certificate-to-event-witness adapter for the
   direct split event-conflict consumer.
3. Avoid the now-refuted certificate-to-comparison forgetful route except as a
   guard/no-go theorem.
4. Only after a non-circular certificate-to-consumer adapter exists, route that
   local seam into candidate exclusion and then into the unchanged upper
   no-simple-step / complex-step / stepwise cascade.

### Success Criteria

- the lower target becomes more proof-oriented and less misleading
- the redesign is strictly local to the concrete next-left layer
- `lake build` passes for edited Lean modules and the full project still builds
- the new certificate seam isolates the remaining mismatch strictly below
  `eventAdmissible`, at one explicit certificate-to-consumer adapter

### Failure Mode

If every plausible certificate-to-consumer adapter still forces immediate
contradiction, stop and treat the downstream consumer contract itself as the
next object to redesign, rather than reintroducing a stronger admission
predicate.

## Milestone 4: Only After Minimality Stabilizes, Attack Promotion

### Objective

Attempt to produce
`Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_promotion_semantics`
from actual filler-side arithmetic or, if Milestone 3 happened, from the replacement event-level admissibility semantics.

### Progress

- CLOSED WITH NEGATIVE RESULT: Milestone 4 was the active frontier and produced a formal obstruction under the current proxy
- DONE: minimality was stabilized first, so the roadmap may advance to promotion without reopening the previous target
- DONE: the unresolved lower slot has been identified explicitly as
  `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotionOn`
  and its actual-skeleton wrapper
  `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_promotion_semantics`
- DONE: the audit showed that neither `cand.k` nor a strictly interior same-phase proxy index is forced in general by the current raw filler simple-step data
- DONE: failure has been escalated into formal Lean evidence rather than left as an informal concern
- NEXT: continue under Milestone 3 with a more honest event-level admissibility redesign

### Files

- `Collatz/Epochs/LongEpochs.lean`
- possibly `Collatz/Foundations/StepClassification.lean`
- possibly `Collatz/Foundations/Core.lean`
- `Collatz/Convergence/MainTheorem.lean`

### Tasks

1. Start with `cand : Epochs.FillerSimpleStepCandidate hphase`.
2. Decide whether promotion should use:
   - `cand.k` directly, or
   - a derived index `k'`.
3. Show that the promoted index satisfies the currently chosen admissibility/proxy predicate.
4. Lift the local promotion theorem into the actual aperiodic wrapper.

### Success Criteria

- one honest local theorem source from `simpleStep` to the chosen admissibility notion
- no new glue-only wrapper layers

### Failure Mode

If `simpleStep` still does not naturally imply the chosen admissibility notion, treat this as evidence that the target remains mis-specified and return to Milestone 3.

## Milestone 5: Collapse the New Layer Back Into the Existing Stream Chain

### Objective

Reconnect the new lower theorem sources without changing the already stable upper cascade.

### Progress

- PARTIALLY DONE: the repaired witness-based next-left layer already collapses into
  `candidate selection` through a single local adapter, without any new upper convergence wrappers
- DONE: the minimality half of the repaired witness-based layer already routes into the unchanged candidate-selection seam
- DONE: the legacy phase-compatible theorem-source path is now internally rewired through the repaired witness-based layer
- DONE: an explicit event-level bridge now converts the future promoted-event source into the witness-relative promotion slot
- DONE: the explicit promoted-event source is now decomposed into strict-interior and right-boundary cases before entering the witness-relative promotion slot
- NEXT: once actual theorem sources for these sharpened local residuals are available, route the full witness-based pair through the existing candidate-selection cascade and re-check the downstream forgetful chain

### Tasks

1. Ensure the chain still collapses cleanly:
   - `canonical next-left phase-compatible promotion` or replacement event-level promotion
   - `canonical next-left phase-compatible minimality` or replacement event-level minimality
   - `candidate selection`
   - `candidate exclusion`
   - `no simple step`
   - existing stream-side cascade
2. Confirm no redundant wrappers were introduced.
3. Update `PaperCodeMapping.lean` only if public symbols changed or stabilized.

### Success Criteria

- upper convergence/theorem-source entrypoints still build
- new lower layer reduces, rather than expands, the actual mathematical burden

## Milestone 6: Verification and Scientific Audit

### Objective

Verify not just compilation but semantic honesty.

### Progress

- DONE: `Collatz.Epochs.LongEpochs` builds after introducing the new negative
  bridge result for the phase-compatible witness
- DONE: full `lake build` now passes again after synchronizing
  `Collatz.Mixing.PhaseMixing` with the current `Q_t`/`p_touch` semantics
- DONE: the current negative result is now scientifically cleaner:
  it isolates witness-language mismatch rather than geometric nonexistence
- DONE: the stronger seam-level obstruction also now builds:
  the current interface cannot simultaneously support boundary admissibility and
  witness-relative next-left minimality on the canonical aperiodic skeleton
- DONE: the split replacement interface also builds, and full `lake build`
  remains green after wiring it into `candidate exclusion`
- DONE: the new split-normalization obstruction also builds, and full
  `lake build` remains green after adding it
- DONE: the stronger structured-seam redesign also builds, and full
  `lake build` remains green after wiring it to candidate exclusion
- DONE: the stronger no-go result for index/order-only structured outputs also
  builds, and full `lake build` remains green after adding it
- DONE: the strongest consumer-driven no-go result also builds, and full
  `lake build` remains green after adding it
- DONE: the new certificate-level seam also builds, and full `lake build`
  remains green after adding:
  - the boundary certificate object and source
  - the certificate-level comparison guard theorem
  - the certificate-to-event-witness adapter no-go theorem
  - the corresponding actual-skeleton wrappers

### Tasks

1. Run `lake build` for the edited modules.
2. Check diagnostics/lints for changed files.
3. Review each new theorem source with the following checklist:
   - Is this theorem-producing semantics or only packaging?
   - Is the target weaker than or equal to what downstream really needs?
   - Did we accidentally encode canonicity/minimality stronger than justified?
   - Did we use article wording as authority instead of Lean evidence?

### Success Criteria

- build passes
- no new lints from the edited files
- no theorem target remains "accepted only because it matches the paper"

## Daily Decision Tree

### Best Case

- Milestone 1 is already stable
- Milestone 2 is already closed by a local theorem-producing source
- Milestone 4 begins or closes promotion

### Good Case

- Milestone 4 shows the current proxy is still not the right target
- Milestone 3 replaces it with a better event-level notion
- Milestone 4 is reformulated around the corrected target

### Acceptable Case

- no new proof closes
- but one invalid or over-strong theorem target is replaced by a better one

This still counts as progress because it reduces future proof waste.

## Deliverables for End of Day

By the end of tomorrow, aim to have one of these outcomes:

1. a proved source for `canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_promotion_semantics`
2. a replacement event-level admissibility object plus repaired lower interfaces
3. a local theorem or impossibility result showing why the current proxy still cannot support promotion from `simpleStep`

Current achieved outcome: item 3, now in the further strengthened form that the
remaining obstruction lies strictly below `eventAdmissible`: the concrete
boundary branch can be theorem-produced up to a stronger boundary certificate,
while the forgetful comparison route is ruled out and the only live residual is
the certificate-to-direct-event-conflict adapter seam.

## Non-Goals for Tomorrow

- do not rewrite the article first
- do not add new high-level convergence wrappers unless a lower theorem source already exists
- do not optimize naming or documentation before the theorem target stabilizes
- do not treat matching the paper as evidence that the Lean target is correct

## First Action Tomorrow

Open:

- `Collatz/Epochs/LongEpochs.lean`
- `Collatz/Convergence/MainTheorem.lean`

Then perform a 15-20 minute audit focused only on:

- `Epochs.BoundaryPromotedSelectedCertificateOn`
- `Epochs.GapLongPhaseReturnsBoundaryPromotedSelectedCertificateEventWitnessAdapterOn`
- which minimal extra semantic field is still missing from the certificate to
  theorem-produce the exact boundary event witness consumed by
  `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftSplitEventConflictOn`

The witness-selection audit is no longer the main frontier. The next active
audit should decide whether the remaining obstruction is solved by one minimal
certificate enrichment, or whether the direct event-conflict consumer itself is
still asking for the wrong local object.
