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
- ACTIVE NEXT STEP: populate the new concrete boundary event theorem source
  itself on the canonical aperiodic skeleton, i.e. attack
  `Convergence.canonical_aperiodic_phase_return_fill_boundary_promoted_selected_event_source_semantics`.
  Only after that should we try to prove a concrete admissibility bridge into a
  chosen witness-relative language.

### Files

- `Collatz/Epochs/LongEpochs.lean`
- `Collatz/Convergence/MainTheorem.lean`
- `Collatz/Documentation/PaperCodeMapping.lean` only if public names stabilize

### Tasks

1. Identify what is missing from the proxy:
   - actual selected-event content,
   - orbit/value semantics,
   - or a more honest canonical-choice witness.
2. Prove a local theorem:
   - redesign only the lower concrete layer,
   - keep the generic `promotion/minimality/selection` chain stable,
   - avoid adding new upper convergence wrappers.
3. Rewire the concrete next-left constructors and actual-skeleton wrappers to the new target.

### Success Criteria

- the lower target becomes more proof-oriented and less misleading
- the redesign is strictly local to the concrete next-left layer
- `lake build` passes for edited Lean modules

### Failure Mode

If the event-level redesign still lacks any realistic lower theorem source, stop and document the missing semantic object rather than wrapping it in stronger assumptions.

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

Current achieved outcome: item 3.

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

- `Epochs.CanonicalNextLeftPhaseCompatibleOn`
- `Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotionOn`
- `Convergence.canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_promotion_semantics`

This audit is now complete: the current phase-compatibility proxy is not sufficient for honest promotion from `simpleStep`, so further filler-side work should proceed under Milestone 3.
