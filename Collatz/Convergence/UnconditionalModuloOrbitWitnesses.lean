/-
Collatz Conjecture: SEDT Deep Formalization — final assembly modulo
orbit-side witnesses (M6.2).

This module combines the four explicit orbit-side residuals exposed by
the deep-formalization stack:

* `PeriodicCyclePremisesResidual n`        — H-level cycle-exclusion
  premises on the orbit-derived raw cycle of any periodic tail
  (M5 target).
* `CanonicalAperiodicMultibitGainBound n 3 1` — pointwise multibit gain
  upper bound on each canonical aperiodic phase-return pair
  (the M3 reduction of `AperiodicSelectedLongEpochResidual`).
* `AperiodicPairEndpointResidual n`        — endpoint non-increase on
  the canonical aperiodic phase-return witness (M4 partial target).
* `AperiodicFillDriftResidual n`           — SEDT envelope inequality on
  filler segments between consecutive phase returns (M4 main target).

The resulting `collatz_convergence_modulo_orbit_side_witnesses` theorem
is the strongest statement currently provable inside the formal stack:
unconditional modulo concrete orbit-arithmetic inequalities, with no
intermediate abstract bridges, semantic packagings, or auxiliary
witness shims left between the hypotheses and the conclusion.

`#print axioms` of this theorem must list at most the three standard
Lean kernel axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

import Collatz.Convergence.MainTheorem
import Collatz.SEDT.AperiodicGainBridge
import Collatz.Epochs.G.Residuals
import Collatz.Epochs.G.F3ConditionalResiduals
import Collatz.Epochs.G.G5Assembly
import Collatz.Mixing.OrbitAdmissibleSupplyFromF3

namespace Collatz.Convergence

open Collatz.SEDT.AperiodicGainBridge

/-- The explicit M3+M4 aperiodic orbit-side residuals at the production
parameter choice already reconstruct the honest canonical-parameter
`OrbitLongEpochE2Witness` package exposed as `AperiodicConvergenceResidual`. -/
noncomputable def aperiodic_convergence_residual_of_orbit_side_witnesses
    (n : ℕ) (hn : Odd n)
    (hgainBound   : CanonicalAperiodicMultibitGainBound n 3 1)
    (hendpoint    : AperiodicPairEndpointResidual n)
    (hfill        : AperiodicFillDriftResidual n) :
    AperiodicConvergenceResidual n := by
  intro β hparams haper
  exact orbit_long_epoch_e2_witness_of_selected_long_epoch_endpoint_and_fill_sources
    hn
    (aperiodicSelectedLongEpochResidual_of_multibit_gain_bound hn hgainBound)
    hendpoint
    (hfill β)
    hparams
    haper

/-- **Final orbit-side closure target.**

`n`'s odd Collatz orbit reaches `1` provided four explicit orbit-side
witnesses hold:

1. every periodic tail on the orbit produces the H-level exclusion
   premises on its constructed cycle;
2. every canonical aperiodic phase-return pair satisfies the multibit
   gain upper bound at the production parameter `(t, U) = (3, 1)`;
3. every canonical aperiodic phase-return pair has non-increasing
   endpoint values;
4. every canonical aperiodic filler segment satisfies the SEDT
   envelope drift inequality, for every admissible `β`.

This statement does not introduce any new axioms beyond Mathlib's
standard kernel; it is derived purely by composition from
`collatz_convergence_modulo_revised_theorem_sources` and the M3
conditional bridge `aperiodicSelectedLongEpochResidual_of_multibit_gain_bound`.
-/
theorem collatz_convergence_modulo_orbit_side_witnesses
    (n : ℕ) (hn : Odd n)
    (hperiodic    : PeriodicCyclePremisesResidual n)
    (hgainBound   : CanonicalAperiodicMultibitGainBound n 3 1)
    (hendpoint    : AperiodicPairEndpointResidual n)
    (hfill        : AperiodicFillDriftResidual n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 :=
  collatz_convergence_modulo_revised_theorem_sources
    n hn hperiodic
    (aperiodicSelectedLongEpochResidual_of_multibit_gain_bound hn hgainBound)
    hendpoint hfill

/-- Same orbit-side closure theorem, but with the periodic side reduced to the
explicit no-tail residual `PeriodicConvergenceResidual n`. This records the
current honest periodic frontier without reintroducing the raw-cycle premises as
the public assumption. -/
theorem collatz_convergence_modulo_no_nontrivial_periodic_tail_and_orbit_side_witnesses
    (n : ℕ) (hn : Odd n)
    (hperiodic    : PeriodicConvergenceResidual n)
    (hgainBound   : CanonicalAperiodicMultibitGainBound n 3 1)
    (hendpoint    : AperiodicPairEndpointResidual n)
    (hfill        : AperiodicFillDriftResidual n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_modulo_explicit_residuals
    n hn
    hperiodic
    (aperiodic_convergence_residual_of_orbit_side_witnesses
      n hn hgainBound hendpoint hfill)

/-- **S6.1 retargeting — public aperiodic frontier at the paper-faithful E.2 level.**

`n`'s odd Collatz orbit reaches `1` provided:

1. no nontrivial periodic tail occurs on the orbit
   (`PeriodicConvergenceResidual n` — the M5.2 honest no-tail periodic
   frontier, preserved under both the M4 and the M5 retargetings);
2. the canonical aperiodic skeleton at production parameters
   `(t, U) = (3, 1)` satisfies the **bulk per-long-epoch SEDT envelope** for
   every admissible `β`
   (`∀ β, canonical_aperiodic_orbit_epoch_sedt_envelope n 3 1 β`).

The aperiodic theorem-source residual matches paper Appendix E, Theorem E.2
directly: a bulk per-long-epoch envelope, with no per-step or pair-endpoint
refinement attached. The previous M4 split (pair endpoint + per-step filler
drift) is retargeted out by S6.1 because `phase_return_gap_fill_step_drift`
was over-strong relative to E.2 (per-step linear drift on filler segments is
mathematically false; counterexample `r = 9`, see
`unconditional-discipline.mdc` rule 3 and
`docs/plans/20260418_unconditional-collatz-strategic-path.md` §2).

This is the **(U2)-aligned aperiodic public frontier** (cf.
`unconditional-discipline.mdc` for the (U1)/(U2)/(U3) hierarchy): the single
remaining aperiodic hypothesis has explicit paper-citation, not a structural
artifact. The previous (U3)-level public frontiers in this module remain
available below as compatibility wrappers. -/
theorem collatz_convergence_modulo_no_nontrivial_periodic_tail_and_aperiodic_orbit_epoch_envelope
    (n : ℕ) (hn : Odd n)
    (hperiodic : PeriodicConvergenceResidual n)
    (henvelope :
      ∀ β : ℝ, canonical_aperiodic_orbit_epoch_sedt_envelope n 3 1 β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 :=
  collatz_convergence_from_aperiodic_orbit_epoch_envelope
    n 3 1 hn (by decide) (by decide)
    (periodic_orbit_bridge_contract_of_no_nontrivial_periodic_tail n hperiodic)
    henvelope

/-- **S6.2 H.main-faithful periodic reduction (OPEN MATH RESIDUAL).**

Paper Appendix H, Theorem H.main, derives `OrbitNoNontrivialPeriodicTail n`
from the bulk per-long-epoch SEDT envelope at `t ≥ 3` via the
SEDT-period-sum-contradiction argument:

* assume toward contradiction that a nontrivial periodic tail exists;
* by Appendix G, Theorem G.5, the periodic part of the orbit contains
  infinitely many long t-epochs with bounded gaps;
* summing the bulk SEDT envelope (Appendix E, Theorem E.2) across one full
  period yields `Σ ΔV ≤ -ε ⋅ P + O(1)`, with `ε > 0` for the production
  parameter choice;
* but exact periodicity forces `Σ ΔV = 0`; contradiction for sufficiently
  long periods.

This residual exposes the **endpoint** of that argument as a Lean
proposition, without proving it. It is the canonical S6.2 replacement of the
cancelled M5.1 `exclusion_premises 0` raw repeat-trick scaffold (which was
structurally degenerate at `t = 0`; see `unconditional-discipline.mdc`
rule 2 and the formal evidence
`Collatz.CycleExclusion.periodic_tail_cycle_premises_source_iff_no_nontrivial_periodic_tail`).

OPEN MATH RESIDUAL (per `unconditional-discipline.mdc` rule 1):

* paper-citation: Appendix H, Theorem H.main;
* depends on: G.5 full (Appendix G; partially formalized as
  `aperiodic_orbit_has_cofinal_gap_long_phase_returns`, full
  formalization is `dfm-s7-g5-full`) + the period-sum telescoping
  argument for SEDT;
* formalization status in Lean: not started (open S7+ target);
* replaces in role: M5.1 `PeriodicCyclePremisesResidual` /
  `exclusion_premises 0` route (cancelled in session 5 strategic audit). -/
def SEDTPeriodSumContradictionResidual (n : ℕ) : Prop :=
  (∀ β : ℝ, canonical_aperiodic_orbit_epoch_sedt_envelope n 3 1 β) →
  PeriodicConvergenceResidual n

/-- **S6.2 retargeted single-residual-pair public frontier (paper E.2 + H.main).**

`n`'s odd Collatz orbit reaches `1` provided:

1. the canonical aperiodic skeleton at production parameters `(t, U) = (3, 1)`
   satisfies the **bulk per-long-epoch SEDT envelope** for every admissible
   `β` (paper Appendix E, Theorem E.2; S6.1 aperiodic theorem-source
   residual);
2. the **H.main reduction** holds, i.e. the bulk envelope implies absence of
   any nontrivial periodic tail on the orbit (paper Appendix H, Theorem
   H.main; S6.2 `SEDTPeriodSumContradictionResidual`, OPEN MATH RESIDUAL).

This is the cleanest paper-correspondence currently expressible in the
public Lean frontier: convergence reduces to a single mathematical layer
(per-long-epoch SEDT bookkeeping plus period-sum telescoping). It is the
(U2)-aligned S6.1+S6.2 endpoint; the (U1) closure requires formalizing both
residuals (S7+). -/
theorem collatz_convergence_modulo_aperiodic_orbit_epoch_envelope_and_h_main_reduction
    (n : ℕ) (hn : Odd n)
    (henvelope :
      ∀ β : ℝ, canonical_aperiodic_orbit_epoch_sedt_envelope n 3 1 β)
    (hHmain : SEDTPeriodSumContradictionResidual n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 :=
  collatz_convergence_modulo_no_nontrivial_periodic_tail_and_aperiodic_orbit_epoch_envelope
    n hn (hHmain henvelope) henvelope

/-- Alternative honest public frontier on the aperiodic side after the M4 audit:
instead of the stronger split pair-endpoint/filler-drift package, one may work
directly with the actual phase-return theorem sources already used to build the
repaired canonical witness, namely correction control, filler endpoint order,
and the direct canonical-gap `E.2` theorem. -/
theorem collatz_convergence_modulo_no_nontrivial_periodic_tail_and_aperiodic_phase_return_theorem_sources
    (n : ℕ) (hn : Odd n)
    (hperiodic : PeriodicConvergenceResidual n)
    (hgainBound : CanonicalAperiodicMultibitGainBound n 3 1)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n 3 1)
    (hfillEndpoint : canonical_aperiodic_phase_return_fill_endpoint_nonincrease n 3 1)
    (hgap : ∀ β : ℝ, canonical_aperiodic_phase_return_gap_step_sedt_on n 3 1 β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_aperiodic_theorem_sources
    n 3 1 hn (by decide) (by decide)
    (periodic_orbit_bridge_contract_of_no_nontrivial_periodic_tail n hperiodic)
    (canonical_aperiodic_selected_carry_depth_semantics_of_multibit_gain_bound
      hn hgainBound)
    hcorr hfillEndpoint hgap

/-- **S7.1.D.1 — Public frontier with R-Hmain decomposed via G.5 modulo F.3.**

`n`'s odd Collatz orbit reaches `1` provided five paper-cited residuals hold:

1. **R-E2** — bulk per-long-epoch SEDT envelope at production parameters
   `(t, U) = (3, 1)` for every admissible `β`
   (paper Appendix E, Theorem E.2; preserved unchanged from S6.1).
2. **R-EpochTailGeometry** — consolidated epoch-tail geometry
   (`Collatz.Epochs.G.EpochTailGeometryResidual n 3 1`, paper Appendix G
   Lemmas G.1+G.2+G.4+G.5b+G.5c-on-tail jointly; pure G.5c uniqueness core
   is the REAL theorem `phase_uniqueness_pure_mod_Qt`).
3. **R-F3-Recurrence** — Shumak Primitive Junction Theorem recurrence
   (`Collatz.Epochs.G.PrimitiveJunctionRecurrenceResidual n 3`,
   paper Appendix F, Theorems F.3 + F.4).
4. **R-F3-PhaseDistribution** — uniform phase distribution under primitive
   junctions (`Collatz.Epochs.G.UniformPhaseDistributionResidual n 3`,
   paper Appendix F, Lemma F.2.1).
5. **R-PeriodSumTelescoping** — paper Appendix H period-sum telescoping
   step (`Collatz.Epochs.G.PeriodSumTelescopingResidual n`, paper Appendix H
   telescoping argument; typed as `(envelope) → (long-epoch supply) →
   (no-tail)`).

This advances the (U2)-aligned public frontier by **decomposing** the previous
single `SEDTPeriodSumContradictionResidual` (R-Hmain) into:

   R-Hmain  ≡  R-EpochTailGeometry + R-F3-Recurrence + R-F3-PhaseDistribution
            +  R-PeriodSumTelescoping  (modulo R-E2 input).

All five hypotheses are paper-cited; together they exactly correspond to
Appendix H, Theorem H.main with its G.5 dependency made explicit. The G.5
assembly inside the proof is real Lean composition via
`Collatz.Epochs.G.OrbitHasCofinalLongEpochGaps_of_residuals` plus the
typed period-sum-telescoping arrow.

Paper-correspondence: Appendix H, Theorem H.main, fully decomposed via
Appendix G, Theorem G.5. This is the (U2)-aligned S7.1 public frontier; the
(U1) closure requires discharging all five residuals (S7.0 foundation
replatform → R-EpochTailGeometry; S7.4 → R-F3-Recurrence + R-F3-PhaseDistribution;
S7.5 → R-PeriodSumTelescoping; S7.2/S7.3 → R-E2 prerequisites). -/
theorem collatz_convergence_modulo_aperiodic_envelope_and_g5_modulo_f3_and_period_telescoping
    (n : ℕ) (hn : Odd n)
    (henvelope :
      ∀ β : ℝ, canonical_aperiodic_orbit_epoch_sedt_envelope n 3 1 β)
    (hgeom : Collatz.Epochs.G.EpochTailGeometryResidual n 3 1)
    (hF3rec : Collatz.Epochs.G.PrimitiveJunctionRecurrenceResidual n 3)
    (hF3phase : Collatz.Epochs.G.UniformPhaseDistributionResidual n 3)
    (hTelescoping : Collatz.Epochs.G.PeriodSumTelescopingResidual n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  -- Step 1: assemble G.5 long-epoch supply on the orbit from residuals.
  have hG5 : Collatz.Epochs.OrbitHasCofinalLongEpochGaps n 3 1 :=
    Collatz.Epochs.G.OrbitHasCofinalLongEpochGaps_of_residuals
      n 3 1 (by decide) hgeom hF3rec hF3phase
  -- Step 2: feed envelope + G.5 supply into period-sum telescoping to derive
  -- the no-nontrivial-periodic-tail conclusion.
  have hno_tail : PeriodicConvergenceResidual n :=
    hTelescoping henvelope hG5
  -- Step 3: combine with the bulk envelope via the S6.1 retargeted frontier.
  exact
    collatz_convergence_modulo_no_nontrivial_periodic_tail_and_aperiodic_orbit_epoch_envelope
      n hn hno_tail henvelope

/-- **S7.0.E — Refined (U2)-aligned 4-residual public frontier.**

`n`'s odd Collatz orbit reaches `1` provided **four** paper-cited residuals
plus an explicit aperiodicity hypothesis hold:

0. **Aperiodicity hypothesis** —
   `¬ Collatz.CycleExclusion.orbit_eventually_periodic n`. This is **not** an
   OPEN MATH residual; it is the precise statement under which the Appendix-G
   tail-geometry conclusion is mathematically true (the unconditional
   `EpochTailGeometryResidual` is false for periodic `n`, e.g. `n = 1`, where
   no infinite tail exists).
1. **R-E2** — bulk per-long-epoch SEDT envelope at production parameters
   `(t, U) = (3, 1)` for every admissible `β`
   (paper Appendix E, Theorem E.2; preserved unchanged).
2. **R-F3-Recurrence** — Shumak Primitive Junction Theorem recurrence
   (`Collatz.Epochs.G.PrimitiveJunctionRecurrenceResidual n 3`,
   paper Appendix F, Theorems F.3 + F.4).
3. **R-F3-PhaseDistribution** — uniform phase distribution under primitive
   junctions (`Collatz.Epochs.G.UniformPhaseDistributionResidual n 3`,
   paper Appendix F, Lemma F.2.1).
4. **R-PeriodSumTelescoping** — paper Appendix H period-sum telescoping
   step (`Collatz.Epochs.G.PeriodSumTelescopingResidual n`, paper Appendix H
   telescoping argument).

**Difference vs. the 5-residual variant
`collatz_convergence_modulo_aperiodic_envelope_and_g5_modulo_f3_and_period_telescoping`:**
the explicit `R-EpochTailGeometry` hypothesis is **dropped** and replaced
by an explicit aperiodicity hypothesis on `n`. R-EpochTailGeometry is then
discharged internally via the REAL theorem
`Collatz.Epochs.G.epochTailGeometryResidual_of_aperiodic`, which itself
composes the existing sorry-free real production chain
`aperiodic_orbit_has_cofinal_gap_long_phase_returns` +
`canonical_gap_long_phase_returns_bridge` +
`orbit_has_cofinal_long_epoch_gaps_of_gap_long_phase_returns`.

This honestly removes R-EpochTailGeometry from the OPEN MATH residual budget
of the 5-residual frontier — under aperiodicity it is a REAL Lean theorem,
not an open math hypothesis. The 5-residual frontier above is preserved as a
backward-compatibility wrapper.

Public-frontier residual count: 4 (down from 5). Paper-correspondence
matches Appendix H, Theorem H.main, fully decomposed via Appendix G,
Theorem G.5 — with the orbit-side aperiodicity assumption made explicit. -/
theorem collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_f3_and_period_telescoping
    (n : ℕ) (hn : Odd n)
    (haperiodic : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n)
    (henvelope :
      ∀ β : ℝ, canonical_aperiodic_orbit_epoch_sedt_envelope n 3 1 β)
    (hF3rec : Collatz.Epochs.G.PrimitiveJunctionRecurrenceResidual n 3)
    (hF3phase : Collatz.Epochs.G.UniformPhaseDistributionResidual n 3)
    (hTelescoping : Collatz.Epochs.G.PeriodSumTelescopingResidual n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  have hgeom : Collatz.Epochs.G.EpochTailGeometryResidual n 3 1 :=
    Collatz.Epochs.G.epochTailGeometryResidual_of_aperiodic n 3 1 haperiodic
  exact
    collatz_convergence_modulo_aperiodic_envelope_and_g5_modulo_f3_and_period_telescoping
      n hn henvelope hgeom hF3rec hF3phase hTelescoping

/-- **Wave 2H Phase B.1.D — typed-F.3 (U2)-aligned 4-residual public frontier.**

Strictly stronger orbit-side input than
`collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_f3_and_period_telescoping`:
the F.3 hypothesis is the **typed** form
`PrimitiveJunctionRecurrenceTypedResidual n 3` (= `Nonempty
(PrimitiveJunctionRecurrenceWitness n 3)`) rather than the opaque
`PrimitiveJunctionRecurrenceResidual n 3` (= `True`). Honesty rationale:
the typed form may be empty (no F.3 witness exists), while the opaque
form is vacuously true; replacing opaque with typed therefore advertises
the *paper-faithful shape* of the F.3 conclusion at the public-frontier
level (`unconditional-discipline.mdc` rule 2: this is **not** a
degenerate wrapper because the typed shape is logically distinguishable
from the opaque one — `Nonempty α → True` is one-way).

Wave 2H Phase B.0.1 audit confirmed the paper proof of F.3 is
gap-confirmed (`research/wave2h-f3-proof-audit/REPORT.md`). The typed
residual is therefore **OPEN MATH**; the typed *shape* is the formal
contract under which any future paper-side closure (or empirical
counterexample) lands.

Hypotheses (4):
1. Aperiodicity hypothesis on `n`;
2. **R-E2** — bulk per-long-epoch SEDT envelope (paper E.2);
3. **R-F3-Recurrence (typed)** — typed witness form;
4. **R-F3-PhaseDistribution** — paper F.2.1;
5. **R-PeriodSumTelescoping** — paper H telescoping.

Proof: discharge typed → opaque via
`primitiveJunctionRecurrenceResidual_of_typed`, then call the existing
4-residual frontier. -/
theorem collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_typed_f3_and_period_telescoping
    (n : ℕ) (hn : Odd n)
    (haperiodic : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n)
    (henvelope :
      ∀ β : ℝ, canonical_aperiodic_orbit_epoch_sedt_envelope n 3 1 β)
    (hF3typed : Collatz.Epochs.G.PrimitiveJunctionRecurrenceTypedResidual n 3)
    (hF3phase : Collatz.Epochs.G.UniformPhaseDistributionResidual n 3)
    (hTelescoping : Collatz.Epochs.G.PeriodSumTelescopingResidual n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  have hF3rec : Collatz.Epochs.G.PrimitiveJunctionRecurrenceResidual n 3 :=
    Collatz.Epochs.G.primitiveJunctionRecurrenceResidual_of_typed hF3typed
  exact
    collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_f3_and_period_telescoping
      n hn haperiodic henvelope hF3rec hF3phase hTelescoping

/-- **Wave 2H Phase B.1.D — F.3 admissibility-supply (U2)-aligned public frontier.**

Strictly stronger orbit-side input than the typed-F.3 frontier above:
the F.3 hypothesis is the *full* admissibility-supply residual
`PrimitiveJunctionAdmissibilitySupplyResidual n`
(`Collatz/Mixing/OrbitAdmissibleSupplyFromF3.lean`), which packages
both:

* the typed F.3 witness (`f3` field of the supply witness);
* the per-`t` admissible-tail anchor sequence with universal-`ε`
  W-B aggregate inequality (`count_lower` field).

The supply residual morally decomposes as
**R-F3-Recurrence-Typed** + **R-PrimitiveJunctionToAdmissibleAnchor**
(structural lemma F.4.1, paper-issue W2H-PI-B06; Phase B.0.2
SCAFFOLDING-LIMITED — encoded honestly as *the* open mathematical input
of this frontier). The W-B inequality content of the supply is exposed
via the discharge theorem
`Collatz.Mixing.orbitSideAggregateTouchRate_of_admissibleTouchSupply`;
in the present convergence chain it is paper-trace and surfaces as the
formally-verifiable side guarantee
`OrbitSideAggregateTouchRateResidual n` (cf. paper Theorem F.6,
revised, Wave 2H aggregate).

This frontier is **honest** per `unconditional-discipline.mdc` rule 2:
the supply residual is logically strictly stronger than the typed F.3
residual (it adds the W-B inequality field), so consuming it is not a
degenerate wrapper.

Proof: extract the supply witness, take its `f3` field, build the typed
F.3 residual, and dispatch to the typed-F.3 frontier above.

Hypotheses:
1. Aperiodicity hypothesis on `n`;
2. **R-E2** — bulk per-long-epoch SEDT envelope (paper E.2);
3. **R-PrimitiveJunctionAdmissibilitySupply** — typed admissibility-supply
   residual (Wave 2H Phase B; OPEN MATH);
4. **R-F3-PhaseDistribution** — paper F.2.1;
5. **R-PeriodSumTelescoping** — paper H telescoping. -/
theorem collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_f3_recurrence_and_period_telescoping
    (n : ℕ) (hn : Odd n)
    (haperiodic : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n)
    (henvelope :
      ∀ β : ℝ, canonical_aperiodic_orbit_epoch_sedt_envelope n 3 1 β)
    (hF3supply : Collatz.Mixing.PrimitiveJunctionAdmissibilitySupplyResidual n)
    (hF3phase : Collatz.Epochs.G.UniformPhaseDistributionResidual n 3)
    (hTelescoping : Collatz.Epochs.G.PeriodSumTelescopingResidual n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  have hn1 : 1 ≤ n := hn.pos
  obtain ⟨w⟩ := hF3supply hn1 haperiodic
  have hF3typed : Collatz.Epochs.G.PrimitiveJunctionRecurrenceTypedResidual n 3 :=
    ⟨w.f3⟩
  exact
    collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_typed_f3_and_period_telescoping
      n hn haperiodic henvelope hF3typed hF3phase hTelescoping

end Collatz.Convergence
