/-
Axiom check after the M1–M3 deep-formalization pass, the S6.1+S6.2
session-6 retargeting, the S7.1 G.5-modulo-F.3 decomposition, the
S7.0.E formal-first refinement of R-EpochTailGeometry, the S7.2
split F.6/F.7 touch-frequency theorem-source hardening, the
**Wave 1 of S7.2 Path 1.algebraic** local-affine-pair constructor
that closes the algebraic core of paper Lemma D.10.b, and the
**Wave 2A** landing of (i) the paper Definition F.0.1 admissibility
predicate `AdmissibleTailF01` (E.1 substep — algebraic interface for
the F.0.1 coset condition on the homogenized entry residue) plus
(ii) the algebraic carry brick `M_k_succ_of_lt` / `M_k_succ_of_gt`
/ `M_k_ModEq_succ_of_lt` for paper Sublemma D.10 on the
sub- and super-diagonal branches (E.2 substep — algebraic recurrence
form of the carry, with the diagonal `+5`-shift jump deliberately
left as a separate brick).

Goal of this file: demonstrate that the entire deep-formalization stack —
M1 (algebraic foundations) + M2 (depth bookkeeping) + M3 (canonical
aperiodic reduction) + S6.1 (paper-E.2-faithful aperiodic theorem-source
residual) + S6.2 (paper-H.main-faithful periodic reduction residual) +
S7.1 (paper-G.5-modulo-F.3 decomposition of R-Hmain) — does not introduce
any new axioms beyond Mathlib's standard kernel
(`propext`, `Classical.choice`, `Quot.sound`).

Public theorems checked, by layer:

* M3 + legacy U3 frontiers (M6.1/M6.2):
  * `collatz_convergence_modulo_revised_theorem_sources`
  * `collatz_convergence_modulo_orbit_side_witnesses`
  * `collatz_convergence_modulo_no_nontrivial_periodic_tail_and_orbit_side_witnesses`
  * `aperiodicSelectedLongEpochBridge_of_multibit_gain_bound`
  * `aperiodicSelectedLongEpochResidual_of_multibit_gain_bound`
  * `canonical_aperiodic_selected_carry_depth_semantics_of_multibit_gain_bound`

* S6.1 retargeted (paper E.2, bulk per-long-epoch envelope; replaces the
  cancelled M4 split pair-endpoint + per-step filler-drift route):
  * `collatz_convergence_from_aperiodic_orbit_epoch_envelope`
  * `collatz_convergence_modulo_no_nontrivial_periodic_tail_and_aperiodic_orbit_epoch_envelope`

* S6.2 retargeted (paper H.main reduction; replaces the cancelled M5.1
  `exclusion_premises 0` raw repeat-trick scaffold; encodes the open
  H.main mathematical residual `SEDTPeriodSumContradictionResidual`
  as an explicit Lean hypothesis):
  * `collatz_convergence_modulo_aperiodic_orbit_epoch_envelope_and_h_main_reduction`

* S7.1 retargeted (paper Appendix G, Theorem G.5 decomposition; the previous
  single R-Hmain residual is now decomposed into R-EpochTailGeometry +
  R-F3-Recurrence + R-F3-PhaseDistribution + R-PeriodSumTelescoping; the pure
  group-theoretic core of G.5c is the REAL theorem
  `phase_uniqueness_pure_mod_Qt`):
  * `collatz_convergence_modulo_aperiodic_envelope_and_g5_modulo_f3_and_period_telescoping`
  * `Collatz.Epochs.G.phase_uniqueness_pure_mod_Qt`

* S7.0.E refined (formal-first refinement of R-EpochTailGeometry — the
  unconditional residual is replaced by an explicit aperiodicity hypothesis
  on `n` and discharged internally by the REAL theorem
  `epochTailGeometryResidual_of_aperiodic`, dropping the public-frontier
  residual count from 5 to 4):
  * `Collatz.Epochs.G.epochTailGeometryResidual_of_aperiodic`
  * `collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_f3_and_period_telescoping`

* S7.2 hardened (paper Appendix F.6/F.7 split into an honest two-sided
  admissible-tail theorem-source plus an explicit `tails -> raw prefix`
  bridge slot, with a derived one-sided E.2-facing corollary):
  * `Collatz.Mixing.admissible_tail_touch_frequency_witness_of_residual`
  * `Collatz.Mixing.admissible_tail_touch_lower_bound_of_residual`
  * `Collatz.Mixing.raw_prefix_touch_frequency_residual_of_bridge`

* S7.2 Wave 1 Path 1.algebraic (paper Lemma D.10.b: local affine pair
  semantics on selected admissible tails; algebraic core of Q_t-periodicity
  mod 2^t derived from `Homogenization` + `OrdFact.three_pow_Qt_modEq_one`,
  with the orbit-side "exactly one touch per Q_t-block" claim kept as an
  explicit input field rather than hidden behind a proxy):
  * `Collatz.OrdFact.three_pow_Qt_modEq_one`
  * `Collatz.Mixing.selectedTailTouchSemantics_of_localAffinePair`
  * `Collatz.Mixing.admissibleTailTouchFrequencyTheoremSource_of_localAffinePair`
  * `Collatz.Mixing.admissibleTailTouchFrequencyResidual_of_localAffinePairResidual`

* S7.2 Wave 2A / **Wave 2E revision** (E.1 substep — paper Definition F.0.1
  admissibility predicate, **revised** form of Wave 2D / route α₃: the
  predicate is now the algebraic-coset test on `v + 3^t · M_entry` rather
  than on `M_entry` alone, biconditionally equivalent to "late-window
  touchCount = 1" by `wave2-d10b-empirical/REPORT-reverse-engineering.md`
  §2; orbit-agnostic algebraic form that the orbit-side supplier of
  `LocalAffinePairSemantics` will instantiate):
  * `Collatz.Mixing.AdmissibleTailF01_iff_exists_pow`
  * `Collatz.Mixing.AdmissibleTailF01_witness_lt_Qt`

* S7.2 Wave 2A (E.2 substep — paper Sublemma D.10 algebraic carry brick
  on the sub- and super-diagonal branches; the exact natural-number form
  on each branch and the `Int.ModEq` lift on the sub-diagonal branch.
  The diagonal `d_k = k` `+5`-shift jump is intentionally NOT covered
  by these bricks and remains a separate algebraic substep):
  * `Collatz.SEDT.AffineNumerator.M_k_succ_of_lt`
  * `Collatz.SEDT.AffineNumerator.M_k_succ_of_gt`
  * `Collatz.SEDT.AffineNumerator.M_k_ModEq_succ_of_lt`

* S7.2 **Wave 2F** (algebraic admissibility ⇒ touchCount = 1 bridge):
  the elementary §2 derivation from
  `wave2-d10b-empirical/REPORT-reverse-engineering.md` formalised on
  the algebraic core. Given the per-plateau-anchored algebraic data
  `(Mentry, v : ZMod (2^t))` and the revised paper Definition F.0.1
  `AdmissibleTailF01 t Mentry v`, the touch count over the canonical
  `Q_t t = 2^(t-2)` window equals exactly `1`. Closes the algebraic-side
  direction of the biconditional `revised F.0.1 ⇔ late-window
  touchCount = 1`. Helper bricks (added in `Collatz/Epochs/OrdFact.lean`)
  show that `(3 : ZMod (2^t))`, `(5 : ZMod (2^t))`, `(3 : ZMod (2^t))⁻¹`,
  and the natural-number cast of `s_t t` are units:
  * `Collatz.OrdFact.isUnit_three_zmod`
  * `Collatz.OrdFact.isUnit_five_zmod`
  * `Collatz.OrdFact.isUnit_three_inv_zmod`
  * `Collatz.OrdFact.natCast_s_t_eq`
  * `Collatz.OrdFact.isUnit_natCast_s_t`
  * `Collatz.Mixing.AdmissibleTailF01.touch_count_eq_one`
  * `Collatz.Mixing.AdmissibleTailF01.touch_count_eq_one_expanded`

* S7.2 **Wave 2H** (repackage paper Theorem F.6 to one-sided aggregate
  touch-rate; replace `R-OrbitSideAdmissibleDensity` by the strictly
  weaker `R-OrbitSideAggregateTouchRate (W-B)`, exposed as
  `Collatz.Mixing.OrbitSideAggregateTouchRateResidual`. The old two-sided
  per-window F.6/F.7 chain (`AdmissibleTailTouchFrequencyResidual`,
  `AdmissibleTailTouchLowerBoundResidual`,
  `RawPrefixTouchFrequencyBridgeResidual`,
  `RawPrefixTouchFrequencyResidual`) is kept as deprecated back-compat
  aliases — see deprecation notes in `Collatz/Mixing/PhaseMixing.lean` and
  `Collatz/Mixing/TouchFrequencyBridge.lean`. The Wave 2G internal
  algebraic supplier `LocalAffinePairSemantics.one_touch_per_period` is
  retained for the deprecated path; the new public W-B residual does not
  expose a per-period `tc = 1` claim on the actual orbit. The strictness
  ordering "W-B is weaker than the previous residual / equidistribution /
  Collatz" is documented at the paper / ledger level
  (`docs/wave2h-research/paper-residual-scope.md` §5.3,
  `docs/residual-budget.md`); no Lean wrapper is produced):
  * `Collatz.Mixing.OrbitSideAggregateTouchRateResidual`
  * `Collatz.Mixing.orbit_aggregate_touch_count_lower_of_residual`

* S7.2 **Wave 2G** (orbit-faithful local algebraic-stack closure with the
  late-regime flush guard): the Wave 2F algebraic-core bridge is now lifted
  to the actual orbit-realised data carried by
  `LocalAffinePairSemantics m t i`. With the new honest fields
  `flushGuard : c k ≡ 0 (k ≥ t)`, `Mentry_eq : Mentry = M 0 - u 0`,
  `v_eq : v = u t`, the previously honest carrier
  `one_touch_per_period_input` becomes a *derived theorem*
  `LocalAffinePairSemantics.one_touch_per_period`, obtained by composing
  `AdmissibleTailF01.touch_count_eq_one_of_realized` (a real proof using
  `homogenization_principle`, `homogenized_iterate`,
  `homogenized_periodic_of_order_dvd`, `three_pow_Qt_modEq_one`, and
  Wave 2F) with the structural fields. The constructor
  `selectedTailTouchSemantics_of_localAffinePair` now derives **both**
  fields of `SelectedTailTouchSemantics` algebraically — no honest input
  for the orbit-side touch count remains. The only residual on the local
  algebraic stack is the orbit-side existence of a
  `LocalAffinePairSemantics` for every admissible tail (i.e. supplying
  the flush-guard, admissibility witness, and bridge fields on the actual
  Collatz orbit), tracked as `R-OrbitSideAdmissibleDensity`:
  * `Collatz.Mixing.AdmissibleTailF01.touch_count_eq_one_of_realized`
  * `Collatz.Mixing.LocalAffinePairSemantics.one_touch_per_period`

* S7.2 **Wave 2H Phase B** (F.3 audit + R-OrbitSideAggregateTouchRate
  discharge from typed admissibility-supply residual). Per the Phase B
  plan steps B.1.A, B.1.B, B.1.C, B.1.D, B.1.E:

  * Phase B.0.1 audit (`research/wave2h-f3-proof-audit/REPORT.md`):
    paper proof of Theorem F.3 in `F-mixing.md` §F.7 is GAP-CONFIRMED
    (Steps F.7.4 and F.7.5 both invalid). `R-F3-Recurrence` therefore
    remains an honest open math residual.
  * Phase B.0.2 reconnaissance
    (`research/wave2h-junction-admissibility/REPORT.md`): the
    structural lemma "primitive junctions are F.0.1-admissible-tail
    anchors" is SCAFFOLDING-LIMITED at present scale; encoded as a
    typed open math residual rather than a derived theorem.
  * Phase B.1.B: `PrimitiveJunctionRecurrenceWitness` typed shape +
    `PrimitiveJunctionRecurrenceTypedResidual` +
    `primitiveJunctionRecurrenceResidual_of_typed` (typed-to-opaque
    arrow). The opaque `PrimitiveJunctionRecurrenceResidual` is
    retained as a backward-compatibility alias.
  * Phase B.1.A + B.1.C: `OrbitAdmissibleTouchSupplyWitness` +
    `PrimitiveJunctionAdmissibilitySupplyResidual` (typed orbit-side
    admissibility supply, OPEN MATH).
  * Phase B.1.D: `orbitSideAggregateTouchRate_of_admissibleTouchSupply`
    (paper-trace alias `orbitSideAggregateTouchRate_of_F3_recurrence`)
    — discharge from supply to W-B; two new public frontiers in
    `UnconditionalModuloOrbitWitnesses.lean`
    (`_typed_f3_` and `_f3_recurrence_` variants):
  * `Collatz.Epochs.G.PrimitiveJunctionRecurrenceTypedResidual`
  * `Collatz.Epochs.G.primitiveJunctionRecurrenceResidual_of_typed`
  * `Collatz.Mixing.PrimitiveJunctionAdmissibilitySupplyResidual`
  * `Collatz.Mixing.orbitSideAggregateTouchRate_of_admissibleTouchSupply`
  * `Collatz.Mixing.orbitSideAggregateTouchRate_of_F3_recurrence`
  * `Collatz.Convergence.collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_typed_f3_and_period_telescoping`
  * `Collatz.Convergence.collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_f3_recurrence_and_period_telescoping`

Use `lake env lean Collatz/Tests/AxiomCheck.lean` to print the list.
Per `unconditional-discipline.mdc`, every public theorem above must
print exactly `[propext, Classical.choice, Quot.sound]`. Any regression
indicates a hidden axiom was introduced; debug by bisecting recent
deep-stack changes.
-/

import Collatz.Convergence.MainTheorem
import Collatz.Convergence.UnconditionalModuloOrbitWitnesses
import Collatz.SEDT.AperiodicGainBridge
import Collatz.Epochs.G.PhaseUniqueness
import Collatz.Epochs.G.G5Assembly
import Collatz.Epochs.G.F3ConditionalResiduals
import Collatz.Mixing.TouchFrequencyBridge
import Collatz.Mixing.TouchFrequencyHomogenization
import Collatz.Mixing.AdmissibleTail
import Collatz.Mixing.AdmissibleTailBridge
import Collatz.Mixing.AggregateTouchRate
import Collatz.Mixing.OrbitAdmissibleSupplyFromF3
import Collatz.SEDT.AffineNumerator
import Collatz.Epochs.OrdFact

open Collatz.Convergence
open Collatz.SEDT.AperiodicGainBridge

#print axioms collatz_convergence_modulo_revised_theorem_sources
#print axioms collatz_convergence_modulo_orbit_side_witnesses
#print axioms collatz_convergence_modulo_no_nontrivial_periodic_tail_and_orbit_side_witnesses
#print axioms aperiodicSelectedLongEpochBridge_of_multibit_gain_bound
#print axioms aperiodicSelectedLongEpochResidual_of_multibit_gain_bound
#print axioms canonical_aperiodic_selected_carry_depth_semantics_of_multibit_gain_bound

-- S6.1 retargeted public frontier (paper E.2 faithful).
#print axioms collatz_convergence_from_aperiodic_orbit_epoch_envelope
#print axioms collatz_convergence_modulo_no_nontrivial_periodic_tail_and_aperiodic_orbit_epoch_envelope

-- S6.2 retargeted single-residual-pair public frontier (paper E.2 + H.main).
#print axioms collatz_convergence_modulo_aperiodic_orbit_epoch_envelope_and_h_main_reduction

-- S7.1 retargeted public frontier (paper E.2 + decomposed H.main via G.5
-- modulo F.3 + period-sum telescoping). REAL group-theoretic core also checked.
#print axioms collatz_convergence_modulo_aperiodic_envelope_and_g5_modulo_f3_and_period_telescoping
#print axioms Collatz.Epochs.G.phase_uniqueness_pure_mod_Qt

-- S7.0.E refined public frontier (R-EpochTailGeometry replaced by explicit
-- aperiodicity hypothesis + REAL discharge theorem; residual count 5 → 4).
#print axioms Collatz.Epochs.G.epochTailGeometryResidual_of_aperiodic
#print axioms collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_f3_and_period_telescoping

-- S7.2 split F.6/F.7 hardening (two-sided tail theorem-source + one-sided
-- corollary + explicit raw-prefix bridge slot).
#print axioms Collatz.Mixing.admissible_tail_touch_frequency_witness_of_residual
#print axioms Collatz.Mixing.admissible_tail_touch_lower_bound_of_residual
#print axioms Collatz.Mixing.raw_prefix_touch_frequency_residual_of_bridge

-- S7.2 Wave 1 Path 1.algebraic (paper D.10.b local-affine-pair constructor;
-- algebraic Q_t-periodicity core via Homogenization + OrdFact bridge).
#print axioms Collatz.OrdFact.three_pow_Qt_modEq_one
#print axioms Collatz.Mixing.selectedTailTouchSemantics_of_localAffinePair
#print axioms Collatz.Mixing.admissibleTailTouchFrequencyTheoremSource_of_localAffinePair
#print axioms Collatz.Mixing.admissibleTailTouchFrequencyResidual_of_localAffinePairResidual

-- S7.2 Wave 2A (E.1 substep): paper Definition F.0.1 admissibility predicate
-- algebraic interface (orbit-agnostic), with power-form unfolding and
-- period-reduction of the witnessing exponent to `[0, Q_t t)`.
#print axioms Collatz.Mixing.AdmissibleTailF01_iff_exists_pow
#print axioms Collatz.Mixing.AdmissibleTailF01_witness_lt_Qt

-- S7.2 Wave 2A (E.2 substep): paper Sublemma D.10 algebraic carry brick
-- on the sub-diagonal (`d_k < k`) and super-diagonal (`k < d_k`) branches,
-- plus the `Int.ModEq` lift on the sub-diagonal branch.
#print axioms Collatz.SEDT.AffineNumerator.M_k_succ_of_lt
#print axioms Collatz.SEDT.AffineNumerator.M_k_succ_of_gt
#print axioms Collatz.SEDT.AffineNumerator.M_k_ModEq_succ_of_lt

-- S7.2 Wave 2F (algebraic admissibility ⇒ touchCount = 1 bridge): the
-- elementary §2 derivation from `wave2-d10b-empirical/REPORT-reverse-
-- engineering.md` formalised on the algebraic core. Closes the
-- biconditional algebraic-side direction of revised paper Definition F.0.1.
-- Helper bricks (added in `Collatz/Epochs/OrdFact.lean`) are also checked.
#print axioms Collatz.OrdFact.isUnit_three_zmod
#print axioms Collatz.OrdFact.isUnit_five_zmod
#print axioms Collatz.OrdFact.isUnit_three_inv_zmod
#print axioms Collatz.OrdFact.natCast_s_t_eq
#print axioms Collatz.OrdFact.isUnit_natCast_s_t
#print axioms Collatz.Mixing.AdmissibleTailF01.touch_count_eq_one
#print axioms Collatz.Mixing.AdmissibleTailF01.touch_count_eq_one_expanded

-- S7.2 Wave 2G (orbit-faithful local algebraic-stack closure): the Wave 2F
-- bridge applied to the orbit-realised carrier sequences with the new
-- `flushGuard`, `Mentry_eq`, `v_eq` fields, deriving the late-window
-- touchCount = 1 obligation for `LocalAffinePairSemantics` algebraically.
#print axioms Collatz.Mixing.AdmissibleTailF01.touch_count_eq_one_of_realized
#print axioms Collatz.Mixing.LocalAffinePairSemantics.one_touch_per_period

-- S7.2 Wave 2H (repackage paper Theorem F.6 to one-sided aggregate touch-rate
-- on the actual Collatz orbit prefix `[0, L)`; replace the previous
-- `R-OrbitSideAdmissibleDensity` orbit-side residual by the strictly weaker
-- `R-OrbitSideAggregateTouchRate (W-B)`. The new public residual asserts
-- `epsDen · N_t(L) · Q_t ≥ epsNum · L` for every `t ≥ 3` and every
-- sufficiently long `L`, with positive natural-number ε-witnesses.
-- The two-sided F.6/F.7 path is preserved as deprecated back-compat
-- aliases in `Collatz/Mixing/PhaseMixing.lean` and
-- `Collatz/Mixing/TouchFrequencyBridge.lean`.).
#print axioms Collatz.Mixing.OrbitSideAggregateTouchRateResidual
#print axioms Collatz.Mixing.orbit_aggregate_touch_count_lower_of_residual
-- Wave 2H Phase 3: also audit the helper definitions and lemmas so that
-- a future refactor cannot leak an axiom through `touchCount_mono` or
-- the `def`-level `orbit_aggregate_touch_count`.
#print axioms Collatz.Mixing.orbit_aggregate_touch_count
#print axioms Collatz.Mixing.orbit_aggregate_touch_count_zero
#print axioms Collatz.Mixing.orbit_aggregate_touch_count_mono

-- Wave 2H Phase B (F.3 audit + R-OrbitSideAggregateTouchRate discharge).
-- Per `phase_b_f.3_audit_and_discharge_*.plan.md` step B.1.E:
-- * typed F.3 witness shape and typed-to-opaque arrow (B.1.B refactor);
-- * orbit-side admissibility-supply witness + residual + W-B discharge
--   (B.1.A + B.1.C + B.1.D); both discharge theorems checked;
-- * two new public frontiers in `UnconditionalModuloOrbitWitnesses.lean`
--   (typed-F.3 form and supply form); both checked.
-- All seven new public symbols must print exactly
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms Collatz.Epochs.G.PrimitiveJunctionRecurrenceTypedResidual
#print axioms Collatz.Epochs.G.primitiveJunctionRecurrenceResidual_of_typed
#print axioms Collatz.Mixing.PrimitiveJunctionAdmissibilitySupplyResidual
#print axioms Collatz.Mixing.orbitSideAggregateTouchRate_of_admissibleTouchSupply
#print axioms Collatz.Mixing.orbitSideAggregateTouchRate_of_F3_recurrence
#print axioms Collatz.Convergence.collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_typed_f3_and_period_telescoping
#print axioms Collatz.Convergence.collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_f3_recurrence_and_period_telescoping
