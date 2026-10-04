/-
Collatz Conjecture: SEDT Deep Formalization — Aperiodic gain bridge
(M3.1 + M3.2 + M3.3 — conditional discharge)

This module assembles the bridge from the orbit-side **multibit gain
upper bound** on the canonical aperiodic phase-return skeleton to the
existing `AperiodicSelectedLongEpochResidual`. It composes:

* the M2.4 producer
  `SelectedCarryDepthSemantics_of_uncapped_gain_bound`
  (`Collatz.SEDT.DepthBookkeeping`),
* the existing
  `canonical_aperiodic_selected_long_epoch_bridge_on_of_depth_semantics`
  in `Collatz.Convergence.MainTheorem`.

The remaining open kernel becomes a single concrete inequality on the
orbit segment between consecutive phase returns:

    `(multibit_gain_on_orbit n leftIdx_j rightIdx_j : ℝ)
        ≤ selected_multibit_gain_budget t U leftIdx_j rightIdx_j`.

This is a strictly stronger residual than the previous abstract
`canonical_aperiodic_selected_long_epoch_bridge_on n t U`: it is a
single-pair pointwise inequality on the actual orbit, dischargeable by
the linear-surplus / touch-density / multibit-bonus toolkit (M1+M2)
once a phase-geometry-side touch density bound is supplied.
-/

import Collatz.SEDT.DepthBookkeeping
import Collatz.Convergence.MainTheorem

namespace Collatz.SEDT.AperiodicGainBridge

open Collatz.Foundations
open Collatz.SEDT.OrbitDepth
open Collatz.SEDT.DepthBookkeeping
open Collatz.Convergence
open Collatz.Epochs

/-- **Concrete orbit-side gain residual.**

For each canonical aperiodic phase-return pair `(leftIdx j, rightIdx j)`,
the orbit-side multibit gain is bounded by the canonical multibit budget. -/
def CanonicalAperiodicMultibitGainBound (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    ∀ j : ℕ,
      let i := (Collatz.Convergence.aperiodic_orbit_has_cofinal_gap_long_phase_returns
                  n t U _ha).leftIdx j
      let k := (Collatz.Convergence.aperiodic_orbit_has_cofinal_gap_long_phase_returns
                  n t U _ha).rightIdx j
      ((multibit_gain_on_orbit n i k : ℕ) : ℝ) ≤
        Collatz.Epochs.selected_multibit_gain_budget t U i k

/-- **M3.1 — Carry-depth semantics from orbit-gain bound.**

Each canonical selected pair gets `SelectedCarryDepthSemantics` via the
M2.4 producer applied to the supplied gain bound. -/
theorem canonical_aperiodic_selected_carry_depth_semantics_of_multibit_gain_bound
    {n t U : ℕ} (hn : Odd n)
    (hbound : CanonicalAperiodicMultibitGainBound n t U) :
    canonical_aperiodic_selected_carry_depth_semantics n t U := by
  intro haper j
  let phase :=
    Collatz.Convergence.aperiodic_orbit_has_cofinal_gap_long_phase_returns
      n t U haper
  have hij : phase.leftIdx j ≤ phase.rightIdx j := by
    have hsep := phase.longSep j
    omega
  exact SelectedCarryDepthSemantics_of_uncapped_gain_bound
    (m := n) hn (t := t) (U := U) (i := phase.leftIdx j) (j := phase.rightIdx j)
    hij (hbound haper j)

/-- **M3.3 — Discharge `AperiodicSelectedLongEpochResidual` conditionally.**

Given the orbit-side multibit gain bound, the
`canonical_aperiodic_selected_long_epoch_bridge_on n t U` source is
constructed. -/
noncomputable def aperiodicSelectedLongEpochBridge_of_multibit_gain_bound
    {n t U : ℕ} (hn : Odd n)
    (hbound : CanonicalAperiodicMultibitGainBound n t U) :
    Collatz.Convergence.canonical_aperiodic_selected_long_epoch_bridge_on n t U :=
  Collatz.Convergence.canonical_aperiodic_selected_long_epoch_bridge_on_of_depth_semantics
    hn
    (canonical_aperiodic_selected_carry_depth_semantics_of_multibit_gain_bound
      hn hbound)

/-- **M3.3 — at the production parameters `(t, U) = (3, 1)`.** -/
noncomputable def aperiodicSelectedLongEpochResidual_of_multibit_gain_bound
    {n : ℕ} (hn : Odd n)
    (hbound : CanonicalAperiodicMultibitGainBound n 3 1) :
    Collatz.Convergence.AperiodicSelectedLongEpochResidual n :=
  aperiodicSelectedLongEpochBridge_of_multibit_gain_bound hn hbound

end Collatz.SEDT.AperiodicGainBridge
