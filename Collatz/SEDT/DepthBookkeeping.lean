/-
Collatz Conjecture: SEDT Deep Formalization — Depth bookkeeping bridge
(M2.4 + M2.5)

This module connects the orbit-side cumulative depth identity from
`OrbitDepth` (M2.3) to the carry-side semantic interface
`SelectedCarryDepthSemantics` from `Epochs.NumeratorCarry`. The
conditional producer `SelectedCarryDepthSemantics_of_uncapped_gain_bound`
takes the deep mathematical hypothesis

    `multibit_gain_on_orbit m i j ≤ selected_multibit_gain_budget t U i j`

and yields the carry-side semantics. This hypothesis is the combined
content of:

* the **touch-density** lower bound (M1.D.4),
* the **multibit period bonus** identity (M1.D.2),
* the **linear-surplus combiner** (M1.E + M2.1),

restricted to the actual orbit segment `[i, j)` of `m`. M3 will
discharge this hypothesis on canonical aperiodic skeletons via the
phase-geometry witness.
-/

import Collatz.SEDT.OrbitDepth
import Collatz.Epochs.NumeratorCarry

namespace Collatz.SEDT.DepthBookkeeping

open Collatz.Foundations
open Collatz.SEDT.OrbitDepth
open Collatz.Epochs

/-- **Conditional producer (M2.4).**

Given an upper bound on the orbit-side multibit gain matching the
canonical multibit budget, the carry-side `SelectedCarryDepthSemantics`
follows directly from the cumulative depth identity (M2.3).
-/
theorem SelectedCarryDepthSemantics_of_uncapped_gain_bound
    {m : ℕ} (hm : Odd m) {t U i j : ℕ} (hij : i ≤ j)
    (hgain_bound :
      ((multibit_gain_on_orbit m i j : ℕ) : ℝ) ≤
        selected_multibit_gain_budget t U i j) :
    SelectedCarryDepthSemantics m t U i j := by
  refine ⟨?_⟩
  dsimp [selected_depth_bookkeeping_bound, selected_multibit_gain_budget]
  -- Cumulative depth identity gives:
  --   depth_diff + (j - i) = multibit_gain (in ℤ).
  have hident :=
    cumulative_depth_identity m hm i j hij
  -- Cast to ℝ and conclude.
  have hreal :
      ((depth_minus ((collatz_step^[j]) m) : ℝ) -
          (depth_minus ((collatz_step^[i]) m) : ℝ)) +
          ((j - i : ℕ) : ℝ) =
        ((multibit_gain_on_orbit m i j : ℕ) : ℝ) := by
    exact_mod_cast hident
  -- multibit_gain_budget = (α - 1) (j-i) + C, want depth_diff ≤ (α - 2) (j-i) + C.
  -- From identity: depth_diff = multibit_gain - (j - i) ≤ budget - (j-i)
  --   = (α - 1)(j-i) + C - (j-i) = (α - 2)(j-i) + C.
  have hdepth_eq :
      ((depth_minus ((collatz_step^[j]) m) : ℝ) -
          (depth_minus ((collatz_step^[i]) m) : ℝ)) =
        ((multibit_gain_on_orbit m i j : ℕ) : ℝ) - ((j - i : ℕ) : ℝ) := by
    linarith
  rw [hdepth_eq]
  have hbudget := hgain_bound
  dsimp [selected_multibit_gain_budget] at hbudget
  have hrhs :
      (Collatz.SEDT.α t U - 1) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U
          - ((j - i : ℕ) : ℝ) =
        (Collatz.SEDT.α t U - 2) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U := by
    ring
  linarith [hrhs]

/-- **Final assembly (M2.5).**

The selected depth bookkeeping bound packaged as a `Prop`
(unfolded form), produced from the same hypothesis as M2.4. -/
theorem selected_depth_bookkeeping_bound_of_uncapped_gain_bound
    {m : ℕ} (hm : Odd m) {t U i j : ℕ} (hij : i ≤ j)
    (hgain_bound :
      ((multibit_gain_on_orbit m i j : ℕ) : ℝ) ≤
        selected_multibit_gain_budget t U i j) :
    selected_depth_bookkeeping_bound m t U i j :=
  (SelectedCarryDepthSemantics_of_uncapped_gain_bound hm hij hgain_bound).depthBound

end Collatz.SEDT.DepthBookkeeping
