/-
Periodic-tail bridge for cycle exclusion.

After separating raw closed-cycle validity from the optional normalization
`cycle_node c 0 = 1`, the periodic side can now produce a genuine orbit-derived
cycle object from a structured periodic-tail witness. The remaining open step is
no longer the construction of the cycle itself, but the H-level premises needed
to feed `main_cycle_exclusion`.

This file:

* constructs the canonical raw cycle carried by `OrbitPeriodicTailWitness`;
* proves that period `> 1` yields a nontrivial closed cycle object;
* exposes the remaining H-level theorem source as
  `PeriodicTailCycleExclusionPremisesSource n`;
* keeps the older vacuous `OrbitNoNontrivialPeriodicTail n` reduction as a
  compatibility fallback for the current top-level residual packaging.
-/
import Collatz.CycleExclusion.Main

namespace Collatz.CycleExclusion

open Collatz.Foundations

/-- The canonical raw cycle attached to a periodic tail witness. Its node set is
the orbit segment of length `hw.period`, rooted at the tail entry `hw.start`. -/
noncomputable def cycle_of_periodic_tail_witness {n : ℕ}
    (hw : OrbitPeriodicTailWitness n) : Cycle where
  len := hw.period - 1
  atIdx := fun i => (Collatz.Foundations.collatz_step^[hw.start + i.1]) n

lemma cycle_of_periodic_tail_witness_size {n : ℕ}
    (hw : OrbitPeriodicTailWitness n) :
    Nat.succ (cycle_of_periodic_tail_witness hw).len = hw.period := by
  simpa [cycle_of_periodic_tail_witness] using
    (Nat.sub_add_cancel (Nat.succ_le_of_lt hw.period_pos))

lemma cycle_of_periodic_tail_witness_node {n : ℕ}
    (hw : OrbitPeriodicTailWitness n) {i : ℕ} (hi : i < hw.period) :
    cycle_node (cycle_of_periodic_tail_witness hw) i =
      (Collatz.Foundations.collatz_step^[hw.start + i]) n := by
  have hperiod : Nat.succ (hw.period - 1) = hw.period := by
    simpa [cycle_of_periodic_tail_witness] using cycle_of_periodic_tail_witness_size hw
  have hmod : i % Nat.succ (hw.period - 1) = i := by
    rw [hperiod]
    exact Nat.mod_eq_of_lt hi
  unfold cycle_node cycle_of_periodic_tail_witness
  simp [hmod]

/-- The raw cycle extracted from a periodic tail witness is a genuine closed
cycle in the odd-step dynamics. -/
theorem cycle_of_periodic_tail_witness_valid {n : ℕ}
    (hw : OrbitPeriodicTailWitness n) :
    is_valid_cycle (cycle_of_periodic_tail_witness hw) := by
  constructor
  · intro i hi
    have hilen : i < hw.period - 1 := by
      simpa [cycle_of_periodic_tail_witness] using hi
    have hi0 : i < hw.period := by
      omega
    have hi1 : i + 1 < hw.period := by
      omega
    rw [cycle_of_periodic_tail_witness_node hw hi1, cycle_of_periodic_tail_witness_node hw hi0]
    simpa [Nat.add_assoc] using
      (Function.iterate_succ_apply' Collatz.Foundations.collatz_step (hw.start + i) n)
  · have hzero : cycle_node (cycle_of_periodic_tail_witness hw) 0 =
        (Collatz.Foundations.collatz_step^[hw.start]) n := by
      simpa using cycle_of_periodic_tail_witness_node hw hw.period_pos
    have hlastIdx : (cycle_of_periodic_tail_witness hw).len < hw.period := by
      have hpred : Nat.pred hw.period < hw.period :=
        Nat.pred_lt (Nat.ne_of_gt hw.period_pos)
      simpa [cycle_of_periodic_tail_witness] using hpred
    have hlast :
        cycle_node (cycle_of_periodic_tail_witness hw)
            (cycle_of_periodic_tail_witness hw).len =
          (Collatz.Foundations.collatz_step^[
            hw.start + (cycle_of_periodic_tail_witness hw).len]) n := by
      exact cycle_of_periodic_tail_witness_node hw hlastIdx
    have hperiod0 :
        (Collatz.Foundations.collatz_step^[hw.start + hw.period]) n =
          (Collatz.Foundations.collatz_step^[hw.start]) n := by
      simpa [Nat.add_assoc] using hw.periodic 0
    have hsucc :
        Collatz.Foundations.collatz_step
            ((Collatz.Foundations.collatz_step^[
              hw.start + (cycle_of_periodic_tail_witness hw).len]) n) =
          (Collatz.Foundations.collatz_step^[hw.start + hw.period]) n := by
      have hlen :
          (cycle_of_periodic_tail_witness hw).len + 1 = hw.period := by
        simpa [cycle_of_periodic_tail_witness] using
          (Nat.sub_add_cancel (Nat.succ_le_of_lt hw.period_pos))
      have hadd :
          hw.start + (cycle_of_periodic_tail_witness hw).len + 1 =
            hw.start + hw.period := by
        calc
          hw.start + (cycle_of_periodic_tail_witness hw).len + 1
              = hw.start + ((cycle_of_periodic_tail_witness hw).len + 1) := by omega
          _ = hw.start + hw.period := by rw [hlen]
      have hsucc' :
          Collatz.Foundations.collatz_step
              ((Collatz.Foundations.collatz_step^[
                hw.start + (cycle_of_periodic_tail_witness hw).len]) n) =
            (Collatz.Foundations.collatz_step^[
              hw.start + (cycle_of_periodic_tail_witness hw).len + 1]) n := by
        simpa [Nat.add_assoc] using
          (Function.iterate_succ_apply' Collatz.Foundations.collatz_step
            (hw.start + (cycle_of_periodic_tail_witness hw).len) n).symm
      simpa [hadd] using hsucc'
    calc
      cycle_node (cycle_of_periodic_tail_witness hw) 0
          = (Collatz.Foundations.collatz_step^[hw.start]) n := hzero
      _ = (Collatz.Foundations.collatz_step^[hw.start + hw.period]) n := hperiod0.symm
      _ = Collatz.Foundations.collatz_step
            ((Collatz.Foundations.collatz_step^[
              hw.start + (cycle_of_periodic_tail_witness hw).len]) n) := hsucc.symm
      _ = Collatz.Foundations.collatz_step
            (cycle_node (cycle_of_periodic_tail_witness hw)
              (cycle_of_periodic_tail_witness hw).len) := by
          rw [hlast]

/-- Period `> 1` on a periodic tail witness yields a genuinely nontrivial raw
closed cycle. -/
theorem cycle_of_periodic_tail_witness_nontrivial {n : ℕ}
    (hw : OrbitPeriodicTailWitness n) (hgt : 1 < hw.period) :
    (cycle_of_periodic_tail_witness hw).is_nontrivial := by
  refine ⟨cycle_of_periodic_tail_witness_valid hw, ?_⟩
  simpa [cycle_of_periodic_tail_witness] using Nat.sub_pos_of_lt hgt

/-- The orbit-derived raw cycle attached to a periodic tail witness has zero
period sum by pure telescoping of successive potential changes. -/
theorem cycle_of_periodic_tail_witness_period_sum_zero {n : ℕ}
    (hw : OrbitPeriodicTailWitness n) :
    period_sum (cycle_of_periodic_tail_witness hw) = 0 := by
  simpa using period_sum_zero (cycle_of_periodic_tail_witness hw)

/-- Exact remaining H-level theorem source after repairing the periodic cycle
interface: the orbit-derived raw cycle attached to each period-`> 1` tail must
satisfy the premises needed by `main_cycle_exclusion`. -/
def PeriodicTailCycleExclusionPremisesSource (n : ℕ) : Prop :=
  ∀ hw : OrbitPeriodicTailWitness n, 1 < hw.period →
    exclusion_premises 0 (cycle_of_periodic_tail_witness hw)

/-- Once the H-level premises are available for the canonical orbit-derived raw
cycle, the theorem-level periodic bridge is discharged without further
packaging. -/
theorem periodic_tail_cycle_bridge_of_constructed_cycle_premises
    (n : ℕ) (hsource : PeriodicTailCycleExclusionPremisesSource n) :
    periodic_tail_cycle_bridge n := by
  intro hw hgt
  refine ⟨cycle_of_periodic_tail_witness hw,
    cycle_of_periodic_tail_witness_nontrivial hw hgt, hsource hw hgt⟩

/-- Explicit residual exposed by the cycle-exclusion architecture: the orbit of
`n` admits no periodic tail of period strictly greater than `1`. This is exactly
the no-nontrivial-cycle part of the Collatz conjecture, and is the minimal
residual through which the `periodic_tail_cycle_bridge n` interface can be
honestly discharged. -/
def OrbitNoNontrivialPeriodicTail (n : ℕ) : Prop :=
  ∀ hw : OrbitPeriodicTailWitness n, hw.period ≤ 1

/-- The repaired raw-cycle theorem source already rules out every nontrivial
periodic tail on the orbit: if such a tail existed, its canonical cycle would
simultaneously satisfy `exclusion_premises 0` and be nontrivial, contradicting
`main_cycle_exclusion`. -/
theorem no_nontrivial_periodic_tail_of_cycle_premises_source
    (n : ℕ) (hsource : PeriodicTailCycleExclusionPremisesSource n) :
    OrbitNoNontrivialPeriodicTail n := by
  intro hw
  rcases orbit_periodic_tail_period_one_or_gt_one hw with hperiod1 | hgt
  · omega
  · exact False.elim <|
      main_cycle_exclusion
        (cycle_of_periodic_tail_witness hw)
        (cycle_of_periodic_tail_witness_nontrivial hw hgt)
        (hsource hw hgt)

/-- Conversely, the repaired raw-cycle theorem source follows vacuously from the
absence of every nontrivial periodic tail. This makes the current periodic
frontier equivalent to `OrbitNoNontrivialPeriodicTail`. -/
theorem periodic_tail_cycle_premises_source_of_no_nontrivial_periodic_tail
    (n : ℕ) (hno : OrbitNoNontrivialPeriodicTail n) :
    PeriodicTailCycleExclusionPremisesSource n := by
  intro hw hgt
  exact False.elim (Nat.not_lt.mpr (hno hw) hgt)

/-- Under the current raw-cycle interface, the theorem source
`PeriodicTailCycleExclusionPremisesSource n` is equivalent to the explicit
residual `OrbitNoNontrivialPeriodicTail n`. -/
theorem periodic_tail_cycle_premises_source_iff_no_nontrivial_periodic_tail
    (n : ℕ) :
    PeriodicTailCycleExclusionPremisesSource n ↔ OrbitNoNontrivialPeriodicTail n := by
  constructor
  · exact no_nontrivial_periodic_tail_of_cycle_premises_source n
  · exact periodic_tail_cycle_premises_source_of_no_nontrivial_periodic_tail n

/-- Compatibility reduction of the older `periodic_tail_cycle_bridge` interface
to the explicit no-tail residual. This remains valid, but is now strictly
weaker than constructing the actual orbit-derived raw cycle. -/
theorem periodic_tail_cycle_bridge_of_no_nontrivial_periodic_tail
    (n : ℕ) (hno : OrbitNoNontrivialPeriodicTail n) :
    periodic_tail_cycle_bridge n := by
  intro hw hgt
  have hle : hw.period ≤ 1 := hno hw
  exact absurd hgt (Nat.not_lt.mpr hle)

end Collatz.CycleExclusion
