/-
Periodic side of the convergence argument.

* `cycle_of_periodic_tail_witness` turns a periodic-tail witness into a valid
  closed `Cycle` object (a genuine construction).
* `OrbitNoNontrivialPeriodicTail n` / `NoNontrivialCycleOnOrbit n` state that
  every value which recurs along the odd-step orbit of `n` equals `1`, i.e. the
  orbit of `n` does not run into a nontrivial cycle. This is an OPEN hypothesis
  (it is the "no nontrivial cycles" half of the Collatz conjecture, restricted
  to one orbit); it is satisfied by `n = 1` and by every `n` whose orbit reaches
  `1` (`no_cycle_on_orbit_of_reaches_one`).
* `NoNontrivialCycles` is the global open conjecture "the only periodic odd
  point of the odd-step map is `1`".

History: the previous definition `OrbitNoNontrivialPeriodicTail n :=
∀ hw, hw.period ≤ 1` did not require minimal periods and was therefore
equivalent to `¬ orbit_eventually_periodic n` (false for `n = 1`, which has
period-2 witnesses). It was replaced by the present definition. The H-level
premise package `PeriodicTailCycleExclusionPremisesSource` (built on the
unsatisfiable `exclusion_premises`) was removed.
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

/-- Period `> 1` on a periodic tail witness yields a closed cycle object with at
least two nodes (`Cycle.is_nontrivial`). Since periods are not minimal, the
nodes may all equal `1` (e.g. a period-2 witness on the fixed point). -/
theorem cycle_of_periodic_tail_witness_nontrivial {n : ℕ}
    (hw : OrbitPeriodicTailWitness n) (hgt : 1 < hw.period) :
    (cycle_of_periodic_tail_witness hw).is_nontrivial := by
  refine ⟨cycle_of_periodic_tail_witness_valid hw, ?_⟩
  simpa [cycle_of_periodic_tail_witness] using Nat.sub_pos_of_lt hgt

/-- The orbit-derived raw cycle attached to a periodic tail witness has zero
period sum. This is the bookkeeping identity `period_sum_zero` (true for every
`Cycle`); it carries no information about the dynamics. -/
theorem cycle_of_periodic_tail_witness_period_sum_zero {n : ℕ}
    (hw : OrbitPeriodicTailWitness n) :
    period_sum (cycle_of_periodic_tail_witness hw) = 0 := by
  simpa using period_sum_zero (cycle_of_periodic_tail_witness hw)

/-- **Open hypothesis (per orbit).** No nontrivial cycle on the orbit of `n`:
every value that recurs along the odd-step orbit of `n` equals `1`. -/
def NoNontrivialCycleOnOrbit (n : ℕ) : Prop :=
  ∀ k p : ℕ, 0 < p → (collatz_step^[k + p]) n = (collatz_step^[k]) n →
    (collatz_step^[k]) n = 1

/-- **Open conjecture (global).** The only odd periodic point of the odd-step
map is `1`, i.e. there is no nontrivial cycle. -/
def NoNontrivialCycles : Prop :=
  ∀ x : ℕ, Odd x → ∀ p : ℕ, 0 < p → (collatz_step^[p]) x = x → x = 1

/-- **Open hypothesis (per orbit), witness form.** Every periodic tail of the
orbit of `n` starts at the value `1`. Equivalent to `NoNontrivialCycleOnOrbit n`
(`orbit_no_nontrivial_periodic_tail_iff_no_cycle_on_orbit`). -/
def OrbitNoNontrivialPeriodicTail (n : ℕ) : Prop :=
  ∀ hw : OrbitPeriodicTailWitness n, (collatz_step^[hw.start]) n = 1

theorem orbit_no_nontrivial_periodic_tail_iff_no_cycle_on_orbit (n : ℕ) :
    OrbitNoNontrivialPeriodicTail n ↔ NoNontrivialCycleOnOrbit n := by
  constructor
  · intro h k p hp hkp
    exact h (OrbitPeriodicTailWitness.ofIterateEq k p hp hkp)
  · intro h hw
    exact h hw.start hw.period hw.period_pos (by simpa using hw.periodic 0)

/-- The global conjecture implies the per-orbit hypothesis for every start. -/
theorem no_cycle_on_orbit_of_no_nontrivial_cycles (h : NoNontrivialCycles) (n : ℕ) :
    NoNontrivialCycleOnOrbit n := by
  intro k p hp hkp
  have hodd : Odd ((collatz_step^[k]) n) := by
    rw [← hkp]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [show k + (q + 1) = (k + q) + 1 by omega, Function.iterate_succ_apply']
    exact collatz_step_is_odd
  refine h _ hodd p hp ?_
  rw [← Function.iterate_add_apply, show p + k = k + p by omega, hkp]

/-- A repetition at time `k` with period `p` repeats at every multiple of `p`. -/
lemma iterate_add_mul_eq_of_iterate_add_eq {n k p : ℕ}
    (hkp : (collatz_step^[k + p]) n = (collatz_step^[k]) n) (m : ℕ) :
    (collatz_step^[k + m * p]) n = (collatz_step^[k]) n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show k + (m + 1) * p = p + (k + m * p) by ring, Function.iterate_add_apply, ih,
        ← Function.iterate_add_apply, show p + k = k + p by omega, hkp]

/-- Every orbit that reaches `1` satisfies `NoNontrivialCycleOnOrbit`; so the
hypothesis is implied by the conclusion of the Collatz conjecture and is not
inconsistent with it. -/
theorem no_cycle_on_orbit_of_reaches_one {n k₀ : ℕ} (h : (collatz_step^[k₀]) n = 1) :
    NoNontrivialCycleOnOrbit n := by
  intro k p hp hkp
  have h1 := iterate_add_mul_eq_of_iterate_add_eq hkp k₀
  have hle : k₀ ≤ k + k₀ * p := by nlinarith
  rw [← h1, ← Nat.sub_add_cancel hle, Function.iterate_add_apply, h, iterate_collatz_step_one]

/-- Periodic branch, with no vacuous hypotheses: an eventually periodic orbit
without a nontrivial cycle reaches `1`. -/
theorem reaches_one_of_periodic_of_no_cycle {n : ℕ}
    (hper : orbit_eventually_periodic n) (hno : NoNontrivialCycleOnOrbit n) :
    ∃ k : ℕ, (collatz_step^[k]) n = 1 := by
  obtain ⟨k, p, hp, h⟩ := hper
  exact ⟨k, hno k p hp (by simpa using h 0)⟩

/-- Sanity: the per-orbit hypothesis holds for `n = 1`. -/
theorem no_cycle_on_orbit_one : NoNontrivialCycleOnOrbit 1 :=
  fun k _ _ _ => iterate_collatz_step_one k

/-- Sanity: the witness form holds for `n = 1`. -/
theorem orbit_no_nontrivial_periodic_tail_one : OrbitNoNontrivialPeriodicTail 1 :=
  fun hw => iterate_collatz_step_one hw.start

end Collatz.CycleExclusion
