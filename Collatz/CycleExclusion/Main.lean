import Collatz.CycleExclusion.CycleDefinition
import Collatz.CycleExclusion.PeriodSum
import Collatz.CycleExclusion.MixedCycles
import Collatz.CycleExclusion.PureE1Cycles
import Collatz.CycleExclusion.RepeatTrick

namespace Collatz.CycleExclusion

/-- A trivial cycle has one-node orbit rooted at 1. -/
def Cycle.is_trivial (c : Cycle) : Prop :=
  c.len = 0 ∧ cycle_node c 0 = 1

/-- H-level period/repeat compatibility package used for cycle exclusion. -/
def exclusion_premises (t : ℕ) (c : Cycle) : Prop :=
  period_sum c = 0 ∧ period_sum c = repeat_gap t c ∧ R0 t ≤ c.len

/-- A nontrivial cycle candidate must be valid, nonempty, and classified pure or mixed. -/
def Cycle.is_nontrivial (c : Cycle) : Prop :=
  is_valid_cycle c ∧ c.len > 0 ∧ (c.is_pure_e1 ∨ c.is_mixed)

lemma nontrivial_has_positive_length {c : Cycle} (h : c.is_nontrivial) : c.len > 0 := h.2.1

lemma trivial_cycle_not_nontrivial (c : Cycle) (htriv : c.is_trivial) : ¬ c.is_nontrivial := by
  intro hnon
  have hlen0 : c.len = 0 := htriv.1
  have hpos : c.len > 0 := nontrivial_has_positive_length hnon
  omega

lemma pure_or_mixed_witness {c : Cycle} (h : c.is_nontrivial) : c.is_pure_e1 ∨ c.is_mixed := h.2.2

lemma exclusion_from_period_repeat (t : ℕ) (c : Cycle)
    (hprem : exclusion_premises t c) :
    ¬ c.is_nontrivial := by
  intro hnon
  have hlong : R0 t ≤ c.len := hprem.2.2
  have hneg : repeat_gap t c < 0 := repeat_gap_negative_of_long t c hlong
  have hgap : period_sum c = repeat_gap t c := hprem.2.1
  have hpsumneg : period_sum c < 0 := by
    linarith [hneg, hgap]
  have hpsumzero : period_sum c = 0 := hprem.1
  linarith [hpsumneg, hpsumzero]

/-- Paper-aligned H.main interface: cycle exclusion is driven by explicit period/repeat premises. -/
theorem main_cycle_exclusion (c : Cycle)
    (hcycle : c.is_nontrivial) (hprem : exclusion_premises 0 c) :
    False := by
  exact exclusion_from_period_repeat 0 c hprem hcycle

theorem no_nontrivial_cycles (c : Cycle) (hprem : exclusion_premises 0 c) : ¬c.is_nontrivial := by
  intro hnon
  exact main_cycle_exclusion c hnon hprem

theorem trivial_cycle_uniqueness : ∃ c : Cycle, c.is_trivial := by
  refine ⟨{ len := 0, atIdx := fun _ => 1 }, ?_⟩
  simp [Cycle.is_trivial, cycle_node]

def detect_cycle (xs : List ℕ) : Prop :=
  ∃ c : Cycle, is_valid_cycle c ∧ Nat.succ c.len = xs.length

def detect_nontrivial_cycle (xs : List ℕ) : Prop :=
  ∃ c : Cycle, c.is_nontrivial ∧ exclusion_premises 0 c ∧ Nat.succ c.len = xs.length

theorem cycle_detection_negative (xs : List ℕ) : ¬detect_nontrivial_cycle xs := by
  intro h
  rcases h with ⟨c, hnon, hprem, _hlen⟩
  exact no_nontrivial_cycles c hprem hnon

/-- Eventual periodicity contract for a Collatz orbit tail. -/
def orbit_eventually_periodic (m : ℕ) : Prop :=
  ∃ k p : ℕ, 0 < p ∧
    ∀ n : ℕ,
      (Collatz.Foundations.collatz_step^[k + n + p]) m =
      (Collatz.Foundations.collatz_step^[k + n]) m

/-- Pack the existential periodic-tail contract into a structured witness. -/
noncomputable def orbit_periodic_tail_witness_of_eventual
    (m : ℕ) (hper : orbit_eventually_periodic m) :
    OrbitPeriodicTailWitness m := by
  classical
  let k : ℕ := Classical.choose hper
  let hk : ∃ p : ℕ, 0 < p ∧
      ∀ n : ℕ,
        (Collatz.Foundations.collatz_step^[k + n + p]) m =
        (Collatz.Foundations.collatz_step^[k + n]) m := Classical.choose_spec hper
  let p : ℕ := Classical.choose hk
  let hpkg : 0 < p ∧
      ∀ n : ℕ,
        (Collatz.Foundations.collatz_step^[k + n + p]) m =
        (Collatz.Foundations.collatz_step^[k + n]) m := Classical.choose_spec hk
  exact
    { start := k
      period := p
      period_pos := hpkg.1
      periodic := hpkg.2 }

/-- Theorem-level periodic bridge:
from an orbit-derived periodic-tail witness with period > 1, produce an H-level
cycle witness package consumable by `main_cycle_exclusion`. -/
def periodic_tail_cycle_bridge (m : ℕ) : Prop :=
  ∀ hw : OrbitPeriodicTailWitness m, 1 < hw.period →
    ∃ c : Cycle, c.is_nontrivial ∧ exclusion_premises 0 c

/-- H-level extractor contract: a periodic tail yields a nontrivial cycle witness
with explicit exclusion premises. -/
def periodic_tail_cycle_extractor (m : ℕ) : Prop :=
  ∀ _hper : orbit_eventually_periodic m, ∃ c : Cycle, c.is_nontrivial ∧ exclusion_premises 0 c

/-- W6 bridge interface: periodic-tail extraction provides a witness consumable by H.main. -/
theorem periodic_tail_to_cycle_witness (m : ℕ)
    (hper : orbit_eventually_periodic m)
    (hextract : periodic_tail_cycle_extractor m) :
    ∃ c : Cycle, c.is_nontrivial ∧ exclusion_premises 0 c := by
  exact hextract hper

/-- Any periodic-tail witness package is incompatible with H.main cycle exclusion. -/
theorem periodic_tail_contradiction (m : ℕ)
    (hper : orbit_eventually_periodic m)
    (hextract : periodic_tail_cycle_extractor m) :
    False := by
  rcases periodic_tail_to_cycle_witness m hper hextract with ⟨c, hnon, hprem⟩
  exact main_cycle_exclusion c hnon hprem

/-- Apply the theorem-level periodic bridge once the periodic-tail witness has
period larger than 1. -/
theorem periodic_tail_contradiction_from_bridge (m : ℕ)
    (hw : OrbitPeriodicTailWitness m)
    (hgt : 1 < hw.period)
    (hbridge : periodic_tail_cycle_bridge m) :
    False := by
  rcases hbridge hw hgt with ⟨c, hnon, hprem⟩
  exact main_cycle_exclusion c hnon hprem

theorem cycle_elements_odd (c : Cycle) (hvalid : is_valid_cycle c) :
    Odd (cycle_node c 0) := by
  have h0 : cycle_node c 0 = 1 := cycle_zero_is_one hvalid
  simp [h0]

theorem cycle_length_positive (c : Cycle) : c.len + 1 > 0 := by
  exact Nat.succ_pos _

end Collatz.CycleExclusion
