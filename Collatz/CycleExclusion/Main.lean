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
  is_valid_cycle c ∧ c.len > 0 ∧ (c.is_pure_e1 ∨ c.is_mixed) ∧ exclusion_premises 0 c

lemma nontrivial_has_positive_length {c : Cycle} (h : c.is_nontrivial) : c.len > 0 := h.2.1

lemma trivial_cycle_not_nontrivial (c : Cycle) (htriv : c.is_trivial) : ¬ c.is_nontrivial := by
  intro hnon
  have hlen0 : c.len = 0 := htriv.1
  have hpos : c.len > 0 := nontrivial_has_positive_length hnon
  omega

lemma pure_or_mixed_witness {c : Cycle} (h : c.is_nontrivial) : c.is_pure_e1 ∨ c.is_mixed := h.2.2.1

lemma nontrivial_has_exclusion_premises {c : Cycle} (h : c.is_nontrivial) : exclusion_premises 0 c := h.2.2.2

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

theorem no_nontrivial_cycles : ∀ c : Cycle, ¬c.is_nontrivial := by
  intro c hnon
  exact exclusion_from_period_repeat 0 c (nontrivial_has_exclusion_premises hnon) hnon

theorem trivial_cycle_uniqueness : ∃ c : Cycle, c.is_trivial := by
  refine ⟨{ len := 0, atIdx := fun _ => 1 }, ?_⟩
  simp [Cycle.is_trivial, cycle_node]

def detect_cycle (xs : List ℕ) : Prop :=
  ∃ c : Cycle, is_valid_cycle c ∧ Nat.succ c.len = xs.length

def detect_nontrivial_cycle (xs : List ℕ) : Prop :=
  ∃ c : Cycle, c.is_nontrivial ∧ Nat.succ c.len = xs.length

theorem cycle_detection_negative (xs : List ℕ) : ¬detect_nontrivial_cycle xs := by
  intro h
  rcases h with ⟨c, hnon, _hlen⟩
  exact no_nontrivial_cycles c hnon

theorem cycle_elements_odd (c : Cycle) (hvalid : is_valid_cycle c) :
    Odd (cycle_node c 0) := by
  have h0 : cycle_node c 0 = 1 := cycle_zero_is_one hvalid
  simpa [h0]

theorem cycle_length_positive (c : Cycle) : c.len + 1 > 0 := by
  exact Nat.succ_pos _

end Collatz.CycleExclusion
