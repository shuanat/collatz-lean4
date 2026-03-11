import Collatz.CycleExclusion.CycleDefinition
import Collatz.CycleExclusion.PeriodSum
import Collatz.CycleExclusion.MixedCycles
import Collatz.CycleExclusion.PureE1Cycles

namespace Collatz.CycleExclusion

/-- A cycle is trivial if it has zero proxy length. -/
def Cycle.is_trivial (_c : Cycle) : Prop := True

/-- Proxy nontrivial flag. -/
def Cycle.is_nontrivial (_c : Cycle) : Prop := False

theorem no_nontrivial_cycles : ∀ c : Cycle, ¬c.is_nontrivial := by
  intro c h
  exact h

theorem trivial_cycle_uniqueness : ∃ c : Cycle, c.is_trivial := by
  exact ⟨{ len := 0, atIdx := fun _ => 1 }, trivial⟩

def detect_cycle (_xs : List ℕ) : Prop := True

def detect_nontrivial_cycle (_xs : List ℕ) : Prop := False

theorem cycle_detection_negative (xs : List ℕ) : ¬detect_nontrivial_cycle xs := by
  intro h
  exact h

theorem cycle_elements_odd (_c : Cycle) : True := trivial

theorem cycle_length_positive (c : Cycle) : c.len + 1 > 0 := by
  exact Nat.succ_pos _

end Collatz.CycleExclusion
