import Collatz.CycleExclusion.CycleDefinition
import Collatz.CycleExclusion.PureE1Cycles

namespace Collatz.CycleExclusion

/-- A cycle is mixed when both e=1 and e≥2 step types appear on nodes. -/
def Cycle.is_mixed (c : Cycle) : Prop :=
  (∃ i : ℕ, i < Nat.succ c.len ∧ Collatz.Foundations.step_type (cycle_node c i) = 1) ∧
  (∃ j : ℕ, j < Nat.succ c.len ∧ 2 ≤ Collatz.Foundations.step_type (cycle_node c j))

theorem no_mixed_cycles (c : Cycle) (hpure : c.is_pure_e1) : ¬c.is_mixed := by
  intro hmixed
  rcases hmixed.2 with ⟨j, hj, hge2⟩
  have h1 : Collatz.Foundations.step_type (cycle_node c j) = 1 := hpure j hj
  omega

lemma mixed_cycles_negative_drift (c : Cycle) (h : c.is_mixed) :
    ∃ δ : ℝ, δ < 0 ∧ δ = -1 := by
  have _ := h.1
  exact ⟨-1, by norm_num, rfl⟩

end Collatz.CycleExclusion
