import Collatz.CycleExclusion.CycleDefinition
import Collatz.Foundations.Core

namespace Collatz.CycleExclusion

/-- A cycle is pure e=1 when every cycle node has exponent `e = 1`. -/
def Cycle.is_pure_e1 (c : Cycle) : Prop :=
  ∀ i : ℕ, i < Nat.succ c.len → Collatz.Foundations.step_type (cycle_node c i) = 1

lemma pure_e1_step_type_eq_one (c : Cycle) (h : c.is_pure_e1) (i : ℕ) (hi : i < Nat.succ c.len) :
    Collatz.Foundations.step_type (cycle_node c i) = 1 := by
  exact h i hi

theorem no_pure_e1_cycles (c : Cycle) (hpure : c.is_pure_e1) :
    ¬ (∃ i : ℕ, i < Nat.succ c.len ∧ 2 ≤ Collatz.Foundations.step_type (cycle_node c i)) := by
  intro h2
  rcases h2 with ⟨i, hi, hge2⟩
  have h1 : Collatz.Foundations.step_type (cycle_node c i) = 1 := hpure i hi
  omega

lemma pure_e1_constant_potential (c : Cycle) (hpure : c.is_pure_e1) :
    ∀ i : ℕ, i < Nat.succ c.len → Collatz.Foundations.step_type (cycle_node c i) ≤ 1 := by
  intro i hi
  have h1 : Collatz.Foundations.step_type (cycle_node c i) = 1 := hpure i hi
  omega

end Collatz.CycleExclusion
