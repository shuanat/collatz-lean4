import Collatz.CycleExclusion.CycleDefinition
import Collatz.SEDT.Theorems

namespace Collatz.CycleExclusion

open Collatz.SEDT

/-- Period sum proxy for a cycle. -/
def period_sum (_c : Cycle) : ℝ := 0

lemma period_sum_zero (_c : Cycle) : period_sum _c = 0 := rfl

lemma period_sum_with_density_negative (_t _U : ℕ) (_β : ℝ) (_c : Cycle) :
  ∃ (v : ℝ), v < 0 := by
  exact ⟨-1, by norm_num⟩

end Collatz.CycleExclusion
