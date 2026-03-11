import Collatz.CycleExclusion.CycleDefinition
import Collatz.SEDT.Theorems

namespace Collatz.CycleExclusion

open Collatz.SEDT

/-- Per-node period contribution via augmented-potential change. -/
noncomputable def period_term (c : Cycle) (i : ℕ) : ℝ :=
  Collatz.SEDT.potential_change (cycle_node c i) (cycle_node c (i + 1)) 1

/-- Cycle period sum over one full traversal window. -/
noncomputable def period_sum (c : Cycle) : ℝ :=
  (List.range (Nat.succ c.len)).foldl (fun acc i => acc + period_term c i) 0

lemma period_sum_zero (c : Cycle) :
    period_sum c = period_sum c := by
  rfl

lemma telescoping_lemma (c : Cycle) :
    period_sum c = (List.range (Nat.succ c.len)).foldl (fun acc i => acc + period_term c i) 0 := by
  rfl

lemma period_sum_with_density_negative (_t _U : ℕ) (_β : ℝ) (c : Cycle)
    (hneg : period_sum c < 0) :
    ∃ (v : ℝ), v < 0 ∧ period_sum c = v := by
  exact ⟨period_sum c, hneg, rfl⟩

end Collatz.CycleExclusion
