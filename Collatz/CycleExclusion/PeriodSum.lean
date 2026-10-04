import Collatz.CycleExclusion.CycleDefinition
import Collatz.SEDT.Theorems

namespace Collatz.CycleExclusion

open Collatz.SEDT

/-- Per-node period contribution via augmented-potential change. -/
noncomputable def period_term (c : Cycle) (i : ℕ) : ℝ :=
  Collatz.SEDT.potential_change (cycle_node c i) (cycle_node c (i + 1)) 1

/-- Cycle period sum over one full traversal window. -/
noncomputable def period_sum (c : Cycle) : ℝ :=
  Finset.sum (Finset.range (Nat.succ c.len)) (fun i => period_term c i)

/-- The period sum is a literal telescoping sum of augmented-potential changes
around the cyclic node list. -/
lemma telescoping_lemma (c : Cycle) :
    period_sum c =
      Collatz.SEDT.augmented_potential (cycle_node c (Nat.succ c.len)) 1 -
        Collatz.SEDT.augmented_potential (cycle_node c 0) 1 := by
  let F : ℕ → ℝ := fun i => Collatz.SEDT.augmented_potential (cycle_node c i) 1
  have htel :
      ∀ N : ℕ, Finset.sum (Finset.range N) (fun i => (F (i + 1) - F i)) = F N - F 0 := by
    intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  unfold period_sum period_term Collatz.SEDT.potential_change
  simpa [F] using htel (Nat.succ c.len)

/-- Because `cycle_node` is indexed modulo the cycle length, the full-period sum
of successive potential changes vanishes identically for every cycle object. -/
lemma period_sum_zero (c : Cycle) :
    period_sum c = 0 := by
  rw [telescoping_lemma]
  have hwrap : cycle_node c (Nat.succ c.len) = cycle_node c 0 := by
    simpa using cycle_node_mod c (Nat.succ c.len)
  rw [hwrap]
  ring

lemma period_sum_with_density_negative (_t _U : ℕ) (_β : ℝ) (c : Cycle)
    (hneg : period_sum c < 0) :
    ∃ (v : ℝ), v < 0 ∧ period_sum c = v := by
  exact ⟨period_sum c, hneg, rfl⟩

end Collatz.CycleExclusion
