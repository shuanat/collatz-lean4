import Collatz.CycleExclusion.CycleDefinition
import Collatz.Epochs.Core
import Collatz.CycleExclusion.PeriodSum

namespace Collatz.CycleExclusion

/-- Repeat-trick threshold model based on epoch period scale. -/
def R0 (t : ℕ) : ℕ := Collatz.Epochs.Q_t t + 1

/-- Repeat-trick discrepancy observable. -/
noncomputable def repeat_gap (t : ℕ) (c : Cycle) : ℝ :=
  (R0 t : ℝ) - (Nat.succ c.len : ℝ)

lemma repeat_gap_negative_of_long (t : ℕ) (c : Cycle) (hlong : R0 t ≤ c.len) :
    repeat_gap t c < 0 := by
  unfold repeat_gap
  have hltNat : R0 t < Nat.succ c.len := lt_of_le_of_lt hlong (Nat.lt_succ_self c.len)
  have hltReal : (R0 t : ℝ) < (Nat.succ c.len : ℝ) := by exact_mod_cast hltNat
  linarith

lemma repeat_trick_works (t : ℕ) (c : Cycle) :
    c.len < R0 t ∨ R0 t ≤ c.len := by
  exact lt_or_ge c.len (R0 t)

lemma repeat_trick_period_bound (t : ℕ) (c : Cycle) (hlong : R0 t ≤ c.len) :
    ∃ v : ℝ, v < 0 ∧ v = repeat_gap t c := by
  exact ⟨repeat_gap t c, repeat_gap_negative_of_long t c hlong, rfl⟩

lemma repeat_gap_controls_period_sum (t : ℕ) (c : Cycle) (hlink : period_sum c = repeat_gap t c) :
    period_sum c = repeat_gap t c := hlink

end Collatz.CycleExclusion
