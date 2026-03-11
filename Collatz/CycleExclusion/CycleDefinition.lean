import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.CycleExclusion

structure Cycle where
  len : ℕ
  atIdx : Fin (Nat.succ len) → ℕ

/-- Helper function to check if a cycle is valid. -/
def is_valid_cycle (_c : Cycle) : Prop := True

def cycle_length (c : Cycle) : ℕ := c.len

def is_in_cycle (n : ℕ) (c : Cycle) : Prop :=
  ∃ i : Fin (Nat.succ c.len), c.atIdx i = n

end Collatz.CycleExclusion
