import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.CycleExclusion

structure Cycle where
  len : ℕ
  atIdx : Fin (Nat.succ len) → ℕ

/-- Access cycle values by natural index modulo cycle size. -/
def cycle_node (c : Cycle) (i : ℕ) : ℕ :=
  c.atIdx ⟨i % (Nat.succ c.len), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- Edge-step relation along the cycle, including wrap-around at `len -> 0`. -/
def cycle_edge_valid (c : Cycle) : Prop :=
  (∀ i : ℕ, i < c.len → cycle_node c (i + 1) = Collatz.Foundations.collatz_step (cycle_node c i)) ∧
  cycle_node c 0 = Collatz.Foundations.collatz_step (cycle_node c c.len)

/-- Helper predicate: a mathematically meaningful closed-orbit cycle contract. -/
def is_valid_cycle (c : Cycle) : Prop :=
  cycle_edge_valid c ∧ cycle_node c 0 = 1

/-- Structured orbit-semantic witness for eventual periodicity.
It keeps the explicit tail entry index and period length that can be consumed
by theorem-level bridges. -/
structure OrbitPeriodicTailWitness (m : ℕ) where
  start : ℕ
  period : ℕ
  period_pos : 0 < period
  periodic :
    ∀ n : ℕ,
      (Collatz.Foundations.collatz_step^[start + n + period]) m =
      (Collatz.Foundations.collatz_step^[start + n]) m

def cycle_length (c : Cycle) : ℕ := c.len

def is_in_cycle (n : ℕ) (c : Cycle) : Prop :=
  ∃ i : Fin (Nat.succ c.len), c.atIdx i = n

lemma cycle_node_mod (c : Cycle) (i : ℕ) :
    cycle_node c i = cycle_node c (i % (Nat.succ c.len)) := by
  unfold cycle_node
  simp [Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.succ_pos _))]

lemma cycle_zero_is_one {c : Cycle} (hvalid : is_valid_cycle c) : cycle_node c 0 = 1 :=
  hvalid.2

lemma cycle_wrap_step {c : Cycle} (hvalid : is_valid_cycle c) :
    cycle_node c 0 = Collatz.Foundations.collatz_step (cycle_node c c.len) :=
  hvalid.1.2

lemma orbit_periodic_tail_period_one_or_gt_one
    {m : ℕ} (hw : OrbitPeriodicTailWitness m) :
    hw.period = 1 ∨ 1 < hw.period := by
  have hle : 1 ≤ hw.period := Nat.succ_le_of_lt hw.period_pos
  simpa [eq_comm] using (eq_or_lt_of_le hle)

end Collatz.CycleExclusion
