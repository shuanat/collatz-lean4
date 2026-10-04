import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.CycleExclusion

/-- `1` is a fixed point of the odd-step map: `T(1) = (3·1+1)/2^2 = 1`.
Proved by unfolding the 2-adic valuation of `4`. -/
theorem collatz_step_one : Collatz.Foundations.collatz_step 1 = 1 := by
  have h4 : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_two]
  simp [Collatz.Foundations.collatz_step, Collatz.Foundations.step_type,
    Collatz.Arithmetic.e, h4]

/-- Every iterate of the odd-step map fixes `1`. -/
theorem iterate_collatz_step_one (k : ℕ) : (Collatz.Foundations.collatz_step^[k]) 1 = 1 :=
  Function.iterate_fixed collatz_step_one k

/-- A cycle object: `len + 1` nodes indexed by `Fin (len + 1)`. No dynamics are
built in; see `is_valid_cycle`. -/
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

/-- Minimal semantic closed-orbit cycle contract. -/
def is_valid_cycle (c : Cycle) : Prop :=
  cycle_edge_valid c

/-- Optional normalization of a closed cycle at the trivial anchor `1`. -/
def is_normalized_cycle (c : Cycle) : Prop :=
  is_valid_cycle c ∧ cycle_node c 0 = 1

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

lemma normalized_cycle_valid {c : Cycle} (hnorm : is_normalized_cycle c) : is_valid_cycle c :=
  hnorm.1

lemma cycle_zero_is_one {c : Cycle} (hnorm : is_normalized_cycle c) : cycle_node c 0 = 1 :=
  hnorm.2

lemma cycle_wrap_step {c : Cycle} (hvalid : is_valid_cycle c) :
    cycle_node c 0 = Collatz.Foundations.collatz_step (cycle_node c c.len) :=
  hvalid.2

/-- A single repetition `T^[k+p](m) = T^[k](m)` with `p > 0` already yields a
periodic-tail witness (determinism of the odd-step map). -/
def OrbitPeriodicTailWitness.ofIterateEq {m : ℕ} (k p : ℕ) (hp : 0 < p)
    (hkp : (Collatz.Foundations.collatz_step^[k + p]) m =
      (Collatz.Foundations.collatz_step^[k]) m) :
    OrbitPeriodicTailWitness m where
  start := k
  period := p
  period_pos := hp
  periodic := fun i => by
    rw [show k + i + p = i + (k + p) by omega, Function.iterate_add_apply, hkp,
      ← Function.iterate_add_apply, show i + k = k + i by omega]

lemma orbit_periodic_tail_period_one_or_gt_one
    {m : ℕ} (hw : OrbitPeriodicTailWitness m) :
    hw.period = 1 ∨ 1 < hw.period := by
  have hle : 1 ≤ hw.period := Nat.succ_le_of_lt hw.period_pos
  simpa [eq_comm] using (eq_or_lt_of_le hle)

end Collatz.CycleExclusion
