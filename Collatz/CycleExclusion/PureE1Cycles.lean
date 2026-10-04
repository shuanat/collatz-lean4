import Collatz.CycleExclusion.CycleDefinition
import Collatz.Foundations.Core

namespace Collatz.CycleExclusion

open Collatz.Foundations

/-- A cycle is pure e=1 when every cycle node has exponent `e = 1`. -/
def Cycle.is_pure_e1 (c : Cycle) : Prop :=
  ∀ i : ℕ, i < Nat.succ c.len → Collatz.Foundations.step_type (cycle_node c i) = 1

lemma pure_e1_step_type_eq_one (c : Cycle) (h : c.is_pure_e1) (i : ℕ) (hi : i < Nat.succ c.len) :
    Collatz.Foundations.step_type (cycle_node c i) = 1 := by
  exact h i hi

/-- An `e = 1` step strictly increases the value: `T(x) = (3x+1)/2 > x`.
(`x = 0` is excluded automatically since `e(0) = ν₂(1) = 0`.) -/
lemma lt_collatz_step_of_step_type_eq_one {x : ℕ} (h : step_type x = 1) :
    x < collatz_step x := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp [step_type, Collatz.Arithmetic.e] at h
  unfold collatz_step
  rw [h, pow_one]
  omega

/-- There is no valid cycle all of whose steps have `e = 1`: every such step
strictly increases the value, so the values cannot return to the start. -/
theorem no_pure_e1_cycle (c : Cycle) (hvalid : is_valid_cycle c) : ¬ c.is_pure_e1 := by
  intro hpure
  have hinc : ∀ i : ℕ, i ≤ c.len → cycle_node c 0 + i ≤ cycle_node c i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
        intro hi
        have h1 := ih (by omega)
        have hstep := hvalid.1 i (by omega)
        have hgt := lt_collatz_step_of_step_type_eq_one (hpure i (by omega))
        rw [hstep]
        omega
  have hlast := hinc c.len le_rfl
  have hgt := lt_collatz_step_of_step_type_eq_one (hpure c.len (Nat.lt_succ_self _))
  have hwrap : cycle_node c 0 = collatz_step (cycle_node c c.len) := hvalid.2
  omega

end Collatz.CycleExclusion
