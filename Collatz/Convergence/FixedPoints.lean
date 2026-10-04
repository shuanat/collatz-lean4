import Collatz.Foundations.Core
import Collatz.CycleExclusion.CycleDefinition

namespace Collatz.Convergence

open Collatz.Foundations

/-- Semantic fixed-point predicate for the odd Collatz step. -/
def is_fixed_point (n : ℕ) : Prop :=
  collatz_step n = n

/-- `1` is a fixed point (kernel proof via `ν₂(4) = 2`). -/
lemma one_is_fixed_point : is_fixed_point 1 :=
  Collatz.CycleExclusion.collatz_step_one

/-- Canonical fixed-point equation for the odd Collatz step: every fixed point
of `collatz_step` satisfies `3x + 1 = 4x`. The proof shows that the only
solution to `(3x+1)/2^{step_type x} = x` in the natural numbers is `x = 1`
(for which `step_type 1 = 2` and `4·1 = 4 = 3·1 + 1`). -/
theorem collatz_step_fixed_point_canonical (x : ℕ) :
    Collatz.Foundations.collatz_step x = x → 3 * x + 1 = 4 * x := by
  intro hfix
  suffices hxeq : x = 1 by
    rw [hxeq]
  set e := Collatz.Foundations.step_type x with he_def
  have hpos : (3 * x + 1) ≠ 0 := by omega
  have hdvd : 2 ^ e ∣ (3 * x + 1) := by
    have hcore : 2 ^ Collatz.Arithmetic.e x ∣ (3 * x + 1) := by
      simpa [Collatz.Arithmetic.e] using
        (Nat.ordProj_dvd (3 * x + 1) 2)
    simpa [he_def, Collatz.Foundations.step_type] using hcore
  have hcs : (3 * x + 1) / 2 ^ e = x := by
    have hh :
        Collatz.Foundations.collatz_step x =
          (3 * x + 1) / 2 ^ Collatz.Foundations.step_type x := rfl
    rw [hh] at hfix
    simpa [he_def] using hfix
  have hexact : 2 ^ e * x = 3 * x + 1 := by
    have hd : (3 * x + 1) / 2 ^ e * 2 ^ e = 3 * x + 1 :=
      Nat.div_mul_cancel hdvd
    rw [hcs] at hd
    linarith
  by_contra hxne
  rcases lt_or_ge e 3 with hlt | hge
  · interval_cases e
    · simp at hexact
      omega
    · have hone : (2 : ℕ) ^ 1 = 2 := by norm_num
      rw [hone] at hexact
      omega
    · have htwo : (2 : ℕ) ^ 2 = 4 := by norm_num
      rw [htwo] at hexact
      omega
  · exfalso
    have hpow8 : 8 ≤ 2 ^ e := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) hge
    have h8x : 8 * x ≤ 2 ^ e * x := Nat.mul_le_mul_right x hpow8
    rw [hexact] at h8x
    have hx0 : x = 0 := by omega
    rw [hx0] at hexact
    simp at hexact

/-- Uniqueness of the fixed point: `T(x) = x` forces `x = 1`. -/
theorem fixed_point_eq_one {x : ℕ} (hfix : is_fixed_point x) : x = 1 := by
  have h := collatz_step_fixed_point_canonical x hfix
  omega

/-- Period-1 periodic tails sit on the fixed point `1`, so the orbit reaches `1`.
(Unconditional: uses `fixed_point_eq_one`.) -/
theorem period_one_tail_reaches_one
    (n : ℕ)
    (hw : Collatz.CycleExclusion.OrbitPeriodicTailWitness n)
    (hperiod1 : hw.period = 1) :
    ∃ k : ℕ, (collatz_step^[k]) n = 1 := by
  have htailEq :
      (collatz_step^[hw.start + 1]) n = (collatz_step^[hw.start]) n := by
    simpa [hperiod1] using hw.periodic 0
  have hfix : is_fixed_point ((collatz_step^[hw.start]) n) := by
    unfold is_fixed_point
    rw [← Function.iterate_succ_apply' collatz_step hw.start n]
    exact htailEq
  exact ⟨hw.start, fixed_point_eq_one hfix⟩

end Collatz.Convergence
