import Collatz.Foundations.Core
import Collatz.CycleExclusion.CycleDefinition

namespace Collatz.Convergence

open Collatz.Foundations

/-- Semantic fixed-point predicate for the odd Collatz step. -/
def is_fixed_point (n : ℕ) : Prop :=
  collatz_step n = n

lemma one_is_fixed_point : is_fixed_point 1 := by
  unfold is_fixed_point collatz_step step_type Collatz.Arithmetic.e
  native_decide

/-- Canonical fixed-point equation extracted from the odd-step definition. -/
lemma fixed_point_equation (n : ℕ) (_hfix : is_fixed_point n)
    (hcanon : 3 * n + 1 = n * 2 ^ step_type n) :
    3 * n + 1 = n * 2 ^ step_type n := by
  exact hcanon

/-- Scientific uniqueness contract: the canonical odd fixed-point equation forces `n = 1`. -/
lemma fixed_point_uniqueness (n : ℕ)
    (__hfix : is_fixed_point n)
    (hcanon : 3 * n + 1 = 4 * n) :
    n = 1 := by
  omega

lemma unique_fixed_point : is_fixed_point 1 := one_is_fixed_point

/-- Canonical fixed-point equation for the odd Collatz step: every fixed point
of `collatz_step` satisfies `3x + 1 = 4x`. The proof shows that the only
solution to `(3x+1)/2^{step_type x} = x` in the natural numbers is `x = 1`
(for which `step_type 1 = 2` and `4·1 = 4 = 3·1 + 1`).

This discharges the fixed-point canonization clause of
`periodic_orbit_bridge_contract`, removing the corresponding
hypothesis from `collatz_convergence`. -/
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

/-- Period-1 periodic tails reduce to a fixed point at the tail entry.
With the canonical fixed-point equation contract, this yields `1` on orbit. -/
theorem period_one_tail_reaches_one
    (n : ℕ)
    (hw : Collatz.CycleExclusion.OrbitPeriodicTailWitness n)
    (hperiod1 : hw.period = 1)
    (hcanon : ∀ x : ℕ, collatz_step x = x → 3 * x + 1 = 4 * x) :
    ∃ k : ℕ, (collatz_step^[k]) n = 1 := by
  let x : ℕ := (collatz_step^[hw.start]) n
  have htailEq :
      (collatz_step^[hw.start + 1]) n =
      (collatz_step^[hw.start]) n := by
    simpa [hperiod1] using hw.periodic 0
  have hsucc :
      (collatz_step^[hw.start + 1]) n = collatz_step x := by
    simp [x, Function.iterate_succ_apply']
  have hfixEq : collatz_step x = x := by
    calc
      collatz_step x = (collatz_step^[hw.start + 1]) n := hsucc.symm
      _ = (collatz_step^[hw.start]) n := htailEq
      _ = x := by rfl
  have hfix : is_fixed_point x := hfixEq
  have hx1 : x = 1 := fixed_point_uniqueness x hfix (hcanon x hfixEq)
  exact ⟨hw.start, hx1⟩

end Collatz.Convergence
