/-
Real-valued forms of the linear-surplus combiner (generic inequalities).

From the hypotheses of `LinearSurplus.linear_surplus` one gets
`B ≥ ((2^U − 1)/2^U)·(L/P − P) = (1 − 2^{−U})·(L/P − P)` in `ℝ`.

Status (2026-10 review). These are *lower* bounds on `B`. They do not bound the
orbit's multibit gain from above and therefore do not discharge the former
`selected_multibit_gain_budget` depth residual (which was an upper-bound
requirement); the hypotheses are not established for Collatz orbits either.
-/

import Mathlib.Tactic
import Collatz.SEDT.LinearSurplus

namespace Collatz.SEDT.LinearSurplusReal

open Real

/-- **Real-valued cross-multiplied form.** Direct cast of the integer
combiner `Collatz.SEDT.LinearSurplus.linear_surplus`. -/
theorem linear_surplus_real_cross
    (P U L N B : ℕ) (hP : 1 ≤ P) (hU : 1 ≤ U)
    (hTouch : N * P + P * P ≥ L)
    (hBonus : B * 2 ^ U ≥ N * (2 ^ U - 1)) :
    ((B : ℝ) * (2 : ℝ) ^ U * P) + (((2 : ℝ) ^ U - 1) * P * P)
      ≥ ((2 : ℝ) ^ U - 1) * L := by
  have hint :=
    Collatz.SEDT.LinearSurplus.linear_surplus P U L N B hP hU hTouch hBonus
  -- `hint : B * 2^U * P + (2^U - 1) * P * P ≥ (2^U - 1) * L`  in ℕ.
  have h2Upos : 1 ≤ (2 : ℕ) ^ U := Nat.one_le_two_pow
  -- Cast via `(2^U - 1 : ℕ) = (2^U : ℕ) - 1 = (2^U : ℝ) - 1`.
  have hcast :
      (((2 ^ U - 1 : ℕ) : ℝ) = ((2 : ℝ) ^ U - 1)) := by
    rw [Nat.cast_sub h2Upos]
    push_cast
    ring
  have hcast_lhs :
      ((B * 2 ^ U * P + (2 ^ U - 1) * P * P : ℕ) : ℝ)
        = (B : ℝ) * (2 : ℝ) ^ U * P + ((2 : ℝ) ^ U - 1) * P * P := by
    push_cast [Nat.cast_sub h2Upos]
    ring
  have hcast_rhs :
      (((2 ^ U - 1) * L : ℕ) : ℝ) = ((2 : ℝ) ^ U - 1) * L := by
    push_cast [Nat.cast_sub h2Upos]
    ring
  have hreal :
      ((B * 2 ^ U * P + (2 ^ U - 1) * P * P : ℕ) : ℝ)
        ≥ (((2 ^ U - 1) * L : ℕ) : ℝ) := by exact_mod_cast hint
  rw [hcast_lhs, hcast_rhs] at hreal
  exact hreal

/-- **Real-valued division form.**

    `B ≥ ((2^U − 1) / 2^U) * (L/P − P)`,

obtained from the cross form by dividing by `2^U * P > 0`. -/
theorem linear_surplus_real_div
    (P U L N B : ℕ) (hP : 1 ≤ P) (hU : 1 ≤ U)
    (hTouch : N * P + P * P ≥ L)
    (hBonus : B * 2 ^ U ≥ N * (2 ^ U - 1)) :
    (B : ℝ) ≥ (((2 : ℝ) ^ U - 1) / (2 : ℝ) ^ U) *
              ((L : ℝ) / P - P) := by
  have hcross :=
    linear_surplus_real_cross P U L N B hP hU hTouch hBonus
  -- `2^U > 0` and `P > 0` in ℝ.
  have h2U_pos : (0 : ℝ) < (2 : ℝ) ^ U := by positivity
  have hP_real_pos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have h2UP_pos : (0 : ℝ) < (2 : ℝ) ^ U * P := mul_pos h2U_pos hP_real_pos
  -- Rearrange `hcross` to:
  --   B * 2^U * P ≥ (2^U − 1) * L − (2^U − 1) * P²
  -- and divide by `2^U * P`:
  --   B ≥ (2^U − 1) * (L / P − P) / 2^U
  --     = ((2^U − 1) / 2^U) * (L/P − P).
  have hineq :
      (B : ℝ) * ((2 : ℝ) ^ U * P)
        ≥ ((2 : ℝ) ^ U - 1) * ((L : ℝ) - P * P) := by
    have hexpand :
        (B : ℝ) * ((2 : ℝ) ^ U * P)
          = (B : ℝ) * (2 : ℝ) ^ U * P := by ring
    rw [hexpand]
    nlinarith [hcross]
  -- Divide by `2^U * P`:
  have hdiv :
      (B : ℝ) ≥ (((2 : ℝ) ^ U - 1) * ((L : ℝ) - P * P)) /
                ((2 : ℝ) ^ U * P) := by
    rw [ge_iff_le, div_le_iff₀ h2UP_pos]
    linarith [hineq]
  -- Rewrite RHS in the requested shape.
  have hRHS_eq :
      (((2 : ℝ) ^ U - 1) * ((L : ℝ) - P * P)) / ((2 : ℝ) ^ U * P)
        = (((2 : ℝ) ^ U - 1) / (2 : ℝ) ^ U) * ((L : ℝ) / P - P) := by
    field_simp
  rw [hRHS_eq] at hdiv
  exact hdiv

/-- **Selected-budget form.**

    `B ≥ (1 − 2^{−U}) * (L/P − P)`. -/
theorem linear_surplus_real_budget
    (P U L N B : ℕ) (hP : 1 ≤ P) (hU : 1 ≤ U)
    (hTouch : N * P + P * P ≥ L)
    (hBonus : B * 2 ^ U ≥ N * (2 ^ U - 1)) :
    (B : ℝ) ≥ (1 - (2 : ℝ) ^ (-(U : ℤ))) * ((L : ℝ) / P - P) := by
  have hdiv :=
    linear_surplus_real_div P U L N B hP hU hTouch hBonus
  have h2U_pos : (0 : ℝ) < (2 : ℝ) ^ U := by positivity
  have h2U_ne : ((2 : ℝ) ^ U) ≠ 0 := ne_of_gt h2U_pos
  have hcoef :
      ((2 : ℝ) ^ U - 1) / (2 : ℝ) ^ U
        = 1 - (2 : ℝ) ^ (-(U : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [hcoef] at hdiv
  exact hdiv

end Collatz.SEDT.LinearSurplusReal
