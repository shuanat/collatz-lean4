import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Collatz.Foundations.Core
import Collatz.Epochs.Core

/-!
# SEDT constants and the envelope expression

Definitions of the constants `α, β₀, C, L₀, ε` and of the expression
`sedt_envelope t U β L = −ε(t,U,β)·L + β·C(t,U)` from paper Appendix E, plus
elementary facts about them (`1 < α < 2` for `t ≥ 3`, `β₀ > 0`, `ε > 0` for
`β > β₀`).

Status (2026-10 review): the paper's Theorem E.2 ("SEDT": the potential change
over every long epoch is at most `sedt_envelope`) is false as stated and is
NOT formalized; it appears in this library only as an explicit hypothesis
(`orbit_epoch_sedt_envelope`, `Convergence/Coercivity.lean`), which is
contradictory on every long-epoch stream of an odd orbit
(`Collatz.Convergence.false_of_orbit_epoch_sedt_envelope`). The placeholder
lemmas formerly in this module and in `SEDT/Theorems.lean`, `SEDT/Axioms.lean`
(e.g. `sedt_full_bound_technical`, `touch_provides_onebit_bonus`,
`period_sum_with_density_negative`) were deleted.
-/

namespace Collatz.SEDT

open Collatz.Epochs (Q_t)
open Real

noncomputable def α (t U : ℕ) : ℝ := 1 + (1 / (Q_t t + U + 1 : ℝ))

noncomputable def β₀ (t U : ℕ) : ℝ := (Real.log (3 / 2) / Real.log 2) / (2 - α t U)

noncomputable def C (t U : ℕ) : ℝ := (2^(t + 1) + 3 * t + 3 * U : ℝ)

def L₀ (t U : ℕ) : ℕ := 2^(t + U) * Q_t (t + U)

noncomputable def ε (t U : ℕ) (β : ℝ) : ℝ := β * (2 - α t U) - Real.log (3 / 2) / Real.log 2

noncomputable def sedt_envelope (t : ℕ) (U : ℕ) (β : ℝ) (L : ℕ) : ℝ :=
  -(ε t U β) * (L : ℝ) + β * C t U

noncomputable def augmented_potential (n : ℕ) (β : ℝ) : ℝ :=
  Real.log (n + 1) / Real.log 2 + β * (Collatz.Foundations.depth_minus n : ℝ)

noncomputable def potential_change (start_val end_val : ℕ) (β : ℝ) : ℝ :=
  augmented_potential end_val β - augmented_potential start_val β

lemma alpha_gt_one (t U : ℕ) : α t U > 1 := by
  unfold α
  have hpos : (0 : ℝ) < (Q_t t + U + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos (Q_t t + U)
  have hfrac : 0 < (1 / (Q_t t + U + 1 : ℝ)) := by
    exact one_div_pos.mpr hpos
  linarith

lemma alpha_lt_two (t U : ℕ) (hden : (2 : ℝ) ≤ (Q_t t + U + 1 : ℝ)) : α t U < 2 := by
  unfold α
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hrec : (1 / (Q_t t + U + 1 : ℝ)) ≤ (1 / 2 : ℝ) := by
    exact one_div_le_one_div_of_le h2pos hden
  linarith

lemma alpha_lt_two_of_ht_hU (t U : ℕ) (ht : 3 ≤ t) (_hU : 1 ≤ U) : α t U < 2 := by
  have hpow : (2 : ℕ) ≤ Q_t t := by
    unfold Q_t
    have h1 : 1 ≤ t - 2 := by omega
    have hp : (2 : ℕ) ^ 1 ≤ 2 ^ (t - 2) := Nat.pow_le_pow_right (by decide) h1
    simpa using hp
  have hnat : (2 : ℕ) ≤ Q_t t + U + 1 := by
    calc
      2 ≤ Q_t t := hpow
      _ ≤ Q_t t + U := Nat.le_add_right _ _
      _ ≤ Q_t t + U + 1 := Nat.le_add_right _ _
  have hden : (2 : ℝ) ≤ (Q_t t + U + 1 : ℝ) := by exact_mod_cast hnat
  exact alpha_lt_two t U hden

lemma beta_zero_pos (t U : ℕ) (hα : α t U < 2) : β₀ t U > 0 := by
  unfold β₀
  have hnum : 0 < Real.log (3 / 2) / Real.log 2 := by
    have h1 : 0 < Real.log (3 / 2) := by
      apply Real.log_pos
      norm_num
    have h2 : 0 < Real.log 2 := by
      apply Real.log_pos
      norm_num
    exact div_pos h1 h2
  have hden : 0 < 2 - α t U := by linarith
  exact div_pos hnum hden

lemma epsilon_pos (t U : ℕ) (β : ℝ)
  (_ht : t ≥ 3) (_hU : U ≥ 1)
  (hα : α t U < 2) (hβ : β > β₀ t U) : ε t U β > 0 := by
  unfold ε β₀ at *
  have hden : 0 < 2 - α t U := by linarith
  have hmul : β * (2 - α t U) > (Real.log (3 / 2) / Real.log 2) := by
    have hβmul : β * (2 - α t U) > ((Real.log (3 / 2) / Real.log 2) / (2 - α t U)) * (2 - α t U) := by
      exact mul_lt_mul_of_pos_right hβ hden
    have hcancel : ((Real.log (3 / 2) / Real.log 2) / (2 - α t U)) * (2 - α t U) =
        Real.log (3 / 2) / Real.log 2 := by
      field_simp [hden.ne']
    simpa [hcancel] using hβmul
  linarith

/-- Exact split of the change of `augmented_potential` into a logarithmic part
and a depth part. -/
lemma potential_change_eq_log_part_plus_depth_part
    (startVal endVal : ℕ) (β : ℝ) :
    potential_change startVal endVal β =
      (Real.log (endVal + 1) - Real.log (startVal + 1)) / Real.log 2 +
        β * (((Collatz.Foundations.depth_minus endVal : ℝ) -
          (Collatz.Foundations.depth_minus startVal : ℝ))) := by
  unfold potential_change augmented_potential
  ring_nf

/-- Rewriting of the SEDT envelope as `L·log₂(3/2) + β((α − 2)L + C)`. -/
lemma sedt_envelope_eq_log_depth_form
    (t U : ℕ) (β : ℝ) (L : ℕ) :
    sedt_envelope t U β L =
      (L : ℝ) * (Real.log (3 / 2) / Real.log 2) +
        β * ((α t U - 2) * (L : ℝ) + C t U) := by
  unfold sedt_envelope ε
  ring

end Collatz.SEDT
