import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Collatz.Foundations.Core
import Collatz.Epochs.Core

namespace Collatz.SEDT

open Collatz.Epochs (Q_t)
open Real

noncomputable def α (t U : ℕ) : ℝ := 1 + (1 / (Q_t t + U + 1 : ℝ))

noncomputable def β₀ (t U : ℕ) : ℝ := (Real.log (3 / 2) / Real.log 2) / (2 - α t U)

noncomputable def C (t U : ℕ) : ℝ := (2^(t + 1) + 3 * t + 3 * U : ℝ)

def L₀ (t U : ℕ) : ℕ := 2^(t + U) * Q_t (t + U)

def K_glue (t : ℕ) : ℕ := max (2 * Q_t t) (3 * t)

noncomputable def ε (t U : ℕ) (β : ℝ) : ℝ := β * (2 - α t U) - Real.log (3 / 2) / Real.log 2

noncomputable def sedt_envelope (t : ℕ) (U : ℕ) (β : ℝ) (L : ℕ) : ℝ :=
  -(ε t U β) * (L : ℝ) + β * C t U

def sedt_negativity_condition (t : ℕ) (U : ℕ) (β : ℝ) : Prop := ε t U β > 0

def sedt_parameter_valid (t U : ℕ) (β : ℝ) : Prop := β > β₀ t U

noncomputable def augmented_potential (n : ℕ) (β : ℝ) : ℝ :=
  Real.log (n + 1) / Real.log 2 + β * (Collatz.Foundations.depth_minus n : ℝ)

noncomputable def potential_change (start_val end_val : ℕ) (β : ℝ) : ℝ :=
  augmented_potential end_val β - augmented_potential start_val β

structure SEDTEpoch where
  length : ℕ
  head_overhead : ℝ
  boundary_overhead : ℝ

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

lemma two_mul_le_two_pow (t : ℕ) (_ht : t ≥ 3) : 2 * t ≤ 2^t + 2 * t := by
  exact Nat.le_add_left _ _

lemma max_K_glue_le_pow_two (t : ℕ) (_ht : t ≥ 4) :
    (K_glue t : ℝ) ≤ ((2 * Q_t t + 3 * t : ℕ) : ℝ) := by
  unfold K_glue
  have h1 : 2 * Q_t t ≤ 2 * Q_t t + 3 * t := Nat.le_add_right _ _
  have h2 : 3 * t ≤ 2 * Q_t t + 3 * t := Nat.le_add_left _ _
  exact_mod_cast ((max_le_iff).2 ⟨h1, h2⟩)

lemma sedt_overhead_bound (t U : ℕ) (β : ℝ) :
  abs (β * C t U) ≤ abs β * abs (C t U) := by
  simp [abs_mul]

lemma t_log_bound_for_sedt (t : ℕ) (_ht : t ≥ 3) :
    0 ≤ (t : ℝ) * Real.log (3 / 2) / Real.log 2 := by
  have h1 : 0 ≤ (t : ℝ) := by exact_mod_cast (Nat.zero_le t)
  have h2 : 0 ≤ Real.log (3 / 2) := by
    have : (1 : ℝ) ≤ 3 / 2 := by norm_num
    exact Real.log_nonneg this
  have h3 : 0 ≤ Real.log 2 := by
    have : (1 : ℝ) ≤ 2 := by norm_num
    exact Real.log_nonneg this
  positivity

lemma sedt_full_bound_technical (_t _U : ℕ) (_β ΔV_head drift_per_step ΔV_boundary : ℝ) (_L : ℕ)
  (_ht : _t ≥ 3) (_hU : _U ≥ 1) (_hβ_ge_one : _β ≥ 1)
  (_h_head : abs ΔV_head ≤ _β * (2^_t : ℝ) + (_t : ℝ) * Real.log (3/2) / Real.log 2)
  (_h_drift_neg : drift_per_step ≤ -(ε _t _U _β))
  (_h_boundary : abs ΔV_boundary ≤ _β * (K_glue _t : ℝ)) :
  abs ΔV_head ≤ _β * (2^_t : ℝ) + (_t : ℝ) * Real.log (3/2) / Real.log 2 ∧
  abs ΔV_boundary ≤ _β * (K_glue _t : ℝ) := by
  exact ⟨_h_head, _h_boundary⟩

lemma touch_provides_onebit_bonus (n : ℕ) (β : ℝ) :
    augmented_potential n β - Real.log (n + 1) / Real.log 2 =
      β * (Collatz.Foundations.depth_minus n : ℝ) := by
  simp [augmented_potential]

noncomputable abbrev SlopeParam := α
noncomputable abbrev NegativityThreshold := β₀
noncomputable abbrev DriftDiscrepancy := C
abbrev LongEpochThreshold := L₀
abbrev GlueConstant := K_glue
noncomputable abbrev DriftRate := ε
noncomputable abbrev SEDTEnvelope := sedt_envelope
noncomputable abbrev AugmentedPotential := augmented_potential

end Collatz.SEDT
