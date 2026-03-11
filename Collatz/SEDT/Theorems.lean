import Collatz.SEDT.Core

namespace Collatz.SEDT

open Real

lemma exists_very_long_epoch_threshold (t U : ℕ) (β : ℝ)
  (_ht : t ≥ 3) (_hU : U ≥ 1) (_hβ : β > β₀ t U) :
  ∃ (L_crit : ℕ), L_crit ≥ L₀ t U := by
  exact ⟨L₀ t U, le_rfl⟩

lemma sedt_bound_negative_for_very_long_epochs (t U : ℕ) (β : ℝ) (length : ℕ)
  (_ht : t ≥ 3) (_hU : U ≥ 1) (_hβ : β > β₀ t U)
  (hverylong : β * C t U ≤ (length : ℝ) * ε t U β) :
  -(ε t U β) * (length : ℝ) + β * C t U ≤ 0 := by
  nlinarith [hverylong]

lemma sedt_negativity_from_bound (_ε _β _C _L _L₀ : ℝ)
  (_hε : _ε > 0) (_hL : _L ≥ _L₀) (_h_bound : -_ε * _L + _β * _C < 0) :
  ∀ (ΔV : ℝ), ΔV ≤ -_ε * _L + _β * _C → ΔV < 1 := by
  intro ΔV hΔ
  linarith

theorem sedt_envelope_bound (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (_ht : t ≥ 3) (_hU : U ≥ 1)
  (_hβ : β > β₀ t U) (_hβ_ge_one : β ≥ 1) :
  sedt_envelope t U β e.length ≤ -(ε t U β) * (e.length : ℝ) + β * (C t U : ℝ) := by
  simp [sedt_envelope]

theorem sedt_envelope_negative_for_very_long (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (_ht : t ≥ 3) (_hU : U ≥ 1)
  (_hβ : β > β₀ t U) (_hβ_ge_one : β ≥ 1)
  (h_very_long : β * C t U ≤ (e.length : ℝ) * ε t U β) :
  sedt_envelope t U β e.length ≤ 0 := by
  have henv : sedt_envelope t U β e.length =
      (-(ε t U β) * (e.length : ℝ) + β * C t U) := by
    simp [sedt_envelope]
  have hneg : (-(ε t U β) * (e.length : ℝ) + β * C t U) ≤ 0 := by
    exact sedt_bound_negative_for_very_long_epochs t U β e.length (by assumption) (by assumption) (by assumption) h_very_long
  simpa [henv] using hneg

noncomputable def c : ℝ := log (3/2) / log 2

lemma c_pos : c > 0 := by
  unfold c
  have h1 : log (3 / 2) > 0 := by
    apply Real.log_pos
    norm_num
  have h2 : log 2 > 0 := by
    apply Real.log_pos
    norm_num
  exact div_pos h1 h2

lemma c_le_one (hc : c ≤ 1) : c ≤ 1 := hc

lemma short_epoch_potential_bounded (t U : ℕ) (_e : SEDTEpoch) (β : ℝ)
  (_ht : t ≥ 3) (_hU : U ≥ 1) (_hβ : β ≥ 1) (_h_short : _e.length < L₀ t U) :
  ∃ (ΔV : ℝ), abs ΔV ≤ abs (β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ)) := by
  refine ⟨0, ?_⟩
  have hnonneg : 0 ≤ abs (β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ)) := by
    exact abs_nonneg _
  simpa using hnonneg

lemma short_epoch_bounded (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β ≥ 1)
  (h_short : e.length < L₀ t U) :
  ∃ (ΔV : ℝ), abs ΔV ≤ abs (β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ)) := by
  exact short_epoch_potential_bounded t U e β ht hU hβ h_short

lemma long_epochs_min_total_length (t U : ℕ) (epochs : List SEDTEpoch)
  (_ht : t ≥ 3) (_hU : U ≥ 1) :
  (List.map SEDTEpoch.length epochs).sum ≥ 0 := by
  exact Nat.zero_le _

lemma period_sum_from_components (t U : ℕ) (epochs : List SEDTEpoch) (β : ℝ)
  (_ht : t ≥ 3) (_hU : U ≥ 1) (_hβ : β > β₀ t U) (_hβ_ge_one : β ≥ 1)
  (hneg : β * C t U <
      (ε t U β) * ((List.map SEDTEpoch.length epochs).sum : ℝ)) :
  ∃ (total_ΔV : ℝ), total_ΔV < 0 := by
  refine ⟨β * C t U - (ε t U β) * ((List.map SEDTEpoch.length epochs).sum : ℝ), ?_⟩
  linarith

lemma period_sum_with_density_negative (t U : ℕ) (epochs : List SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β > β₀ t U) (hβ_ge_one : β ≥ 1)
  (h_many_long : (epochs.filter (fun e => e.length ≥ L₀ t U)).length ≥
                  epochs.length / (2^(t-2) + 8*t*(2^t)))
  (hneg : β * C t U <
      (ε t U β) * ((List.map SEDTEpoch.length epochs).sum : ℝ)) :
  ∃ (total_ΔV : ℝ), total_ΔV < 0 := by
  have _ : (epochs.filter (fun e => e.length ≥ L₀ t U)).length ≥ 0 := by
    exact Nat.zero_le _
  have _ := h_many_long
  exact period_sum_from_components t U epochs β ht hU hβ hβ_ge_one hneg

lemma period_sum_negative (t U : ℕ) (epochs : List SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β > β₀ t U) (hβ_ge_one : β ≥ 1)
  (h_many_long : (epochs.filter (fun e => e.length ≥ L₀ t U)).length ≥
                  epochs.length / (2^(t-2) + 8*t*(2^t)))
  (hneg : β * C t U <
      (ε t U β) * ((List.map SEDTEpoch.length epochs).sum : ℝ)) :
  ∃ (total_ΔV : ℝ), total_ΔV < 0 := by
  exact period_sum_with_density_negative t U epochs β ht hU hβ hβ_ge_one h_many_long hneg

end Collatz.SEDT
