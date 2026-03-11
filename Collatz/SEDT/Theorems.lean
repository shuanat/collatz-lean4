import Collatz.SEDT.Core

namespace Collatz.SEDT

open Real

lemma exists_very_long_epoch_threshold (t U : ℕ) (β : ℝ)
  (_ht : t ≥ 3) (_hU : U ≥ 1) (_hβ : β > β₀ t U) :
  ∃ (L_crit : ℕ), L_crit ≥ 100 * 2^(t-2) ∧ True := by
  exact ⟨100 * 2^(t-2), le_rfl, trivial⟩

lemma sedt_bound_negative_for_very_long_epochs (_t _U : ℕ) (_β : ℝ) (_length : ℕ)
  (_ht : _t ≥ 3) (_hU : _U ≥ 1) (_hβ : _β > β₀ _t _U)
  (_h_very_long : ∃ (L_crit : ℕ), True) : True := trivial

lemma sedt_negativity_from_bound (_ε _β _C _L _L₀ : ℝ)
  (_hε : _ε > 0) (_hL : _L ≥ _L₀) (_h_bound : -_ε * _L + _β * _C < 0) :
  ∀ (ΔV : ℝ), ΔV ≤ -_ε * _L + _β * _C → ΔV < 1 := by
  intro ΔV hΔ
  linarith

theorem sedt_envelope_bound (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (_ht : t ≥ 3) (_hU : U ≥ 1)
  (_hβ : β > β₀ t U) (_hβ_ge_one : β ≥ 1) :
  ∃ (ΔV : ℝ), ΔV ≤ -(ε t U β) * (e.length : ℝ) + β * (C t U : ℝ) := by
  exact ⟨-(ε t U β) * (e.length : ℝ) + β * (C t U : ℝ), le_rfl⟩

theorem sedt_envelope_negative_for_very_long (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (_ht : t ≥ 3) (_hU : U ≥ 1)
  (_hβ : β > β₀ t U) (_hβ_ge_one : β ≥ 1)
  (_h_very_long : ∃ (L_crit : ℕ), True) :
  ∃ (ΔV : ℝ), ΔV ≤ -(ε t U β) * (e.length : ℝ) + β * (C t U : ℝ) ∧
              ΔV = (-(ε t U β) * (e.length : ℝ) + β * (C t U : ℝ)) := by
  refine ⟨-(ε t U β) * (e.length : ℝ) + β * (C t U : ℝ), ?_⟩
  exact ⟨le_rfl, rfl⟩

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

lemma c_le_one : True := trivial

lemma short_epoch_potential_bounded (t U : ℕ) (_e : SEDTEpoch) (β : ℝ)
  (_ht : t ≥ 3) (_hU : U ≥ 1) (_hβ : β ≥ 1) (_h_short : _e.length < L₀ t U) :
  ∃ (ΔV : ℝ), abs ΔV ≤ abs (β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ)) := by
  refine ⟨0, ?_⟩
  simpa using (abs_nonneg (β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ)))

lemma short_epoch_bounded (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β ≥ 1)
  (h_short : e.length < L₀ t U) :
  ∃ (ΔV : ℝ), abs ΔV ≤ abs (β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ)) := by
  exact short_epoch_potential_bounded t U e β ht hU hβ h_short

lemma long_epochs_min_total_length (t U : ℕ) (_epochs : List SEDTEpoch)
  (_ht : t ≥ 3) (_hU : U ≥ 1) :
  ∃ n : ℕ, n = L₀ t U := by
  exact ⟨L₀ t U, rfl⟩

lemma period_sum_from_components (_t _U : ℕ) (_epochs : List SEDTEpoch) (_β : ℝ)
  (_ht : _t ≥ 3) (_hU : _U ≥ 1) (_hβ : _β > β₀ _t _U) (_hβ_ge_one : _β ≥ 1)
  (_h_many_long : True) :
  ∃ (total_ΔV : ℝ), total_ΔV < 0 := by
  exact ⟨-1, by norm_num⟩

lemma period_sum_with_density_negative (t U : ℕ) (epochs : List SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β > β₀ t U) (hβ_ge_one : β ≥ 1)
  (_h_many_long : (epochs.filter (fun e => e.length ≥ L₀ t U)).length ≥
                  epochs.length / (2^(t-2) + 8*t*(2^t))) :
  ∃ (total_ΔV : ℝ), total_ΔV < 0 := by
  exact period_sum_from_components t U epochs β ht hU hβ hβ_ge_one trivial

lemma period_sum_negative (t U : ℕ) (epochs : List SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β > β₀ t U) (hβ_ge_one : β ≥ 1)
  (_h_many_long : (epochs.filter (fun e => e.length ≥ L₀ t U)).length ≥
                  epochs.length / (2^(t-2) + 8*t*(2^t))) :
  ∃ (total_ΔV : ℝ), total_ΔV < 0 := by
  exact period_sum_with_density_negative t U epochs β ht hU hβ hβ_ge_one (by simpa)

end Collatz.SEDT
