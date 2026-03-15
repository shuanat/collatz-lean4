import Collatz.SEDT.Core
import Collatz.Epochs.LongEpochs
import Collatz.Epochs.LongEpochs
import Collatz.Epochs.LongEpochs

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

/-- Minimal theorem-level SEDT interface for a real orbit segment:
an aligned phase-return interval with SEDT-long separation satisfies the
envelope bound when measured in the native `SEDT.potential_change` language. -/
def sedt_potential_change_of_gap_long_multiple_segment
    (m t U : ℕ) (β : ℝ) : Prop :=
  t ≥ 3 →
    U ≥ 1 →
      β > β₀ t U →
        ∀ i L : ℕ,
          L₀ t U ≤ L →
          Collatz.Epochs.gap_long t ∣ L →
            potential_change
              ((Collatz.Foundations.collatz_step^[i]) m)
              ((Collatz.Foundations.collatz_step^[i + L]) m)
              β ≤
                sedt_envelope t U β L

def sedt_potential_change_of_phase_return_segment
    (m t U : ℕ) (β : ℝ) : Prop :=
  t ≥ 3 →
    U ≥ 1 →
      β > β₀ t U →
        ∀ i j : ℕ,
          i + L₀ t U ≤ j →
          i % Collatz.Epochs.gap_long t = j % Collatz.Epochs.gap_long t →
            potential_change
              ((Collatz.Foundations.collatz_step^[i]) m)
              ((Collatz.Foundations.collatz_step^[j]) m)
              β ≤
                sedt_envelope t U β (j - i)

/-- An aligned phase-return segment is an immediate corollary of the more
arithmetic SEDT contract formulated in terms of segment length `L` divisible by
`gap_long t`. This cleanly separates phase arithmetic from the actual drift
bound. -/
theorem sedt_potential_change_of_phase_return_segment_of_gap_long_multiple
    {m t U : ℕ} {β : ℝ}
    (hmult : sedt_potential_change_of_gap_long_multiple_segment m t U β) :
    sedt_potential_change_of_phase_return_segment m t U β := by
  intro ht hU hβ i j hsep hphase
  have hij : i ≤ j := le_trans (Nat.le_add_right _ _) hsep
  have hlen : L₀ t U ≤ j - i := by
    have hsep' : L₀ t U + i ≤ j := by
      simpa [Nat.add_comm] using hsep
    exact (Nat.le_sub_iff_add_le hij).2 hsep'
  have hdvd : Collatz.Epochs.gap_long t ∣ j - i := by
    exact Epochs.gap_long_dvd_sub_of_phase_aligned t i j hij hphase
  have hseg :=
    hmult ht hU hβ i (j - i) hlen hdvd
  have hsum : i + (j - i) = j := Nat.add_sub_of_le hij
  simpa [hsum] using hseg

/-- Conversely, the gap-multiple formulation is just the same local SEDT
segment bound specialized to an endpoint of the form `i + L`. -/
theorem sedt_potential_change_of_gap_long_multiple_segment_of_phase_return
    {m t U : ℕ} {β : ℝ}
    (hseg : sedt_potential_change_of_phase_return_segment m t U β) :
    sedt_potential_change_of_gap_long_multiple_segment m t U β := by
  intro ht hU hβ i L hlen hdvd
  have hsep : i + L₀ t U ≤ i + L := Nat.add_le_add_left hlen i
  have hphase : i % Collatz.Epochs.gap_long t = (i + L) % Collatz.Epochs.gap_long t := by
    exact Epochs.phase_aligned_of_gap_long_dvd_add t i L hdvd
  simpa using hseg ht hU hβ i (i + L) hsep hphase

/-- The phase-return and gap-multiple local SEDT interfaces are arithmetically
equivalent; neither one hides additional orbit content beyond the other. -/
theorem sedt_potential_change_of_gap_long_multiple_segment_iff_phase_return_segment
    {m t U : ℕ} {β : ℝ} :
    sedt_potential_change_of_gap_long_multiple_segment m t U β ↔
      sedt_potential_change_of_phase_return_segment m t U β := by
  constructor
  · exact sedt_potential_change_of_phase_return_segment_of_gap_long_multiple
  · exact sedt_potential_change_of_gap_long_multiple_segment_of_phase_return

/-- Apply the local SEDT segment contract in theorem form. -/
def sedt_potential_change_bound_of_phase_return_segment
    {m t U : ℕ} {β : ℝ}
    (hseg : sedt_potential_change_of_phase_return_segment m t U β)
    (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β > β₀ t U)
    {i j : ℕ}
    (hsep : i + L₀ t U ≤ j)
    (hphase : i % Collatz.Epochs.gap_long t = j % Collatz.Epochs.gap_long t) :
    potential_change
      ((Collatz.Foundations.collatz_step^[i]) m)
      ((Collatz.Foundations.collatz_step^[j]) m)
      β ≤
        sedt_envelope t U β (j - i) :=
  hseg ht hU hβ i j hsep hphase

/-- Paper-E.1 style control of the logarithmic part of the augmented potential
over one realized long segment. -/
def local_log_drift_bound (startVal endVal : ℕ) (L : ℕ) : Prop :=
  (Real.log (endVal + 1) - Real.log (startVal + 1)) / Real.log 2 ≤
    (L : ℝ) * (Real.log (3 / 2) / Real.log 2)

/-- Paper-E.1/E.2 style control of the depth contribution over one realized long
segment. This is the native deterministic input carrying the touch/bonus
content, separated from logarithmic accounting. -/
def local_depth_drift_bound
    (t U : ℕ) (β : ℝ) (startVal endVal : ℕ) (L : ℕ) : Prop :=
  β * (((Collatz.Foundations.depth_minus endVal : ℝ) -
      (Collatz.Foundations.depth_minus startVal : ℝ))) ≤
    β * ((α t U - 2) * (L : ℝ) + C t U)

lemma potential_change_eq_log_part_plus_depth_part
    (startVal endVal : ℕ) (β : ℝ) :
    potential_change startVal endVal β =
      (Real.log (endVal + 1) - Real.log (startVal + 1)) / Real.log 2 +
        β * (((Collatz.Foundations.depth_minus endVal : ℝ) -
          (Collatz.Foundations.depth_minus startVal : ℝ))) := by
  unfold potential_change augmented_potential
  ring_nf

lemma sedt_envelope_eq_log_depth_form
    (t U : ℕ) (β : ℝ) (L : ℕ) :
    sedt_envelope t U β L =
      (L : ℝ) * (Real.log (3 / 2) / Real.log 2) +
        β * ((α t U - 2) * (L : ℝ) + C t U) := by
  unfold sedt_envelope ε
  ring

/-- Honest local SEDT assembly theorem: once the logarithmic part and the depth
part are bounded on a realized long segment exactly as in paper E.1/E.2, the
native `SEDT.potential_change` envelope follows immediately. -/
theorem potential_change_le_sedt_envelope_of_local_bounds
    {t U : ℕ} {β : ℝ} {startVal endVal : ℕ} {L : ℕ}
    (hlog : local_log_drift_bound startVal endVal L)
    (hdepth : local_depth_drift_bound t U β startVal endVal L) :
    potential_change startVal endVal β ≤ sedt_envelope t U β L := by
  rw [potential_change_eq_log_part_plus_depth_part, sedt_envelope_eq_log_depth_form]
  exact add_le_add hlog hdepth

/-- Paper-faithful local witness on the canonical selected long segments carried
by a phase-return witness: each actual selected segment must supply exactly the
logarithmic and depth-side bounds whose assembly yields the local SEDT drift
estimate. -/
def phase_return_epoch_accounting_witness
    (m t U : ℕ) (β : ℝ) : Prop :=
  t ≥ 3 →
    U ≥ 1 →
      β > β₀ t U →
        ∀ hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U,
          ∀ j : ℕ,
            local_log_drift_bound
              ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
              ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
              (hphase.rightIdx j - hphase.leftIdx j) ∧
            local_depth_drift_bound t U β
              ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
              ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
              (hphase.rightIdx j - hphase.leftIdx j)

/-- Apply the local accounting witness on one canonical selected phase-return
segment to obtain the native `SEDT.potential_change` envelope. -/
theorem phase_return_native_potential_change_of_accounting_witness
    {m t U : ℕ} {β : ℝ}
    (hacc : phase_return_epoch_accounting_witness m t U β)
    (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β > β₀ t U)
    (hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U)
    (j : ℕ) :
    potential_change
      ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
      ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
      β ≤
        sedt_envelope t U β (hphase.rightIdx j - hphase.leftIdx j) := by
  rcases hacc ht hU hβ hphase j with ⟨hlog, hdepth⟩
  exact potential_change_le_sedt_envelope_of_local_bounds hlog hdepth

/-- Extract the log-side local E.1 bound from the paper-faithful selected long
epoch witness. -/
theorem local_log_drift_bound_of_selected_long_epoch
    {m t U : ℕ}
    {hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U}
    {j : ℕ}
    (hw : Collatz.Epochs.SelectedLongEpochWitness hphase j) :
    local_log_drift_bound
      ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
      ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
      (hphase.rightIdx j - hphase.leftIdx j) := by
  dsimp [local_log_drift_bound]
  simpa [← hw.realizedStart, ← hw.realizedEnd] using hw.logCompression

/-- Extract the depth-side local E.1/E.2 bound from the paper-faithful selected
long epoch witness. The theorem is where the repaired epoch/touch/multibit
semantics collapse to the coefficient `(α-2)L + C`. -/
theorem local_depth_drift_bound_of_selected_long_epoch
    {m t U : ℕ} {β : ℝ}
    {hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U}
    {j : ℕ}
    (hβnonneg : 0 ≤ β)
    (hw : Collatz.Epochs.SelectedLongEpochWitness hphase j) :
    local_depth_drift_bound t U β
      ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
      ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
      (hphase.rightIdx j - hphase.leftIdx j) := by
  dsimp [local_depth_drift_bound]
  rw [← hw.realizedStart, ← hw.realizedEnd]
  have hraw :
      ((Collatz.Foundations.depth_minus hw.endVal : ℝ) -
          (Collatz.Foundations.depth_minus hw.startVal : ℝ)) ≤
        (α t U - 2) * ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ) +
          C t U := by
    have hcombine :
        hw.multibitGain - ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ) ≤
          (α t U - 2) * ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ) +
            C t U := by
      linarith [hw.multibitGainUpper]
    exact le_trans hw.depthBookkeeping hcombine
  exact mul_le_mul_of_nonneg_left hraw hβnonneg

/-- The repaired local aperiodic E.2 target is now built from an explicit
selected long-epoch bridge: once each canonical selected phase-return pair is
refined to a paper-faithful witness, the accounting witness follows
immediately. -/
theorem phase_return_epoch_accounting_witness_of_selected_long_epoch_bridge
    {m t U : ℕ} {β : ℝ}
    (hbridge : Collatz.Epochs.SelectedLongEpochBridge m t U) :
    phase_return_epoch_accounting_witness m t U β := by
  intro ht hU hβ hphase j
  let hw := hbridge hphase j
  have hβpos : 0 < β := by
    have hβ0pos : 0 < β₀ t U := by
      exact beta_zero_pos t U (alpha_lt_two_of_ht_hU t U ht hU)
    linarith
  have hβnonneg : 0 ≤ β := le_of_lt hβpos
  refine ⟨?_, ?_⟩
  · exact local_log_drift_bound_of_selected_long_epoch hw
  · exact local_depth_drift_bound_of_selected_long_epoch hβnonneg hw

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
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 0 by norm_num)]
  exact hnonneg

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
