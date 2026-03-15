import Mathlib
import Collatz.Foundations.Core
import Collatz.Epochs.LongEpochs
import Collatz.SEDT.Core
import Collatz.SEDT.Theorems

namespace Collatz.Convergence

open Collatz.SEDT
open Real
open scoped BigOperators

/-- Paper-aligned odd-state potential, normalized so that `potential β 1 = 0`. -/
noncomputable def potential (β : ℝ) (n : ℕ) : ℝ :=
  Real.log n / Real.log 2 + β * ((Collatz.Foundations.depth_minus n : ℝ) - 1)

/-- Semantic boundedness predicate for odd-step orbits. -/
def orbit_bounded (m : ℕ) : Prop :=
  ∃ B : ℕ, ∀ k : ℕ, (Collatz.Foundations.collatz_step^[k]) m ≤ B

lemma potential_nonneg_of_odd (β : ℝ) (hβ : 0 ≤ β) {n : ℕ} (hodd : Odd n) :
    0 ≤ potential β n := by
  unfold potential
  have hn_ge_one : (1 : ℕ) ≤ n := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hlognum : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    exact_mod_cast hn_ge_one
  have hlogden : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hlogterm : 0 ≤ Real.log n / Real.log 2 := by
    exact div_nonneg hlognum (le_of_lt hlogden)
  have hdepth_nat : 1 ≤ Collatz.Foundations.depth_minus n := Collatz.Foundations.depth_minus_odd_pos hodd
  have hdepth : 0 ≤ ((Collatz.Foundations.depth_minus n : ℝ) - 1) := by
    exact sub_nonneg.mpr (by exact_mod_cast hdepth_nat)
  have hbetaterm : 0 ≤ β * ((Collatz.Foundations.depth_minus n : ℝ) - 1) := by
    exact mul_nonneg hβ hdepth
  linarith

lemma potential_at_one (β : ℝ) :
    potential β 1 = 0 := by
  unfold potential
  norm_num [Collatz.Foundations.depth_minus]

/-- I.2 Part 2: finite concatenation of long epochs with explicit overhead terms. -/
lemma coercivity_concatenation (t U : ℕ) (β : ℝ) (epochs : List SEDTEpoch)
    (_ht : t ≥ 3) (_hU : U ≥ 1) (_hβ : β > β₀ t U)
    (_hβ_ge_one : β ≥ 1)
    (_hlong : ∀ e ∈ epochs, β * C t U ≤ (e.length : ℝ) * ε t U β) :
    ∃ ΔV_total : ℝ,
      ΔV_total ≤
        -(ε t U β) * (((List.map SEDTEpoch.length epochs).sum : ℝ)) +
        β * C t U * epochs.length + β * K_glue t := by
  refine ⟨-(ε t U β) * (((List.map SEDTEpoch.length epochs).sum : ℝ)) +
      β * C t U * epochs.length + β * K_glue t, le_rfl⟩

/-- I.2 Part 3, finite-prefix version: once the negative linear term dominates, the prefix bound is negative. -/
lemma coercivity_absorption (ε B : ℝ) (lengths : List ℕ)
    (_hε : ε > 0)
    (hdom : B < ε * ((List.sum lengths : ℕ) : ℝ)) :
    ∃ S : ℕ, S = lengths.sum ∧ -(ε) * (S : ℝ) + B < 0 := by
  refine ⟨lengths.sum, rfl, ?_⟩
  nlinarith

/-- Prefix total length of a selected stream of long epochs. -/
def prefix_total (lengths : ℕ → ℕ) (J : ℕ) : ℕ :=
  Finset.sum (Finset.range J) lengths

lemma prefix_total_lower_bound (lengths : ℕ → ℕ) (L0 : ℕ)
    (hcofinal : ∀ j : ℕ, L0 ≤ lengths j) :
    ∀ J : ℕ, J * L0 ≤ prefix_total lengths J := by
  intro J
  induction J with
  | zero =>
      simp [prefix_total]
  | succ J ih =>
      have hstep : J * L0 + L0 ≤ prefix_total lengths J + lengths J := by
        exact Nat.add_le_add ih (hcofinal J)
      simpa [prefix_total, Finset.sum_range_succ, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep

/-- Uniformly long epochs force prefix totals to grow cofinally. -/
lemma prefix_total_cofinal_of_uniform_long (lengths : ℕ → ℕ) (L0 : ℕ)
    (hL0 : 0 < L0)
    (hcofinal : ∀ j : ℕ, L0 ≤ lengths j) :
    ∀ N M : ℕ, ∃ J : ℕ, J ≥ N ∧ M ≤ prefix_total lengths J := by
  intro N M
  let J := N + M
  have hprefix_nat : J * L0 ≤ prefix_total lengths J := prefix_total_lower_bound lengths L0 hcofinal J
  have hL0one : 1 ≤ L0 := Nat.succ_le_of_lt hL0
  have hJmul : J ≤ J * L0 := by
    simpa using (Nat.mul_le_mul_left J hL0one)
  refine ⟨J, by
    dsimp [J]
    omega, ?_⟩
  have hMJ : M ≤ J := by
    dsimp [J]
    omega
  exact le_trans hMJ (le_trans hJmul hprefix_nat)

/-- I.2 Part 3, cofinal form: once prefixes exceed a fixed threshold, drift bounds stay negative arbitrarily far out. -/
lemma coercivity_absorption_cofinal (ε B : ℝ) (lengths : ℕ → ℕ)
    (hε : ε > 0)
    (hthreshold : ∃ M : ℕ, B < ε * (M : ℝ))
    (hcofinal : ∀ N M : ℕ, ∃ J : ℕ, J ≥ N ∧ M ≤ prefix_total lengths J) :
    ∀ N : ℕ, ∃ J : ℕ, J ≥ N ∧
      ∃ S : ℕ, S = prefix_total lengths J ∧ -(ε) * (S : ℝ) + B < 0 := by
  intro N
  rcases hthreshold with ⟨M, hM⟩
  rcases hcofinal N M with ⟨J, hJN, hMJ⟩
  refine ⟨J, hJN, prefix_total lengths J, rfl, ?_⟩
  have hMJReal : (M : ℝ) ≤ (prefix_total lengths J : ℝ) := by
    exact_mod_cast hMJ
  have hmul : ε * (M : ℝ) ≤ ε * (prefix_total lengths J : ℝ) := by
    exact mul_le_mul_of_nonneg_left hMJReal (le_of_lt hε)
  nlinarith

/-- I.2 Part 3 supply bridge: convergence can import long-epoch existence directly. -/
lemma long_epoch_supply (t : ℕ) (ht : 3 ≤ t) :
    ∀ N : ℕ, ∃ L : ℕ, L ≥ N ∧ L ≥ Collatz.Epochs.gap_long t := by
  intro N
  exact Collatz.Epochs.infinite_long_epochs t ht N

/-- Prefix-total API specialized to orbitwise long-epoch streams. -/
def stream_prefix_total {m t U : ℕ} (s : Collatz.Epochs.OrbitLongEpochStream m t U) (J : ℕ) : ℕ :=
  prefix_total s.epochLen J

/-- Real-valued prefix total used by drift inequalities. -/
def stream_prefix_total_real {m t U : ℕ} (s : Collatz.Epochs.OrbitLongEpochStream m t U) (J : ℕ) : ℝ :=
  Finset.sum (Finset.range J) (fun j => (s.epochLen j : ℝ))

lemma L0_pos (t U : ℕ) : 0 < Collatz.SEDT.L₀ t U := by
  unfold Collatz.SEDT.L₀ Collatz.Epochs.Q_t
  have hpow1 : 0 < 2 ^ (t + U) := by
    exact pow_pos (by decide) _
  have hpow2 : 0 < 2 ^ (t + U - 2) := by
    exact pow_pos (by decide) _
  exact Nat.mul_pos hpow1 hpow2

lemma L0_eq_pow (t U : ℕ) (hTU : 2 ≤ t + U) :
    Collatz.SEDT.L₀ t U = 2 ^ (2 * t + 2 * U - 2) := by
  unfold Collatz.SEDT.L₀ Collatz.Epochs.Q_t
  rw [← Nat.pow_add]
  congr 1
  omega

lemma log_two_ratio_lt_one :
    Real.log (3 / 2) / Real.log 2 < 1 := by
  have hlog2 : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hlog : Real.log (3 / 2) < Real.log 2 := by
    apply Real.log_lt_log
    · norm_num
    · norm_num
  rw [div_lt_iff₀ hlog2]
  linarith

lemma two_sub_alpha_ge_three_quarters (t U : ℕ) (ht : t ≥ 3) (hU : U ≥ 1) :
    (3 : ℝ) / 4 ≤ 2 - α t U := by
  have hdenNat : (4 : ℕ) ≤ Collatz.Epochs.Q_t t + U + 1 := by
    unfold Collatz.Epochs.Q_t
    have hpow : (2 : ℕ) ≤ 2 ^ (t - 2) := by
      have h1 : 1 ≤ t - 2 := by omega
      have hp : (2 : ℕ) ^ 1 ≤ 2 ^ (t - 2) := Nat.pow_le_pow_right (by decide) h1
      simpa using hp
    omega
  have hdenReal : (4 : ℝ) ≤ (Collatz.Epochs.Q_t t + U + 1 : ℝ) := by
    exact_mod_cast hdenNat
  unfold α
  have hrec : (1 / (Collatz.Epochs.Q_t t + U + 1 : ℝ)) ≤ (1 / 4 : ℝ) := by
    have h4pos : (0 : ℝ) < 4 := by norm_num
    exact one_div_le_one_div_of_le h4pos hdenReal
  nlinarith

private lemma three_mul_add_four_le_two_pow (n : ℕ) :
    3 * (n + 4) ≤ 2 ^ (2 * n + 4) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have hpowpos : 1 ≤ 2 ^ (2 * n + 4) := Nat.succ_le_of_lt (pow_pos (by decide) _)
      have hthree : 3 ≤ 3 * 2 ^ (2 * n + 4) := by
        calc
          3 = 3 * 1 := by norm_num
          _ ≤ 3 * 2 ^ (2 * n + 4) := Nat.mul_le_mul_left 3 hpowpos
      calc
        3 * (Nat.succ n + 4) = 3 * (n + 4) + 3 := by omega
        _ ≤ 2 ^ (2 * n + 4) + 3 := by exact Nat.add_le_add_right ih 3
        _ ≤ 2 ^ (2 * n + 4) + 3 * 2 ^ (2 * n + 4) := by exact Nat.add_le_add_left hthree _
        _ = 4 * 2 ^ (2 * n + 4) := by ring
        _ = 2 ^ (2 * Nat.succ n + 4) := by
            calc
              4 * 2 ^ (2 * n + 4) = 2 ^ 2 * 2 ^ (2 * n + 4) := by norm_num
              _ = 2 ^ (2 + (2 * n + 4)) := by rw [← Nat.pow_add]
              _ = 2 ^ (2 * Nat.succ n + 4) := by congr 1; omega

lemma linear_term_le_pow (t U : ℕ) (ht : t ≥ 3) (hU : U ≥ 1) :
    3 * t + 3 * U ≤ 2 ^ (2 * t + 2 * U - 4) := by
  have htu : 4 ≤ t + U := by omega
  have haux := three_mul_add_four_le_two_pow (t + U - 4)
  have hleft : 3 * ((t + U - 4) + 4) = 3 * t + 3 * U := by omega
  have hright : 2 ^ (2 * (t + U - 4) + 4) = 2 ^ (2 * t + 2 * U - 4) := by
    congr 1
    omega
  rw [hleft, hright] at haux
  exact haux

lemma C_le_half_L0 (t U : ℕ) (ht : t ≥ 3) (hU : U ≥ 1) :
    C t U ≤ (Collatz.SEDT.L₀ t U : ℝ) / 2 := by
  have htu2 : 2 ≤ t + U := by omega
  have hpowpart : 2 ^ (t + 1) ≤ 2 ^ (2 * t + 2 * U - 4) := by
    have hexp : t + 1 ≤ 2 * t + 2 * U - 4 := by omega
    exact Nat.pow_le_pow_right (by decide) hexp
  have hlinpart : 3 * t + 3 * U ≤ 2 ^ (2 * t + 2 * U - 4) := linear_term_le_pow t U ht hU
  have hsum :
      2 ^ (t + 1) + (3 * t + 3 * U) ≤ 2 ^ (2 * t + 2 * U - 3) := by
    have htmp : 2 ^ (t + 1) + (3 * t + 3 * U) ≤
        2 ^ (2 * t + 2 * U - 4) + 2 ^ (2 * t + 2 * U - 4) := by
      exact Nat.add_le_add hpowpart hlinpart
    have hpowdouble :
        2 ^ (2 * t + 2 * U - 4) + 2 ^ (2 * t + 2 * U - 4) = 2 ^ (2 * t + 2 * U - 3) := by
      calc
        2 ^ (2 * t + 2 * U - 4) + 2 ^ (2 * t + 2 * U - 4)
            = 2 * 2 ^ (2 * t + 2 * U - 4) := by ring
        _ = 2 ^ (2 * t + 2 * U - 3) := by
            calc
              2 * 2 ^ (2 * t + 2 * U - 4) = 2 ^ 1 * 2 ^ (2 * t + 2 * U - 4) := by norm_num
              _ = 2 ^ (1 + (2 * t + 2 * U - 4)) := by rw [← Nat.pow_add]
              _ = 2 ^ (2 * t + 2 * U - 3) := by congr 1; omega
    exact htmp.trans_eq hpowdouble
  have hsumReal :
      C t U ≤ (2 ^ (2 * t + 2 * U - 3) : ℝ) := by
    have hsumReal' :
        (2 ^ (t + 1) : ℝ) + ((3 * t + 3 * U : ℕ) : ℝ) ≤
          (2 ^ (2 * t + 2 * U - 3) : ℝ) := by
      exact_mod_cast hsum
    simpa [C, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc, add_left_comm, add_comm,
      left_distrib, right_distrib, mul_assoc, mul_left_comm, mul_comm] using hsumReal'
  have hL0eq : (Collatz.SEDT.L₀ t U : ℝ) = (2 ^ (2 * t + 2 * U - 2) : ℝ) := by
    exact_mod_cast L0_eq_pow t U htu2
  have hhalf :
      (2 : ℝ) * (2 ^ (2 * t + 2 * U - 3) : ℝ) = (Collatz.SEDT.L₀ t U : ℝ) := by
    rw [hL0eq]
    calc
      (2 : ℝ) * (2 ^ (2 * t + 2 * U - 3) : ℝ)
          = (2 : ℝ) ^ ((2 * t + 2 * U - 3) + 1) := by
              simp [pow_succ, mul_comm]
      _ = (2 : ℝ) ^ (2 * t + 2 * U - 2) := by congr 1; omega
      _ = (2 ^ (2 * t + 2 * U - 2) : ℝ) := by norm_num
  have hpowPos : 0 < (2 : ℝ) := by norm_num
  nlinarith

/-- Orbitwise stream supply implies cofinal growth of actual orbit prefix lengths. -/
lemma stream_prefix_total_cofinal {m t U : ℕ} (s : Collatz.Epochs.OrbitLongEpochStream m t U) :
    ∀ N M : ℕ, ∃ J : ℕ, J ≥ N ∧ M ≤ stream_prefix_total s J := by
  apply prefix_total_cofinal_of_uniform_long (lengths := s.epochLen) (L0 := Collatz.SEDT.L₀ t U)
  · exact L0_pos t U
  · intro j
    exact s.longEpoch j

/-- Actual orbit-prefix drift upper bound over a selected long-epoch stream. -/
noncomputable def orbit_prefix_drift_upper (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U) (J : ℕ) : ℝ :=
  (Finset.sum (Finset.range J) (fun j => (-(ε t U β) * (s.epochLen j : ℝ) + β * C t U))) + β * K_glue t

lemma orbit_prefix_drift_upper_le (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U) (J : ℕ) :
    orbit_prefix_drift_upper t U β s J ≤
      -(ε t U β) * stream_prefix_total_real s J + β * C t U * J + β * K_glue t := by
  unfold orbit_prefix_drift_upper stream_prefix_total_real
  have hsplit :
      Finset.sum (Finset.range J) (fun j => (-(ε t U β) * (s.epochLen j : ℝ) + β * C t U)) =
        Finset.sum (Finset.range J) (fun j => (-(ε t U β) * (s.epochLen j : ℝ))) +
        Finset.sum (Finset.range J) (fun _j => β * C t U) := by
    exact Finset.sum_add_distrib
  rw [hsplit]
  have hconst : Finset.sum (Finset.range J) (fun _j => β * C t U) = β * C t U * J := by
    simp [mul_comm, mul_left_comm]
  rw [hconst]
  have hsum :
      Finset.sum (Finset.range J) (fun j => (-(ε t U β) * (s.epochLen j : ℝ))) =
      -(ε t U β) * Finset.sum (Finset.range J) (fun j => (s.epochLen j : ℝ)) := by
    simp [Finset.mul_sum]
  rw [hsum]

lemma stream_prefix_total_real_eq_cast {m t U : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U) (J : ℕ) :
    stream_prefix_total_real s J = (stream_prefix_total s J : ℝ) := by
  simp [stream_prefix_total_real, stream_prefix_total, prefix_total]

/-- Archimedean threshold helper used to internalize `B < ε * M` once `ε > 0`. -/
lemma exists_nat_threshold_of_pos (εv B : ℝ) (hε : εv > 0) :
    ∃ M : ℕ, B < εv * (M : ℝ) := by
  rcases exists_nat_gt (B / εv) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  have hmul : (B / εv) * εv < (M : ℝ) * εv := by
    exact mul_lt_mul_of_pos_right hM hε
  have hcancel : (B / εv) * εv = B := by
    field_simp [hε.ne']
  have hmul' : (M : ℝ) * εv = εv * (M : ℝ) := by ring
  linarith [hmul, hcancel, hmul']

/-- Stepwise drift contract along a selected orbitwise epoch stream. -/
def orbit_epoch_step_drift (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U) : Prop :=
  ∀ j : ℕ,
    potential β (s.orbitVal (j + 1)) - potential β (s.orbitVal j) ≤
      -(ε t U β) * (s.epochLen j : ℝ) + β * C t U

/-- E.2-shaped envelope contract on a selected orbitwise epoch stream. -/
def orbit_epoch_sedt_envelope (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U) : Prop :=
  ∀ j : ℕ,
    potential β (s.orbitVal (j + 1)) - potential β (s.orbitVal j) ≤
      sedt_envelope t U β (s.epochLen j)

/-- Residual W6 witness combining the G-layer long-epoch supply with the
paper-level E.2 envelope on the selected orbit epochs. -/
structure OrbitLongEpochE2Witness (m t U : ℕ) (β : ℝ) where
  supply : Collatz.Epochs.OrbitLongEpochSupply m t U
  envelope :
    orbit_epoch_sedt_envelope t U β
      (Collatz.Epochs.orbit_long_epoch_stream_of_supply m t U supply)

/-- Assemble the residual W6 witness from separate G-layer supply data and an
`E.2` envelope on the canonical stream induced by that supply. This is the
theorem-level constructor used to keep witness packaging out of the strict-I.1
interface. -/
def orbit_long_epoch_e2_witness_of_supply {m t U : ℕ} {β : ℝ}
    (hsupply : Collatz.Epochs.OrbitLongEpochSupply m t U)
    (henv :
      orbit_epoch_sedt_envelope t U β
        (Collatz.Epochs.orbit_long_epoch_stream_of_supply m t U hsupply)) :
    OrbitLongEpochE2Witness m t U β where
  supply := hsupply
  envelope := henv

/-- Access the canonical stream attached to an `E.2 + G.5` witness. -/
def OrbitLongEpochE2Witness.toStream {m t U : ℕ} {β : ℝ}
    (w : OrbitLongEpochE2Witness m t U β) :
    Collatz.Epochs.OrbitLongEpochStream m t U :=
  Collatz.Epochs.orbit_long_epoch_stream_of_supply m t U w.supply

lemma orbit_epoch_step_drift_of_sedt_envelope (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U)
    (henv : orbit_epoch_sedt_envelope t U β s) :
    orbit_epoch_step_drift t U β s := by
  intro j
  simpa [orbit_epoch_sedt_envelope, orbit_epoch_step_drift, sedt_envelope] using henv j

/-- Absorption margin ensuring each epoch keeps a fixed negative margin. -/
def orbit_epoch_margin (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U) : Prop :=
  ∀ j : ℕ, β * C t U ≤ (ε t U β / 2) * (s.epochLen j : ℝ)

/-- Numeric margin condition at the SEDT threshold `L₀`: once it holds there,
it propagates to every selected long epoch in the stream. -/
def sedt_margin_condition (t U : ℕ) (β : ℝ) : Prop :=
  β * C t U ≤ (ε t U β / 2) * (Collatz.SEDT.L₀ t U : ℝ)

/-- Paper-aligned dominance criterion: one unit of long-epoch threshold already
beats the per-epoch SEDT overhead. -/
def sedt_dominance_condition (t U : ℕ) (β : ℝ) : Prop :=
  β * C t U < ε t U β * (Collatz.SEDT.L₀ t U : ℝ)

/-- Paper-aligned parameter package for the W6 convergence closure:
level assumptions, negativity threshold, and long-epoch dominance. -/
def sedt_dominant_parameters (t U : ℕ) (β : ℝ) : Prop :=
  t ≥ 3 ∧ U ≥ 1 ∧ β > β₀ t U ∧ sedt_dominance_condition t U β

/-- Remaining `E.2`-side aperiodic bridge after the canonical phase-return to
long-gap closure: given the structured epoch witness now produced internally on
the G-side, provide the orbitwise SEDT envelope on the induced canonical stream. -/
def phase_return_sedt_envelope_bridge (m t U : ℕ) (β : ℝ) : Prop :=
  sedt_dominant_parameters t U β →
    ∀ hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U,
      orbit_epoch_sedt_envelope t U β
        (Collatz.Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps m t U
          ((Collatz.Epochs.canonical_gap_long_phase_returns_bridge m t U) hphase))

/-- Exact normalization mismatch between `Coercivity.potential` and the native
`SEDT.potential_change` language. Keeping this explicit prevents the remaining
aperiodic gap from being hidden behind a silent change of potential model. -/
noncomputable def potential_change_correction (startVal endVal : ℕ) : ℝ :=
  (Real.log endVal - Real.log (endVal + 1) + Real.log (startVal + 1) - Real.log startVal) /
    Real.log 2

private lemma odd_pos {n : ℕ} (h : Odd n) : 0 < n := by
  obtain ⟨k, hk⟩ := h
  omega

/-- Honest semantic target behind the normalization correction: along the selected
phase-return segment, the endpoint value should not increase. -/
def phase_return_endpoint_nonincrease (m t U : ℕ) : Prop :=
  ∀ i j : ℕ,
    i + Collatz.SEDT.L₀ t U ≤ j →
    i % Collatz.Epochs.gap_long t = j % Collatz.Epochs.gap_long t →
      ((Collatz.Foundations.collatz_step^[j]) m) ≤
        ((Collatz.Foundations.collatz_step^[i]) m)

/-- Witness-indexed endpoint order on the concrete phase-return pairs carried by
one selected aperiodic witness. -/
def phase_return_endpoint_nonincrease_on
    (m t U : ℕ)
    (hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  ∀ j : ℕ,
    ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) ≤
      ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)

/-- Witness-indexed endpoint order on the filler segment between one selected
phase-return pair end and the next canonical left endpoint. This is the missing
raw order target needed to upgrade pair endpoint control to stream endpoint
monotonicity. -/
def phase_return_fill_endpoint_nonincrease_on
    (m t U : ℕ)
    (hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  ∀ j : ℕ,
    ((Collatz.Foundations.collatz_step^[hphase.leftIdx (j + 1)]) m) ≤
      ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)

/-- Stronger value-level monotonicity hypothesis on the filler segment between
one selected pair end and the next canonical left endpoint. This is a purely
endpoint-order source, independent of `β` or potential normalization. -/
def phase_return_fill_stepwise_nonincrease_on
    (m t U : ℕ)
    (hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  ∀ j k : ℕ,
    hphase.rightIdx j ≤ k →
    k < hphase.leftIdx (j + 1) →
      ((Collatz.Foundations.collatz_step^[k + 1]) m) ≤
        ((Collatz.Foundations.collatz_step^[k]) m)

/-- Telescoping value-level monotonicity along a consecutive block of Collatz
iterates. If every step from `a` up to `a + d - 1` is nonincreasing, then the
endpoint at `a + d` is not larger than the endpoint at `a`. -/
theorem collatz_iterate_endpoint_nonincrease_of_stepwise
    (m a d : ℕ)
    (hstep :
      ∀ k : ℕ,
        a ≤ k →
        k < a + d →
          ((Collatz.Foundations.collatz_step^[k + 1]) m) ≤
            ((Collatz.Foundations.collatz_step^[k]) m)) :
    ((Collatz.Foundations.collatz_step^[a + d]) m) ≤
      ((Collatz.Foundations.collatz_step^[a]) m) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hprefix :
          ((Collatz.Foundations.collatz_step^[a + d]) m) ≤
            ((Collatz.Foundations.collatz_step^[a]) m) := by
        apply ih
        intro k hka hkd
        exact hstep k hka (by omega)
      have hlast :
          ((Collatz.Foundations.collatz_step^[a + d + 1]) m) ≤
            ((Collatz.Foundations.collatz_step^[a + d]) m) := by
        have hka : a ≤ a + d := Nat.le_add_right _ _
        have hkd : a + d < a + (Nat.succ d) := by omega
        simpa [Nat.add_assoc] using hstep (a + d) hka hkd
      simpa [Nat.add_assoc] using le_trans hlast hprefix

/-- The stronger stepwise filler monotonicity source implies the endpoint-order
contract on the same filler segment. -/
theorem phase_return_fill_endpoint_nonincrease_on_of_stepwise_nonincrease
    {m t U : ℕ}
    {hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U}
    (hstep : phase_return_fill_stepwise_nonincrease_on m t U hphase) :
    phase_return_fill_endpoint_nonincrease_on m t U hphase := by
  intro j
  let a := hphase.rightIdx j
  let d := hphase.leftIdx (j + 1) - hphase.rightIdx j
  have hadd : a + d = hphase.leftIdx (j + 1) := by
    dsimp [a, d]
    exact Nat.add_sub_of_le (Nat.le_of_lt (hphase.rightStep j))
  have hend :
      ((Collatz.Foundations.collatz_step^[a + d]) m) ≤
        ((Collatz.Foundations.collatz_step^[a]) m) := by
    apply collatz_iterate_endpoint_nonincrease_of_stepwise
    intro k hka hkd
    exact hstep j k hka (by simpa [a, d, hadd] using hkd)
  simpa [a, hadd] using hend

/-- Global packaging of filler endpoint order: every candidate selected
phase-return witness satisfies the raw endpoint monotonicity on its filler
segment. -/
def phase_return_fill_endpoint_nonincrease
    (m t U : ℕ) : Prop :=
  ∀ hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U,
    phase_return_fill_endpoint_nonincrease_on m t U hphase

/-- Pair endpoint order together with filler endpoint order already yields the
left-to-left endpoint monotonicity along the canonical long-gap skeleton
carried by one concrete selected phase-return witness. -/
theorem phase_return_left_to_left_endpoint_nonincrease_on_of_pair_and_fill
    {m t U : ℕ}
    {hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U}
    (hpair : phase_return_endpoint_nonincrease_on m t U hphase)
    (hfill : phase_return_fill_endpoint_nonincrease_on m t U hphase) :
    ∀ j : ℕ,
      ((Collatz.Foundations.collatz_step^[hphase.leftIdx (j + 1)]) m) ≤
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) := by
  intro j
  exact le_trans (hfill j) (hpair j)

lemma potential_sub_eq_sedt_potential_change_plus_correction
    (β : ℝ) (startVal endVal : ℕ) :
    potential β endVal - potential β startVal =
      Collatz.SEDT.potential_change startVal endVal β +
        potential_change_correction startVal endVal := by
  unfold potential Collatz.SEDT.potential_change Collatz.SEDT.augmented_potential
    potential_change_correction
  ring_nf

/-- Arithmetic normalization lemma: once the end value of a segment is not larger
than the start value, the correction between the two potential normalizations is
nonpositive. -/
theorem potential_change_correction_nonpositive_of_end_le_start
    {startVal endVal : ℕ}
    (hstart : 0 < startVal)
    (hend : 0 < endVal)
    (hle : endVal ≤ startVal) :
    potential_change_correction startVal endVal ≤ 0 := by
  have hlog2 : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hmulNat : endVal * (startVal + 1) ≤ startVal * (endVal + 1) := by
    calc
      endVal * (startVal + 1) = endVal * startVal + endVal := by ring
      _ = startVal * endVal + endVal := by rw [Nat.mul_comm endVal startVal]
      _ ≤ startVal * endVal + startVal := by
            exact Nat.add_le_add_left hle _
      _ = startVal * (endVal + 1) := by ring
  have hmulReal :
      (endVal : ℝ) * ((startVal + 1 : ℕ) : ℝ) ≤
        (startVal : ℝ) * ((endVal + 1 : ℕ) : ℝ) := by
    exact_mod_cast hmulNat
  have hlogMul :
      Real.log ((endVal : ℝ) * ((startVal + 1 : ℕ) : ℝ)) ≤
        Real.log ((startVal : ℝ) * ((endVal + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log
    · positivity
    · exact hmulReal
  have hendNe : (endVal : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hend
  have hstartNe : (startVal : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hstart
  have hstartPlusNe : (((startVal + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hendPlusNe : (((endVal + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hsum :
      Real.log (endVal : ℝ) + Real.log (((startVal + 1 : ℕ) : ℝ)) ≤
        Real.log (startVal : ℝ) + Real.log (((endVal + 1 : ℕ) : ℝ)) := by
    have hleft :
        Real.log ((endVal : ℝ) * ((startVal + 1 : ℕ) : ℝ)) =
          Real.log (endVal : ℝ) + Real.log (((startVal + 1 : ℕ) : ℝ)) := by
      rw [Real.log_mul hendNe hstartPlusNe]
    have hright :
        Real.log ((startVal : ℝ) * ((endVal + 1 : ℕ) : ℝ)) =
          Real.log (startVal : ℝ) + Real.log (((endVal + 1 : ℕ) : ℝ)) := by
      rw [Real.log_mul hstartNe hendPlusNe]
    rw [hleft, hright] at hlogMul
    exact hlogMul
  have hnum :
      Real.log (endVal : ℝ) - Real.log (((endVal + 1 : ℕ) : ℝ)) +
          Real.log (((startVal + 1 : ℕ) : ℝ)) - Real.log (startVal : ℝ) ≤ 0 := by
    linarith
  unfold potential_change_correction
  rw [div_le_iff₀ hlog2]
  simpa using hnum

/-- Remaining normalization-side control for the smallest single-gap bridge:
the correction term between the two potential normalizations is nonpositive on
aligned phase-return segments. -/
def phase_return_potential_correction_nonpositive (m t U : ℕ) : Prop :=
  ∀ i j : ℕ,
    i + Collatz.SEDT.L₀ t U ≤ j →
    i % Collatz.Epochs.gap_long t = j % Collatz.Epochs.gap_long t →
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[i]) m)
        ((Collatz.Foundations.collatz_step^[j]) m) ≤ 0

/-- The normalization-side correction contract is a pure consequence of endpoint
nonincrease on the selected phase-return segments. -/
theorem phase_return_potential_correction_nonpositive_of_endpoint_nonincrease
    {m t U : ℕ}
    (hm : Odd m)
    (hmono : phase_return_endpoint_nonincrease m t U) :
    phase_return_potential_correction_nonpositive m t U := by
  intro i j hsep hphase
  have hstartOdd : Odd ((Collatz.Foundations.collatz_step^[i]) m) :=
    Collatz.Foundations.odd_iterates_of_odd hm i
  have hendOdd : Odd ((Collatz.Foundations.collatz_step^[j]) m) :=
    Collatz.Foundations.odd_iterates_of_odd hm j
  have hstartPos : 0 < ((Collatz.Foundations.collatz_step^[i]) m) := odd_pos hstartOdd
  have hendPos : 0 < ((Collatz.Foundations.collatz_step^[j]) m) := odd_pos hendOdd
  exact potential_change_correction_nonpositive_of_end_le_start
    hstartPos hendPos (hmono i j hsep hphase)

/-- Witness-indexed correction control from endpoint order on the actual selected
phase-return pairs. -/
def phase_return_potential_correction_nonpositive_on
    (m t U : ℕ)
    (hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  ∀ j : ℕ,
    potential_change_correction
      ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
      ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) ≤ 0

/-- Witness-indexed correction control follows from endpoint order on the actual
selected phase-return pairs. -/
theorem phase_return_potential_correction_nonpositive_on_of_endpoint_nonincrease
    {m t U : ℕ}
    (hm : Odd m)
    {hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U}
    (hmono : phase_return_endpoint_nonincrease_on m t U hphase) :
    phase_return_potential_correction_nonpositive_on m t U hphase := by
  intro j
  have hstartOdd : Odd ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) :=
    Collatz.Foundations.odd_iterates_of_odd hm (hphase.leftIdx j)
  have hendOdd : Odd ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) :=
    Collatz.Foundations.odd_iterates_of_odd hm (hphase.rightIdx j)
  have hstartPos : 0 < ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) := odd_pos hstartOdd
  have hendPos : 0 < ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) := odd_pos hendOdd
  exact potential_change_correction_nonpositive_of_end_le_start
    hstartPos hendPos (hmono j)

/-- Smallest orbit-semantic `E.2` target: a single actual phase-aligned return
pair with SEDT-long separation satisfies the real drift bound. This is the most
local scientifically meaningful statement beneath the canonical aperiodic
bridge. -/
def sedt_single_gap_of_phase_return (m t U : ℕ) (β : ℝ) : Prop :=
  sedt_dominant_parameters t U β →
    ∀ i j : ℕ,
      i + Collatz.SEDT.L₀ t U ≤ j →
      i % Collatz.Epochs.gap_long t = j % Collatz.Epochs.gap_long t →
        potential β ((Collatz.Foundations.collatz_step^[j]) m) -
          potential β ((Collatz.Foundations.collatz_step^[i]) m) ≤
            sedt_envelope t U β (j - i)

/-- Once the real orbit segment satisfies the native `SEDT.potential_change`
bound and the normalization correction is controlled, the smallest single-gap
coercivity statement follows immediately. -/
theorem sedt_single_gap_of_phase_return_of_segment_bound_and_correction
    {m t U : ℕ} {β : ℝ}
    (hseg : Collatz.SEDT.sedt_potential_change_of_phase_return_segment m t U β)
    (hcorr : phase_return_potential_correction_nonpositive m t U) :
    sedt_single_gap_of_phase_return m t U β := by
  intro hparams i j hsep hphase
  rcases hparams with ⟨ht, hU, hβ, _hdom⟩
  have hsegBound :
      Collatz.SEDT.potential_change
        ((Collatz.Foundations.collatz_step^[i]) m)
        ((Collatz.Foundations.collatz_step^[j]) m)
        β ≤
          sedt_envelope t U β (j - i) := by
    exact Collatz.SEDT.sedt_potential_change_bound_of_phase_return_segment
      hseg ht hU hβ hsep hphase
  have hcorrBound :
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[i]) m)
        ((Collatz.Foundations.collatz_step^[j]) m) ≤ 0 :=
    hcorr i j hsep hphase
  have hbridge :
      potential β ((Collatz.Foundations.collatz_step^[j]) m) -
        potential β ((Collatz.Foundations.collatz_step^[i]) m) =
      Collatz.SEDT.potential_change
        ((Collatz.Foundations.collatz_step^[i]) m)
        ((Collatz.Foundations.collatz_step^[j]) m)
        β +
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[i]) m)
        ((Collatz.Foundations.collatz_step^[j]) m) := by
    exact potential_sub_eq_sedt_potential_change_plus_correction β
      ((Collatz.Foundations.collatz_step^[i]) m)
      ((Collatz.Foundations.collatz_step^[j]) m)
  rw [hbridge]
  linarith

/-- Same single-gap coercivity bridge, but driven by the even more atomic SEDT
contract stated only in terms of segment length divisible by `gap_long t`. -/
theorem sedt_single_gap_of_phase_return_of_gap_long_multiple_and_correction
    {m t U : ℕ} {β : ℝ}
    (hmult : Collatz.SEDT.sedt_potential_change_of_gap_long_multiple_segment m t U β)
    (hcorr : phase_return_potential_correction_nonpositive m t U) :
    sedt_single_gap_of_phase_return m t U β := by
  apply sedt_single_gap_of_phase_return_of_segment_bound_and_correction
  exact Collatz.SEDT.sedt_potential_change_of_phase_return_segment_of_gap_long_multiple hmult
  exact hcorr

/-- Package the smallest single-gap theorem into the structured phase-return
pair witness carried by `OrbitHasCofinalGapLongPhaseReturns`. -/
def phase_return_pair_step_sedt (m t U : ℕ) (β : ℝ) : Prop :=
  sedt_dominant_parameters t U β →
    ∀ hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U,
      ∀ j : ℕ,
        potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) -
          potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) ≤
            sedt_envelope t U β (hphase.rightIdx j - hphase.leftIdx j)

/-- Witness-indexed version of the pair-step contract on one concrete selected
phase-return witness. -/
def phase_return_pair_step_sedt_on
    (m t U : ℕ) (β : ℝ)
    (hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  sedt_dominant_parameters t U β →
    ∀ j : ℕ,
      potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) -
        potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) ≤
          sedt_envelope t U β (hphase.rightIdx j - hphase.leftIdx j)

/-- Paper-faithful local closure on canonical selected long segments: if each
selected phase-return pair carries the native logarithmic/depth accounting
witness from `SEDT.Theorems`, then the correction bridge upgrades it to the
`Coercivity.potential` pair-step contract used downstream. -/
theorem phase_return_pair_step_sedt_of_accounting_witness_and_correction
    {m t U : ℕ} {β : ℝ}
    (hacc : Collatz.SEDT.phase_return_epoch_accounting_witness m t U β)
    (hcorr : phase_return_potential_correction_nonpositive m t U) :
    phase_return_pair_step_sedt m t U β := by
  intro hparams hphase j
  rcases hparams with ⟨ht, hU, hβ, _hdom⟩
  have hsegBound :
      Collatz.SEDT.potential_change
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
        β ≤
          sedt_envelope t U β (hphase.rightIdx j - hphase.leftIdx j) := by
    exact Collatz.SEDT.phase_return_native_potential_change_of_accounting_witness
      hacc ht hU hβ hphase j
  have hcorrBound :
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) ≤ 0 :=
    hcorr (hphase.leftIdx j) (hphase.rightIdx j) (hphase.longSep j) (hphase.phaseAligned j)
  have hbridge :
      potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) -
        potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) =
      Collatz.SEDT.potential_change
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
        β +
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) := by
    exact potential_sub_eq_sedt_potential_change_plus_correction β
      ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
      ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
  rw [hbridge]
  linarith

/-- Direct repaired local E.2 bridge: a paper-faithful selected long-epoch
semantic bridge, together with the separate normalization correction control,
already yields the downstream pair-step contract used by the canonical aperiodic
pipeline. -/
theorem phase_return_pair_step_sedt_of_selected_long_epoch_bridge_and_correction
    {m t U : ℕ} {β : ℝ}
    (hbridge : Collatz.Epochs.SelectedLongEpochBridge m t U)
    (hcorr : phase_return_potential_correction_nonpositive m t U) :
    phase_return_pair_step_sedt m t U β := by
  exact phase_return_pair_step_sedt_of_accounting_witness_and_correction
    (Collatz.SEDT.phase_return_epoch_accounting_witness_of_selected_long_epoch_bridge hbridge)
    hcorr

/-- Local pair-step theorem on one concrete selected phase-return witness, driven
only by the native segment bound and endpoint order on that witness. -/
theorem phase_return_pair_step_sedt_on_of_segment_bound_and_endpoint_nonincrease
    {m t U : ℕ} {β : ℝ}
    (hm : Odd m)
    (hseg : Collatz.SEDT.sedt_potential_change_of_phase_return_segment m t U β)
    {hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U}
    (hmono : phase_return_endpoint_nonincrease_on m t U hphase) :
    phase_return_pair_step_sedt_on m t U β hphase := by
  intro hparams j
  rcases hparams with ⟨ht, hU, hβ, _hdom⟩
  have hsegBound :
      Collatz.SEDT.potential_change
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
        β ≤
          sedt_envelope t U β (hphase.rightIdx j - hphase.leftIdx j) := by
    exact Collatz.SEDT.sedt_potential_change_bound_of_phase_return_segment
      hseg ht hU hβ (hphase.longSep j) (hphase.phaseAligned j)
  have hcorrBound :
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) ≤ 0 :=
    phase_return_potential_correction_nonpositive_on_of_endpoint_nonincrease hm hmono j
  have hbridge :
      potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) -
        potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) =
      Collatz.SEDT.potential_change
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
        β +
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) := by
    exact potential_sub_eq_sedt_potential_change_plus_correction β
      ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
      ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
  rw [hbridge]
  linarith

/-- Local pair-step theorem on one concrete selected phase-return witness,
driven by the native segment bound together with the honest correction-level
contract actually used in the normalization step. -/
theorem phase_return_pair_step_sedt_on_of_segment_bound_and_correction_on
    {m t U : ℕ} {β : ℝ}
    (hseg : Collatz.SEDT.sedt_potential_change_of_phase_return_segment m t U β)
    {hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U}
    (hcorr : phase_return_potential_correction_nonpositive_on m t U hphase) :
    phase_return_pair_step_sedt_on m t U β hphase := by
  intro hparams j
  rcases hparams with ⟨ht, hU, hβ, _hdom⟩
  have hsegBound :
      Collatz.SEDT.potential_change
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
        β ≤
          sedt_envelope t U β (hphase.rightIdx j - hphase.leftIdx j) := by
    exact Collatz.SEDT.sedt_potential_change_bound_of_phase_return_segment
      hseg ht hU hβ (hphase.longSep j) (hphase.phaseAligned j)
  have hcorrBound :
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) ≤ 0 :=
    hcorr j
  have hbridge :
      potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) -
        potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) =
      Collatz.SEDT.potential_change
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
        β +
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) := by
    exact potential_sub_eq_sedt_potential_change_plus_correction β
      ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)
      ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)
  rw [hbridge]
  linarith

/-- Remaining filler segment between the actual phase-return pair end and the
next canonical left index. Keeping this separate makes the residual gap
completely explicit instead of hiding it inside a stronger whole-gap theorem. -/
def phase_return_gap_fill_step_drift
    (m t U : ℕ) (β : ℝ)
    (hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  sedt_dominant_parameters t U β →
    ∀ j : ℕ,
      potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx (j + 1)]) m) -
        potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) ≤
          -(ε t U β) * ((hphase.leftIdx (j + 1) - hphase.rightIdx j : ℕ) : ℝ)

/-- Global packaging of the repaired filler contract: the local theorem is now
witness-indexed, and only this wrapper quantifies over all candidate selected
phase-return witnesses. -/
def phase_return_gap_fill_bridge (m t U : ℕ) (β : ℝ) : Prop :=
  ∀ hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U,
    phase_return_gap_fill_step_drift m t U β hphase

/-- Any proof of the smallest single-gap statement immediately supplies the
structured pair-step contract on the explicit phase-return witness. -/
theorem phase_return_pair_step_sedt_of_single_gap
    {m t U : ℕ} {β : ℝ}
    (hsingle : sedt_single_gap_of_phase_return m t U β) :
    phase_return_pair_step_sedt m t U β := by
  intro hparams hphase j
  exact hsingle hparams (hphase.leftIdx j) (hphase.rightIdx j)
    (hphase.longSep j) (hphase.phaseAligned j)

/-- Witness-indexed canonical-gap local target on one concrete selected
phase-return witness. -/
def canonical_phase_return_gap_step_sedt_on
    (m t U : ℕ) (β : ℝ)
    (hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  sedt_dominant_parameters t U β →
    ∀ j : ℕ,
      potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx (j + 1)]) m) -
        potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) ≤
          sedt_envelope t U β (hphase.leftIdx (j + 1) - hphase.leftIdx j)

/-- Localized form of the remaining aperiodic `E.2` bridge: it suffices to
bound the potential drop across each single canonical long gap extracted from
the structured phase-return witness. This isolates the true residual content of
the bridge at the per-gap level instead of a whole-stream packaging theorem. -/
def canonical_phase_return_gap_step_sedt (m t U : ℕ) (β : ℝ) : Prop :=
  sedt_dominant_parameters t U β →
    ∀ hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U,
      let hcofinal := (Collatz.Epochs.canonical_gap_long_phase_returns_bridge m t U) hphase
      ∀ j : ℕ,
        potential β ((Collatz.Foundations.collatz_step^[hcofinal.idx (j + 1)]) m) -
          potential β ((Collatz.Foundations.collatz_step^[hcofinal.idx j]) m) ≤
            sedt_envelope t U β (hcofinal.idx (j + 1) - hcofinal.idx j)

/-- Decompose the canonical left-to-left gap into the actual aligned return pair
plus the remaining filler segment. If both pieces satisfy their local drift
contracts, the current canonical-gap target follows immediately. -/
theorem canonical_phase_return_gap_step_sedt_of_pair_and_fill
    {m t U : ℕ} {β : ℝ}
    (hpair : phase_return_pair_step_sedt m t U β)
    (hfill : phase_return_gap_fill_bridge m t U β) :
    canonical_phase_return_gap_step_sedt m t U β := by
  intro hparams hphase
  dsimp [canonical_phase_return_gap_step_sedt]
  intro j
  change
    potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx (j + 1)]) m) -
        potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) ≤
      sedt_envelope t U β (hphase.leftIdx (j + 1) - hphase.leftIdx j)
  have hpairj := hpair hparams hphase j
  have hfillj := hfill hphase hparams j
  have hsplit :
      potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx (j + 1)]) m) -
          potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) =
        (potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx (j + 1)]) m) -
            potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)) +
        (potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) -
            potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)) := by
    ring
  have hlen :
      hphase.leftIdx (j + 1) - hphase.leftIdx j =
        (hphase.rightIdx j - hphase.leftIdx j) +
        (hphase.leftIdx (j + 1) - hphase.rightIdx j) :=
    Collatz.Epochs.phase_return_pair_gap_decomposition hphase j
  have hlenR :
      ((hphase.leftIdx (j + 1) - hphase.leftIdx j : ℕ) : ℝ) =
        ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ) +
        ((hphase.leftIdx (j + 1) - hphase.rightIdx j : ℕ) : ℝ) := by
    exact_mod_cast hlen
  have henv :
      sedt_envelope t U β (hphase.rightIdx j - hphase.leftIdx j) +
          (-(ε t U β) * ((hphase.leftIdx (j + 1) - hphase.rightIdx j : ℕ) : ℝ)) =
        sedt_envelope t U β (hphase.leftIdx (j + 1) - hphase.leftIdx j) := by
    unfold sedt_envelope
    rw [hlenR]
    ring
  rw [hsplit]
  have hsumBound :
      (potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx (j + 1)]) m) -
          potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)) +
        (potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) -
          potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)) ≤
        sedt_envelope t U β (hphase.rightIdx j - hphase.leftIdx j) +
          (-(ε t U β) * ((hphase.leftIdx (j + 1) - hphase.rightIdx j : ℕ) : ℝ)) := by
    linarith
  exact hsumBound.trans_eq henv

/-- Local reassembly theorem on one concrete selected phase-return witness. -/
theorem canonical_phase_return_gap_step_sedt_on_of_pair_and_fill
    {m t U : ℕ} {β : ℝ}
    {hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U}
    (hpair : phase_return_pair_step_sedt_on m t U β hphase)
    (hfill : phase_return_gap_fill_step_drift m t U β hphase) :
    canonical_phase_return_gap_step_sedt_on m t U β hphase := by
  intro hparams j
  have hpairj := hpair hparams j
  have hfillj := hfill hparams j
  have hsplit :
      potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx (j + 1)]) m) -
          potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m) =
        (potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx (j + 1)]) m) -
            potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)) +
        (potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) -
            potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)) := by
    ring
  have hlen :
      hphase.leftIdx (j + 1) - hphase.leftIdx j =
        (hphase.rightIdx j - hphase.leftIdx j) +
        (hphase.leftIdx (j + 1) - hphase.rightIdx j) :=
    Collatz.Epochs.phase_return_pair_gap_decomposition hphase j
  have hlenR :
      ((hphase.leftIdx (j + 1) - hphase.leftIdx j : ℕ) : ℝ) =
        ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ) +
        ((hphase.leftIdx (j + 1) - hphase.rightIdx j : ℕ) : ℝ) := by
    exact_mod_cast hlen
  have henv :
      sedt_envelope t U β (hphase.rightIdx j - hphase.leftIdx j) +
          (-(ε t U β) * ((hphase.leftIdx (j + 1) - hphase.rightIdx j : ℕ) : ℝ)) =
        sedt_envelope t U β (hphase.leftIdx (j + 1) - hphase.leftIdx j) := by
    unfold sedt_envelope
    rw [hlenR]
    ring
  rw [hsplit]
  have hsumBound :
      (potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx (j + 1)]) m) -
          potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)) +
        (potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m) -
          potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m)) ≤
        sedt_envelope t U β (hphase.rightIdx j - hphase.leftIdx j) +
          (-(ε t U β) * ((hphase.leftIdx (j + 1) - hphase.rightIdx j : ℕ) : ℝ)) := by
    linarith
  exact hsumBound.trans_eq henv

/-- Packaging theorem on one concrete selected phase-return witness: the local
canonical-gap inequality yields the orbitwise SEDT envelope on the induced
canonical stream for that witness alone. -/
theorem orbit_epoch_sedt_envelope_of_gap_step_sedt_on
    {m t U : ℕ} {β : ℝ}
    {hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U}
    (hlocal : canonical_phase_return_gap_step_sedt_on m t U β hphase)
    (hparams : sedt_dominant_parameters t U β) :
    orbit_epoch_sedt_envelope t U β
      (Collatz.Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps m t U
        ((Collatz.Epochs.canonical_gap_long_phase_returns_bridge m t U) hphase)) := by
  intro j
  simpa [canonical_phase_return_gap_step_sedt_on,
    orbit_epoch_sedt_envelope, Collatz.Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps,
    Collatz.Epochs.orbit_long_epoch_stream_of_supply,
    Collatz.Epochs.orbit_long_epoch_supply_of_cofinal_long_epoch_gaps]
    using hlocal hparams j

/-- Converse localization: on the canonical stream induced by one concrete
phase-return witness, the orbitwise SEDT envelope is definitionally the same
content as the local canonical-gap theorem. This lets the remaining actual
aperiodic source be stated either at stream level or directly on the skeleton. -/
theorem canonical_phase_return_gap_step_sedt_on_of_orbit_epoch_sedt_envelope
    {m t U : ℕ} {β : ℝ}
    {hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U}
    (henv : orbit_epoch_sedt_envelope t U β
      (Collatz.Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps m t U
        ((Collatz.Epochs.canonical_gap_long_phase_returns_bridge m t U) hphase))) :
    canonical_phase_return_gap_step_sedt_on m t U β hphase := by
  intro hparams j
  simpa [canonical_phase_return_gap_step_sedt_on,
    orbit_epoch_sedt_envelope, Collatz.Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps,
    Collatz.Epochs.orbit_long_epoch_stream_of_supply,
    Collatz.Epochs.orbit_long_epoch_supply_of_cofinal_long_epoch_gaps]
    using henv j

/-- Packaging theorem: a local per-gap SEDT inequality on the canonical
phase-return gaps immediately yields the previously exposed stream-level
`phase_return_sedt_envelope_bridge`. -/
theorem phase_return_sedt_envelope_bridge_of_gap_step_sedt
    {m t U : ℕ} {β : ℝ}
    (hlocal : canonical_phase_return_gap_step_sedt m t U β) :
    phase_return_sedt_envelope_bridge m t U β := by
  intro hparams hphase j
  simpa [canonical_phase_return_gap_step_sedt, phase_return_sedt_envelope_bridge,
    orbit_epoch_sedt_envelope, Collatz.Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps,
    Collatz.Epochs.orbit_long_epoch_stream_of_supply,
    Collatz.Epochs.orbit_long_epoch_supply_of_cofinal_long_epoch_gaps]
    using hlocal hparams hphase j

/-- Apply the remaining `E.2` bridge in theorem form so convergence-level code
can talk about a single canonicalized aperiodic envelope constructor. -/
def orbit_epoch_sedt_envelope_of_phase_returns
    {m t U : ℕ} {β : ℝ}
    (hbridge : phase_return_sedt_envelope_bridge m t U β)
    (hparams : sedt_dominant_parameters t U β)
    (hphase : Collatz.Epochs.OrbitHasCofinalGapLongPhaseReturns m t U) :
    orbit_epoch_sedt_envelope t U β
      (Collatz.Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps m t U
        ((Collatz.Epochs.canonical_gap_long_phase_returns_bridge m t U) hphase)) :=
  hbridge hparams hphase

lemma beta0_lt_four (t U : ℕ) (ht : t ≥ 3) (hU : U ≥ 1) :
    β₀ t U < 4 := by
  have hα : α t U < 2 := alpha_lt_two_of_ht_hU t U ht hU
  have hfrac : (3 : ℝ) / 4 ≤ 2 - α t U := two_sub_alpha_ge_three_quarters t U ht hU
  have hden : 0 < 2 - α t U := by linarith
  unfold β₀
  rw [div_lt_iff₀ hden]
  have hloglt : Real.log (3 / 2) / Real.log 2 < 1 := log_two_ratio_lt_one
  have hbig : (1 : ℝ) < 4 * (2 - α t U) := by
    nlinarith
  exact lt_trans hloglt hbig

lemma sedt_dominance_condition_at_four (t U : ℕ) (ht : t ≥ 3) (hU : U ≥ 1) :
    sedt_dominance_condition t U 4 := by
  have hαge : (3 : ℝ) / 4 ≤ 2 - α t U := two_sub_alpha_ge_three_quarters t U ht hU
  have hC : C t U ≤ (Collatz.SEDT.L₀ t U : ℝ) / 2 := C_le_half_L0 t U ht hU
  have hL0pos : 0 < (Collatz.SEDT.L₀ t U : ℝ) := by
    exact_mod_cast L0_pos t U
  have hloglt : Real.log (3 / 2) / Real.log 2 < 1 := log_two_ratio_lt_one
  have h4C : 4 * C t U ≤ 2 * (Collatz.SEDT.L₀ t U : ℝ) := by
    nlinarith
  have hcoef :
      (3 - Real.log (3 / 2) / Real.log 2) * (Collatz.SEDT.L₀ t U : ℝ) ≤
        (4 * (2 - α t U) - Real.log (3 / 2) / Real.log 2) * (Collatz.SEDT.L₀ t U : ℝ) := by
    have hcoef' :
        3 - Real.log (3 / 2) / Real.log 2 ≤
          4 * (2 - α t U) - Real.log (3 / 2) / Real.log 2 := by
      nlinarith
    exact mul_le_mul_of_nonneg_right hcoef' hL0pos.le
  have hstrict :
      2 * (Collatz.SEDT.L₀ t U : ℝ) <
        (3 - Real.log (3 / 2) / Real.log 2) * (Collatz.SEDT.L₀ t U : ℝ) := by
    nlinarith
  unfold sedt_dominance_condition Collatz.SEDT.ε
  have hmain :
      4 * C t U <
        (4 * (2 - α t U) - Real.log (3 / 2) / Real.log 2) * (Collatz.SEDT.L₀ t U : ℝ) := by
    exact lt_of_le_of_lt h4C (lt_of_lt_of_le hstrict hcoef)
  nlinarith

theorem exists_sedt_dominant_parameters (t U : ℕ) (ht : t ≥ 3) (hU : U ≥ 1) :
    ∃ β : ℝ, sedt_dominant_parameters t U β := by
  refine ⟨4, ht, hU, beta0_lt_four t U ht hU, sedt_dominance_condition_at_four t U ht hU⟩

lemma orbit_epoch_margin_of_sedt_margin (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U)
    (hε : ε t U β > 0)
    (hmargin0 : sedt_margin_condition t U β) :
    orbit_epoch_margin t U β s := by
  intro j
  have hlongNat : Collatz.SEDT.L₀ t U ≤ s.epochLen j := s.longEpoch j
  have hlongReal : (Collatz.SEDT.L₀ t U : ℝ) ≤ (s.epochLen j : ℝ) := by
    exact_mod_cast hlongNat
  have hscale :
      (ε t U β / 2) * (Collatz.SEDT.L₀ t U : ℝ) ≤
        (ε t U β / 2) * (s.epochLen j : ℝ) := by
    exact mul_le_mul_of_nonneg_left hlongReal (le_of_lt (by linarith))
  exact le_trans hmargin0 hscale

/-- Part 2-style orbitwise raw inequality: long epochs contribute a negative linear term
plus one bounded overhead per selected epoch. -/
lemma strong_i2_orbitwise_raw (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U)
    (hstep : orbit_epoch_step_drift t U β s) :
    ∀ J : ℕ,
      potential β (s.orbitVal J) ≤
        potential β (s.orbitVal 0) -
          (ε t U β) * (stream_prefix_total s J : ℝ) + β * C t U * J := by
  intro J
  induction J with
  | zero =>
      simp [stream_prefix_total]
  | succ J ih =>
      have hstepJ := hstep J
      have hcast :
          (stream_prefix_total s (J + 1) : ℝ) =
            (stream_prefix_total s J : ℝ) + (s.epochLen J : ℝ) := by
        simp [stream_prefix_total, prefix_total, Finset.sum_range_succ, Nat.cast_add]
      have hsucc :
          β * C t U * ((J + 1 : ℕ) : ℝ) = β * C t U * (J : ℝ) + β * C t U := by
        calc
          β * C t U * ((J + 1 : ℕ) : ℝ)
              = β * C t U * ((J : ℝ) + 1) := by norm_num [Nat.cast_add]
          _ = β * C t U * (J : ℝ) + β * C t U := by ring
      have hbound :
          potential β (s.orbitVal (J + 1)) ≤
            potential β (s.orbitVal J) -
              (ε t U β) * (s.epochLen J : ℝ) + β * C t U := by
        linarith
      rw [hcast, hsucc]
      have ih' := ih
      nlinarith [hbound, ih']

/-- Strong orbitwise I.2 packaging via the paper-level dominance criterion
`ε(t,U,β) * L₀(t,U) > β * C(t,U)`. -/
lemma strong_i2_orbitwise_packaged_of_dominance (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U)
    (_hε : ε t U β > 0)
    (hβ : 0 ≤ β)
    (hstep : orbit_epoch_step_drift t U β s)
    (hdom : sedt_dominance_condition t U β) :
    ∃ εv B : ℝ, εv > 0 ∧
      (∀ J : ℕ,
        potential β (s.orbitVal J) ≤
          -(εv) * (stream_prefix_total s J : ℝ) + B) ∧
      (∃ M : ℕ, B < εv * (M : ℝ)) := by
  let L0r : ℝ := (Collatz.SEDT.L₀ t U : ℝ)
  let εv : ℝ := ε t U β - β * C t U / L0r
  let B : ℝ := potential β (s.orbitVal 0)
  have hL0pos_nat : 0 < Collatz.SEDT.L₀ t U := L0_pos t U
  have hL0pos : 0 < L0r := by
    dsimp [L0r]
    exact_mod_cast hL0pos_nat
  have hCnonneg : 0 ≤ C t U := by
    unfold C
    positivity
  have hβCnonneg : 0 ≤ β * C t U := mul_nonneg hβ hCnonneg
  have hεv : 0 < εv := by
    dsimp [εv, L0r]
    have hdom' : β * C t U / (Collatz.SEDT.L₀ t U : ℝ) < ε t U β := by
      rw [div_lt_iff₀ hL0pos]
      simpa [sedt_dominance_condition, mul_comm, mul_left_comm, mul_assoc] using hdom
    nlinarith
  refine ⟨εv, B, hεv, ?_, ?_⟩
  · intro J
    have hraw := strong_i2_orbitwise_raw t U β s hstep J
    have hprefixNat : J * Collatz.SEDT.L₀ t U ≤ stream_prefix_total s J := by
      exact prefix_total_lower_bound s.epochLen (Collatz.SEDT.L₀ t U) s.longEpoch J
    have hprefixReal :
        (J : ℝ) * L0r ≤ (stream_prefix_total s J : ℝ) := by
      dsimp [L0r]
      exact_mod_cast hprefixNat
    have hJle :
        (J : ℝ) ≤ (stream_prefix_total s J : ℝ) / L0r := by
      rw [le_div_iff₀ hL0pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprefixReal
    have hover :
        β * C t U * (J : ℝ) ≤ β * C t U * ((stream_prefix_total s J : ℝ) / L0r) := by
      have hmul := mul_le_mul_of_nonneg_left hJle hβCnonneg
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul
    have hover' :
        β * C t U * (J : ℝ) ≤ (β * C t U / L0r) * (stream_prefix_total s J : ℝ) := by
      have hrew : β * C t U * ((stream_prefix_total s J : ℝ) / L0r) =
          (β * C t U / L0r) * (stream_prefix_total s J : ℝ) := by
        field_simp [hL0pos.ne']
      simpa [hrew] using hover
    dsimp [εv, B]
    nlinarith [hraw, hover']
  · exact exists_nat_threshold_of_pos εv B hεv

/-- Strong orbitwise I.2 form: prefix potential has linear negative upper bound on selected long epochs. -/
lemma strong_i2_orbitwise_prefix (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U)
    (hstep : orbit_epoch_step_drift t U β s)
    (hmargin : orbit_epoch_margin t U β s) :
    ∀ J : ℕ,
      potential β (s.orbitVal J) ≤
        potential β (s.orbitVal 0) -
          (ε t U β / 2) * (stream_prefix_total s J : ℝ) := by
  intro J
  induction J with
  | zero =>
      simp [stream_prefix_total]
  | succ J ih =>
      have hstepJ := hstep J
      have hmarginJ := hmargin J
      have hcast :
          (stream_prefix_total s (J + 1) : ℝ) =
            (stream_prefix_total s J : ℝ) + (s.epochLen J : ℝ) := by
        simp [stream_prefix_total, prefix_total, Finset.sum_range_succ, Nat.cast_add]
      have hbound :
          potential β (s.orbitVal (J + 1)) ≤
            potential β (s.orbitVal J) - (ε t U β / 2) * (s.epochLen J : ℝ) := by
        have hstep' :
            potential β (s.orbitVal (J + 1)) ≤
              potential β (s.orbitVal J) +
                (-(ε t U β) * (s.epochLen J : ℝ) + β * C t U) := by
          linarith
        have hneg :
            (-(ε t U β) * (s.epochLen J : ℝ) + β * C t U) ≤
              -((ε t U β) / 2) * (s.epochLen J : ℝ) := by
          have hmargin' :
              β * C t U ≤ ((ε t U β) / 2) * (s.epochLen J : ℝ) := by
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmarginJ
          nlinarith
        linarith
      have ih' :
          potential β (s.orbitVal J) ≤
            potential β (s.orbitVal 0) -
              (ε t U β / 2) * (stream_prefix_total s J : ℝ) := ih
      rw [hcast]
      nlinarith

/-- Packaged strong I.2 bridge with explicit `(εv, B)` and caller-free threshold witness. -/
lemma strong_i2_orbitwise_packaged (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U)
    (hε : ε t U β > 0)
    (hstep : orbit_epoch_step_drift t U β s)
    (hmargin : orbit_epoch_margin t U β s) :
    ∃ εv B : ℝ, εv > 0 ∧
      (∀ J : ℕ,
        potential β (s.orbitVal J) ≤
          -(εv) * (stream_prefix_total s J : ℝ) + B) ∧
      (∃ M : ℕ, B < εv * (M : ℝ)) := by
  refine ⟨ε t U β / 2, potential β (s.orbitVal 0), ?_, ?_, ?_⟩
  · linarith
  · intro J
    have hmain := strong_i2_orbitwise_prefix t U β s hstep hmargin J
    linarith
  · exact exists_nat_threshold_of_pos (ε t U β / 2) (potential β (s.orbitVal 0)) (by linarith)

/-- Orbitwise absorbed cofinal negativity: the W6 cofinal I.2 bridge for real orbit streams. -/
lemma orbitwise_absorbed_cofinal_negativity (t U : ℕ) (_β εv B : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U)
    (hε : εv > 0)
    (hthreshold : ∃ M : ℕ, B < εv * (M : ℝ)) :
    ∀ N : ℕ, ∃ J : ℕ, J ≥ N ∧
      -(εv) * (stream_prefix_total s J : ℝ) + B < 0 := by
  intro N
  have hcofinal : ∀ N M : ℕ, ∃ J : ℕ, J ≥ N ∧ M ≤ prefix_total s.epochLen J := by
    intro N' M'
    simpa [stream_prefix_total] using stream_prefix_total_cofinal s N' M'
  rcases coercivity_absorption_cofinal εv B s.epochLen hε hthreshold hcofinal N with
    ⟨J, hJN, S, hS, hneg⟩
  subst hS
  refine ⟨J, hJN, ?_⟩
  simpa [stream_prefix_total] using hneg

/-- Scientific W6 bridge: coercivity packages boundedness together with potential normalization. -/
lemma coercivity (m : ℕ)
    (hbounded : orbit_bounded m)
    (β : ℝ) (hβ : 0 ≤ β)
    (hoddIter : ∀ k : ℕ, Odd ((Collatz.Foundations.collatz_step^[k]) m)) :
    orbit_bounded m ∧ ∀ k : ℕ, 0 ≤ potential β ((Collatz.Foundations.collatz_step^[k]) m) := by
  refine ⟨hbounded, ?_⟩
  intro k
  exact potential_nonneg_of_odd β hβ (hoddIter k)

end Collatz.Convergence
