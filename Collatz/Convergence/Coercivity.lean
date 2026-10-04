import Mathlib
import Collatz.Foundations.Core
import Collatz.Epochs.LongEpochs
import Collatz.SEDT.Core

/-!
# Potential, long-epoch streams and the SEDT envelope

Definitions of the potential `V_β(n) = log₂ n + β (depth₋(n) − 1)`, of the
per-epoch SEDT envelope on a long-epoch stream, and the coercivity lemmas that
sum the envelope. The sum argument shows (see
`false_of_orbit_epoch_sedt_envelope` in `MainTheorem.lean`) that the envelope
at dominant parameters is contradictory on *every* long-epoch stream of an odd
orbit. Hence a hypothesis that yields the envelope (at dominant parameters) on
some long-epoch stream of an odd orbit is contradictory, unless it is guarded by
`¬ orbit_eventually_periodic n`, in which case it is equivalent to eventual
periodicity of the orbit. The paper's Lemma I.2 (coercivity for every orbit) is
the no-divergence conjecture and is not formalized; the lemmas below only sum
an *assumed* per-epoch bound. The former placeholders `coercivity` (returned
its hypothesis), `coercivity_concatenation` (`∃ x, x ≤ x`) and the
phase-return / filler plumbing were deleted in the 2026-10 clean-up.
-/

namespace Collatz.Convergence

open Collatz.SEDT
open Real
open scoped BigOperators

/-- Potential `V_β(n) = log₂ n + β (depth₋(n) − 1)`, normalized so that
`potential β 1 = 0`; nonnegative on odd `n` for `β ≥ 0`. -/
noncomputable def potential (β : ℝ) (n : ℕ) : ℝ :=
  Real.log n / Real.log 2 + β * ((Collatz.Foundations.depth_minus n : ℝ) - 1)

/-- The odd-step orbit of `m` is bounded. -/
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

/-- `∑_{j < J} lengths j`. -/
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

/-- If `ε > 0` and prefix totals are cofinally unbounded, then `−ε·S + B < 0` for
prefix totals `S` arbitrarily far out. Elementary. -/
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

/-- Prefix total of the epoch lengths of a long-epoch stream. -/
def stream_prefix_total {m t U : ℕ} (s : Collatz.Epochs.OrbitLongEpochStream m t U) (J : ℕ) : ℕ :=
  prefix_total s.epochLen J

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

/-- Prefix totals of a long-epoch stream are cofinally unbounded. -/
lemma stream_prefix_total_cofinal {m t U : ℕ} (s : Collatz.Epochs.OrbitLongEpochStream m t U) :
    ∀ N M : ℕ, ∃ J : ℕ, J ≥ N ∧ M ≤ stream_prefix_total s J := by
  apply prefix_total_cofinal_of_uniform_long (lengths := s.epochLen) (L0 := Collatz.SEDT.L₀ t U)
  · exact L0_pos t U
  · intro j
    exact s.longEpoch j

/-- Archimedean threshold: `ε > 0 → ∃ M, B < ε·M`. -/
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

/-- Hypothesis shape: per-epoch drift bound `−ε·L_j + β·C` on a stream. -/
def orbit_epoch_step_drift (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U) : Prop :=
  ∀ j : ℕ,
    potential β (s.orbitVal (j + 1)) - potential β (s.orbitVal j) ≤
      -(ε t U β) * (s.epochLen j : ℝ) + β * C t U

/-- Hypothesis shape (paper E.2 on a stream): the potential change over each epoch
is at most `sedt_envelope`. At dominant parameters it is contradictory on every
long-epoch stream of an odd orbit (`false_of_orbit_epoch_sedt_envelope`). -/
def orbit_epoch_sedt_envelope (t U : ℕ) (β : ℝ) {m : ℕ}
    (s : Collatz.Epochs.OrbitLongEpochStream m t U) : Prop :=
  ∀ j : ℕ,
    potential β (s.orbitVal (j + 1)) - potential β (s.orbitVal j) ≤
      sedt_envelope t U β (s.epochLen j)

/-- An index supply together with the E.2 envelope on the induced stream. For odd
`m` and dominant parameters this type is empty
(`aperiodic_tail_contradiction_from_coercivity`). -/
structure OrbitLongEpochE2Witness (m t U : ℕ) (β : ℝ) where
  supply : Collatz.Epochs.OrbitLongEpochSupply m t U
  envelope :
    orbit_epoch_sedt_envelope t U β
      (Collatz.Epochs.orbit_long_epoch_stream_of_supply m t U supply)

/-- The stream underlying an `OrbitLongEpochE2Witness`. -/
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

/-- Dominance: `β·C(t,U) < ε(t,U,β)·L₀(t,U)`. -/
def sedt_dominance_condition (t U : ℕ) (β : ℝ) : Prop :=
  β * C t U < ε t U β * (Collatz.SEDT.L₀ t U : ℝ)

/-- Parameter conditions `t ≥ 3`, `U ≥ 1`, `β > β₀`, and dominance. Satisfiable
(`exists_sedt_dominant_parameters`). -/
def sedt_dominant_parameters (t U : ℕ) (β : ℝ) : Prop :=
  t ≥ 3 ∧ U ≥ 1 ∧ β > β₀ t U ∧ sedt_dominance_condition t U β

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

/-- Summing an assumed per-epoch drift bound along a stream. -/
lemma stream_potential_le_of_step_drift (t U : ℕ) (β : ℝ) {m : ℕ}
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

/-- Under dominance `ε·L₀ > β·C`, the summed per-epoch bound gives a linear
upper bound `−ε'·S + B` on the potential along the stream. -/
lemma stream_potential_linear_bound_of_dominance (t U : ℕ) (β : ℝ) {m : ℕ}
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
    have hraw := stream_potential_le_of_step_drift t U β s hstep J
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

/-- `coercivity_absorption_cofinal` specialized to a long-epoch stream. -/
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

end Collatz.Convergence
