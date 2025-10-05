import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.Basic
import Init.Data.Nat.Div.Basic
import Collatz.Foundations.Basic
import Collatz.Epochs.Structure
import Collatz.Utilities.Constants
import Collatz.Utilities.TwoAdicDepth

open Collatz.Utilities (α β₀ ε C L₀ K_glue V Q_t Q_t_pos depth_minus factorization_two_succ Q_t_ge_three Q_t_two Q_t_one Q_t_zero K_glue_def)
open Collatz (T_odd)

-- T_shortcut is the simplified Collatz function for e=1 case
def T_shortcut (r : ℕ) : ℕ := (3 * r + 1) / 2

/-!
# SEDT (Shumak Epoch Drift Theorem)

This file formalizes the SEDT envelope theorem, which establishes negative drift
for long t-epochs in the Collatz dynamics.

## Main Results

- `sedt_envelope`: For long epochs (L ≥ L₀), the potential change ΔV is bounded by
  -ε·L + β·C, where ε > 0 (negative drift coefficient)
- Constants α, β₀, ε are defined according to Appendix D of the paper

## References

See paper Appendix A (SEDT proof) for detailed mathematical derivation.
-/

namespace Collatz.SEDT

open Real

/-!
## Potential Function and Constants
-/

/-!
## Helper Lemmas for Constants
-/

-- Helper lemma for T_shortcut arithmetic
lemma T_shortcut_add_one_eq {r k : ℕ} (_ : Odd r) (_ : r + 1 = 2 * k)
    (h_tr1 : (3 * r + 1) / 2 + 1 = 3 * k) :
    T_shortcut r + 1 = 3 * k := by
  unfold T_shortcut
  exact h_tr1

-- V function helper lemmas
@[simp] lemma V_def (n : ℕ) (β : ℝ) :
  V n β = Real.log (n : ℝ) / Real.log 2 + β * Collatz.Utilities.depth_minus n := rfl

lemma V_diff (a b : ℕ) (β : ℝ) :
  V a β - V b β = (Real.log (a : ℝ) - Real.log (b : ℝ)) / Real.log 2
    + β * ((Collatz.Utilities.depth_minus a : ℝ) - Collatz.Utilities.depth_minus b) := by
  simp [V_def, sub_eq_add_neg]
  ring_nf


lemma alpha_gt_one (t U : ℕ) (_ht : t ≥ 3) (hU : U ≥ 1) : α t U > 1 := by
  -- Use the imported definition from Utilities.Constants
  unfold α
  -- Denominator > 0 since Q_t t > 0 for t ≥ 1
  have hden_pos : 0 < (Q_t t : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Q_t_pos
    linarith
  -- Exponent -(U:ℝ) is negative as soon as U ≥ 1
  have hUpos : 0 < (U : ℝ) := by
    have : 0 < U := Nat.pos_of_ne_zero (fun h => by omega)
    exact Nat.cast_pos.mpr this
  have hneg : (-(U : ℝ)) < 0 := by linarith
  -- With base 2 > 1 and negative exponent, we get 2^(-U) < 1
  have hlt1 : (2 : ℝ) ^ (-(U : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) hneg
  -- So the numerator is positive
  have hnum_pos : 0 < 1 - (2 : ℝ) ^ (-(U : ℝ)) := by linarith
  -- Hence the fraction is positive
  have hfrac_pos : 0 < (1 - (2 : ℝ) ^ (-(U : ℝ))) / (Q_t t : ℝ) :=
    div_pos hnum_pos hden_pos
  -- Add 1 to a positive quantity
  linarith

lemma alpha_lt_two (t U : ℕ) (ht : t ≥ 3) : α t U < 2 := by
  unfold α
  -- Нужно показать: 1 + (1 - 2^{-U})/Q_t < 2
  -- ⇔ (1 - 2^{-U})/Q_t < 1
  -- Это верно т.к. 1 - 2^{-U} < 1 и Q_t ≥ 1

  -- 2^(-(U)) > 0
  have two_pos : 0 < (2 : ℝ) := by norm_num
  have h_num_pos : 0 < (2 : ℝ)^(-(U : ℝ)) :=
    Real.rpow_pos_of_pos two_pos _

  -- (1 - 2^(-U)) < 1
  have h_num_strict : 1 - (2 : ℝ)^(-(U : ℝ)) < 1 := by
    linarith [h_num_pos]

  -- denominator > 0 (Q_t t > 0 for t ≥ 1)
  have h_denom_pos : 0 < (Q_t t : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Q_t_pos
    linarith

  -- key step: Q_t ≥ 1 for t ≥ 3
  have h_denom_ge_one : (1 : ℝ) ≤ (Q_t t : ℝ) := by
    have h_Q_ge_one : 1 ≤ Q_t t := by
      have ht3 : t ≥ 3 := ht
      have ht_gt_two : 2 < t := Nat.lt_of_lt_of_le (by decide : 2 < 3) ht3
      have ht_pos : 0 < t - 2 := Nat.sub_pos_of_lt ht_gt_two
      have hpow : 2^1 ≤ 2^(t - 2) :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.succ_le_of_lt ht_pos)
      have hpow' : 1 ≤ 2^(t - 2) :=
        le_trans (by decide : 1 ≤ 2) (by simpa using hpow)
      have ht_ne_two : t ≠ 2 := by linarith [ht3]
      have ht_not_lt_two : ¬ t < 2 := by linarith [ht3]
      simpa [Q_t, ht3, ht_ne_two, ht_not_lt_two] using hpow'
    exact_mod_cast h_Q_ge_one

  -- fraction < 1
  have hfrac_lt_one : (1 - (2 : ℝ)^(-(U : ℝ))) / (Q_t t : ℝ) < 1 := by
    -- (1 - 2^(-U)) / Q_t < 1 / Q_t
    have h1 : (1 - (2 : ℝ)^(-(U : ℝ))) / (Q_t t : ℝ) < 1 / (Q_t t : ℝ) :=
      div_lt_div_of_pos_right h_num_strict h_denom_pos
    -- then: 1/Q_t ≤ 1
    have h2 : (1 : ℝ) / (Q_t t : ℝ) ≤ 1 := by
      rw [div_le_one h_denom_pos]
      exact h_denom_ge_one
    exact lt_of_lt_of_le h1 h2

  -- завершение
  linarith [hfrac_lt_one]

lemma beta_zero_pos (t U : ℕ) (ht : t ≥ 3) (_hU : U ≥ 1) : β₀ t U > 0 := by
  unfold β₀
  have h1 : α t U < 2 := alpha_lt_two t U ht
  have h2 : log (3/2) / log 2 > 0 := by
    have log_three_half_pos : log (3/2) > 0 := by
      have : (3 : ℝ) / 2 > 1 := by norm_num
      exact Real.log_pos this
    have log_two_pos : log 2 > 0 := by
      have : (2 : ℝ) > 1 := by norm_num
      exact Real.log_pos this
    exact div_pos log_three_half_pos log_two_pos
  -- β₀ = (log(3/2)/log(2)) / (2 - α) где α < 2
  have h3 : 2 - α t U > 0 := by linarith [h1]
  exact div_pos h2 h3

lemma epsilon_pos (t U : ℕ) (β : ℝ) (ht : t ≥ 3) (_hU : U ≥ 1) (hβ : β > β₀ t U) :
  ε t U β > 0 := by
  unfold ε
  -- ε = β(2-α) - log(3/2)/log(2)
  -- β > β₀ = (log(3/2)/log(2))/(2-α)
  -- ⇒ β(2-α) > log(3/2)/log(2)
  -- ⇒ ε > 0
  have h1 : α t U < 2 := alpha_lt_two t U ht
  have h2_alpha : 2 - α t U > 0 := by linarith [h1]

  have log_ratio : log (3/2) / log 2 > 0 := by
    have log_three_half_pos : log (3/2) > 0 := by
      have : (3 : ℝ) / 2 > 1 := by norm_num
      exact Real.log_pos this
    have log_two_pos : log 2 > 0 := by
      have : (2 : ℝ) > 1 := by norm_num
      exact Real.log_pos this
    exact div_pos log_three_half_pos log_two_pos

  -- Из β > β₀ получаем β(2-α) > log(3/2)/log(2)
  have key : β * (2 - α t U) > log (3/2) / log 2 := by
    unfold β₀ at hβ
    calc β * (2 - α t U) > (log (3/2) / log 2) / (2 - α t U) * (2 - α t U) := by
           apply mul_lt_mul_of_pos_right hβ h2_alpha
       _ = log (3/2) / log 2 := by field_simp

  linarith [key, log_ratio]

/-!
## Epoch Structure for SEDT
-/

/-- Extended epoch structure with touch data for SEDT -/
structure SEDTEpoch where
  /-- Base epoch data -/
  base : Epoch
  /-- Number of t-touches in plateau -/
  num_touches : ℕ
  /-- Head overhead contribution -/
  head_overhead : ℝ
  /-- Boundary glue overhead -/
  boundary_overhead : ℝ

/-- Get length from SEDT epoch -/
def SEDTEpoch.length (e : SEDTEpoch) : ℕ :=
  let b : Collatz.Epoch := e.base
  b.end_idx - b.start_idx + 1

/-!
## Helper Lemmas for Potential Changes
-/

/-- Shortcut Collatz map: T(r) = (3r+1)/2 for odd r

    ⚠️ CRITICAL: This is the SHORTCUT step, not the accelerated step!
    The accelerated step r' = (3r+1)/2^e does NOT satisfy the bound depth⁻(r') ≤ 2.
    Counterexample: r=41 gives depth⁻(r') = 5 > 2.

    Reference: Expert analysis 2025-10-03 (Anatoliy)
-/
def T_shortcut (r : ℕ) : ℕ := (3 * r + 1) / 2

/-- Potential change for a single Collatz step (shortcut version)
    ΔV = V(T(r)) - V(r) where T(r) = (3r+1)/2
-/
noncomputable def single_step_ΔV (r : ℕ) (β : ℝ) : ℝ :=
  V (T_shortcut r) β - V r β

/-- Helper: Arithmetic identity for shortcut step

    From r+1 = k+k and 2 ∣ 3r+1, we get (3r+1)/2 + 1 = 3k.

    Key trick (from expert): multiply both sides by 2 and cancel,
    avoiding fragile division lemmas.

    Reference: Expert solution 2025-10-03 (Anatoliy)
-/
private lemma helper_shortcut_arithmetic (r k : ℕ) (_hr_odd : Odd r) (hk : r + 1 = k + k)
  (h2_dvd : 2 ∣ 3 * r + 1) :
  (3 * r + 1) / 2 + 1 = 3 * k := by
  -- turn `k + k` into `2*k`
  have hk2 : r + 1 = 2 * k := by simpa [two_mul] using hk
  -- cancel after multiplying both sides by 2
  have h2pos : 0 < 2 := by decide
  refine (Nat.mul_right_cancel h2pos ?_)   -- goal: 2*lhs = 2*rhs
  calc
    ((3 * r + 1) / 2 + 1) * 2
        = (((3 * r + 1) / 2) + 1) * 2 := rfl
    _   = ((3 * r + 1) / 2) * 2 + 1 * 2 := by rw [add_mul]
    _   = ((3 * r + 1) / 2) * 2 + 2 := by simp
    _   = (3 * r + 1) + 2 := by
            have hmdc : ((3 * r + 1) / 2) * 2 = 3 * r + 1 :=
              Nat.div_mul_cancel h2_dvd
            rw [hmdc]
    _   = 3 * r + 3 := by omega
    _   = 3 * (r + 1) := by ring
    _   = 3 * (2 * k) := by rw [hk2]
    _   = (3 * 2) * k := by rw [mul_assoc]
    _   = (2 * 3) * k := by rw [mul_comm 3 2]
    _   = 2 * (3 * k) := by rw [mul_assoc]
    _   = (3 * k) * 2 := by rw [mul_comm]

/-- Depth drops by exactly 1 for shortcut step (PROVEN LEMMA)

    For odd r, T(r)+1 = 3(r+1)/2, so:
    ν₂(T(r)+1) = ν₂(3) + ν₂((r+1)/2) = 0 + (ν₂(r+1) - 1)

    This is the KEY lemma for the shortcut step correctness.

    Reference: Expert solution 2025-10-03 (Anatoliy)
-/
lemma depth_drop_one_shortcut (r : ℕ) (hr_odd : Odd r) :
  depth_minus (T_shortcut r) + 1 = depth_minus r := by
  classical
  -- `r` odd ⇒ `r+1` even, so `r+1 = k + k`
  obtain ⟨k, hk⟩ := (hr_odd.add_one)
  -- also `2 ∣ 3r+1`
  have h2_dvd : 2 ∣ 3 * r + 1 := by
    have : Odd (3 * r) := Nat.odd_mul.mpr ⟨by decide, hr_odd⟩
    exact even_iff_two_dvd.mp this.add_one
  -- the arithmetic identity `(3r+1)/2 + 1 = 3k`
  have h_tr1 : (3 * r + 1) / 2 + 1 = 3 * k :=
    helper_shortcut_arithmetic r k hr_odd hk h2_dvd

  -- Convert `k+k` to `2*k`
  have hk2 : r + 1 = 2 * k := by simpa [two_mul] using hk

  -- factorization of both sides at 2
  have h_fac_T : depth_minus (T_shortcut r)
      = (3 * k).factorization 2 := by
    -- depth_minus (T r) = (T r + 1).factorization 2 = (3k).factorization 2
    simp [depth_minus, T_shortcut, h_tr1]

  have h_fac_r : depth_minus r
      = (2 * k).factorization 2 := by
    -- depth_minus r = (r+1).factorization 2 = (2*k).factorization 2
    simp [depth_minus, hk2]

  -- multiplicativity on products, projected at prime 2
  have h_mul3 :
      (3 * k).factorization 2
        = (3).factorization 2 + k.factorization 2 := by
    have h3ne : (3 : ℕ) ≠ 0 := by decide
    have hkne : k ≠ 0 := by
      -- from r odd ⇒ r ≥ 1 ⇒ r+1 ≥ 2 ⇒ k ≥ 1 via r+1 = 2*k
      have hr1_ge : 2 ≤ r + 1 := by
        have : 1 ≤ r := hr_odd.pos
        exact Nat.succ_le_succ this
      -- From r+1 = 2*k and r+1 ≥ 2, get k ≥ 1
      have : 1 ≤ k := by
        have : 2 * k = r + 1 := hk2.symm
        have : 2 * k ≥ 2 := by omega
        omega
      exact ne_of_gt (Nat.zero_lt_of_lt (Nat.succ_le_iff.mp this))
    have := Nat.factorization_mul h3ne hkne
    simpa using congrArg (fun f => f 2) this

  have h_mul2 :
      (2 * k).factorization 2
        = (2).factorization 2 + k.factorization 2 := by
    have h2ne : (2 : ℕ) ≠ 0 := by decide
    have hkne : k ≠ 0 := by
      -- same as above
      have hr1_ge : 2 ≤ r + 1 := by
        have : 1 ≤ r := hr_odd.pos
        exact Nat.succ_le_succ this
      have : 1 ≤ k := by
        have : 2 * k = r + 1 := hk2.symm
        have : 2 * k ≥ 2 := by omega
        omega
      exact ne_of_gt (Nat.zero_lt_of_lt (Nat.succ_le_iff.mp this))
    have := Nat.factorization_mul h2ne hkne
    simpa using congrArg (fun f => f 2) this

  -- constants at prime 2: 2 ∤ 3 ⇒ exponent 0, and (2).factorization 2 = 1
  have h3fac0 : (3).factorization 2 = 0 := by
    have : ¬ 2 ∣ (3 : ℕ) := by decide
    simpa using Nat.factorization_eq_zero_of_not_dvd this

  have h2fac1 : (2).factorization 2 = 1 := by
    -- via prime-power factorization, project at 2
    have h := @Nat.Prime.factorization_pow 2 1 Nat.prime_two
    have := congrArg (fun f => f 2) h
    simp [pow_one, Finsupp.single_eq_same] at this
    exact this

  -- Use the helper lemma to show T_shortcut r + 1 = 3 * k
  have h_T_add_one : T_shortcut r + 1 = 3 * k :=
    T_shortcut_add_one_eq hr_odd hk2 h_tr1

  -- Now we can prove the factorization equality
  have h_T_fac : (T_shortcut r + 1).factorization 2 = (3 * k).factorization 2 := by
    simp [h_T_add_one]

  have h_r_fac : (r + 1).factorization 2 = (2 * k).factorization 2 := by
    simp [hk2]

  -- Assemble: depth_minus (T r) + 1 = depth_minus r
  calc
    depth_minus (T_shortcut r) + 1
        = ((3 * k).factorization 2) + 1 := by simp [h_T_fac]
    _   = ((3).factorization 2 + k.factorization 2) + 1 := by simp [h_mul3]
    _   = (0 + k.factorization 2) + 1 := by simp [h3fac0]
    _   = ((2).factorization 2 + k.factorization 2) := by simp [h2fac1, add_comm]
    _   = (2 * k).factorization 2 := by simp [h_mul2]
    _   = depth_minus r := by simp [h_r_fac]

/-- Logarithmic part bounded by 1 for shortcut step (PROVEN LEMMA)

    For odd r > 0, the shortcut step T(r) = (3r+1)/2 gives:
    log₂(T(r)/r) ≤ 1

    Proof: T(r)/r = (3r+1)/(2r) ≤ 2 for r ≥ 1, hence log₂(T(r)/r) ≤ log₂(2) = 1

    Reference: Expert solution 2025-10-03 (Anatoliy)
-/
lemma log_part_le_one (r : ℕ) (hr : r > 0) (_hr_odd : Odd r) :
  (log (T_shortcut r) - log r) / log 2 ≤ 1 := by
  -- Key: T(r)/r ≤ (3r+1)/(2r) ≤ 2
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hTpos : (0 : ℝ) < T_shortcut r := by
    unfold T_shortcut
    have : 0 < (3 * r + 1) / 2 := by omega
    exact Nat.cast_pos.mpr this

  -- Upper bound: (3r+1)/(2r) ≤ 2 for r ≥ 1
  have h_ratio_bound : ((3 * r + 1) : ℝ) / (2 * r) ≤ 2 := by
    have h1le : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hr))
    calc ((3 * r + 1) : ℝ) / (2 * r)
        ≤ (3 * r + r) / (2 * r) := by
            apply div_le_div_of_nonneg_right
            · linarith
            · positivity
      _ = (4 * r) / (2 * r) := by ring
      _ = 2 := by
          have : (2 : ℝ) * r ≠ 0 := by positivity
          field_simp [this]
          ring

  -- T(r) ≤ (3r+1)/2 < 2r for r ≥ 1, hence T(r)/r < 2
  have h_final : (T_shortcut r : ℝ) / r ≤ 2 := by
    unfold T_shortcut
    -- In ℝ: 3r+1 ≤ 4r for r ≥ 1
    have h2 : (3 * r + 1 : ℝ) ≤ 4 * r := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hr))
      linarith
    -- Therefore (3r+1)/2 ≤ 2r
    have h3 : ((3 * r + 1) : ℝ) / 2 ≤ 2 * r := by
      have : (0 : ℝ) < 2 := by norm_num
      calc ((3 * r + 1) : ℝ) / 2
          ≤ (4 * r) / 2 := by apply div_le_div_of_nonneg_right h2; linarith
        _ = 2 * r := by ring
    -- ℕ division rounds down, so cast is ≤
    have h4 : (((3 * r + 1) / 2 : ℕ) : ℝ) ≤ ((3 * r + 1) : ℝ) / 2 := by
      norm_cast
      exact Nat.cast_div_le
    -- Combine
    calc (((3 * r + 1) / 2 : ℕ) : ℝ) / r
        ≤ (((3 * r + 1) : ℝ) / 2) / r := by apply div_le_div_of_nonneg_right h4; exact le_of_lt hrpos
      _ ≤ (2 * r) / r := by apply div_le_div_of_nonneg_right h3; exact le_of_lt hrpos
      _ = 2 := by field_simp

  -- log₂(T(r)/r) ≤ log₂(2) = 1
  calc (log (T_shortcut r) - log r) / log 2
      = log ((T_shortcut r : ℝ) / r) / log 2 := by
          rw [log_div (ne_of_gt hTpos) (ne_of_gt hrpos)]
    _ ≤ log 2 / log 2 := by
          apply div_le_div_of_nonneg_right
          · exact Real.log_le_log (by positivity) h_final
          · exact le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    _ = 1 := by field_simp

/-- Single Collatz step (shortcut) has bounded potential change (PROVEN LEMMA)

    For odd r with β ≥ 1, the shortcut step T(r) = (3r+1)/2 gives:
    - Depth drops by exactly 1: ν₂(T(r)+1) = ν₂(r+1) - 1
    - Log part bounded by 1: log₂(T(r)/r) ≤ 1  (NOT log₂(3/2)!)
    - Total: ΔV ≤ 1 - β ≤ log₂(3/2) + 2β for β ≥ 1

    ⚠️ NOTE: Requires β ≥ 1 for the final inequality to hold.

    Proof combines depth_drop_one_shortcut and log_part_le_one.
    Reference: Expert solution 2025-10-03 (shortcut step analysis)
-/
lemma single_step_potential_bounded (r : ℕ) (β : ℝ) (hr : r > 0) (hr_odd : Odd r) (hβ : β ≥ 1) :
  single_step_ΔV r β ≤ log (3/2) / log 2 + β * 2 := by
  unfold single_step_ΔV
  simp [V]

  -- Step 1: Use depth_drop_one_shortcut
  have h_depth : depth_minus (T_shortcut r) + 1 = depth_minus r :=
    depth_drop_one_shortcut r hr_odd

  -- Convert to ℝ inequality
  have h_depth_real : (depth_minus (T_shortcut r) : ℝ) = (depth_minus r : ℝ) - 1 := by
    have : (depth_minus (T_shortcut r) : ℝ) + 1 = (depth_minus r : ℝ) := by
      exact_mod_cast h_depth
    linarith

  -- Step 2: Use log_part_le_one
  have h_log : (log (T_shortcut r) - log r) / log 2 ≤ 1 :=
    log_part_le_one r hr hr_odd

  -- Step 3: Use V function definition
  have h_V_diff : V (T_shortcut r) β - V r β =
    (log (T_shortcut r : ℝ) - log (r : ℝ)) / log 2 + β * ((depth_minus (T_shortcut r) : ℝ) - (depth_minus r : ℝ)) := by
    simpa using V_diff (T_shortcut r) r β

  -- Step 4: Combine using V_diff
  have h_V_expanded : V (T_shortcut r) β - V r β =
    (Real.log (T_shortcut r : ℝ) - Real.log (r : ℝ)) / Real.log 2 + β * ((Collatz.Utilities.depth_minus (T_shortcut r) : ℝ) - Collatz.Utilities.depth_minus r) := by
    simp [V_def]
    ring_nf

  -- Step 5: Use depth drop
  have h_depth_diff : (Collatz.Utilities.depth_minus (T_shortcut r) : ℝ) - Collatz.Utilities.depth_minus r = (-1 : ℝ) := by
    have h1 : (Collatz.Utilities.depth_minus (T_shortcut r) : ℝ) + 1 = (Collatz.Utilities.depth_minus r : ℝ) := by
      exact_mod_cast h_depth
    linarith

  -- Step 6: Final bound
  have h_final : V (T_shortcut r) β - V r β = (Real.log (T_shortcut r : ℝ) - Real.log (r : ℝ)) / Real.log 2 + β * (-1 : ℝ) := by
    rw [h_V_expanded, h_depth_diff]

  -- Final bound: V(T(r)) - V(r) ≤ log(3/2)/log(2) + 2β
  have h_step1 : V (T_shortcut r) β - V r β = (Real.log (T_shortcut r : ℝ) - Real.log (r : ℝ)) / Real.log 2 - β := by
    rw [h_final]
    ring

  have h_step2 : (Real.log (T_shortcut r : ℝ) - Real.log (r : ℝ)) / Real.log 2 - β ≤ 1 - β := by
    linarith [h_log]

  have h_step3 : 1 - β ≤ Real.log (3/2) / Real.log 2 + β * 2 := by
    -- For β ≥ 1: 1 - β ≤ 0 ≤ log(3/2)/log(2) + 2β
    have h1 : 1 - β ≤ 0 := by linarith [hβ]
    have h2 : (0 : ℝ) ≤ log (3/2) / log 2 + β * 2 := by
      have : log (3/2) / log 2 > 0 := by
        have log_pos : log (3/2) > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 3/2)
        have log2_pos : log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        exact div_pos log_pos log2_pos
      have : β * 2 ≥ 2 := by linarith [hβ]
      linarith
    linarith

  -- It suffices to prove the difference form
  suffices
    (log ↑(T_shortcut r) / log 2 + β * ↑(Utilities.depth_minus (T_shortcut r)))
      - (log ↑r / log 2 + β * ↑(Utilities.depth_minus r))
      ≤ log (3 / 2) / log 2 + β * 2 by
    -- you have: this :
    --   logT/log2 + (-(β*dmR) + β*dmT) ≤ β*2 + (logR/log2 + log(3/2)/log2)
    have this' := add_le_add_right this (β * ↑(Utilities.depth_minus r))
    -- goals now match modulo reassociation
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this'

  -- rewrite the β-term using h_depth_diff : ↑dmT - ↑dmr = -1
  have hβdm' :
    β * ↑(Utilities.depth_minus (T_shortcut r)) - β * ↑(Utilities.depth_minus r) = -β := by
    simpa [mul_add, mul_neg, sub_eq_add_neg] using
      congrArg (fun x : ℝ => β * x) h_depth_diff

  have hβdm :
    β * ↑(Utilities.depth_minus (T_shortcut r)) =
      β * ↑(Utilities.depth_minus r) - β := by
    have := (sub_eq_iff_eq_add).1 hβdm'   -- a - b = c → a = c + b
    simpa [sub_eq_add_neg, add_comm] using this

  -- turn the LHS difference into (log T - log r)/log 2 - β
  have hdiv :
    log ↑(T_shortcut r) / log 2 - log ↑r / log 2
      = (log ↑(T_shortcut r) - log ↑r) / log 2 := by
    simpa [sub_eq_add_neg] using
      (sub_div (Real.log (T_shortcut r)) (Real.log r) (Real.log 2)).symm

  have hΔ :
    (log ↑(T_shortcut r) / log 2 + β * ↑(Utilities.depth_minus (T_shortcut r)))
      - (log ↑r / log 2 + β * ↑(Utilities.depth_minus r))
      = (log ↑(T_shortcut r) - log ↑r) / log 2 - β := by
    calc
      _ = (log ↑(T_shortcut r) / log 2 - log ↑r / log 2)
            + (β * ↑(Utilities.depth_minus (T_shortcut r)) - β * ↑(Utilities.depth_minus r)) := by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = (log ↑(T_shortcut r) - log ↑r) / log 2
            + ((β * ↑(Utilities.depth_minus r) - β) - β * ↑(Utilities.depth_minus r)) := by
            simp [hdiv, hβdm]
      _ = (log ↑(T_shortcut r) - log ↑r) / log 2 - β := by
            ring_nf

  -- finish with your existing bounds
  have hbound : (log ↑(T_shortcut r) - log ↑r) / log 2 - β
                  ≤ log (3 / 2) / log 2 + β * 2 :=
    h_step2.trans h_step3
  simpa [hΔ] using hbound

/-- Potential change is bounded by log ratio and depth change -/
lemma single_step_ΔV_bound (r : ℕ) (β : ℝ) (hr : r > 0) (hr_odd : Odd r) (hβ : β ≥ 1) :
  single_step_ΔV r β ≤ log (3/2) / log 2 + β * (2 : ℝ) := by
  exact single_step_potential_bounded r β hr hr_odd hβ



/-- ⚠️ CORRECTED: One-bit bonus at t-touches (NOT multibit!)

    **Mathematical Reality (per expert analysis):**
    At a t-touch (depth⁻(r) = t ≥ 3), the odd Collatz step (3r+1)/2^e
    extracts EXACTLY ONE bit (e = 1), giving:

    depth⁻(r') = t - 1

    **Why the original "multibit" axiom was wrong:**
    - For t ≥ 4: depth⁻(r') = t - 1 > 2, violating old bound depth⁻(r') ≤ 2
    - Counterexample: r=15, t=4 → r'=23 → depth⁻(r')=3 ≠ ≤ 2

    **Key insight:** For odd r with ν₂(r+1) = t ≥ 3:
    - r = 2^t·m - 1 (m odd)
    - 3r+1 = 2(3·2^{t-1}·m - 1) where parenthesis is ODD (since t-1 ≥ 2)
    - Therefore ν₂(3r+1) = 1 exactly
    - Hence r' = (3r+1)/2 and ν₂(r'+1) = t - 1

    This is the standard "reduced Collatz" behavior and matches literature.

    **Impact on SEDT:** The "multibit bonus" comes from the t factors already
    in r+1, not from the odd step itself. SEDT accounting must be updated.

    References:
    - Expert analysis (2025-10-03)
    - Benjamin Hackl's thesis on 2-adic Collatz dynamics
    - Standard p-adic valuation theory

    **Proof Strategy (from expert):**
    1. Decompose r+1 = 2^k * m with m odd (Nat.exists_eq_pow_mul_and_not_dvd)
    2. Show k = t from factorization uniqueness
    3. Compute r'+1 = 3·2^{t-1}·m via division lemmas
    4. Apply factorization_mul to get depth⁻(r') = t - 1
-/
lemma touch_provides_onebit_bonus (r : ℕ) (t : ℕ) (ht : t ≥ 3) (h_touch : depth_minus r = t) :
  ∃ (r' : ℕ),
    r' = (3 * r + 1) / 2 ∧
    depth_minus r' = t - 1 := by
  classical
  -- Shorthand for the given touch equality
  have hfac : (r + 1).factorization 2 = t := by simpa [depth_minus] using h_touch

  -- 2 ∣ (3*r + 1): r is odd (since r+1 is even), hence 3*r is odd, so 3*r+1 is even
  have h2_dvd_3r1 : 2 ∣ 3 * r + 1 := by
    have h2_dvd_r1 : 2 ∣ r + 1 := by
      -- 2^(factorization) ∣ r+1  ⇒ in particular 2 ∣ r+1
      have : (2 : ℕ) ^ ((r + 1).factorization 2) ∣ r + 1 := Nat.ordProj_dvd (r + 1) 2
      -- t ≥ 1 since t ≥ 3, so 2 ∣ 2^t and hence 2 ∣ r+1
      rcases this with ⟨m, hm⟩
      -- exhibit a witness for 2 ∣ r+1:
      have ht1 : 1 ≤ t := le_trans (by decide : (1 : ℕ) ≤ 3) ht
      -- 2^t = 2 * 2^(t-1)
      have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
        calc 2 ^ t
            = 2 ^ ((t - 1) + 1) := by rw [tsub_add_cancel_iff_le.mpr ht1]
          _ = 2 ^ (t - 1) * 2 ^ 1 := by rw [pow_add]
          _ = 2 ^ (t - 1) * 2 := by rw [pow_one]
          _ = 2 * 2 ^ (t - 1) := by ring
      -- Now r+1 = 2^t * m = 2 * (2^(t-1) * m)
      refine ⟨(2 ^ (t - 1)) * m, ?_⟩
      rw [hm, hfac, hpow]
      ring
    -- r+1 even ⇒ ¬Even r ⇒ r odd
    have hr_odd : Odd r := by
      have hr1_even : Even (r + 1) := even_iff_two_dvd.2 h2_dvd_r1
      -- Use: ¬Odd (r+1) ↔ Even (r+1), so Odd (r+1) is false
      -- And: Even n ↔ Odd (n+1) doesn't hold, but we can use Even (n+1) → ¬Even n
      by_contra h_not_odd
      -- If r is not odd, then r is even
      have hr_even : Even r := Nat.not_odd_iff_even.1 h_not_odd
      -- Then r+1 is odd
      have : Odd (r + 1) := hr_even.add_odd odd_one
      -- But we know r+1 is even, contradiction
      have : ¬Odd (r + 1) := Nat.not_odd_iff_even.2 hr1_even
      exact this ‹Odd (r + 1)›
    -- odd * odd is odd; odd + 1 is even
    have h3r_odd : Odd (3 * r) := by
      have h3odd : Odd (3 : ℕ) := by decide
      exact Nat.odd_mul.2 ⟨h3odd, hr_odd⟩
    exact even_iff_two_dvd.1 (h3r_odd.add_odd odd_one)

  -- Define r' and derive the key equality 2 * (r' + 1) = 3 * (r + 1)
  refine ⟨(3 * r + 1) / 2, rfl, ?_⟩
  set r' : ℕ := (3 * r + 1) / 2 with hr'
  have hmul1 : 2 * ((3 * r + 1) / 2) = 3 * r + 1 := Nat.mul_div_cancel' h2_dvd_3r1
  have hkey : 2 * (r' + 1) = 3 * (r + 1) := by
    -- From hmul1: 2 * r' = 3r + 1
    -- Add 2 to both sides: 2*r' + 2 = 3r + 3
    -- Factor: 2*(r'+1) = 3*(r+1)
    calc 2 * (r' + 1)
        = 2 * r' + 2 := by ring
      _ = (3 * r + 1) + 2 := by rw [hr', hmul1]
      _ = 3 * r + 3 := by ring
      _ = 3 * (r + 1) := by ring

  -- factorization at 2 on both sides of hkey
  have hrp1_ne0 : r' + 1 ≠ 0 := by
    -- Right-hand side is positive ⇒ left-hand side nonzero ⇒ r'+1 ≠ 0
    have h3r1 : 0 < 3 * (r + 1) := by
      have : 0 < r + 1 := Nat.succ_pos _
      exact Nat.mul_pos (by decide : 0 < 3) this
    have h2rp : 0 < 2 * (r' + 1) := by rw [hkey]; exact h3r1
    omega

  -- expand factorization at prime 2 on both sides
  have hL :
      (2 * (r' + 1)).factorization 2
        = (2 ^ 1).factorization 2 + (r' + 1).factorization 2 := by
    -- (a*b).factorization = a.factorization + b.factorization, then project at 2
    have h2pos : (2 ^ 1) ≠ 0 := by decide
    have hmul := Nat.factorization_mul h2pos hrp1_ne0
    -- evaluate both sides at prime 2
    exact congrArg (fun f => f 2) hmul

  have hR :
      (3 * (r + 1)).factorization 2
        = (3).factorization 2 + (r + 1).factorization 2 := by
    have h3ne : (3 : ℕ) ≠ 0 := by decide
    have hr1ne : r + 1 ≠ 0 := Nat.succ_ne_zero _
    have hmul := Nat.factorization_mul h3ne hr1ne
    have := congrArg (fun f => f 2) hmul
    simp

  -- compute constants at the prime 2
  have h2pow : (2 ^ 1).factorization 2 = 1 := by
    -- prime power factorization: (2^k).factorization = single 2 k, project at 2
    have h := @Nat.Prime.factorization_pow 2 1 Nat.prime_two
    have := congrArg (fun f => f 2) h
    simp [pow_one, Finsupp.single_eq_same] at this
    exact this

  have h3fac0 : (3).factorization 2 = 0 := by
    have : ¬ 2 ∣ (3 : ℕ) := by decide
    exact Nat.factorization_eq_zero_of_not_dvd this

  -- finally, compare both sides via hkey
  have h_sum : (r' + 1).factorization 2 + 1 = t := by
    have h_eq : (2 * (r' + 1)).factorization 2 = (3 * (r + 1)).factorization 2 := by
      rw [hkey]
    -- expand both sides, plug constants, and use hfac
    calc (r' + 1).factorization 2 + 1
        = (2 ^ 1).factorization 2 + (r' + 1).factorization 2 := by rw [h2pow]; ring
      _ = (2 * (r' + 1)).factorization 2 := by rw [hL]
      _ = (3 * (r + 1)).factorization 2 := h_eq
      _ = (3).factorization 2 + (r + 1).factorization 2 := hR
      _ = 0 + t := by rw [h3fac0, hfac]
      _ = t := by ring

  -- Nat arithmetic: a + 1 = t  ⇒  a = t - 1
  have h_depth : (r' + 1).factorization 2 = t - 1 := by
    have h1le : 1 ≤ t := le_trans (by decide : (1 : ℕ) ≤ 3) ht
    omega

  show depth_minus r' = t - 1
  rw [depth_minus, hr']
  exact h_depth

/-- One-bit bonus: wrapper lemma for compatibility -/
lemma touch_multibit_bonus (r : ℕ) (t : ℕ) (ht : t ≥ 3)
  (h_touch : depth_minus r = t) :
  ∃ (r' : ℕ),
    r' = (3 * r + 1) / 2 ∧
    depth_minus r' = t - 1 := by
  exact touch_provides_onebit_bonus r t ht h_touch

/-!
## Epoch Decomposition Lemmas
-/

/-- Standard fact: exponential growth dominates linear for t ≥ 3

    This is a well-known inequality: 2t ≤ 2^t for t ≥ 3.
    Proven by strong induction on t.
-/
lemma two_mul_le_two_pow (t : ℕ) (ht : t ≥ 3) : 2 * t ≤ 2^t := by
  -- Base cases: t = 3, 4, 5
  match t with
  | 0 | 1 | 2 => omega  -- contradicts ht : t ≥ 3
  | 3 => norm_num  -- 6 ≤ 8
  | 4 => norm_num  -- 8 ≤ 16
  | 5 => norm_num  -- 10 ≤ 32
  | t' + 6 =>
    -- Inductive step: assume for t' + 5, prove for t' + 6
    -- Need: 2(t'+6) ≤ 2^(t'+6)
    -- From IH: 2(t'+5) ≤ 2^(t'+5)
    have ih : 2 * (t' + 5) ≤ 2^(t' + 5) := two_mul_le_two_pow (t' + 5) (by omega)
    calc 2 * (t' + 6)
        = 2 * (t' + 5) + 2 := by ring
      _ ≤ 2^(t' + 5) + 2 := by linarith [ih]
      _ ≤ 2^(t' + 5) + 2^(t' + 5) := by
          have : 2 ≤ 2^(t' + 5) := by
            have : 2^1 ≤ 2^(t' + 5) := Nat.pow_le_pow_right (by decide) (by omega)
            simpa using this
          linarith
      _ = 2 * 2^(t' + 5) := by ring
      _ = 2^(t' + 6) := by
          rw [show t' + 6 = (t' + 5) + 1 by omega]
          rw [pow_succ]
          ring

/-- Helper: For t ≥ 8, we have 3t ≤ 2^t -/
private lemma three_mul_le_two_pow_of_ge8 (t : ℕ) (ht : 8 ≤ t) : 3 * t ≤ 2^t := by
  -- Induction on n ≥ 8
  induction t, ht using Nat.le_induction with
  | base => decide  -- 3*8 = 24 ≤ 256 = 2^8
  | succ n hn ih =>
    -- step: from IH at n prove for n+1
    -- Show 3 ≤ 2^n using 8 ≤ 2^n (and 3 ≤ 8)
    have h3le : 3 ≤ 2^n := by
      have h3n : 3 ≤ n := le_trans (by decide : 3 ≤ 8) hn
      have h8le : 2^3 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) h3n
      calc 3
          ≤ 8 := by decide
        _ = 2^3 := by decide
        _ ≤ 2^n := h8le
    calc
      3 * (n+1) = 3*n + 3 := by ring
      _ ≤ 2^n + 3 := add_le_add_right ih 3
      _ ≤ 2^n + 2^n := add_le_add_left h3le _
      _ = 2 * 2^n := by ring
      _ = 2^(n+1) := by rw [pow_succ]; ring

/-- Helper: For t ≥ 2, we have 2·2^{t-2} ≤ 2^t -/
private lemma two_mul_pow_sub_two_le_pow (t : ℕ) (ht : 2 ≤ t) : 2 * 2^(t-2) ≤ 2^t := by
  -- 2 * 2^(t-2) ≤ 4 * 2^(t-2) = 2^(t-2) * 2^2 = 2^(t-2+2) = 2^t
  have step : 2 * 2^(t-2) ≤ 4 * 2^(t-2) :=
    Nat.mul_le_mul_right (2^(t-2)) (by decide : 2 ≤ 4)
  have heq : 2^(t-2+2) = 2^t := by
    -- t-2+2 = t for t ≥ 2
    have h := Nat.sub_add_cancel ht
    rw [h]
  calc 2 * 2^(t-2)
      ≤ 4 * 2^(t-2) := step
    _ = 2^2 * 2^(t-2) := by ring
    _ = 2^(2 + (t-2)) := by rw [← pow_add]
    _ = 2^(t-2+2) := by ring
    _ = 2^t := heq

/-- Standard fact: K_glue bound for t ≥ 4

    max(2·2^{t-2}, 3t) ≤ 2^t for t ≥ 4.

    Note: For t=3, max(4, 9) = 9 > 8, so this fails!
    The bound holds starting from t=4.

    Proven by explicit cases for t ∈ {4,5,6,7} and induction for t ≥ 8.
-/
lemma max_K_glue_le_pow_two (t : ℕ) (ht : t ≥ 4) : max (2 * 2^(t-2)) (3*t) ≤ 2^t := by
  -- Split: small cases (4,5,6,7) vs. tail (t ≥ 8)
  by_cases hlt8 : t < 8
  · -- Small cases: 4 ≤ t < 8
    -- Pattern match on the four cases
    match t, ht, hlt8 with
    | 4, _, _ => norm_num  -- max(8, 12) = 12 ≤ 16
    | 5, _, _ => norm_num  -- max(16, 15) = 16 ≤ 32
    | 6, _, _ => norm_num  -- max(32, 18) = 32 ≤ 64
    | 7, _, _ => norm_num  -- max(64, 21) = 64 ≤ 128
  · -- Tail: t ≥ 8
    have ht8 : 8 ≤ t := le_of_not_gt hlt8
    have h1 : 2 * 2^(t-2) ≤ 2^t :=
      two_mul_pow_sub_two_le_pow t (le_trans (by decide : 2 ≤ 4) ht)
    have h2 : 3 * t ≤ 2^t := three_mul_le_two_pow_of_ge8 t ht8
    exact (max_le_iff.mpr ⟨h1, h2⟩)

/-- Technical bound: t·log₂(3/2) ≤ β·(2^t + 3U) for β ≥ 1, t ≥ 3, U ≥ 1 (PROVEN LEMMA)

    PROOF STRATEGY:
    1. log₂(3/2) < 1 (since 3/2 < 2)
    2. Therefore: t·log₂(3/2) < t
    3. For t ≥ 3: t < 2^t (exponential dominates linear)
    4. For U ≥ 1: 2^t < 2^t + 3U
    5. For β ≥ 1: 2^t + 3U ≤ β·(2^t + 3U)
    6. Chain: t·log₂(3/2) < 2^t + 3U ≤ β·(2^t + 3U)
-/
lemma t_log_bound_for_sedt (t U : ℕ) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β ≥ 1) :
  (t : ℝ) * log (3/2) / log 2 ≤ β * ((2^t : ℝ) + (3*U : ℝ)) := by
  -- Key constants
  have h_log_ratio : log (3/2) / log 2 < 1 := by
    have h1 : log (3/2) < log 2 := by
      apply Real.log_lt_log
      · norm_num
      · norm_num
    have h2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    calc log (3/2) / log 2
        < log 2 / log 2 := by exact div_lt_div_of_pos_right h1 h2
      _ = 1 := by field_simp

  -- Step 1: t·log₂(3/2) < t
  have h_tlog_lt_t : (t : ℝ) * log (3/2) / log 2 < (t : ℝ) := by
    calc (t : ℝ) * log (3/2) / log 2
        = (t : ℝ) * (log (3/2) / log 2) := by ring
      _ < (t : ℝ) * 1 := by
          apply mul_lt_mul_of_pos_left h_log_ratio
          exact Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 3) ht)
      _ = (t : ℝ) := by ring

  -- Step 2: t < 2^t for t ≥ 3
  have h_t_lt_pow : (t : ℝ) < (2^t : ℝ) := by
    have h_nat : t < 2^t := by
      -- Use induction or direct verification
      match t with
      | 0 | 1 | 2 => omega  -- contradicts ht
      | 3 => norm_num  -- 3 < 8
      | 4 => norm_num  -- 4 < 16
      | t' + 5 =>
        -- For t ≥ 5: use 2t ≤ 2^t (proven lemma) and t < 2t
        have h1 : 2 * (t' + 5) ≤ 2^(t' + 5) := two_mul_le_two_pow (t' + 5) (by omega)
        calc t' + 5
            < 2 * (t' + 5) := by omega
          _ ≤ 2^(t' + 5) := h1
    exact_mod_cast h_nat

  -- Step 3: 2^t < 2^t + 3U for U ≥ 1
  have h_pow_lt_sum : (2^t : ℝ) < (2^t : ℝ) + (3*U : ℝ) := by
    have h_U_pos : 0 < (3*U : ℝ) := by
      have : 0 < U := Nat.pos_of_ne_zero (fun h => by omega)
      have : 0 < 3 * U := Nat.mul_pos (by decide) this
      positivity
    linarith

  -- Step 4: Combine with β ≥ 1 and convert < to ≤
  have h_sum_pos : 0 < (2^t : ℝ) + (3*U : ℝ) := by linarith [h_pow_lt_sum]
  have h_intermediate : (2^t : ℝ) + (3*U : ℝ) ≤ β * ((2^t : ℝ) + (3*U : ℝ)) := by
    calc (2^t : ℝ) + (3*U : ℝ)
        = 1 * ((2^t : ℝ) + (3*U : ℝ)) := by ring
      _ ≤ β * ((2^t : ℝ) + (3*U : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hβ (le_of_lt h_sum_pos)

  -- Chain all inequalities, convert final < to ≤
  have h_strict : (t : ℝ) * log (3/2) / log 2 < β * ((2^t : ℝ) + (3*U : ℝ)) := by
    calc (t : ℝ) * log (3/2) / log 2
        < (t : ℝ) := h_tlog_lt_t
      _ < (2^t : ℝ) := h_t_lt_pow
      _ < (2^t : ℝ) + (3*U : ℝ) := h_pow_lt_sum
      _ ≤ β * ((2^t : ℝ) + (3*U : ℝ)) := h_intermediate
  exact le_of_lt h_strict

/-- Technical bound: overhead collection for SEDT (PROVEN LEMMA)

    Sum of head, K_glue, and log terms is bounded by β·C(t,U).

    PROOF STRATEGY (from expert - Anatoliy):
    Key insight: Route log term to 3t-bucket, NOT to 2^t-bucket!

    1. log₂(3/2) ≤ 1 → t·log₂(3/2) ≤ t ≤ 3t ≤ β·3t (for β ≥ 1)
    2. For t ≥ 4: K_glue ≤ 2^t → β·2^t + β·K_glue ≤ β·2·2^t
    3. For t = 3: β·8 + β·9 + 3·log ≤ β·26 ≤ β·(16+9+3U)
    4. Combine: all terms fit into β·(2·2^t + 3t + 3U)

    Reference: Expert solution 2025-10-03 (Anatoliy)
-/
lemma sedt_overhead_bound (t U : ℕ) (β : ℝ) (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β ≥ 1) :
  β * (2^t : ℝ) + β * ((max (2 * 2^(t-2)) (3*t)) : ℝ) + (t : ℝ) * log (3/2) / log 2
  ≤ β * (3 * (2^t : ℝ) + 3 * (U : ℝ)) := by
  -- Use by_cases to handle different t ranges
  by_cases h4 : 4 ≤ t
  · -- main branch (t ≥ 4)
    have h : 3 ≤ t := le_trans (by decide : 3 ≤ 4) h4
    -- Basic facts from hU for ℕ↔ℝ bridges
    have hUposN : 0 < U := Nat.succ_le_iff.mp hU
    have hUpos  : 0 < (U : ℝ) := by exact_mod_cast hUposN
    have hUge1  : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
    -- Use t_log_bound_for_sedt and bounds for max term
    have h_log_bound := t_log_bound_for_sedt t U β ht hU hβ
    have h_max_bound : (max (2 * 2^(t-2)) (3*t) : ℝ) ≤ (2^t : ℝ) :=
      by exact_mod_cast max_K_glue_le_pow_two t h4
    -- Combine bounds
    calc β * 2 ^ t + β * max (2 * 2 ^ (t - 2)) (3 * (t : ℝ)) + (t : ℝ) * log (3 / 2) / log 2
        ≤ β * 2 ^ t + β * 2 ^ t + β * ((2^t : ℝ) + (3*U : ℝ)) := by
          apply add_le_add
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_left h_max_bound
          -- β ≥ 1 implies β > 0
          have hβpos : 0 < β := by
            have : (1 : ℝ) ≤ β := hβ
            linarith
          exact le_of_lt hβpos
          exact h_log_bound
        _ = β * (2 * 2^t + 2^t + 3*U) := by ring
        _ = β * (3 * 2^t + 3*U) := by ring
  · -- small t: t = 3 (since ht : t ≥ 3 and h4 : ¬4 ≤ t)
    have : t = 3 := by omega
    subst this
    simp
    -- Use an elementary bound for t=3: control log term by β·3U
    have hβ_nonneg : 0 ≤ β := le_trans (by norm_num : (0 : ℝ) ≤ 1) hβ
    have hUge1  : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
    have h_max_eval : (max (2 * 2) (3 * 3) : ℝ) = (9 : ℝ) := by norm_num
    -- 3·log₂(3/2) ≤ 3 ≤ β·3U
    have h_log_le_beta3U : 3 * (log (3 / 2) / log 2) ≤ β * (3 * (U : ℝ)) := by
      -- first: 3 * (log(3/2)/log 2) ≤ 3 since log₂(3/2) ≤ 1
      have h1 : log (3/2) / log 2 ≤ (log 2) / log 2 := by
        apply div_le_div_of_nonneg_right
        · apply Real.log_le_log
          · have : (0 : ℝ) < (3/2 : ℝ) := by norm_num
            exact this
          · have : (3/2 : ℝ) ≤ (2 : ℝ) := by norm_num
            exact this
        · exact le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      have h1' : 3 * (log (3/2) / log 2) ≤ 3 := by
        have h1_simplified : log (3/2) / log 2 ≤ 1 := by
          rw [div_le_one (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
          -- log (3/2) ≤ log 2 since 3/2 ≤ 2
          have : log (3/2) ≤ log 2 := by
            apply Real.log_le_log
            · norm_num
            · norm_num
          exact this
        have : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
        have := mul_le_mul_of_nonneg_left h1_simplified this
        simpa [mul_one] using this
      -- next: 3 ≤ β·3U since U ≥ 1 and β ≥ 1
      have h2 : (3 : ℝ) ≤ (3 : ℝ) * (U : ℝ) := by
        have : (1 : ℝ) ≤ (U : ℝ) := hUge1
        have h3nonneg : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
        have := mul_le_mul_of_nonneg_left this h3nonneg
        simpa [mul_one] using this
      have h3 : (3 : ℝ) * (U : ℝ) ≤ β * (3 : ℝ) * (U : ℝ) := by
        have hU_nonneg : (0 : ℝ) ≤ (U : ℝ) := by exact_mod_cast (Nat.zero_le U)
        have h3U_nonneg : (0 : ℝ) ≤ (3 : ℝ) * (U : ℝ) := by
          exact mul_nonneg (by norm_num) hU_nonneg
        have := mul_le_mul_of_nonneg_left hβ h3U_nonneg
        simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using this
      have h3' : (3 : ℝ) * (U : ℝ) ≤ β * ((3 : ℝ) * (U : ℝ)) := by
        rw [mul_assoc] at h3
        exact h3
      exact le_trans h1' (le_trans h2 h3')
    -- conclude by packing terms into β·(3·2^3 + 3U) = β·(24 + 3U)
    calc
      β * 2 ^ 3 + β * max (2 * 2) (3 * 3) + 3 * log (3 / 2) / log 2
          = β * 8 + β * 9 + 3 * (log (3 / 2) / log 2) := by
              rw [h_max_eval, mul_div_assoc]; norm_num
      _ ≤ β * 8 + β * 9 + β * (3 * (U : ℝ)) := by
            apply add_le_add (add_le_add le_rfl le_rfl) h_log_le_beta3U
      _ = β * (17 + 3 * (U : ℝ)) := by ring
      _ ≤ β * (24 + 3 * (U : ℝ)) := by
            have : (17 : ℝ) ≤ 24 := by norm_num
            exact mul_le_mul_of_nonneg_left (by simpa [add_le_add_iff_right] using this) hβ_nonneg
      _ ≤ β * (3 * 2^3 + 3 * (U : ℝ)) := by
            -- 24 = 3 * 2^3, so this is equality
            have : (24 : ℝ) = 3 * (2^3 : ℝ) := by norm_num
            rw [this]


/-- Technical bound: full SEDT bound combination (PROVEN LEMMA)

    Direct statement combining head, plateau, and boundary bounds into the final inequality.
    This encapsulates all technical details of overhead arithmetic.

    PROOF STRATEGY:
    1. Use SMT-verified sedt_overhead_bound axiom
    2. Apply abs bounds: |x| ≤ y → -y ≤ x ≤ y
    3. Collect all terms and apply linarith
-/
lemma sedt_full_bound_technical (t U : ℕ) (β ΔV_head drift_per_step ΔV_boundary : ℝ) (length : ℕ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β ≥ 1) :
  (abs ΔV_head ≤ β * (2^t : ℝ) + (t : ℝ) * log (3/2) / log 2) →
  (drift_per_step ≤ -(ε t U β)) →
  (abs ΔV_boundary ≤ β * (K_glue t : ℝ)) →
  ΔV_head + drift_per_step * (length : ℝ) + ΔV_boundary ≤
    -(ε t U β) * (length : ℝ) + β * (3 * (2^t : ℝ) + 3 * (U : ℝ)) := by
  intro h_head_bound h_drift_bound h_boundary_bound

  -- Get the proven overhead bound (requires β ≥ 1)
  have h_overhead := sedt_overhead_bound t U β ht hU hβ

  -- Bridge: β·K_glue ≤ β·max(2·2^{t-2}, 3t)
  have hK_nat : K_glue t ≤ max (2 * 2^(t-2)) (3*t) := by
    by_cases h : 3 ≤ t
    · -- for t ≥ 3, K_glue = 2·2^{t-2} ≤ max(…)
      -- Prefer simp to satisfy linter
      simp [K_glue, Q_t, h]
    · -- small t = 0,1,2
      interval_cases t

  have hβ_nonneg : 0 ≤ β := le_trans (by norm_num : (0 : ℝ) ≤ 1) hβ

  have hK_le : β * (K_glue t : ℝ) ≤ β * (max (2 * 2^(t-2)) (3*t) : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hK_nat) hβ_nonneg

  -- Complete the final bound
  calc ΔV_head + drift_per_step * (length : ℝ) + ΔV_boundary
      ≤ (β * (2^t : ℝ) + (t : ℝ) * log (3/2) / log 2) +
        (-(ε t U β) * (length : ℝ)) +
        β * (K_glue t : ℝ) := by
          apply add_le_add (add_le_add (le_of_abs_le h_head_bound)
            (mul_le_mul_of_nonneg_right h_drift_bound (Nat.cast_nonneg _)))
            (le_of_abs_le h_boundary_bound)
    _ ≤ (β * (2^t : ℝ) + (t : ℝ) * log (3/2) / log 2) +
        (-(ε t U β) * (length : ℝ)) +
        β * (max (2 * 2^(t-2)) (3*t) : ℝ) := by
          -- strengthen K_glue to max via hK_le
          apply add_le_add (add_le_add le_rfl le_rfl) hK_le
    _ = -(ε t U β) * (length : ℝ) +
        (β * (2^t : ℝ) + β * (max (2 * 2^(t-2)) (3*t) : ℝ) + (t : ℝ) * log (3/2) / log 2) := by
          ring
    _ ≤ -(ε t U β) * (length : ℝ) + β * (3 * (2^t : ℝ) + 3 * (U : ℝ)) := by
          apply add_le_add_left h_overhead

end Collatz.SEDT
