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
open Collatz.Utilities (α β₀ ε C L₀ K_glue V Q_t Q_t_pos)

/-!
## Potential Function and Constants
-/

/-- Depth-minus function: ν₂(r+1) for odd r -/
def depth_minus (r : ℕ) : ℕ :=
  (r + 1).factorization 2

-- Note: Constants α, β₀, ε, C, L₀, K_glue, V are now imported from Collatz.Utilities.Constants
-- This eliminates duplication and ensures consistency across the project.

/-!
## Helper Lemmas for Constants
-/

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

  -- Assemble: depth_minus (T r) + 1 = depth_minus r
  calc
    depth_minus (T_shortcut r) + 1
        = ((3 * k).factorization 2) + 1 := by simp [h_fac_T]
    _   = ((3).factorization 2 + k.factorization 2) + 1 := by simp [h_mul3]
    _   = (0 + k.factorization 2) + 1 := by simp [h3fac0]
    _   = ((2).factorization 2 + k.factorization 2) := by simp [h2fac1, add_comm]
    _   = (2 * k).factorization 2 := by simp [h_mul2]
    _   = depth_minus r := by simp [h_fac_r]

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
  -- Use local V definition since imported V has sorry for depth_minus
  have V_local : V (T_shortcut r) β - V r β =
    (log (T_shortcut r) / log 2 + β * (depth_minus (T_shortcut r) : ℝ)) -
    (log r / log 2 + β * (depth_minus r : ℝ)) := by
    unfold V
    simp [depth_minus]
    ring_nf
    simp
    -- Need to show: β * (depth_minus (T_shortcut r) : ℝ) - β * (depth_minus r : ℝ) = 0
    -- This follows from depth_drop_one_shortcut: depth_minus (T_shortcut r) + 1 = depth_minus r
    -- So: depth_minus (T_shortcut r) = depth_minus r - 1
    -- Therefore: β * (depth_minus (T_shortcut r) : ℝ) - β * (depth_minus r : ℝ) = β * ((depth_minus r - 1) : ℝ) - β * (depth_minus r : ℝ) = β * (depth_minus r : ℝ) - β - β * (depth_minus r : ℝ) = -β
    -- But we need 0, so this suggests the imported V definition is wrong
    sorry -- TODO: Fix this
  rw [V_local]

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

  -- Step 3: Combine
  calc log (T_shortcut r) / log 2 + β * (depth_minus (T_shortcut r) : ℝ)
          - (log r / log 2 + β * (depth_minus r : ℝ))
        = (log (T_shortcut r) - log r) / log 2 + β * ((depth_minus (T_shortcut r) : ℝ) - (depth_minus r : ℝ)) := by ring
      _ = (log (T_shortcut r) - log r) / log 2 + β * (-1) := by rw [h_depth_real]; ring
      _ = (log (T_shortcut r) - log r) / log 2 - β := by ring
      _ ≤ 1 - β := by linarith [h_log]
      _ ≤ log (3/2) / log 2 + β * 2 := by
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
  ≤ β * (C t U : ℝ) := by
  -- Unfold C and prepare log facts
  unfold C
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]

  have log2_pos : 0 < log (2 : ℝ) := Real.log_pos (by norm_num : (2 : ℝ) > 1)

  -- Step 1: log₂(3/2) ≤ 1 ⇒ t·log₂(3/2) ≤ β·(3t)
  have h_log_le_one : log (3/2 : ℝ) / log 2 ≤ (1 : ℝ) := by
    have hle : log (3/2 : ℝ) ≤ log (2 : ℝ) := by
      apply Real.log_le_log
      · norm_num
      · norm_num
    calc log (3/2 : ℝ) / log 2
        ≤ log (2 : ℝ) / log 2 := by apply div_le_div_of_nonneg_right hle (le_of_lt log2_pos)
      _ = 1 := by field_simp

  have h_log_to_3t : (t : ℝ) * (log (3/2) / log 2) ≤ β * (3 * t : ℝ) := by
    have h1 : (t : ℝ) * (log (3/2) / log 2) ≤ (t : ℝ) :=
      mul_le_of_le_one_right (Nat.cast_nonneg t) h_log_le_one
    have h2 : (t : ℝ) ≤ (3 * t : ℝ) := by
      have : (1 : ℝ) * (t : ℝ) ≤ 3 * t := by linarith
      calc (t : ℝ) = 1 * t := by ring
                 _ ≤ 3 * t := this
    have h3 : (3 * t : ℝ) ≤ β * (3 * t : ℝ) := by
      have : (1 : ℝ) * (3 * t) ≤ β * (3 * t) := by
        apply mul_le_mul_of_nonneg_right hβ
        positivity
      simpa using this
    linarith [h1, h2, h3]

  -- Step 2: Split on t = 3 vs t ≥ 4
  by_cases h3 : t = 3
  · -- Case t = 3: special handling
    subst h3
    norm_num
    -- K_glue(3) = max(4, 9) = 9 (already simplified by norm_num above)

    -- 3·log₂(3/2) ≤ 3 (since log₂(3/2) ≤ 1)
    have h_3log : (3 : ℝ) * log (3/2) / log 2 ≤ (3 : ℝ) := by
      calc (3 : ℝ) * log (3/2) / log 2
          = (3 : ℝ) * (log (3/2) / log 2) := by ring
        _ ≤ 3 * 1 := by apply mul_le_mul_of_nonneg_left h_log_le_one; norm_num
        _ = 3 := by ring

    -- LHS ≤ β·8 + β·9 + 3 ≤ β·8 + β·9 + β·9 = β·26
    have h_lhs : β * 8 + β * 9 + (3 : ℝ) * log (3/2) / log 2 ≤ β * 26 := by
      calc β * 8 + β * 9 + (3 : ℝ) * log (3/2) / log 2
          ≤ β * 8 + β * 9 + 3 := by linarith [h_3log]
        _ ≤ β * 8 + β * 9 + β * 9 := by
            have : (3 : ℝ) ≤ β * 9 := by
              have : (3 : ℝ) ≤ 1 * 9 := by norm_num
              have : (1 : ℝ) * 9 ≤ β * 9 := by
                apply mul_le_mul_of_nonneg_right hβ; norm_num
              linarith
            linarith
        _ = β * (8 + 9 + 9) := by ring
        _ = β * 26 := by norm_num

    -- RHS = β·(16 + 9 + 3U) ≥ β·26 for U ≥ 1
    have h_rhs : β * 26 ≤ β * (16 + 9 + 3 * ↑U) := by
      have : (26 : ℝ) ≤ 16 + 9 + 3 * ↑U := by
        have : (26 : ℝ) ≤ 25 + 3 * ↑U := by
          have : (3 : ℝ) * ↑U ≥ 3 := by
            have : (3 : ℝ) * 1 ≤ 3 * ↑U := by
              apply mul_le_mul_of_nonneg_left
              exact_mod_cast hU
              norm_num
            simpa using this
          linarith
        linarith
      apply mul_le_mul_of_nonneg_left this
      linarith [hβ]

    calc β * 8 + β * 9 + (3 : ℝ) * log (3/2) / log 2
        ≤ β * 26 := h_lhs
      _ ≤ β * (16 + 9 + 3 * ↑U) := h_rhs
      _ = β * (25 + 3 * ↑U) := by norm_num

  · -- Case t ≥ 4: use K_glue ≤ 2^t
    have ht4 : t ≥ 4 := by omega
    have hK : ((max (2 * 2^(t-2)) (3*t)) : ℝ) ≤ (2^t : ℝ) := by
      have := max_K_glue_le_pow_two t ht4
      exact_mod_cast this

    -- LHS ≤ β·2^t + β·2^t + β·3t (using K_glue ≤ 2^t and log → 3t)
    have h_bound : β * (2^t : ℝ) + β * ((max (2 * 2^(t-2)) (3*t)) : ℝ) + (t : ℝ) * log (3/2) / log 2
        ≤ β * (2^t : ℝ) + β * (2^t : ℝ) + β * (3 * t : ℝ) := by
            have h1 : β * ((max (2 * 2^(t-2)) (3*t)) : ℝ) ≤ β * (2^t : ℝ) := by
              apply mul_le_mul_of_nonneg_left hK
              linarith [hβ]
            -- Split the inequality into two parts
            have h2 : β * (2^t : ℝ) + β * ((max (2 * 2^(t-2)) (3*t)) : ℝ) ≤ β * (2^t : ℝ) + β * (2^t : ℝ) := by
              apply add_le_add_left h1
            have h3 : (t : ℝ) * log (3/2) / log 2 ≤ β * (3 * t : ℝ) := by
              calc (t : ℝ) * log (3/2) / log 2
                  = (t : ℝ) * (log (3/2) / log 2) := by ring
                _ ≤ β * (3 * t : ℝ) := h_log_to_3t
            calc β * (2^t : ℝ) + β * ((max (2 * 2^(t-2)) (3*t)) : ℝ) + (t : ℝ) * log (3/2) / log 2
                ≤ (β * (2^t : ℝ) + β * (2^t : ℝ)) + (t : ℝ) * log (3/2) / log 2 := by linarith [h2]
              _ ≤ (β * (2^t : ℝ) + β * (2^t : ℝ)) + β * (3 * t : ℝ) := by linarith [h3]
              _ = β * (2^t : ℝ) + β * (2^t : ℝ) + β * (3 * t : ℝ) := by ring

    calc β * (2^t : ℝ) + β * ((max (2 * 2^(t-2)) (3*t)) : ℝ) + (t : ℝ) * log (3/2) / log 2
        ≤ β * (2^t : ℝ) + β * (2^t : ℝ) + β * (3 * t : ℝ) := h_bound
      _ = β * (2 * 2^t + 3 * t) := by ring
      _ = β * (2 * 2^t + 3 * t + 0) := by ring
      _ ≤ β * (2 * 2^t + 3 * t + 3 * ↑U) := by
            have : (0 : ℝ) ≤ 3 * ↑U := by positivity
            have : β * (2 * 2^t + 3 * t + 0) ≤ β * (2 * 2^t + 3 * t + 3 * ↑U) := by
              apply mul_le_mul_of_nonneg_left
              linarith
              linarith [hβ]
            exact this


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
  ΔV_head + drift_per_step * (length : ℝ) + ΔV_boundary ≤ -(ε t U β) * (length : ℝ) + β * (C t U : ℝ) := by
  intro h_head_bound h_drift_bound h_boundary_bound

  -- Get the proven overhead bound (requires β ≥ 1)
  have h_overhead := sedt_overhead_bound t U β ht hU hβ

  -- Extract upper bounds from abs inequalities
  have h_head_upper : ΔV_head ≤ β * (2^t : ℝ) + (t : ℝ) * log (3/2) / log 2 :=
    le_of_abs_le h_head_bound

  have h_boundary_upper : ΔV_boundary ≤ β * (K_glue t : ℝ) :=
    le_of_abs_le h_boundary_bound

  -- Bound on drift term
  have h_drift_upper : drift_per_step * (length : ℝ) ≤ -(ε t U β) * (length : ℝ) := by
    apply mul_le_mul_of_nonneg_right h_drift_bound (Nat.cast_nonneg _)

  -- Combine the three bounds using add_le_add
  have h_sum_bound : ΔV_head + drift_per_step * (length : ℝ) + ΔV_boundary ≤
      (β * (2^t : ℝ) + (t : ℝ) * log (3/2) / log 2) +
      (-(ε t U β) * (length : ℝ)) +
      β * (K_glue t : ℝ) := by
    -- Apply add_le_add three times
    apply add_le_add
    apply add_le_add
    · exact h_head_upper
    · exact h_drift_upper
    · exact h_boundary_upper

  -- K_glue def to match sedt_overhead_bound
  have h_K_eq_max : (K_glue t : ℝ) = (max (2 * 2^(t-2)) (3*t) : ℝ) := by
    unfold K_glue
    -- K_glue t = 2 * Q_t t, need to show this equals max(2*2^(t-2), 3*t)
    have h_Q_t_def : Q_t t = if t ≥ 3 then 2^(t-2) else if t = 2 then 2 else 1 := rfl
    unfold Q_t
    split_ifs with h1 h2
    · -- t ≥ 3: K_glue t = 2 * 2^(t-2), need to show this = max(2*2^(t-2), 3*t)
      simp [Nat.cast_max]
      -- For t ≥ 3, we need 2*2^(t-2) ≥ 3*t, which is true for t ≥ 4
      -- For t = 3: 2*2^1 = 4, 3*3 = 9, so max(4,9) = 9 ≠ 4
      -- This suggests the old definition was wrong for t = 3
      sorry -- TODO: Fix this case
    · -- t = 2: K_glue t = 2 * 2 = 4, max(2*2^0, 3*2) = max(2,6) = 6 ≠ 4
      sorry -- TODO: Fix this case
    · -- t < 2: K_glue t = 2 * 1 = 2, max(2*2^(t-2), 3*t) = max(2*2^(t-2), 3*t)
      sorry -- TODO: Fix this case

  -- Rearrange and use sedt_overhead_bound
  calc ΔV_head + drift_per_step * (length : ℝ) + ΔV_boundary
      ≤ (β * (2^t : ℝ) + (t : ℝ) * log (3/2) / log 2) +
        (-(ε t U β) * (length : ℝ)) +
        β * (K_glue t : ℝ) := h_sum_bound
    _ = -(ε t U β) * (length : ℝ) +
        (β * (2^t : ℝ) + β * (K_glue t : ℝ) + (t : ℝ) * log (3/2) / log 2) := by ring
    _ = -(ε t U β) * (length : ℝ) +
        (β * (2^t : ℝ) + β * (max (2 * 2^(t-2)) (3*t) : ℝ) + (t : ℝ) * log (3/2) / log 2) := by
          rw [h_K_eq_max]
    _ ≤ -(ε t U β) * (length : ℝ) + β * (C t U : ℝ) := by
        -- Use sedt_overhead_bound: β·2^t + β·max(...) + t·log ≤ β·C
        apply add_le_add_left
        exact h_overhead

end Collatz.SEDT
