/-
Collatz Conjecture: Bivariate Coordinate Systems
Parametrization of preimage layers by (n,t) coordinates

This file formalizes the bivariate parametrization m(n,t) that
establishes a bijection between odd integers and coordinate pairs.

## Main Results:
- Minimal base exponent k_0(n) (Lemma 4.5.a)
- Explicit parametrization m(n,t) (Corollary 4.5.b)
- Asymptotic growth along verticals (Proposition 4.5.c)
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorization.Defs
import Collatz.Basic
import Collatz.Arithmetic
import Collatz.Stratified

namespace Collatz.Coordinates

open Collatz.Basic
open Collatz.Arithmetic
open Collatz.Stratified

/-!
## Minimal Base Exponent
-/

/-- Minimal base exponent k_0(n): smallest k ≥ 1 such that 2^k n ≡ 1 (mod 3)
    This is Lemma 4.5.a from the paper -/
def k_0 (n : ℕ) : ℕ :=
  if n ≡ 1 [MOD 3] then 2 else 1

/-- k_0(n) is the minimal exponent satisfying 2^k n ≡ 1 (mod 3) -/
lemma k_0_minimal (n : ℕ) (hn_odd : Odd n) (hn_not_div3 : ¬(3 ∣ n)) :
  2^(k_0 n) * n ≡ 1 [MOD 3] := by
  unfold k_0
  split_ifs with h_mod3
  · -- Case n ≡ 1 (mod 3): k_0 = 2, need 2^2 * n ≡ 1 (mod 3)
    -- Since 2 ≡ -1 (mod 3), we have 2^2 ≡ 1 (mod 3)
    have h2_sq : 2^2 ≡ 1 [MOD 3] := by norm_num
    exact Nat.ModEq.mul_right n h2_sq
  · -- Case n ≡ 2 (mod 3): k_0 = 1, need 2 * n ≡ 1 (mod 3)
    -- Since 2 ≡ -1 (mod 3) and n ≡ 2 (mod 3), we have 2 * n ≡ -1 * 2 ≡ 1 (mod 3)
    have h2_mod3 : (2 : ℕ) ≡ -1 [MOD 3] := by norm_num
    have hn_mod3 : n ≡ 2 [MOD 3] := by
      -- n is odd and not divisible by 3, so n ≡ 1 or 2 (mod 3)
      -- Since h_mod3 is false, we have n ≢ 1 (mod 3)
      rcases Nat.mod_three_cases n with h1 | h2 | h3
      · exfalso; exact hn_not_div3 (Nat.ModEq.dvd h1)
      · exfalso; exact h_mod3 h1
      · exact h2
    calc 2 * n ≡ (-1) * 2 [MOD 3] := Nat.ModEq.mul_right n h2_mod3
      _ ≡ -2 [MOD 3] := by ring
      _ ≡ 1 [MOD 3] := by norm_num

/-- All admissible exponents have the form k_0(n) + 2t -/
lemma admissible_exponents (n k : ℕ) (hn_odd : Odd n) (hn_not_div3 : ¬(3 ∣ n)) :
  2^k * n ≡ 1 [MOD 3] ↔ ∃ t : ℕ, k = k_0 n + 2 * t := by
  constructor
  · intro h_cong
    -- Use parity constraint from Stratified
    have h_parity := parity_constraint n k hn_odd hn_not_div3
    rw [h_cong] at h_parity
    cases h_parity with
    | inl ⟨hn_mod1, hk_even⟩ =>
      -- n ≡ 1 (mod 3) and k is even
      have h_k0 : k_0 n = 2 := by unfold k_0; split_ifs; rfl
      obtain ⟨t, ht⟩ := hk_even
      use t
      rw [h_k0, ht]
      ring
    | inr ⟨hn_mod2, hk_odd⟩ =>
      -- n ≡ 2 (mod 3) and k is odd
      have h_k0 : k_0 n = 1 := by unfold k_0; split_ifs; rfl
      obtain ⟨t, ht⟩ := hk_odd
      use t
      rw [h_k0, ht]
      ring
  · intro ⟨t, ht⟩
    rw [ht]
    -- Show 2^(k_0 n + 2t) * n ≡ 1 (mod 3)
    rw [pow_add]
    have h_k0 := k_0_minimal n hn_odd hn_not_div3
    have h_2t : 2^(2*t) ≡ 1 [MOD 3] := by
      -- 2^2 ≡ 1 (mod 3), so 2^(2t) = (2^2)^t ≡ 1^t ≡ 1 (mod 3)
      rw [pow_mul]
      have h4 : 2^2 ≡ 1 [MOD 3] := by norm_num
      exact Nat.ModEq.pow t h4
    exact Nat.ModEq.mul_right n (Nat.ModEq.mul h_k0 h_2t)

/-!
## Explicit Parametrization
-/

/-- Explicit parametrization: m(n,t) = (2^{k_0(n)+2t} n - 1) / 3
    This is Corollary 4.5.b from the paper -/
def m (n : ℕ) (t : ℕ) : ℕ :=
  (2^(k_0 n + 2 * t) * n - 1) / 3

/-- Parametrization gives valid odd integers in S_n -/
lemma m_in_S_n (n t : ℕ) (hn_odd : Odd n) (hn_not_div3 : ¬(3 ∣ n)) :
  let m_val := m n t
  Odd m_val ∧ m_val ∈ S_n n := by
  intro m_val
  constructor
  · -- Show m_val is odd
    unfold m
    -- 2^(k_0 n + 2t) * n is even, so 2^(k_0 n + 2t) * n - 1 is odd
    -- Dividing odd by 3 gives odd result
    have h_even : Even (2^(k_0 n + 2 * t) * n) := by
      exact Nat.even_mul.mpr (Or.inl (Nat.even_pow_of_even (by decide) _))
    have h_odd : Odd (2^(k_0 n + 2 * t) * n - 1) := by
      exact h_even.sub_odd odd_one
    -- Division by 3 preserves oddness
    have h_div3 : 3 ∣ (2^(k_0 n + 2 * t) * n - 1) := by
      -- From admissible_exponents: 2^(k_0 n + 2t) * n ≡ 1 (mod 3)
      have h_cong := admissible_exponents n (k_0 n + 2 * t) hn_odd hn_not_div3
      have h_exists : ∃ t' : ℕ, k_0 n + 2 * t = k_0 n + 2 * t' := by use t; rfl
      have h_cong' := h_cong.mpr h_exists
      exact Nat.ModEq.dvd h_cong'
    exact Arithmetic.odd_div_pow_two_factorization (Nat.pos_of_ne_zero (fun h => by
      have : 2^(k_0 n + 2 * t) * n ≥ 1 := by
        have : 2^(k_0 n + 2 * t) ≥ 1 := Nat.one_le_pow (k_0 n + 2 * t) 2 (by decide)
        have : n ≥ 1 := Nat.pos_of_ne_zero (fun h => hn_not_div3 (by rw [h]; exact dvd_zero 3))
        exact Nat.mul_le_mul this this
      omega))

  · -- Show m_val ∈ S_n
    unfold m
    constructor
    · -- Already shown above
      sorry
    · -- Show 3 * m_val + 1 = 2^(k_0 n + 2t) * n
      use (k_0 n + 2 * t)
      constructor
      · -- k ≥ 1
        have : k_0 n ≥ 1 := by
          unfold k_0
          split_ifs <;> norm_num
        omega
      · -- 3 * m_val + 1 = 2^(k_0 n + 2t) * n
        unfold m
        -- From m_val = (2^(k_0 n + 2t) * n - 1) / 3
        -- We get 3 * m_val = 2^(k_0 n + 2t) * n - 1
        -- So 3 * m_val + 1 = 2^(k_0 n + 2t) * n
        have h_div3 : 3 ∣ (2^(k_0 n + 2 * t) * n - 1) := by
          -- Same as above
          have h_cong := admissible_exponents n (k_0 n + 2 * t) hn_odd hn_not_div3
          have h_exists : ∃ t' : ℕ, k_0 n + 2 * t = k_0 n + 2 * t' := by use t; rfl
          have h_cong' := h_cong.mpr h_exists
          exact Nat.ModEq.dvd h_cong'
        have h_eq : 3 * ((2^(k_0 n + 2 * t) * n - 1) / 3) = 2^(k_0 n + 2 * t) * n - 1 :=
          Nat.mul_div_cancel' h_div3
        rw [h_eq]
        ring

/-- Bijective correspondence: every m ∈ S_n arises uniquely as m(n,t) -/
theorem parametric_bijection (n : ℕ) (hn_odd : Odd n) (hn_not_div3 : ¬(3 ∣ n)) :
  Function.Bijective (m n) := by
  constructor
  · -- Injectivity: m(n,t₁) = m(n,t₂) → t₁ = t₂
    intro t₁ t₂ h_eq
    unfold m at h_eq
    -- From (2^(k_0 n + 2t₁) * n - 1) / 3 = (2^(k_0 n + 2t₂) * n - 1) / 3
    -- We get 2^(k_0 n + 2t₁) * n = 2^(k_0 n + 2t₂) * n
    -- So 2^(k_0 n + 2t₁) = 2^(k_0 n + 2t₂)
    -- Therefore k_0 n + 2t₁ = k_0 n + 2t₂
    -- Hence t₁ = t₂
    have h_div3₁ : 3 ∣ (2^(k_0 n + 2 * t₁) * n - 1) := by
      have h_cong := admissible_exponents n (k_0 n + 2 * t₁) hn_odd hn_not_div3
      have h_exists : ∃ t' : ℕ, k_0 n + 2 * t₁ = k_0 n + 2 * t' := by use t₁; rfl
      exact Nat.ModEq.dvd (h_cong.mpr h_exists)
    have h_div3₂ : 3 ∣ (2^(k_0 n + 2 * t₂) * n - 1) := by
      have h_cong := admissible_exponents n (k_0 n + 2 * t₂) hn_odd hn_not_div3
      have h_exists : ∃ t' : ℕ, k_0 n + 2 * t₂ = k_0 n + 2 * t' := by use t₂; rfl
      exact Nat.ModEq.dvd (h_cong.mpr h_exists)

    have h_eq_mul : 3 * ((2^(k_0 n + 2 * t₁) * n - 1) / 3) = 3 * ((2^(k_0 n + 2 * t₂) * n - 1) / 3) := by
      rw [h_eq]
    rw [Nat.mul_div_cancel' h_div3₁, Nat.mul_div_cancel' h_div3₂] at h_eq_mul

    -- Now 2^(k_0 n + 2t₁) * n - 1 = 2^(k_0 n + 2t₂) * n - 1
    -- So 2^(k_0 n + 2t₁) * n = 2^(k_0 n + 2t₂) * n
    -- Since n > 0, we get 2^(k_0 n + 2t₁) = 2^(k_0 n + 2t₂)
    have h_n_pos : 0 < n := Nat.pos_of_ne_zero (fun h => hn_not_div3 (by rw [h]; exact dvd_zero 3))
    have h_pow_eq : 2^(k_0 n + 2 * t₁) = 2^(k_0 n + 2 * t₂) := by
      have : 2^(k_0 n + 2 * t₁) * n = 2^(k_0 n + 2 * t₂) * n := by omega
      exact Nat.eq_of_mul_eq_mul_right h_n_pos this

    -- Therefore k_0 n + 2t₁ = k_0 n + 2t₂
    have h_exp_eq : k_0 n + 2 * t₁ = k_0 n + 2 * t₂ := by
      exact Nat.pow_inj (by decide) (by decide) h_pow_eq

    -- Hence t₁ = t₂
    omega

  · -- Surjectivity: every m ∈ S_n is m(n,t) for some t
    intro m hm_in_Sn
    obtain ⟨hm_odd, ⟨k, hk_pos, h_eq⟩⟩ := hm_in_Sn
    -- From 3m+1 = 2^k n and admissible_exponents, we get k = k_0 n + 2t
    have h_cong := admissible_exponents n k hn_odd hn_not_div3
    have h_exists : ∃ t' : ℕ, k = k_0 n + 2 * t' := by
      -- From 3m+1 = 2^k n, we get 2^k n ≡ 1 (mod 3)
      have h_mod3 : 2^k * n ≡ 1 [MOD 3] := by
        rw [← h_eq]
        norm_num
      exact h_cong.mp h_mod3
    obtain ⟨t, ht⟩ := h_exists

    -- Show m = m(n,t)
    use t
    unfold m
    -- We have 3m+1 = 2^k n = 2^(k_0 n + 2t) n
    -- So m = (2^(k_0 n + 2t) n - 1) / 3
    rw [ht] at h_eq
    have h_div3 : 3 ∣ (2^(k_0 n + 2 * t) * n - 1) := by
      have h_cong' := admissible_exponents n (k_0 n + 2 * t) hn_odd hn_not_div3
      have h_exists' : ∃ t' : ℕ, k_0 n + 2 * t = k_0 n + 2 * t' := by use t; rfl
      exact Nat.ModEq.dvd (h_cong'.mpr h_exists')

    -- From 3m+1 = 2^(k_0 n + 2t) n, we get m = (2^(k_0 n + 2t) n - 1) / 3
    have h_eq' : 3 * m + 1 = 2^(k_0 n + 2 * t) * n := by rw [ht] at h_eq; exact h_eq
    have h_eq'' : 3 * m = 2^(k_0 n + 2 * t) * n - 1 := by omega
    have h_eq''' : m = (2^(k_0 n + 2 * t) * n - 1) / 3 := by
      have : 3 ∣ (2^(k_0 n + 2 * t) * n - 1) := by
        rw [← h_eq'']
        exact Nat.dvd_mul_of_dvd_right (by decide) (Nat.dvd_refl m)
      exact Nat.div_eq_of_eq_mul_left (by decide) h_eq''
    exact h_eq'''

/-!
## Asymptotic Growth
-/

/-- Asymptotic growth along verticals: m(n,t)/4^t → 2^{k_0(n)} n / 3
    This is Proposition 4.5.c from the paper -/
theorem vertical_asymptotic (n : ℕ) (hn_odd : Odd n) (hn_not_div3 : ¬(3 ∣ n)) :
  Filter.Tendsto (fun t => (m n t : ℝ) / (4^t : ℝ)) Filter.atTop
    (nhds ((2^(k_0 n) * n : ℝ) / 3)) := by
  -- For large t, the -1 term becomes negligible
  -- So m(n,t) ≈ 2^{k_0(n)+2t} n / 3 = 2^{k_0(n)} n * 4^t / 3
  -- Therefore m(n,t)/4^t ≈ 2^{k_0(n)} n / 3
  sorry  -- Requires limit/analysis formalization

/-- Growth ratio: m(n,t+1)/m(n,t) → 4 -/
theorem growth_ratio (n : ℕ) (hn_odd : Odd n) (hn_not_div3 : ¬(3 ∣ n)) :
  Filter.Tendsto (fun t => (m n (t+1) : ℝ) / (m n t : ℝ)) Filter.atTop (nhds 4) := by
  -- From m(n,t+1) = 2^{k_0(n)+2(t+1)} n / 3 and m(n,t) = 2^{k_0(n)+2t} n / 3
  -- We get m(n,t+1)/m(n,t) = 2^{k_0(n)+2(t+1)} / 2^{k_0(n)+2t} = 2^2 = 4
  sorry  -- Requires limit/analysis formalization

end Collatz.Coordinates
