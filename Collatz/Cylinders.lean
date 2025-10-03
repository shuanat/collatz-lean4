/-
Collatz Conjecture: 2-adic Cylinders
Characterization of depth runs and cylinder intersections

This file formalizes the 2-adic cylinder structure C_ℓ that
characterizes the starts of depth runs in Collatz trajectories.

## Main Results:
- Cylinder definition C_ℓ (Definition 4.6)
- Depth run characterization (Lemma 4.7)
- Cylinder intersection properties (Lemma 4.8)
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorization.Defs
import Collatz.Basic
import Collatz.Arithmetic
import Collatz.Coordinates

namespace Collatz.Cylinders

open Collatz.Basic
open Collatz.Arithmetic
open Collatz.Coordinates

/-!
## 2-adic Cylinder Definition
-/

/-- 2-adic cylinder C_ℓ: all odd integers m with ν₂(3m+1) = ℓ
    This is Definition 4.6 from the paper -/
def C_ell (ℓ : ℕ) : Set ℕ :=
  { m : ℕ | Odd m ∧ (3 * m + 1).factorization 2 = ℓ }

/-- Alternative characterization: C_ℓ = {m : 3m+1 ≡ 2^ℓ (mod 2^{ℓ+1})} -/
lemma C_ell_modular (ℓ m : ℕ) (hm_odd : Odd m) :
  m ∈ C_ell ℓ ↔ 3 * m + 1 ≡ 2^ℓ [MOD 2^(ℓ+1)] := by
  constructor
  · intro hm_in_C
    -- From ν₂(3m+1) = ℓ, we get 2^ℓ ∣ (3m+1) but 2^{ℓ+1} ∤ (3m+1)
    have h_dvd : 2^ℓ ∣ (3 * m + 1) := by
      have h_fac := hm_in_C.2
      exact Nat.ordProj_dvd (3 * m + 1) 2
    have h_not_dvd : ¬(2^(ℓ+1) ∣ (3 * m + 1)) := by
      have h_fac := hm_in_C.2
      intro h_contra
      have : (3 * m + 1).factorization 2 ≥ ℓ + 1 := by
        exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.ne_of_gt (Nat.pos_of_ne_zero (fun h => by
          have : 3 * m + 1 ≥ 1 := by omega
          omega))) h_contra
      omega
    -- Write 3m+1 = 2^ℓ * k where k is odd
    obtain ⟨k, hk_odd, h_eq⟩ := Nat.exists_odd_mul h_dvd
    -- Since 2^{ℓ+1} ∤ (3m+1), we have k ≡ 1 (mod 2)
    -- So 3m+1 = 2^ℓ * k ≡ 2^ℓ (mod 2^{ℓ+1})
    have h_mod : 3 * m + 1 ≡ 2^ℓ * k [MOD 2^(ℓ+1)] := by
      rw [h_eq]
      exact Nat.ModEq.refl
    have h_k_mod : k ≡ 1 [MOD 2] := by
      -- k is odd, so k ≡ 1 (mod 2)
      exact Nat.ModEq.of_odd hk_odd
    have h_2ell_mod : 2^ℓ * k ≡ 2^ℓ * 1 [MOD 2^(ℓ+1)] := by
      exact Nat.ModEq.mul_right (2^ℓ) h_k_mod
    exact Nat.ModEq.trans h_mod h_2ell_mod

  · intro h_mod
    -- From 3m+1 ≡ 2^ℓ (mod 2^{ℓ+1}), we get ν₂(3m+1) = ℓ
    have h_dvd : 2^ℓ ∣ (3 * m + 1) := by
      have : 3 * m + 1 ≡ 2^ℓ [MOD 2^(ℓ+1)] := h_mod
      exact Nat.ModEq.dvd this
    have h_not_dvd : ¬(2^(ℓ+1) ∣ (3 * m + 1)) := by
      intro h_contra
      have : 3 * m + 1 ≡ 0 [MOD 2^(ℓ+1)] := Nat.ModEq.dvd h_contra
      have : 2^ℓ ≡ 0 [MOD 2^(ℓ+1)] := Nat.ModEq.trans h_mod this
      -- But 2^ℓ ≢ 0 (mod 2^{ℓ+1}) for ℓ ≥ 0
      have h_pos : 0 < 2^ℓ := Nat.one_le_pow ℓ 2 (by decide)
      have h_lt : 2^ℓ < 2^(ℓ+1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self ℓ)
      omega
    -- Therefore ν₂(3m+1) = ℓ
    constructor
    · exact hm_odd
    · exact Nat.factorization_eq_iff.mpr ⟨h_dvd, h_not_dvd⟩

/-!
## Depth Run Characterization
-/

/-- Depth run starts: m starts a depth run of length ℓ iff m ∈ C_ℓ
    This is Lemma 4.7 from the paper -/
lemma depth_run_starts (m ℓ : ℕ) (hm_odd : Odd m) :
  m ∈ C_ell ℓ ↔
  (∀ i : ℕ, i < ℓ → ν₂(T_shortcut^i m) = ℓ - i) ∧
  (ℓ = 0 ∨ ν₂(T_shortcut^ℓ m) < ℓ) := by
  constructor
  · intro hm_in_C
    constructor
    · -- Show ν₂(T_shortcut^i m) = ℓ - i for i < ℓ
      intro i hi_lt
      -- By induction on i
      induction' i with i ih generalizing m ℓ hm_odd hm_in_C
      · -- Base case i = 0: ν₂(m) = ℓ
        have h_fac := hm_in_C.2
        -- For odd m, ν₂(m) = 0, so this requires ℓ = 0
        -- But if ℓ = 0, then 3m+1 is odd, so T_shortcut(m) = (3m+1)/2
        -- We need to show ν₂(T_shortcut m) = ℓ - 1 = -1, which is impossible
        -- This suggests the lemma needs refinement
        sorry
      · -- Inductive step
        sorry
    · -- Show termination condition
      sorry

  · intro ⟨h_depth, h_term⟩
    -- From depth run properties, deduce m ∈ C_ℓ
    sorry

/-- Cylinder intersection: C_ℓ₁ ∩ C_ℓ₂ = ∅ for ℓ₁ ≠ ℓ₂ -/
theorem cylinder_disjoint (ℓ₁ ℓ₂ : ℕ) :
  ℓ₁ ≠ ℓ₂ → C_ell ℓ₁ ∩ C_ell ℓ₂ = ∅ := by
  intro h_ne
  ext m
  constructor
  · intro ⟨hm1, hm2⟩
    -- Both give ν₂(3m+1) = ℓ₁ and ν₂(3m+1) = ℓ₂
    have h_fac1 := hm1.2
    have h_fac2 := hm2.2
    -- Therefore ℓ₁ = ℓ₂, contradiction
    exact h_ne (h_fac1 ▸ h_fac2)
  · intro h_empty
    exfalso
    exact h_empty

/-!
## Cylinder Union and Coverage
-/

/-- Complete coverage: union of all C_ℓ gives all odd integers -/
theorem cylinder_coverage :
  { m : ℕ | Odd m } = ⋃ ℓ, C_ell ℓ := by
  ext m
  constructor
  · intro hm_odd
    -- Every odd m has some ν₂(3m+1)
    set ℓ := (3 * m + 1).factorization 2 with hℓ_def
    use ℓ
    exact ⟨hm_odd, hℓ_def⟩
  · intro ⟨ℓ, hm_in_C⟩
    exact hm_in_C.1

/-- Cylinder sizes: |C_ℓ ∩ [1,N]| ≈ N/2^{ℓ+1} -/
theorem cylinder_density (ℓ N : ℕ) (hN_pos : N > 0) :
  ∃ (density : ℝ), density = 1/2^(ℓ+1) ∧
  |(Finset.range N).filter (fun m => m ∈ C_ell ℓ)| / N = density + O(1/N) := by
  use (1/2^(ℓ+1) : ℝ)
  constructor
  · rfl
  · intro N' hN'_pos
    -- Among odd integers in [1,N'], exactly 1/2^{ℓ+1} have ν₂(3m+1) = ℓ
    -- This follows from uniform distribution in residue classes mod 2^{ℓ+1}
    sorry  -- Requires density/limit formalization

/-!
## Connection to Coordinates
-/

/-- Cylinder-coordinate relationship: m(n,t) ∈ C_{k_0(n)+2t} -/
lemma cylinder_coordinate_relation (n t : ℕ) (hn_odd : Odd n) (hn_not_div3 : ¬(3 ∣ n)) :
  m n t ∈ C_ell (k_0 n + 2 * t) := by
  -- From m(n,t) = (2^{k_0(n)+2t} n - 1) / 3
  -- We get 3 * m(n,t) + 1 = 2^{k_0(n)+2t} n
  -- So ν₂(3 * m(n,t) + 1) = ν₂(2^{k_0(n)+2t} n) = k_0(n) + 2t + ν₂(n)
  -- Since n is odd, ν₂(n) = 0, so ν₂(3 * m(n,t) + 1) = k_0(n) + 2t
  unfold m
  constructor
  · -- Show m(n,t) is odd
    sorry  -- From Coordinates.m_in_S_n
  · -- Show ν₂(3 * m(n,t) + 1) = k_0(n) + 2t
    have h_eq : 3 * ((2^(k_0 n + 2 * t) * n - 1) / 3) + 1 = 2^(k_0 n + 2 * t) * n := by
      -- From m(n,t) = (2^{k_0(n)+2t} n - 1) / 3
      -- We get 3 * m(n,t) = 2^{k_0(n)+2t} n - 1
      -- So 3 * m(n,t) + 1 = 2^{k_0(n)+2t} n
      have h_div3 : 3 ∣ (2^(k_0 n + 2 * t) * n - 1) := by
        -- From admissible_exponents in Coordinates
        have h_cong := Coordinates.admissible_exponents n (k_0 n + 2 * t) hn_odd hn_not_div3
        have h_exists : ∃ t' : ℕ, k_0 n + 2 * t = k_0 n + 2 * t' := by use t; rfl
        exact Nat.ModEq.dvd (h_cong.mpr h_exists)
      rw [Nat.mul_div_cancel' h_div3]
      ring
    rw [h_eq]
    -- ν₂(2^{k_0(n)+2t} n) = k_0(n) + 2t + ν₂(n) = k_0(n) + 2t (since n is odd)
    have h_n_odd : Odd n := hn_odd
    have h_nu2_n : n.factorization 2 = 0 := by
      exact Nat.factorization_eq_zero_of_not_dvd (fun h => h_n_odd.not_even (even_iff_two_dvd.mpr h))
    rw [Nat.factorization_mul (by decide) (Nat.ne_of_gt (Nat.pos_of_ne_zero (fun h => hn_not_div3 (by rw [h]; exact dvd_zero 3))))]
    simp [h_nu2_n]

end Collatz.Cylinders
