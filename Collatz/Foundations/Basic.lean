/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Basic definitions and imports

This file contains the foundational definitions for the Collatz framework:
- Collatz function (odd version)
- Exponent function
- Basic properties
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Collatz.Foundations.Arithmetic
import Collatz.Foundations.TwoAdicDepth

namespace Collatz

-- Import e function from Arithmetic
open Arithmetic (e)

/-- Collatz function for odd integers: T_odd(m) = (3m+1) / 2^e where e = ν_2(3m+1) -/
def T_odd (m : ℕ) : ℕ :=
  if m = 0 then 0
  else
    let numerator := 3 * m + 1
    numerator / (2 ^ (numerator.factorization 2))



/-- Collatz sequence starting from r₀ -/
def collatz_seq (r₀ : ℕ) : ℕ → ℕ
  | 0 => r₀
  | n + 1 => T_odd (collatz_seq r₀ n)

/-- Basic lemma: T_odd preserves oddness (when m is odd) -/
lemma T_odd_odd_of_odd {m : ℕ} (h : Odd m) : Odd (T_odd m) := by
  unfold T_odd
  by_cases hm : m = 0
  · -- m = 0 contradicts Odd m
    rw [hm] at h
    obtain ⟨k, hk⟩ := h
    omega
  · -- m ≠ 0: 3m+1 is even, dividing by 2^e gives odd number
    simp only [hm, ↓reduceIte]
    -- The key: (3m+1) / 2^(factorization (3m+1) 2) is the odd part
    have h_even := Arithmetic.three_mul_odd_plus_one_even h
    have h_pos : 0 < 3 * m + 1 := by omega
    -- After division by maximal power of 2, we get an odd number
    exact Arithmetic.odd_div_pow_two_factorization h_pos

/-- Basic lemma: e(m) ≥ 1 for odd m -/
lemma e_pos_of_odd {m : ℕ} (h : Odd m) (hm : m ≠ 0) : e m ≥ 1 := by
  unfold e
  simp only [hm, ↓reduceIte]
  -- 3m+1 is even (from Arithmetic), so factorization 2 ≥ 1
  have h_even := Arithmetic.three_mul_odd_plus_one_even h
  have h_pos : 0 < 3 * m + 1 := by omega
  obtain ⟨k, hk⟩ := h_even
  -- Even number 3m+1 = 2k has factorization 2 ≥ 1
  rw [hk]
  have h_dvd : 2 ∣ k + k := by use k; ring
  have h_ne_zero : k + k ≠ 0 := by omega
  exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two h_ne_zero h_dvd

end Collatz
