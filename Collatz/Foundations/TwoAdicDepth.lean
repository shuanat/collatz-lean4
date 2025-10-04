/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Two-adic depth definitions and properties

This file contains definitions and properties related to 2-adic depth:
- depth_minus function
- Properties of depth_minus
-/
import Mathlib.Data.Nat.Factorization.Basic
import Collatz.Foundations.Arithmetic

namespace Collatz

/-- Depth to -1 (2-adic depth): depth_-(r) = ν_2(r+1) -/
def depth_minus (r : ℕ) : ℕ := (r + 1).factorization 2

/-- Basic property: depth_minus is non-negative -/
lemma depth_minus_nonneg (r : ℕ) : depth_minus r ≥ 0 := by
  unfold depth_minus
  exact Nat.zero_le _

/-- depth_minus of 0 is 1 -/
lemma depth_minus_zero : depth_minus 0 = 1 := by
  sorry -- TODO: Complete proof

/-- depth_minus of odd numbers is at least 1 -/
lemma depth_minus_odd_pos {r : ℕ} (h : Odd r) : depth_minus r ≥ 1 := by
  unfold depth_minus
  have h_dvd : 2 ∣ (r + 1) := by
    obtain ⟨k, hk⟩ := h
    use k + 1
    omega
  have h_pos : r + 1 ≠ 0 := by omega
  exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two h_pos h_dvd

end Collatz
