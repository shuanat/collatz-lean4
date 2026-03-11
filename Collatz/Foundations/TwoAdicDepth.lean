/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Two-adic depth definitions and properties

This file contains definitions and properties related to 2-adic depth:
- depth_minus function
- Properties of depth_minus
-/
import Collatz.Foundations.Core

namespace Collatz

/-- Compatibility alias to canonical depth definition in Foundations.Core. -/
abbrev depth_minus := Collatz.Foundations.depth_minus

/-- Basic property: depth_minus is non-negative (forwarded from Foundations.Core). -/
lemma depth_minus_nonneg (r : ℕ) : depth_minus r ≥ 0 :=
  Collatz.Foundations.depth_minus_nonneg r

/-- depth_minus of 0 is 0 (forwarded from Foundations.Core). -/
lemma depth_minus_zero : depth_minus 0 = 0 :=
  Collatz.Foundations.depth_minus_zero

/-- depth_minus of odd numbers is at least 1 (forwarded from Foundations.Core). -/
lemma depth_minus_odd_pos {r : ℕ} (h : Odd r) : depth_minus r ≥ 1 := by
  exact Collatz.Foundations.depth_minus_odd_pos h

end Collatz
