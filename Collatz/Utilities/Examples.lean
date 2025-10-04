import Collatz.Foundations.Basic
import Collatz.Foundations.Arithmetic
import Collatz.Epochs.OrdFact

/-!
# Worked Examples for Collatz Formalization

This file contains simple concrete examples demonstrating key computations.
-/

namespace Collatz.Examples

/-!
## Example 1: Powers of 2
-/

/-- 2^3 = 8 -/
example : (2 : ℕ) ^ 3 = 8 := by norm_num

/-- 2^5 = 32 -/
example : (2 : ℕ) ^ 5 = 32 := by norm_num

/-- 2^t > 0 for any t -/
example : 0 < (2 : ℕ) ^ 5 := by norm_num

/-!
## Example 2: ZMod computations (key for Ord‑Fact)
-/

/-- 3^2 ≡ 1 (mod 8) -/
example : (3 : ZMod 8) ^ 2 = 1 := by decide

/-- 3^4 ≡ 1 (mod 16) -/
example : (3 : ZMod 16) ^ 4 = 1 := by decide

/-- 3^8 ≡ 1 (mod 32) -/
example : (3 : ZMod 32) ^ 8 = 1 := by decide

/-!
## Example 3: Non-trivial powers (for minimality)
-/

/-- 3 ≠ 1 (mod 8) -/
example : (3 : ZMod 8) ^ 1 ≠ 1 := by decide

/-- 3^2 ≠ 1 (mod 16) -/
example : (3 : ZMod 16) ^ 2 ≠ 1 := by decide

/-- 3^4 ≠ 1 (mod 32) -/
example : (3 : ZMod 32) ^ 4 ≠ 1 := by decide

/-!
## Example 4: Parity checks
-/

/-- 7 is odd -/
example : Odd (7 : ℕ) := by norm_num

/-- 27 is odd -/
example : Odd (27 : ℕ) := by norm_num

/-- 8 is even -/
example : Even (8 : ℕ) := by norm_num

/-- 16 is even -/
example : Even (16 : ℕ) := by norm_num

end Collatz.Examples
