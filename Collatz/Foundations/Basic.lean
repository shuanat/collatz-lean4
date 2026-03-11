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
import Collatz.Foundations.Core

namespace Collatz

-- Import e function from Arithmetic
open Arithmetic (e)
open Collatz.Foundations (step_type collatz_step step_type_odd_pos)

/-- Collatz function for odd integers: T_odd(m) = (3m+1) / 2^e where e = ν_2(3m+1) -/
def T_odd (m : ℕ) : ℕ := collatz_step m



/-- Collatz sequence starting from r₀ -/
def collatz_seq (r₀ : ℕ) : ℕ → ℕ
  | 0 => r₀
  | n + 1 => T_odd (collatz_seq r₀ n)

/-- Basic lemma: T_odd preserves oddness (when m is odd) -/
lemma T_odd_odd_of_odd {m : ℕ} (_h : Odd m) : Odd (T_odd m) := by
  unfold T_odd collatz_step step_type
  have h_pos : 0 < 3 * m + 1 := by omega
  simpa [Collatz.Arithmetic.e] using Arithmetic.odd_div_pow_two_factorization h_pos

/-- Basic lemma: e(m) ≥ 1 for odd m -/
lemma e_pos_of_odd {m : ℕ} (h : Odd m) (_hm : m ≠ 0) : e m ≥ 1 := by
  have h_step : step_type m ≥ 1 := step_type_odd_pos h
  simpa [step_type, e] using h_step

end Collatz
