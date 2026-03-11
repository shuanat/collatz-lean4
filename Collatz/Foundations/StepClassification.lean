/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Step classification definitions

This file contains definitions for classifying Collatz steps:
- e=1 steps (simple steps)
- e≥2 steps (complex steps)
-/
import Collatz.Foundations.Core

namespace Collatz

open Collatz.Foundations (step_type)

/-- Simple step proxy used in non-production modules:
    `3m+1 ≡ 2 (mod 4)`, matching the paper characterization for odd inputs. -/
def is_simple_step (m : ℕ) : Prop := (3 * m + 1) % 4 = 2

/-- Complex step proxy used in non-production modules:
    `3m+1 ≡ 0 (mod 4)`, matching the paper characterization for odd inputs. -/
def is_complex_step (m : ℕ) : Prop := (3 * m + 1) % 4 = 0

/-- Simple step characterization in mod-4 form. -/
lemma simple_step_iff_mod_four {m : ℕ} (_hm : m ≠ 0) :
  is_simple_step m ↔ (3 * m + 1) % 4 = 2 := by
  rfl

/-- Complex step characterization in mod-4 form. -/
lemma complex_step_iff_mod_four {m : ℕ} (_hm : m ≠ 0) :
  is_complex_step m ↔ (3 * m + 1) % 4 = 0 := by
  rfl

/-- Bridge to the canonical exponent model used in production (`step_type = e`):
    for odd `m`, a simple step implies at least one factor 2 in `3m+1`. -/
lemma simple_step_implies_step_type_pos {m : ℕ} (hodd : Odd m) (_hs : is_simple_step m) :
    1 ≤ step_type m := by
  have h_even : Even (3 * m + 1) := by
    exact Collatz.Arithmetic.three_mul_odd_plus_one_even hodd
  obtain ⟨k, hk⟩ := h_even
  have h_dvd : 2 ∣ (3 * m + 1) := by
    refine ⟨k, ?_⟩
    simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk
  have h_pos : 3 * m + 1 ≠ 0 := by omega
  have hcore : 1 ≤ Collatz.Arithmetic.e m := by
    simpa [Collatz.Arithmetic.e] using
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two h_pos h_dvd
  simpa [step_type] using hcore

end Collatz
