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

/-- A complex step already forces two factors of `2` in `3m+1`, hence
`step_type m ≥ 2`. This is the mod-4 bridge underlying the narrower
stream-side filler target. -/
lemma complex_step_implies_step_type_ge_two {m : ℕ}
    (hodd : Odd m) (hs : is_complex_step m) :
    2 ≤ step_type m := by
  have hbase : 1 ≤ step_type m := by
    have h_even : Even (3 * m + 1) := Collatz.Arithmetic.three_mul_odd_plus_one_even hodd
    obtain ⟨k, hk⟩ := h_even
    have h_dvd : 2 ∣ (3 * m + 1) := by
      refine ⟨k, ?_⟩
      simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk
    have h_pos : 3 * m + 1 ≠ 0 := by omega
    have hcore : 1 ≤ Collatz.Arithmetic.e m := by
      simpa [Collatz.Arithmetic.e] using
        Nat.Prime.factorization_pos_of_dvd Nat.prime_two h_pos h_dvd
    simpa [step_type] using hcore
  by_contra hlt
  have hle : step_type m ≤ 1 := by omega
  have hone : step_type m = 1 := by omega
  have hdvd4 : 4 ∣ (3 * m + 1) := by
    exact Nat.dvd_of_mod_eq_zero hs
  have h_pos : 3 * m + 1 ≠ 0 := by omega
  have hnot :
      ¬ 2 ^ (step_type m + 1) ∣ (3 * m + 1) := by
    simpa [step_type, Collatz.Arithmetic.e] using
      (Nat.pow_succ_factorization_not_dvd h_pos Nat.prime_two)
  have hpow4 : 2 ^ (step_type m + 1) ∣ (3 * m + 1) := by
    simpa [hone] using hdvd4
  exact hnot hpow4

/-- For an odd input, the normalized odd step is necessarily either simple or
complex in the mod-4 sense; there is no third residue possibility. -/
lemma odd_is_simple_or_complex {m : ℕ} (hodd : Odd m) :
    is_simple_step m ∨ is_complex_step m := by
  have h_even : Even (3 * m + 1) := Collatz.Arithmetic.three_mul_odd_plus_one_even hodd
  obtain ⟨k, hk⟩ := h_even
  have hmod :
      (3 * m + 1) % 4 = 0 ∨ (3 * m + 1) % 4 = 2 := by
    rw [hk]
    have hlt : (2 * k) % 4 < 4 := Nat.mod_lt _ (by decide)
    omega
  cases hmod with
  | inl hzero =>
      exact Or.inr (by simpa [is_complex_step] using hzero)
  | inr htwo =>
      exact Or.inl (by simpa [is_simple_step] using htwo)

/-- Therefore, on odd inputs, excluding simple steps forces complex ones. This
is the exact bridge used when filler semantics are naturally phrased as
"no simple step appears" rather than directly as a complex-step theorem. -/
lemma complex_step_of_not_simple {m : ℕ}
    (hodd : Odd m) (hns : ¬ is_simple_step m) :
    is_complex_step m := by
  rcases odd_is_simple_or_complex hodd with hs | hc
  · exact False.elim (hns hs)
  · exact hc

end Collatz
