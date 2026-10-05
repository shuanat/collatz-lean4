/-
Exact form of one odd step.

For every natural `m`: `3m + 1 = 2^{e(m)} · T(m)` with `T(m)` odd, where
`e = step_type` and `T = collatz_step`. Conversely, if `3m + 1 = 2^k · n` with
`n` odd, then `e(m) = k` and `T(m) = n`. These are the identities behind
paper Definition 2.3 (`3m+1 = 2^k n`) and Lemma 2.13; they are used by
`Collatz/Layers/PreimageLayers.lean` and `Collatz/Blocks/BlockStep.lean`.
-/
import Collatz.Foundations.Core

namespace Collatz.Foundations

/-- `ν₂(2^k · q) = k` for odd `q`. -/
lemma factorization_two_pow_mul_of_odd (k : ℕ) {q : ℕ} (hq : Odd q) :
    (2 ^ k * q).factorization 2 = k := by
  have hq0 : q ≠ 0 := hq.pos.ne'
  have hndvd : ¬ 2 ∣ q := by
    rintro ⟨c, hc⟩
    obtain ⟨d, hd⟩ := hq
    omega
  rw [Nat.factorization_mul (pow_ne_zero k two_ne_zero) hq0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]

/-- A positive natural number is `2^{ν₂(N)}` times an odd number:
`N = 2^{ν₂(N)} · (N / 2^{ν₂(N)})` with the quotient odd. -/
lemma two_pow_factorization_mul_odd_part {N : ℕ} (hN : 0 < N) :
    2 ^ N.factorization 2 * (N / 2 ^ N.factorization 2) = N ∧
      Odd (N / 2 ^ N.factorization 2) :=
  ⟨Nat.mul_div_cancel' (Nat.ordProj_dvd N 2),
    Collatz.Arithmetic.odd_div_pow_two_factorization hN⟩

/-- `3m + 1 = 2^{e(m)} · T(m)` for every natural `m`. -/
theorem two_pow_step_type_mul_collatz_step (m : ℕ) :
    2 ^ step_type m * collatz_step m = 3 * m + 1 := by
  unfold collatz_step step_type Collatz.Arithmetic.e
  exact Nat.mul_div_cancel' (Nat.ordProj_dvd (3 * m + 1) 2)

/-- If `3m + 1 = 2^k · n` with `n` odd, then `e(m) = ν₂(3m+1) = k`. -/
theorem step_type_eq_of_three_mul_add_one_eq {m k n : ℕ} (hn : Odd n)
    (h : 3 * m + 1 = 2 ^ k * n) : step_type m = k := by
  unfold step_type Collatz.Arithmetic.e
  rw [h]
  exact factorization_two_pow_mul_of_odd k hn

/-- If `3m + 1 = 2^k · n` with `n` odd, then `T(m) = n`. -/
theorem collatz_step_eq_of_three_mul_add_one_eq {m k n : ℕ} (hn : Odd n)
    (h : 3 * m + 1 = 2 ^ k * n) : collatz_step m = n := by
  unfold collatz_step
  rw [step_type_eq_of_three_mul_add_one_eq hn h, h]
  exact Nat.mul_div_cancel_left n (pow_pos two_pos k)

/-- `depth₋(x) = α` whenever `x + 1 = 2^α · y` with `y` odd. -/
theorem depth_minus_eq_of_add_one_eq {x α y : ℕ} (hy : Odd y)
    (hx : x + 1 = 2 ^ α * y) : depth_minus x = α := by
  unfold depth_minus
  rw [hx]
  exact factorization_two_pow_mul_of_odd α hy

/-- Odd part of `x + 1`: `x + 1 = 2^{depth₋(x)} · y` with `y` odd. -/
theorem exists_odd_add_one_eq_two_pow_depth_mul (x : ℕ) :
    ∃ y, Odd y ∧ x + 1 = 2 ^ depth_minus x * y := by
  obtain ⟨h1, h2⟩ := two_pow_factorization_mul_odd_part (Nat.succ_pos x)
  exact ⟨_, h2, h1.symm⟩

end Collatz.Foundations
