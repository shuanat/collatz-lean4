/-
Collatz Conjecture: Arithmetic Lemmas
Foundational lemmas for modular arithmetic and powers of 2

This file contains basic arithmetic lemmas needed for the Ord‑Fact proof.
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic

namespace Collatz.Arithmetic

/-- Powers of 2 are always positive -/
lemma pow_two_pos (n : ℕ) : 0 < 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc 2^(n+1) = 2 * 2^n := by ring
    _ > 0 := Nat.mul_pos (by norm_num : 0 < 2) ih

/-- Powers of 2 are even (for n ≥ 1) -/
lemma pow_two_even {n : ℕ} (hn : n ≥ 1) : Even (2^n) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  rw [hm, pow_succ]
  exact ⟨2^m, by ring⟩

/-- 3 is odd -/
lemma three_odd : Odd 3 := by
  use 1
  norm_num

/-- Modular equivalence lemma for powers of 2 -/
lemma mod_pow_two_eq {a b : ℕ} {t : ℕ} (h : a ≡ b [MOD 2^t]) :
  a % 2^t = b % 2^t := by
  exact h

/-- Multiplication preserves modular equivalence -/
lemma mul_modEq {a b c : ℕ} {m : ℕ} (h : a ≡ b [MOD m]) :
  a * c ≡ b * c [MOD m] := by
  exact Nat.ModEq.mul_right c h

/-- Addition preserves modular equivalence -/
lemma add_modEq {a b c d : ℕ} {m : ℕ} (h1 : a ≡ b [MOD m]) (h2 : c ≡ d [MOD m]) :
  a + c ≡ b + d [MOD m] := by
  exact Nat.ModEq.add h1 h2

/-- Power preserves modular equivalence -/
lemma pow_modEq {a b : ℕ} {m k : ℕ} (h : a ≡ b [MOD m]) :
  a^k ≡ b^k [MOD m] := by
  exact Nat.ModEq.pow k h

/-- Transitivity of modular equivalence -/
lemma modEq_trans {a b c : ℕ} {m : ℕ} (h1 : a ≡ b [MOD m]) (h2 : b ≡ c [MOD m]) :
  a ≡ c [MOD m] := by
  exact Nat.ModEq.trans h1 h2

/-- Symmetry of modular equivalence -/
lemma modEq_symm {a b : ℕ} {m : ℕ} (h : a ≡ b [MOD m]) :
  b ≡ a [MOD m] := by
  exact Nat.ModEq.symm h

/-- Reflexivity of modular equivalence -/
lemma modEq_refl (a m : ℕ) : a ≡ a [MOD m] := by
  exact Nat.ModEq.refl a

-- Additional lemmas for Ord‑Fact proof

/-- If m is odd, then 3m is odd -/
lemma three_mul_odd_is_odd {m : ℕ} (h : Odd m) : Odd (3 * m) := by
  obtain ⟨k, hk⟩ := h
  use 3 * k + 1
  rw [hk]
  ring

/-- If m is odd, then 3m+1 is even -/
lemma three_mul_odd_plus_one_even {m : ℕ} (h : Odd m) : Even (3 * m + 1) := by
  have : Odd (3 * m) := three_mul_odd_is_odd h
  obtain ⟨k, hk⟩ := this
  use k + 1
  rw [hk]
  ring

/-- If m is odd and positive, then 3m+1 ≥ 4 -/
lemma three_mul_odd_plus_one_ge_four {m : ℕ} (h : Odd m) (_hm : m ≠ 0) : 3 * m + 1 ≥ 4 := by
  obtain ⟨k, hk⟩ := h
  rw [hk]
  omega

/-- If m is odd and positive, then 3m+1 > 1 -/
lemma three_mul_odd_plus_one_pos {m : ℕ} (h : Odd m) (hm : m ≠ 0) : 3 * m + 1 > 1 := by
  have : 3 * m + 1 ≥ 4 := three_mul_odd_plus_one_ge_four h hm
  omega

/-- 3^k is odd for all k -/
lemma three_pow_odd (k : ℕ) : Odd (3^k) := by
  induction k with
  | zero =>
    use 0
    norm_num
  | succ k ih =>
    obtain ⟨n, hn⟩ := ih
    use 3 * n + 1
    rw [pow_succ, hn]
    ring

/-- Product of odd numbers is odd -/
lemma odd_mul_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) : Odd (a * b) := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  use 2 * m * n + m + n
  rw [hm, hn]
  ring

/-- For t ≥ 1, we have 2^t ≡ 0 (mod 2^t) -/
lemma pow_two_modEq_zero (t : ℕ) (_ht : t ≥ 1) : 2^t ≡ 0 [MOD 2^t] := by
  show 2^t % 2^t = 0 % 2^t
  simp

/-- If a ≡ b (mod m) and c divides m, then a ≡ b (mod c) -/
lemma modEq_of_modEq_of_dvd {a b m c : ℕ} (h : a ≡ b [MOD m]) (hc : c ∣ m) :
  a ≡ b [MOD c] := by
  obtain ⟨k, hk⟩ := hc
  rw [hk] at h
  -- Use Nat.ModEq.of_mul_right from mathlib
  exact Nat.ModEq.of_mul_right k h

/-- Powers of 2: 2^(a+b) = 2^a * 2^b -/
lemma pow_two_add (a b : ℕ) : 2^(a + b) = 2^a * 2^b := by
  exact pow_add 2 a b

/-- If k < 2^t, then k + 2^t ≡ k (mod 2^t) -/
lemma add_pow_two_modEq {k t : ℕ} (hk : k < 2^t) : k + 2^t ≡ k [MOD 2^t] := by
  show (k + 2^t) % 2^t = k % 2^t
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero]
  simp [Nat.mod_eq_of_lt hk]

/-- If 0 < a < b, then a^n < b^n for n ≥ 1 -/
lemma pow_lt_pow_of_lt {a b n : ℕ} (hab : a < b) (_ha : 0 < a) (hn : n ≥ 1) : a^n < b^n := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  rw [hm]
  exact Nat.pow_lt_pow_left hab (Nat.succ_ne_zero m)

/-- 3 ≡ 3 (mod 2^t) for all t -/
lemma three_modEq_three (t : ℕ) : 3 ≡ 3 [MOD 2^t] := by
  exact Nat.ModEq.refl _

/-- Dividing by maximal power of 2 gives odd number (odd part) -/
lemma odd_div_pow_two_factorization {n : ℕ} (hn : n > 0) :
  Odd (n / 2^(n.factorization 2)) := by
  -- Notation
  set k : ℕ := n.factorization 2
  set m : ℕ := n / 2^k with hm

  -- (1) 2^k ∣ n  (k is the 2-adic order)
  have hpow : 2^k ∣ n := by
    simpa [k] using (Nat.ordProj_dvd n 2)

  -- (2) n = 2^k * m
  have hn_eq : n = 2^k * m := by
    -- Nat.div_mul_cancel gives (n / 2^k) * 2^k = n
    -- flip sides and rearrange to taste
    simpa [m, Nat.mul_comm] using (Nat.div_mul_cancel hpow).symm

  -- (3) If m were even, we would get 2^(k+1) ∣ n
  have hnot : ¬ 2^(k+1) ∣ n := by
    -- the "maximality of factorization" lemma for p = 2
    simpa [k] using
      (Nat.pow_succ_factorization_not_dvd (Nat.ne_of_gt hn) Nat.prime_two)

  -- split on parity of m
  rcases Nat.even_or_odd m with hm_even | hm_odd
  · obtain ⟨m', hm_eq⟩ := hm_even
    have : 2^(k+1) ∣ n := by
      refine ⟨m', ?_⟩
      -- n = 2^k * (2 * m') = 2^(k+1) * m'
      rw [hn_eq, hm_eq, pow_succ]
      ring
    exact (hnot this).elim
  · exact hm_odd

/-- Helper: (1 + 2^t)^2 ≡ 1 (mod 2^{t+1}) for t ≥ 1

    This is a standard Hensel-type lifting lemma. The proof expands
    (1 + 2^t)^2 = 1 + 2·2^t + (2^t)^2 and observes that both
    2·2^t = 2^{t+1} and (2^t)^2 = 2^{2t} are divisible by the modulus 2^{t+1}.
-/
lemma one_plus_pow_two_sq (t : ℕ) (ht : t ≥ 1) :
  ((1 : ZMod (2^(t+1))) + (2^t : ZMod (2^(t+1))))^2 = 1 := by
  -- Разложим скобки и покажем, что оба лишних члена обнуляются
  have h_expand : ((1 : ZMod (2^(t+1))) + (2^t : ZMod (2^(t+1))))^2
                 = 1 + 2 * (2^t : ZMod (2^(t+1))) + (2^t : ZMod (2^(t+1)))^2 := by ring

  -- Покажем, что 2 * 2^t = 2^{t+1} = 0 в ZMod (2^{t+1})
  have h1 : (2 * 2^t : ZMod (2^(t+1))) = 0 := by
    norm_cast
    convert ZMod.natCast_self (2^(t+1)) using 1
    ring_nf

  -- Покажем, что (2^t)^2 = 0 в ZMod (2^{t+1})
  have h2 : ((2^t : ZMod (2^(t+1))))^2 = 0 := by
    have h_div : (2^(t+1) : ℕ) ∣ 2^t * 2^t := by
      have : 2^t * 2^t = 2^(t + t) := by rw [← pow_add]
      rw [this]
      apply pow_dvd_pow 2
      omega
    rw [sq]
    -- Цель: (2^t : ZMod) * (2^t : ZMod) = 0
    have : (2^t : ZMod (2^(t+1))) * (2^t : ZMod (2^(t+1))) = ((2^t * 2^t : ℕ) : ZMod (2^(t+1))) := by
      simp [Nat.cast_mul]
    rw [this, ZMod.natCast_eq_zero_iff]
    exact h_div

  -- Подставляем и упрощаем
  calc ((1 : ZMod (2^(t+1))) + (2^t : ZMod (2^(t+1))))^2
      = 1 + 2 * (2^t : ZMod (2^(t+1))) + (2^t : ZMod (2^(t+1)))^2 := by ring
    _ = 1 + 0 + 0 := by rw [h1, h2]
    _ = 1 := by ring

/-- Lifting lemma: if a^k ≡ 1 (mod 2^t), then a^{2k} ≡ 1 (mod 2^{t+1})

    This is the key doubling step used in proving ord_{2^t}(3) = 2^{t-2}.
    Standard result in modular arithmetic (Hensel lifting).

    Simplified proof: We work directly in ZMod using the two-element lifting.
    If a^k ≡ 1 (mod 2^t), then a^k mod 2^{t+1} ∈ {1, 1+2^t}.
    In both cases, squaring gives 1 mod 2^{t+1}.
-/
lemma pow_lift_double {a k t : ℕ} (_ha : Odd a) (ht : t ≥ 1) (h : (a : ZMod (2^t))^k = 1) :
  (a : ZMod (2^(t+1)))^(2*k) = 1 := by
  rw [mul_comm 2 k, pow_mul]
  -- Let x = (a : ZMod (2^{t+1}))^k
  -- From h: a^k ≡ 1 (mod 2^t), so x ∈ {1, 1+2^t} in ZMod (2^{t+1})
  -- Need to show: x^2 = 1

  -- Use castHom to relate the two rings
  -- Since a^k ≡ 1 (mod 2^t), we have a^k = 1 + m·2^t for some m
  -- When viewed mod 2^{t+1}, either m is even (so a^k ≡ 1) or m is odd (so a^k ≡ 1 + 2^t)
  have h_lift : (a : ZMod (2^(t+1)))^k = 1 ∨ (a : ZMod (2^(t+1)))^k = 1 + (2^t : ZMod (2^(t+1))) := by
    -- From h: (a : ZMod (2^t))^k = 1, мы знаем что a^k ≡ 1 (mod 2^t)
    -- Это означает 2^t | (a^k - 1), т.е. a^k = 1 + m·2^t для некоторого m
    -- В ZMod (2^{t+1}): либо m четное → a^k ≡ 1, либо m нечетное → a^k ≡ 1 + 2^t

    -- Переведем h к делимости: (a : ZMod (2^t))^k = 1 означает 2^t ∣ a^k - 1
    have h_nat : 2^t ∣ a^k - 1 := by
      have ha_ge : a^k ≥ 1 := Nat.one_le_pow k a (Nat.pos_of_ne_zero (Odd.pos _ha).ne')
      rw [← ZMod.natCast_eq_zero_iff]
      calc ((a^k - 1 : ℕ) : ZMod (2^t))
          = (a^k : ZMod (2^t)) - (1 : ZMod (2^t)) := by
            rw [Nat.cast_sub ha_ge]; norm_cast
        _ = 1 - 1 := by rw [h]
        _ = 0 := by norm_num

    -- Существует m такое, что a^k - 1 = m·2^t, т.е. a^k = 1 + m·2^t
    obtain ⟨m, hm⟩ := h_nat

    -- Рассмотрим четность m
    rcases Nat.even_or_odd m with ⟨m', hm_even⟩ | ⟨m', hm_odd⟩
    · -- Случай 1: m = 2·m' (четное) → a^k ≡ 1 (mod 2^{t+1})
      left
      -- a^k - 1 = (2·m')·2^t = m'·2^{t+1}, поэтому a^k = 1 + m'·2^{t+1} ≡ 1 (mod 2^{t+1})
      have h_div : a^k - 1 = m' * 2^(t+1) := by
        calc a^k - 1
            = 2^t * m := hm
          _ = 2^t * (m' + m') := by rw [hm_even]
          _ = 2^t * (2 * m') := by ring
          _ = m' * 2^(t+1) := by rw [pow_succ]; ring
      have ha_ge : a^k ≥ 1 := Nat.one_le_pow k a (Nat.pos_of_ne_zero (Odd.pos _ha).ne')
      have ha_eq : a^k = m' * 2^(t+1) + 1 := by
        have : a^k = a^k - 1 + 1 := by omega
        rw [this, h_div]
      calc (a^k : ZMod (2^(t+1)))
          = ((m' * 2^(t+1) + 1 : ℕ) : ZMod (2^(t+1))) := by norm_cast; rw [ha_eq]
        _ = (1 : ZMod (2^(t+1))) := by simp

    · -- Случай 2: m = 2·m' + 1 (нечетное) → a^k ≡ 1 + 2^t (mod 2^{t+1})
      right
      -- a^k - 1 = (2·m'+1)·2^t = m'·2^{t+1} + 2^t, поэтому a^k = m'·2^{t+1} + 2^t + 1
      have h_div : a^k - 1 = m' * 2^(t+1) + 2^t := by
        calc a^k - 1
            = 2^t * m := hm
          _ = 2^t * (2 * m' + 1) := by rw [hm_odd]
          _ = 2^t * 2 * m' + 2^t := by ring
          _ = m' * 2^(t+1) + 2^t := by rw [pow_succ]; ring
      have ha_ge : a^k ≥ 1 := Nat.one_le_pow k a (Nat.pos_of_ne_zero (Odd.pos _ha).ne')
      have ha_eq : a^k = m' * 2^(t+1) + 2^t + 1 := by
        have : a^k = a^k - 1 + 1 := by omega
        rw [this, h_div]
      calc (a^k : ZMod (2^(t+1)))
          = ((m' * 2^(t+1) + 2^t + 1 : ℕ) : ZMod (2^(t+1))) := by norm_cast; rw [ha_eq]
        _ = ((2^t + 1 : ℕ) : ZMod (2^(t+1))) := by simp
        _ = (1 : ZMod (2^(t+1))) + (2^t : ZMod (2^(t+1))) := by norm_cast; ring_nf

  rcases h_lift with h1 | h2
  · -- Case 1: (a : ZMod (2^{t+1}))^k = 1
    rw [h1]
    norm_num
  · -- Case 2: (a : ZMod (2^{t+1}))^k = 1 + 2^t
    rw [h2]
    -- Применяем one_plus_pow_two_sq напрямую
    exact one_plus_pow_two_sq t ht

/-! ## Helper леммы для конвертации между Int.ModEq и ZMod -/

/-- Эквивалентность Int.ModEq и равенства в ZMod для натуральных чисел -/
lemma int_modEq_iff_zmod_eq {a b n : ℕ} :
  (a : ℤ) ≡ (b : ℤ) [ZMOD (n : ℤ)] ↔ (a : ZMod n) = (b : ZMod n) := by
  constructor
  · intro h
    -- Int.ModEq → ZMod
    have : ((a : ℤ) : ZMod n) = ((b : ℤ) : ZMod n) := by
      rw [ZMod.intCast_eq_intCast_iff]
      exact h
    have ha : ((a : ℤ) : ZMod n) = ((a : ℕ) : ZMod n) := by norm_cast
    have hb : ((b : ℤ) : ZMod n) = ((b : ℕ) : ZMod n) := by norm_cast
    rw [ha, hb] at this
    exact this
  · intro h
    -- ZMod → Int.ModEq
    rw [← ZMod.intCast_eq_intCast_iff]
    have ha : ((a : ℤ) : ZMod n) = ((a : ℕ) : ZMod n) := by norm_cast
    have hb : ((b : ℤ) : ZMod n) = ((b : ℕ) : ZMod n) := by norm_cast
    rw [ha, hb, h]

/-- Конвертация из Int.ModEq к ZMod для натуральных чисел -/
lemma int_modEq_to_zmod {a b n : ℕ} (h : (a : ℤ) ≡ (b : ℤ) [ZMOD (n : ℤ)]) :
  (a : ZMod n) = (b : ZMod n) := by
  rw [← int_modEq_iff_zmod_eq]
  exact h

/-- Конвертация из ZMod к Int.ModEq для натуральных чисел -/
lemma zmod_to_int_modEq {a b n : ℕ} (h : (a : ZMod n) = (b : ZMod n)) :
  (a : ℤ) ≡ (b : ℤ) [ZMOD (n : ℤ)] := by
  rw [int_modEq_iff_zmod_eq]
  exact h

/-- Степень с натуральным основанием коммутирует с кастом ℤ → ZMod -/
lemma natCast_pow_zmod_eq_one {a n k : ℕ} :
  (((a : ℤ) : ZMod n)^k = 1) ↔ ((a : ZMod n)^k = 1) := by
  have : ((a : ℤ) : ZMod n) = ((a : ℕ) : ZMod n) := by norm_cast
  rw [this]

/-- Конвертация степеней между ℕ и ℤ в ZMod -/
lemma natCast_pow_eq_intCast_pow {a k n : ℕ} :
  ((a^k : ℕ) : ZMod n) = ((a : ℕ) : ZMod n)^k := by
  norm_cast

/-- Exponent at step m: e(m) = ν_2(3m+1) -/
def e (m : ℕ) : ℕ :=
  if m = 0 then 0
  else (3 * m + 1).factorization 2

end Collatz.Arithmetic
