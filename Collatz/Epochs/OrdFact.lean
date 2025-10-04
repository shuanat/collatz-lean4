/-
Collatz Conjecture: Ord‑Fact Theorem
Main theorem: ord_{2^t}(3) = 2^{t-2} for t ≥ 3

This is the foundational theorem for phase mixing analysis.
It states that the multiplicative order of 3 modulo 2^t is exactly Q_t = 2^{t-2}.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Collatz.Foundations.Arithmetic
import Mathlib.Data.ZMod.Basic



open Collatz.Arithmetic

namespace Collatz.OrdFact

/-- Q_t definition: ord_{2^t}(3) for t ≥ 3 -/
def Q_t (t : ℕ) : ℕ := 2^(t-2)

/-!
## Helper Lemmas

These lemmas are used to prove the main Ord‑Fact theorem.
-/

/-- 3^{2^{t-2}} ≡ 1 (mod 2^t) for t ≥ 3 -/
lemma three_pow_Qt_eq_one (t : ℕ) (ht : t ≥ 3) :
  (3 : ZMod (2^t))^(Q_t t) = 1 := by
  -- Strategy: Prove by strong induction on t
  -- Base case: t = 3 → Q_3 = 2 → 3^2 ≡ 1 (mod 8)
  -- Inductive step: Use lifting lemma for doubling modulus

  induction t, ht using Nat.le_induction with
  | base =>
    -- Base case: t = 3, Q_3 = 2, show (3 : ZMod 8)^2 = 1
    unfold Q_t
    decide
  | succ t ht ih =>
    -- Inductive step: t → t+1
    -- Given: (3 : ZMod (2^t))^(2^{t-2}) = 1
    -- Show: (3 : ZMod (2^{t+1}))^(2^{t-1}) = 1
    unfold Q_t at ih ⊢
    simp only [Nat.succ_sub_succ_eq_sub] at ih ⊢

    -- Key: 2^{t-1} = 2 * 2^{t-2}
    have h_double : 2^(t-1) = 2 * 2^(t-2) := by
      cases t with
      | zero => omega
      | succ t' =>
        cases t' with
        | zero => omega
        | succ t'' =>
          simp [pow_succ]
          ring

    rw [h_double]

    -- Apply lifting lemma (3 is odd)
    have ht_ge : t ≥ 1 := by omega
    have h_odd : Odd 3 := by norm_num
    exact Arithmetic.pow_lift_double h_odd ht_ge ih

/-  (removed auxiliary lemma; not needed for the main theorem) -/

/-!
## Helper: 2-adic Valuation of 3^{2^k} - 1

Key fact: ν₂(3^{2^k} - 1) = k + 2 for k ≥ 0
This is the Lifting-the-Exponent (LTE) lemma for p=2.
-/

/-- 2-adic valuation of 3^{2^k} - 1 equals k + 2

    This is a consequence of the Lifting-the-Exponent lemma.
    For our purposes: 3^{2^k} ≡ 1 (mod 2^{k+2}) but 3^{2^k} ≢ 1 (mod 2^{k+3})
-/
lemma three_pow_two_pow_sub_one_valuation (k : ℕ) (hk : k ≥ 1) :
  (3 : ℤ)^(2^k) ≡ 1 [ZMOD 2^(k+2)] ∧ ¬((3 : ℤ)^(2^k) ≡ 1 [ZMOD 2^(k+3)]) := by
  induction k with
  | zero => omega  -- k = 0 противоречит hk : k ≥ 1
  | succ k ih =>
    by_cases hk_prev : k = 0
    · -- Базовый случай: k = 0 → k+1 = 1
      -- Нужно: 3^2 ≡ 1 (mod 8) ∧ ¬(3^2 ≡ 1 (mod 16))
      subst hk_prev
      constructor
      · -- 3^2 = 9 ≡ 1 mod 8
        norm_num
      · -- 3^2 = 9 ≢ 1 mod 16
        intro h
        norm_num at h
    · -- Индуктивный шаг: k ≥ 1
      have hk_ge : k ≥ 1 := Nat.one_le_of_lt (Nat.pos_of_ne_zero hk_prev)
      have ⟨ih_lower, ih_upper⟩ := ih hk_ge
      constructor
      · -- Нижняя граница: 3^{2^{k+1}} ≡ 1 (mod 2^{k+3})
        -- Используем pow_lift_double
        have h_exp : 2^(k+1) = 2 * 2^k := by ring
        rw [h_exp]
        -- Конвертируем ih_lower в ZMod
        -- 1) Turn [ZMOD] into [MOD]
        have ih_nat : 3 ^ 2 ^ k ≡ 1 [MOD 2 ^ (k + 2)] := by
          -- both sides/modulus are naturals coerced to ℤ
          simpa using
            (Int.natCast_modEq_iff).mp (by simpa using ih_lower)

        -- 2) Use the Nat-version bridge to ZMod equality
        have h' :
            ((3 ^ (2 ^ k) : ℕ) : ZMod (2^(k+2))) = (1 : ZMod (2^(k+2))) := by
          have h :=
            (ZMod.natCast_eq_natCast_iff
                (a := 3 ^ (2 ^ k)) (b := 1) (c := 2 ^ (k + 2))).mpr ih_nat
          simpa [Nat.cast_one] using h

        -- 3) Final shape
        have h_zmod : (3 : ZMod (2^(k+2)))^(2^k) = 1 := by
          simpa [Nat.cast_pow] using h'
        -- Применяем pow_lift_double
        have ht : k + 2 ≥ 1 := by omega
        have h_lifted : (3 : ZMod (2^(k+3)))^(2 * 2^k) = 1 :=
          Arithmetic.pow_lift_double Arithmetic.three_odd ht h_zmod
        -- Конвертируем обратно в Int.ModEq
        -- 1) equality in ZMod → Nat.ModEq
        have h_lifted_nat :
            ((3^(2*2^k) : ℕ) : ZMod (2^(k+3))) = (1 : ZMod (2^(k+3))) := by
          simpa [Nat.cast_pow, Nat.cast_mul] using h_lifted

        have h_mod_nat : 3^(2*2^k) ≡ 1 [MOD 2^(k+3)] :=
          (ZMod.natCast_eq_natCast_iff
              (a := 3^(2*2^k)) (b := 1) (c := 2^(k+3))).mp
            (by simpa [Nat.cast_one] using h_lifted_nat)

        -- 2) Nat.ModEq → Int.ModEq
        have h_mod_int : (3 : ℤ)^(2*2^k) ≡ 1 [ZMOD 2^(k+3)] := by
          simpa using (Int.natCast_modEq_iff).mpr h_mod_nat

        exact h_mod_int
      · -- Верхняя граница: ¬(3^{2^{k+1}} ≡ 1 (mod 2^{k+4}))
        intro h_contra
        -- Если бы 3^{2^{k+1}} ≡ 1 (mod 2^{k+4}), то 3^{2^k} ≡ ±1 (mod 2^{k+3})
        -- Но из ih_lower: 3^{2^k} ≡ 1 (mod 2^{k+2}), значит 3^{2^k} = 1 + r·2^{k+2}
        -- Если 3^{2^{k+1}} ≡ 1 (mod 2^{k+4}), то (3^{2^k})^2 ≡ 1 (mod 2^{k+4})
        -- Из (1 + r·2^{k+2})^2 ≡ 1 (mod 2^{k+4}) получаем
        -- 1 + 2r·2^{k+2} + r^2·2^{2k+4} ≡ 1 (mod 2^{k+4})
        -- 2r·2^{k+2} ≡ 0 (mod 2^{k+4}), т.е. r·2^{k+3} ≡ 0 (mod 2^{k+4})
        -- Значит r чётно, т.е. 3^{2^k} ≡ 1 (mod 2^{k+3}), противоречие с ih_upper
        have h_exp : 2^(k+1) = 2 * 2^k := by ring
        rw [h_exp] at h_contra
        -- 3^{2·2^k} = (3^{2^k})^2
        have h_sq : (3 : ℤ)^(2 * 2^k) = ((3 : ℤ)^(2^k))^2 := by
          rw [← pow_mul]; ring_nf
        rw [h_sq] at h_contra
        -- Пусть a = 3^{2^k}, тогда a ≡ 1 (mod 2^{k+2}) и a^2 ≡ 1 (mod 2^{k+4})
        set a := (3 : ℤ)^(2^k)
        -- Из ih_lower и Int.ModEq получаем делимость 2^{k+2} ∣ (a - 1)
        have h_div_lower : (2^(k+2) : ℤ) ∣ (a - 1) := by
          rw [Int.modEq_iff_dvd, dvd_sub_comm] at ih_lower
          exact ih_lower
        -- Значит a = 1 + r·2^{k+2} для некоторого r
        obtain ⟨r, hr⟩ := h_div_lower
        -- Из h_contra: a^2 ≡ 1 (mod 2^{k+4}), т.е. 2^{k+4} ∣ (a^2 - 1)
        have h_div_contra : (2^(k+4) : ℤ) ∣ (a^2 - 1) := by
          rw [Int.modEq_iff_dvd, dvd_sub_comm] at h_contra
          exact h_contra
        -- Разложим: a^2 - 1 = (a - 1)(a + 1) = r·2^{k+2}·(2 + r·2^{k+2})
        have h_factor : a^2 - 1 = r * 2^(k+2) * (2 + r * 2^(k+2)) := by
          have ha : a = 1 + r * 2^(k+2) := by
            have := congrArg (fun z : ℤ => z + 1) hr
            simpa [sub_add_cancel, add_comm, add_left_comm, add_assoc,
                   mul_comm, mul_left_comm, mul_assoc] using this
          calc a^2 - 1
              = (a - 1) * (a + 1) := by ring
            _ = r * 2^(k+2) * (a + 1) := by rw [hr]; ring
            _ = r * 2^(k+2) * ((1 + r * 2^(k+2)) + 1) := by rw [← ha]
            _ = r * 2^(k+2) * (2 + r * 2^(k+2)) := by ring
        rw [h_factor] at h_div_contra
        -- Из делимости 2^{k+4} ∣ r·2^{k+2}·(2 + r·2^{k+2}) и того, что 2 ∤ (2 + r·2^{k+2})
        -- (так как 2 + r·2^{k+2} ≡ 2 (mod 4) при k ≥ 1), получаем 2^2 ∣ r, т.е. r чётно
        have h_r_even : (2 : ℤ) ∣ r := by
          -- Перепишем: 2^{k+4} ∣ r·2^{k+2}·(2 + r·2^{k+2}) ⇒ 2^2 ∣ r·(2 + r·2^{k+2})
          have : (4 : ℤ) ∣ r * (2 + r * 2^(k+2)) := by
            have h_cancel : (2 : ℤ) ^ (k + 4) = (2 : ℤ) ^ (k + 2) * 4 := by
              simpa [Nat.add_assoc, pow_two, two_mul] using
                (pow_add (2 : ℤ) (k + 2) 2)
            rw [h_cancel] at h_div_contra
            have hpos : (0 : ℤ) < 2^(k+2) := by
              have : (0 : ℤ) < (2 : ℤ) := by decide
              exact pow_pos this (k+2)
            obtain ⟨q, hq⟩ := h_div_contra
            use q
            have h1 : r * 2^(k+2) * (2 + r * 2^(k+2)) = 2^(k+2) * 4 * q := hq
            have h2 : r * 2^(k+2) * (2 + r * 2^(k+2)) = 2^(k+2) * (4 * q) := by ring_nf at h1 ⊢; exact h1
            have h3 : 2^(k+2) * (r * (2 + r * 2^(k+2))) = 2^(k+2) * (4 * q) := by ring_nf at h2 ⊢; exact h2
            have : r * (2 + r * 2^(k+2)) = 4 * q := Int.eq_of_mul_eq_mul_left (ne_of_gt hpos) h3
            exact this
          -- 2 + r·2^{k+2} ≡ 2 (mod 4) (так как k ≥ 1 ⇒ k+2 ≥ 3 ⇒ 2^{k+2} ≡ 0 (mod 4))
          have h_mod4 : (2 + r * 2^(k+2)) % 4 = 2 % 4 := by
            have h_pow : (2^(k+2) : ℤ) % 4 = 0 := by
              have : k + 2 ≥ 2 := by omega
              have : (2^(k+2) : ℤ) = 4 * 2^k := by
                calc (2^(k+2) : ℤ)
                    = 2^(2 + k) := by rw [add_comm]
                  _ = 2^2 * 2^k := by rw [← pow_add]
                  _ = 4 * 2^k := by norm_num
              rw [this, Int.mul_emod_right]
            calc (2 + r * 2^(k+2)) % 4
                = (2 % 4 + (r * 2^(k+2)) % 4) % 4 := by rw [Int.add_emod]
              _ = (2 % 4 + (r % 4 * (2^(k+2) % 4)) % 4) % 4 := by rw [Int.mul_emod]
              _ = (2 % 4 + (r % 4 * 0) % 4) % 4 := by rw [h_pow]
              _ = (2 % 4 + 0) % 4 := by norm_num
              _ = 2 % 4 := by norm_num
          -- Значит 2 + r·2^{k+2} = 2 + 4·t для некоторого t, т.е. 2 | (2 + r·2^{k+2})
          -- но ¬(4 | (2 + r·2^{k+2})) (так как остаток 2, а не 0)
          have h_not_div4 : ¬ (4 : ℤ) ∣ (2 + r * 2^(k+2)) := by
            intro h
            rw [Int.dvd_iff_emod_eq_zero] at h
            rw [h_mod4] at h
            norm_num at h
          have h_div2 : (2 : ℤ) ∣ (2 + r * 2^(k+2)) := by
            rw [Int.dvd_iff_emod_eq_zero]
            have : (2 + r * 2^(k+2)) % 2 = 2 % 2 := by
              have : (2^(k+2) : ℤ) % 2 = 0 := by
                have : (2^(k+2) : ℤ) = 2 * 2^(k+1) := by rw [pow_succ]; ring
                rw [this]
                norm_num
              calc (2 + r * 2^(k+2)) % 2
                  = (2 % 2 + (r * 2^(k+2)) % 2) % 2 := by rw [Int.add_emod]
                _ = (2 % 2 + (r % 2 * (2^(k+2) % 2)) % 2) % 2 := by rw [Int.mul_emod]
                _ = (2 % 2 + (r % 2 * 0) % 2) % 2 := by rw [this]
                _ = 2 % 2 := by norm_num
            simpa using this
          -- Из 4 ∣ r·(2 + r·2^{k+2}), 2 ∣ (2 + r·2^{k+2}), ¬(4 ∣ (2 + r·2^{k+2}))
          -- получаем 2 ∣ r
          obtain ⟨u, hu⟩ := h_div2
          rw [hu] at this
          -- 4 ∣ r·2·u ⇒ 2 ∣ r·u
          have : (2 : ℤ) ∣ r * u := by
            have h4 : (4 : ℤ) = 2 * 2 := by norm_num
            rw [h4] at this
            obtain ⟨q, hq⟩ := this
            -- r * (2 * u) = 2 * 2 * q
            have : r * u * 2 = 2 * (2 * q) := by
              calc r * u * 2 = r * (u * 2) := by ring
                   _ = r * (2 * u) := by ring
                   _ = 2 * 2 * q := hq
                   _ = 2 * (2 * q) := by ring
            have h_cancel : r * u * 2 = 2 * (r * u) := by ring
            have h_eq : 2 * (r * u) = 2 * (2 * q) := by rw [← h_cancel]; exact this
            have h_ru : r * u = 2 * q := by
              have : (2 : ℤ) ≠ 0 := by norm_num
              exact Int.eq_of_mul_eq_mul_left this h_eq
            exact ⟨q, h_ru⟩
          -- Если u нечётно, то 2 ∣ r; если u чётно, то из ¬(4 ∣ 2·u) следует u нечётно
          by_cases hu_even : (2 : ℤ) ∣ u
          · -- u чётно ⇒ 2 + r·2^{k+2} = 2·u ⇒ 4 ∣ (2 + r·2^{k+2}), противоречие
            rw [hu] at h_not_div4
            obtain ⟨v, hv⟩ := hu_even
            have : (4 : ℤ) ∣ 2 * u := by
              rw [hv]
              use v
              ring
            exact absurd this h_not_div4
          · -- u нечётно ⇒ из 2 ∣ r·u следует 2 ∣ r
            have h_prime : Prime (2 : ℤ) := by norm_num
            exact (Prime.dvd_mul h_prime).mp this |>.resolve_right hu_even
        -- Если r = 2s, то a = 1 + 2s·2^{k+2} = 1 + s·2^{k+3}, т.е. a ≡ 1 (mod 2^{k+3})
        obtain ⟨s, hs⟩ := h_r_even
        have h_contra_upper : a ≡ 1 [ZMOD 2^(k+3)] := by
          have ha : a = 1 + s * 2^(k+3) := by
            have h1 : a = 1 + r * 2^(k+2) := by
              have := congrArg (fun z : ℤ => z + 1) hr
              simpa [sub_add_cancel, add_comm, mul_comm] using this
            calc a
                = 1 + r * 2^(k+2) := h1
              _ = 1 + (2 * s) * 2^(k+2) := by rw [hs]
              _ = 1 + s * (2 * 2^(k+2)) := by ring
              _ = 1 + s * 2^(k+3) := by
                have : (2 : ℤ) * 2^(k+2) = 2^(k+3) := by
                  calc (2 : ℤ) * 2^(k+2)
                      = 2^1 * 2^(k+2) := by norm_num
                    _ = 2^(1 + (k+2)) := by rw [← pow_add]
                    _ = 2^(k+3) := by ring
                rw [this]
          rw [Int.modEq_iff_dvd, dvd_sub_comm]
          use s
          rw [ha]
          ring
        -- Противоречие с ih_upper
        exact ih_upper h_contra_upper

/-- If m < t-2 (with t ≥ 3), then (3 : ZMod (2^t))^(2^m) ≠ 1. -/
lemma three_pow_twoPow_lt_Qt_ne_one (t : ℕ) (ht : t ≥ 3)
    (m : ℕ) (hm : m < t - 2) :
  (3 : ZMod (2^t))^(2^m) ≠ 1 := by
  -- handle m = 0 directly: (3 : ZMod (2^t)) ≠ 1 for t ≥ 3
  by_cases hm0 : m = 0
  · subst hm0
    -- goal: (3 : ZMod (2^t))^1 ≠ 1
    have h3ne1 : (3 : ZMod (2^t)) ≠ 1 := by
      -- Since t ≥ 3, we have 2^t ≥ 8 > 3, so 3 and 1 are distinct in ZMod (2^t)
      have ht_large : 2^t > 3 := by
        have : 2^t ≥ 2^3 := Nat.pow_le_pow_right (by decide) ht
        omega
      intro h_eq
      have : 3 ≡ 1 [MOD 2^t] := by
        exact (ZMod.natCast_eq_natCast_iff (a := 3) (b := 1) (c := 2^t)).mp
          (by simpa [Nat.cast_one] using h_eq)
      have : (2^t : ℕ) ∣ 2 := by
        have h_dvd_int := Nat.ModEq.dvd this
        exact Int.natCast_dvd.mp h_dvd_int
      have : 2^t ≤ 2 := Nat.le_of_dvd (by decide) this
      omega
    simpa [pow_one] using h3ne1
  · -- now m ≥ 1
    have hm1 : m ≥ 1 := Nat.pos_of_ne_zero hm0
    have hval := three_pow_two_pow_sub_one_valuation m hm1
    have h_upper := hval.2
    -- Suppose contrary in ZMod (2^t)
    intro h_contra
    -- ZMod equality → Nat.ModEq → Int.ModEq
    have h_zmod_nat :
      ((3^(2^m) : ℕ) : ZMod (2^t)) = (1 : ZMod (2^t)) := by
      simpa [Nat.cast_pow, Nat.cast_one] using h_contra
    have h_mod_nat : 3^(2^m) ≡ 1 [MOD 2^t] :=
      (ZMod.natCast_eq_natCast_iff (a := 3^(2^m)) (b := 1) (c := 2^t)).mp
        (by simpa [Nat.cast_one] using h_zmod_nat)
    have h_mod_int_t : (3 : ℤ)^(2^m) ≡ 1 [ZMOD 2^t] := by
      simpa using (Int.natCast_modEq_iff).mpr h_mod_nat
    have h_dvd_t : (2^t : ℤ) ∣ ((3 : ℤ)^(2^m) - 1) := by
      simpa [Int.modEq_iff_dvd, dvd_sub_comm] using h_mod_int_t

    -- из m < t - 2 → m+3 ≤ t, значит 2^(m+3) ∣ 2^t
    have hm3_le_t : m + 3 ≤ t := by omega
    have h_pow_dvd_nat : (2^(m+3) : ℕ) ∣ 2^t :=
      Nat.pow_dvd_pow 2 hm3_le_t
    have h_pow_dvd_z : (2^(m+3) : ℤ) ∣ (2^t : ℤ) := by
      have : ((2^(m+3) : ℕ) : ℤ) ∣ ((2^t : ℕ) : ℤ) := by
        obtain ⟨k, hk⟩ := h_pow_dvd_nat
        use (k : ℤ)
        simp [hk]
      simpa using this

    -- транзитивность делимости
    have h_dvd_m3 : (2^(m+3) : ℤ) ∣ ((3 : ℤ)^(2^m) - 1) :=
      Int.dvd_trans h_pow_dvd_z h_dvd_t

    -- получаем конгруэнцию mod 2^(m+3) и противоречим h_upper
    have : (3 : ℤ)^(2^m) ≡ 1 [ZMOD 2^(m+3)] := by
      simpa [Int.modEq_iff_dvd, dvd_sub_comm] using h_dvd_m3
    exact h_upper this

/-- Minimality: for any k < Q_t, (3 : ZMod (2^t))^k ≠ 1. -/
lemma three_pow_lt_Qt_ne_one (t : ℕ) (ht : t ≥ 3) (k : ℕ) (hkpos : 0 < k) (hk : k < Q_t t) :
  (3 : ZMod (2^t))^k ≠ 1 := by
  intro h
  -- Let d = orderOf(3) in ZMod (2^t). From three_pow_Qt_eq_one we get d ∣ 2^(t-2).
  have h_div_Qt : orderOf (3 : ZMod (2^t)) ∣ 2^(t-2) := by
    have hPow : (3 : ZMod (2^t))^(2^(t-2)) = 1 := three_pow_Qt_eq_one t ht
    simpa [Q_t] using
      (orderOf_dvd_iff_pow_eq_one (x := (3 : ZMod (2^t))) (n := 2^(t-2))).2 hPow
  obtain ⟨m, hm_le, hm_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h_div_Qt
  -- And from h we get d ∣ k
  have h_div_k : orderOf (3 : ZMod (2^t)) ∣ k :=
    (orderOf_dvd_iff_pow_eq_one (x := (3 : ZMod (2^t))) (n := k)).mpr
      (by simpa using (h : (3 : ZMod (2^t))^k = 1))
  -- If m = t-2 then 2^(t-2) ∣ k contradicts k < 2^(t-2)
  by_cases hmeq : m = t - 2
  · subst hmeq
    have : (2^(t-2)) ∣ k := by simpa [hm_eq]
      using h_div_k
    have : 2^(t-2) ≤ k :=
      Nat.le_of_dvd hkpos this
    exact (not_lt_of_ge this) (by simpa [Q_t] using hk)
  -- Otherwise m < t-2, and so (3)^(2^m) ≠ 1 by the 2-adic valuation lemma
  have hm_lt : m < t - 2 := lt_of_le_of_ne hm_le hmeq
  have h_base : (3 : ZMod (2^t))^(2^m) ≠ 1 := three_pow_twoPow_lt_Qt_ne_one t ht m hm_lt
  -- But (3)^(orderOf 3) = 1; with d = 2^m this contradicts h_base
  have : (3 : ZMod (2^t))^(orderOf (3 : ZMod (2^t))) = 1 := pow_orderOf_eq_one _
  have : (3 : ZMod (2^t))^(2^m) = 1 := by simpa [hm_eq] using this
  exact h_base this

/-!
## Main Theorem: Ord‑Fact

For t ≥ 3, the multiplicative order of 3 modulo 2^t equals 2^{t-2}.
-/

/-- Main theorem: ord_{2^t}(3) = 2^{t-2} for t ≥ 3

    PROOF STRATEGY (avoiding circular dependency):
    1. Show: 3^{Q_t} ≡ 1 (mod 2^t) via three_pow_Qt_eq_one
    2. Therefore: orderOf 3 ∣ Q_t (via orderOf_dvd_iff_pow_eq_one)
    3. Since Q_t = 2^{t-2}, divisors are 2^k for k ≤ t-2 (via Nat.dvd_prime_pow)
    4. Exclude k < t-2 by showing 3^{2^k} ≠ 1 (mod 2^t) for k < t-2
    5. Therefore: orderOf 3 = 2^{t-2} = Q_t

    This approach integrates minimality directly, avoiding separate lemma dependency.
-/
theorem ord_three_mod_pow_two (t : ℕ) (ht : t ≥ 3) :
  orderOf (3 : ZMod (2^t)) = Q_t t := by
  -- Step 1: 3^{Q_t} = 1 (mod 2^t)
  have h_pow_Qt : (3 : ZMod (2^t))^(Q_t t) = 1 := three_pow_Qt_eq_one t ht

  -- Step 2: orderOf 3 ∣ Q_t (since Q_t = 2^{t-2})
  have h_div_Qt : orderOf (3 : ZMod (2^t)) ∣ Q_t t :=
    (orderOf_dvd_iff_pow_eq_one (x := (3 : ZMod (2^t))) (n := Q_t t)).2 h_pow_Qt

  -- Step 3: Q_t = 2^{t-2}, so divisors are 2^k for k ≤ t-2
  rw [Q_t] at h_div_Qt
  have ht2 : t ≥ 2 := by omega  -- t ≥ 3 implies t-2 ≥ 1

  -- Apply Nat.dvd_prime_pow: if d ∣ 2^{t-2}, then d = 2^k for some k ≤ t-2
  obtain ⟨k, hk, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h_div_Qt

  -- Step 4: Exclude k < t-2 (minimality)
  have h_minimal : k = t - 2 := by
    by_contra h_ne
    have hk_lt : k < t - 2 := lt_of_le_of_ne hk h_ne
    have h_ne_one : (3 : ZMod (2^t))^(2^k) ≠ 1 :=
      three_pow_twoPow_lt_Qt_ne_one t ht k hk_lt
    have h_eq_one : (3 : ZMod (2^t))^(2^k) = 1 := by
      simpa [hk_eq] using pow_orderOf_eq_one (3 : ZMod (2^t))
    exact h_ne_one h_eq_one

  -- Step 5: Conclude orderOf 3 = 2^{t-2} = Q_t
  calc orderOf (3 : ZMod (2^t)) = 2^k := hk_eq
       _ = 2^(t-2) := by rw [h_minimal]
       _ = Q_t t := by rfl

/-!
## Concrete Examples

Verify the theorem for small values of t.
-/

/-- Example: ord_8(3) = 2 (t=3) -/
example : orderOf (3 : ZMod 8) = 2 := by
  have hx2 : (3 : ZMod 8) ^ 2 = 1 := by decide
  have hdiv : orderOf (3 : ZMod 8) ∣ (2^1 : ℕ) := by
    rw [show (2^1 : ℕ) = 2 by norm_num]
    exact (orderOf_dvd_iff_pow_eq_one (x := (3 : ZMod 8)) (n := 2)).2 hx2
  -- Divisors of 2^1 are 2^k for k ≤ 1
  rcases (Nat.dvd_prime_pow Nat.prime_two).1 hdiv with ⟨k, hk, hkEq⟩
  -- Exclude k = 0 (d = 1): would mean 3 = 1
  have h3ne1 : (3 : ZMod 8) ≠ 1 := by decide
  have hk_ne0 : k ≠ 0 := by
    intro h; have : orderOf (3 : ZMod 8) = 1 := by simp [hkEq, h]
    have := (orderOf_eq_one_iff (x := (3 : ZMod 8))).1 this
    exact h3ne1 this
  -- Remaining: k = 1
  have : k = 1 := by omega
  simp [hkEq, this]

/-- Example: ord_16(3) = 4 (t=4) -/
example : orderOf (3 : ZMod 16) = 4 := by
  have hx4  : (3 : ZMod 16) ^ 4 = 1 := by decide
  have hx2n : (3 : ZMod 16) ^ 2 ≠ 1 := by decide
  have hdiv : orderOf (3 : ZMod 16) ∣ (2^2 : ℕ) := by
    rw [show (2^2 : ℕ) = 4 by norm_num]
    exact (orderOf_dvd_iff_pow_eq_one (x := (3 : ZMod 16)) (n := 4)).2 hx4
  -- d ∣ 2^2 ⇒ d = 2^k, k ≤ 2
  obtain ⟨k, hk, hkEq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv
  -- Exclude k = 0 (d=1): would mean 3=1
  have h3ne1 : (3 : ZMod 16) ≠ 1 := by decide
  have hk_ne0 : k ≠ 0 := by
    intro h; have : orderOf (3 : ZMod 16) = 1 := by simp [hkEq, h]
    have := (orderOf_eq_one_iff (x := (3 : ZMod 16))).1 this
    exact h3ne1 this
  -- Exclude k = 1 (d=2): would mean 3^2 = 1, contradicts hx2n
  have hk_ne1 : k ≠ 1 := by
    intro h
    have : orderOf (3 : ZMod 16) ∣ 2 := by simp [hkEq, h]
    have : (3 : ZMod 16) ^ 2 = 1 :=
      (orderOf_dvd_iff_pow_eq_one (x := (3 : ZMod 16)) (n := 2)).1 this
    exact (hx2n this).elim
  -- Remaining: k = 2
  have : k = 2 := by omega
  simp [hkEq, this]

/-- Example: ord_32(3) = 8 (t=5) -/
example : orderOf (3 : ZMod 32) = 8 := by
  have hx8  : (3 : ZMod 32) ^ 8 = 1 := by decide
  have hx4n : (3 : ZMod 32) ^ 4 ≠ 1 := by decide
  have hx2n : (3 : ZMod 32) ^ 2 ≠ 1 := by decide
  have hdiv : orderOf (3 : ZMod 32) ∣ (2^3 : ℕ) := by
    rw [show (2^3 : ℕ) = 8 by norm_num]
    exact (orderOf_dvd_iff_pow_eq_one (x := (3 : ZMod 32)) (n := 8)).2 hx8
  obtain ⟨k, hk, hkEq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv  -- d = 2^k, k ≤ 3
  have h3ne1 : (3 : ZMod 32) ≠ 1 := by decide
  have hk_ne0 : k ≠ 0 := by
    intro h; have : orderOf (3 : ZMod 32) = 1 := by simp [hkEq, h]
    have := (orderOf_eq_one_iff (x := (3 : ZMod 32))).1 this
    exact h3ne1 this
  have hk_ne1 : k ≠ 1 := by
    intro h
    have : orderOf (3 : ZMod 32) ∣ 2 := by simp [hkEq, h]
    have : (3 : ZMod 32) ^ 2 = 1 :=
      (orderOf_dvd_iff_pow_eq_one (x := (3 : ZMod 32)) (n := 2)).1 this
    exact (hx2n this).elim
  have hk_ne2 : k ≠ 2 := by
    intro h
    have : orderOf (3 : ZMod 32) ∣ 4 := by simp [hkEq, h]
    have : (3 : ZMod 32) ^ 4 = 1 :=
      (orderOf_dvd_iff_pow_eq_one (x := (3 : ZMod 32)) (n := 4)).1 this
    exact (hx4n this).elim
  -- Remaining: k = 3
  have : k = 3 := by omega
  simp [hkEq, this]

/-!
## Powers of 3 Tables

Precomputed tables for verification (from paper Appendix A).
-/

/-- Powers of 3 modulo 8 (t=3, Q_3=2) -/
def powers_mod_8 : List (ZMod 8) := [1, 3]  -- 3^0, 3^1 mod 8

/-- Powers of 3 modulo 16 (t=4, Q_4=4) -/
def powers_mod_16 : List (ZMod 16) := [1, 3, 9, 11]  -- 3^0..3^3 mod 16

/-- Powers of 3 modulo 32 (t=5, Q_5=8) -/
def powers_mod_32 : List (ZMod 32) := [1, 3, 9, 27, 17, 19, 25, 11]  -- 3^0..3^7 mod 32

end Collatz.OrdFact
