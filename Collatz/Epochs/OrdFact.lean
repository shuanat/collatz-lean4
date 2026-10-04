/-
Collatz Conjecture: Ord-Fact Theorem (paper Lemma B.2)

Main theorem: `orderOf (3 : ZMod (2^t)) = 2^(t-2)` for `t ≥ 3`.

This module replaces the previous Wave A scaffolding (which stated
`True := by sorry`) with a real, axiom-clean proof of the multiplicative
order of `3` modulo `2^t`.

Proof strategy (S7.1.0.B2 of the deep formalization plan):
  1. `orderOf (9 : ZMod (2^(n+3))) = 2^n` follows from Mathlib's
     `ZMod.orderOf_one_add_mul_prime_pow` with `p = 2`, `m = 3`, `a = 1`
     (since `1 + 2^3 * 1 = 9`).
  2. `(3 : ZMod (2^t))^2 = 9` by `norm_num`.
  3. Mathlib's `orderOf_pow` gives `orderOf (3^2) = orderOf 3 / gcd (orderOf 3) 2`.
  4. `orderOf (3 : ZMod (2^t))` is even for `t ≥ 2` because the natural
     projection `ZMod (2^t) → ZMod 4` sends `3 ↦ 3` and
     `orderOf (3 : ZMod 4) = 2`, and `orderOf` is monotone under ring homs.
  5. Combining: `2^n = orderOf 3 / 2`, hence `orderOf 3 = 2^(n+1) = 2^(t-2)`.

Compatibility: the original stub name `ord_fact_main` is preserved as an alias.
The previous meaningless `helper_lemma_*`, `ord_fact_examples*`,
`ord_fact_phase_mixing`, `ord_fact_touch_frequency`, `ord_fact_corollary`,
`ord_fact_specific_values` stubs (all of type `True := by sorry`) had no
substantive downstream use and have been removed.
-/

import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.ModEq
import Collatz.Epochs.Core

namespace Collatz.OrdFact

open ZMod

set_option maxHeartbeats 400000

/-! ## Step (1) — order of `3^2` modulo `2^t` -/

/-- `orderOf ((3 : ZMod (2^(n+3))) ^ 2) = 2^n`.

This is a direct application of `ZMod.orderOf_one_add_mul_prime_pow` with
`p = 2`, `m = 3`, `a = 1`, after observing that `1 + 2^3 * 1 = 9 = 3^2`
in any `ZMod m`. The side condition `m + 2 ≤ p * m` becomes `5 ≤ 6`. -/
lemma orderOf_three_sq_eq (n : ℕ) :
    orderOf ((3 : ZMod (2 ^ (n + 3))) ^ 2) = 2 ^ n := by
  have key :
      orderOf ((1 + (2 : ℕ) ^ 3 * (1 : ℤ) : ZMod ((2 : ℕ) ^ (n + 3)))) = 2 ^ n :=
    ZMod.orderOf_one_add_mul_prime_pow Nat.prime_two 3 (by decide) (by decide)
      (1 : ℤ) (by decide) n
  have h9 :
      ((1 + (2 : ℕ) ^ 3 * (1 : ℤ) : ZMod ((2 : ℕ) ^ (n + 3)))) =
        ((3 : ZMod (2 ^ (n + 3))) ^ 2) := by
    push_cast
    ring
  rw [h9] at key
  exact key

/-! ## Step (2) — `orderOf 3` is even for `t ≥ 2` -/

/-- The natural ring homomorphism `ZMod (2^t) → ZMod 4` for `t ≥ 2`.

Built via `ZMod.castHom` with the divisibility witness `4 ∣ 2^t`. -/
private def castToFour (t : ℕ) (ht : 2 ≤ t) : ZMod (2 ^ t) →+* ZMod 4 :=
  ZMod.castHom
    (show (4 : ℕ) ∣ 2 ^ t by
      have : (2 : ℕ) ^ 2 ∣ 2 ^ t := pow_dvd_pow 2 ht
      simpa using this)
    (ZMod 4)

private lemma castToFour_three (t : ℕ) (ht : 2 ≤ t) :
    castToFour t ht (3 : ZMod (2 ^ t)) = (3 : ZMod 4) := by
  show (ZMod.castHom (show (4 : ℕ) ∣ 2 ^ t by
    have : (2 : ℕ) ^ 2 ∣ 2 ^ t := pow_dvd_pow 2 ht
    simpa using this) (ZMod 4)) (3 : ZMod (2 ^ t)) = (3 : ZMod 4)
  have hnat :
      (ZMod.castHom (show (4 : ℕ) ∣ 2 ^ t by
        have : (2 : ℕ) ^ 2 ∣ 2 ^ t := pow_dvd_pow 2 ht
        simpa using this) (ZMod 4)) ((3 : ℕ) : ZMod (2 ^ t)) =
      ((3 : ℕ) : ZMod 4) := by
    rw [map_natCast]
  simpa using hnat

/-- In `ZMod 4`, the element `3` has multiplicative order exactly `2`. -/
lemma orderOf_three_ZMod_four : orderOf (3 : ZMod 4) = 2 := by
  have hsq : (3 : ZMod 4) ^ 2 = 1 := by decide
  have hne : (3 : ZMod 4) ≠ 1 := by decide
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime hsq hne

/-- `orderOf (3 : ZMod (2^t))` is even for `t ≥ 2`. -/
lemma two_dvd_orderOf_three {t : ℕ} (ht : 2 ≤ t) :
    2 ∣ orderOf (3 : ZMod (2 ^ t)) := by
  -- Order is monotone under ring homs: `orderOf (f x) ∣ orderOf x`.
  have hmap : orderOf (castToFour t ht (3 : ZMod (2 ^ t))) ∣
              orderOf (3 : ZMod (2 ^ t)) :=
    orderOf_map_dvd (castToFour t ht).toMonoidHom (3 : ZMod (2 ^ t))
  rw [castToFour_three t ht, orderOf_three_ZMod_four] at hmap
  exact hmap

/-! ## Step (3) — main theorem -/

/-- **Paper Lemma B.2.** The multiplicative order of `3` modulo `2^t`
is exactly `2^(t-2)` for `t ≥ 3`. -/
theorem orderOf_three_eq_pow_two {t : ℕ} (ht : 3 ≤ t) :
    orderOf (3 : ZMod (2 ^ t)) = 2 ^ (t - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, t = n + 3 := ⟨t - 3, by omega⟩
  show orderOf (3 : ZMod (2 ^ (n + 3))) = 2 ^ (n + 1)
  set A : ℕ := orderOf (3 : ZMod (2 ^ (n + 3))) with hAdef
  have h32 : orderOf ((3 : ZMod (2 ^ (n + 3))) ^ 2) = 2 ^ n :=
    orderOf_three_sq_eq n
  have hpow : orderOf ((3 : ZMod (2 ^ (n + 3))) ^ 2) = A / Nat.gcd A 2 := by
    rw [hAdef]
    exact orderOf_pow' (3 : ZMod (2 ^ (n + 3))) (by decide : (2 : ℕ) ≠ 0)
  have hAdiv : A / Nat.gcd A 2 = 2 ^ n := by rw [← hpow]; exact h32
  have h2A : (2 : ℕ) ∣ A := two_dvd_orderOf_three (by omega)
  have hgcd : Nat.gcd A 2 = 2 := Nat.gcd_eq_right h2A
  rw [hgcd] at hAdiv
  have hAeq : A = 2 * 2 ^ n := by
    have hAdivEq : A = (A / 2) * 2 := (Nat.div_mul_cancel h2A).symm
    rw [hAdiv] at hAdivEq
    linarith
  rw [hAeq, pow_succ, mul_comm]

/-- Backward-compatible alias matching the original stub theorem name.
The original stub had type `True`; the real type is now the paper-faithful
statement above. -/
theorem ord_fact_main (t : ℕ) (ht : 3 ≤ t) :
    orderOf (3 : ZMod (2 ^ t)) = 2 ^ (t - 2) :=
  orderOf_three_eq_pow_two ht

/-! ## Step (4) — bridge to integer congruence used by the
    SEDT/Homogenization toolkit (Wave 1 of S7.2 Path 1.algebraic) -/

/-- Order specialization to the epoch period: `3 ^ (Q_t t) = 1` in
`ZMod (2 ^ t)` for `t ≥ 3`. Direct consequence of `orderOf_three_eq_pow_two`
(`Q_t t` is definitionally `2 ^ (t - 2)`). -/
lemma three_pow_Qt_eq_one_zmod {t : ℕ} (ht : 3 ≤ t) :
    (3 : ZMod (2 ^ t)) ^ (Collatz.Epochs.Q_t t) = 1 := by
  have hord : orderOf (3 : ZMod (2 ^ t)) = 2 ^ (t - 2) :=
    orderOf_three_eq_pow_two ht
  have hQt : Collatz.Epochs.Q_t t = 2 ^ (t - 2) := rfl
  calc
    (3 : ZMod (2 ^ t)) ^ (Collatz.Epochs.Q_t t)
        = (3 : ZMod (2 ^ t)) ^ orderOf (3 : ZMod (2 ^ t)) := by
              rw [hQt, hord]
    _   = 1 := pow_orderOf_eq_one _

/-! ## Step (5) — Wave 2F bridge bricks (`admissible ⇒ touchCount = 1`)

Auxiliary `IsUnit` facts about `(3 : ZMod (2^t))`, its inverse, and the
paper touch residue `s_t t = -5 · 3⁻¹` cast back to `ZMod (2^t)`. These
are the algebraic prerequisites for the Wave 2F bridge theorem
`Collatz.Mixing.AdmissibleTailF01.touch_count_eq_one`. -/

/-- `(3 : ZMod (2^t))` is a unit for `t ≥ 1`. Direct consequence of
`Nat.Coprime 3 (2^t)` (since `gcd(3, 2) = 1`) and `ZMod.isUnit_iff_coprime`. -/
lemma isUnit_three_zmod {t : ℕ} (_ht : 1 ≤ t) :
    IsUnit (3 : ZMod (2 ^ t)) := by
  have hcop : Nat.Coprime 3 (2 ^ t) :=
    Nat.Coprime.pow_right t (by decide : Nat.Coprime 3 2)
  have h : IsUnit ((3 : ℕ) : ZMod (2 ^ t)) :=
    (ZMod.isUnit_iff_coprime 3 (2 ^ t)).mpr hcop
  have heq : ((3 : ℕ) : ZMod (2 ^ t)) = (3 : ZMod (2 ^ t)) := by norm_cast
  rwa [heq] at h

/-- `(5 : ZMod (2^t))` is a unit for `t ≥ 1`. Direct consequence of
`Nat.Coprime 5 (2^t)` (since `gcd(5, 2) = 1`) and `ZMod.isUnit_iff_coprime`. -/
lemma isUnit_five_zmod {t : ℕ} (_ht : 1 ≤ t) :
    IsUnit (5 : ZMod (2 ^ t)) := by
  have hcop : Nat.Coprime 5 (2 ^ t) :=
    Nat.Coprime.pow_right t (by decide : Nat.Coprime 5 2)
  have h : IsUnit ((5 : ℕ) : ZMod (2 ^ t)) :=
    (ZMod.isUnit_iff_coprime 5 (2 ^ t)).mpr hcop
  have heq : ((5 : ℕ) : ZMod (2 ^ t)) = (5 : ZMod (2 ^ t)) := by norm_cast
  rwa [heq] at h

/-- `(3 : ZMod (2^t))⁻¹` is a unit for `t ≥ 1`. From `ZMod.coe_mul_inv_eq_one`
applied at `x = 3`: `(3 : ZMod (2^t)) * (3 : ZMod (2^t))⁻¹ = 1`, hence
`(3 : ZMod (2^t))⁻¹` admits a left inverse. -/
lemma isUnit_three_inv_zmod {t : ℕ} (_ht : 1 ≤ t) :
    IsUnit ((3 : ZMod (2 ^ t))⁻¹) := by
  have hcop : Nat.Coprime 3 (2 ^ t) :=
    Nat.Coprime.pow_right t (by decide : Nat.Coprime 3 2)
  have h : ((3 : ℕ) : ZMod (2 ^ t)) * ((3 : ℕ) : ZMod (2 ^ t))⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one 3 hcop
  have heq : ((3 : ℕ) : ZMod (2 ^ t)) = (3 : ZMod (2 ^ t)) := by norm_cast
  rw [heq] at h
  exact isUnit_of_mul_eq_one_right _ _ h

/-- The paper touch residue `s_t t` (defined as `((-5) * 3⁻¹).val` for `t ≥ 2`),
cast back to `ZMod (2^t)`, equals `(-5 : ZMod (2^t)) * (3 : ZMod (2^t))⁻¹`. -/
lemma natCast_s_t_eq {t : ℕ} (ht : 2 ≤ t) :
    ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t)) =
      (-5 : ZMod (2 ^ t)) * (3 : ZMod (2 ^ t))⁻¹ := by
  haveI : NeZero ((2 : ℕ) ^ t) := ⟨by positivity⟩
  have hbody : Collatz.Epochs.s_t t =
      ((-5 : ZMod (2 ^ t)) * (3 : ZMod (2 ^ t))⁻¹).val := by
    unfold Collatz.Epochs.s_t
    simp [ht]
  rw [hbody, ZMod.natCast_zmod_val]

/-- The natural-number cast of `s_t t` is a unit in `ZMod (2^t)` for `t ≥ 2`.
Combines `natCast_s_t_eq` with `IsUnit.neg` of `isUnit_five_zmod` and
`isUnit_three_inv_zmod`. -/
lemma isUnit_natCast_s_t {t : ℕ} (ht : 2 ≤ t) :
    IsUnit ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t)) := by
  rw [natCast_s_t_eq ht]
  have h5 : IsUnit (5 : ZMod (2 ^ t)) := isUnit_five_zmod (by omega : 1 ≤ t)
  have h3inv : IsUnit ((3 : ZMod (2 ^ t))⁻¹) := isUnit_three_inv_zmod (by omega : 1 ≤ t)
  have hneg5 : IsUnit (-5 : ZMod (2 ^ t)) := h5.neg
  exact hneg5.mul h3inv

/-- **Bridge lemma (Wave 1 of S7.2 Path 1.algebraic).**
Reformulation of the order fact in `Int.ModEq` shape consumed by
`Collatz.SEDT.Homogenization.homogenized_periodic_of_order_dvd`:
`3 ^ (Q_t t) ≡ 1 (mod 2 ^ t)` as integers. -/
theorem three_pow_Qt_modEq_one {t : ℕ} (ht : 3 ≤ t) :
    (3 : ℤ) ^ (Collatz.Epochs.Q_t t) ≡ 1 [ZMOD ((2 : ℤ) ^ t)] := by
  have hzmod : (3 : ZMod (2 ^ t)) ^ (Collatz.Epochs.Q_t t) = 1 :=
    three_pow_Qt_eq_one_zmod ht
  have htpos : (0 : ℕ) < 2 ^ t := pow_pos (by decide) _
  haveI : NeZero ((2 : ℕ) ^ t) := ⟨Nat.pos_iff_ne_zero.mp htpos⟩
  -- Push the ZMod equality to a vanishing of the integer difference.
  have hcast0 :
      (((3 : ℤ) ^ (Collatz.Epochs.Q_t t) - 1 : ℤ) : ZMod (2 ^ t)) = 0 := by
    push_cast
    rw [hzmod]
    ring
  -- Translate the ZMod-zero statement into integer divisibility.
  have hdvdNat :
      ((2 ^ t : ℕ) : ℤ) ∣ (3 : ℤ) ^ (Collatz.Epochs.Q_t t) - 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast0
  have hcastPow : ((2 ^ t : ℕ) : ℤ) = (2 : ℤ) ^ t := by push_cast; ring
  have hdvd : ((2 : ℤ) ^ t) ∣ (3 : ℤ) ^ (Collatz.Epochs.Q_t t) - 1 := by
    rw [hcastPow] at hdvdNat
    exact hdvdNat
  -- Convert `n ∣ a - 1` into `a ≡ 1 [ZMOD n]`.
  have hdvd' :
      ((2 : ℤ) ^ t) ∣ 1 - (3 : ℤ) ^ (Collatz.Epochs.Q_t t) := by
    have := dvd_neg.mpr hdvd
    simpa [neg_sub] using this
  exact Int.modEq_iff_dvd.mpr hdvd'

end Collatz.OrdFact
