/-
Collatz Conjecture: SEDT Deep Formalization — Tail Homogenization
(Appendix D.10 algebraic core)

This module implements the **algebraic core** of Lemma D.10 from the
paper:

* The **homogenization principle** (generic): if two integer sequences
  `M, u : ℕ → ℤ` satisfy the same affine update mod `n`,

      `M_{k+1} ≡ 3 M_k + c_k  (mod n)`,
      `u_{k+1} ≡ 3 u_k + c_k  (mod n)`,

  then their difference `Mtilde_k := M_k − u_k` satisfies the **homogeneous**
  update

      `Mtilde_{k+1} ≡ 3 Mtilde_k  (mod n)`.

  This is the substance of the standard "subtract a particular solution"
  reduction.

* The **`Q_t` order bound**: if `Mtilde_{k+1} ≡ 3 Mtilde_k (mod n)`, then
  `Mtilde_{k+m} ≡ 3^m Mtilde_k (mod n)` by trivial induction. The order of `3`
  in the unit group `(ℤ/n)ˣ` then bounds the period of `Mtilde_k`.

The full statement of Lemma D.10 (existence of a periodic forcing
`c_k` along an actual t-epoch tail of the Collatz orbit) requires
the orbit-side tail structure (which lives downstream of the
affine numerator module). This file deliberately separates the
**algebraic** half (provable by pure `Int.ModEq` arithmetic) from
the **orbit-side** half (which needs the deeper t-epoch analysis).
-/

import Mathlib.Tactic
import Mathlib.Data.Int.ModEq

namespace Collatz.SEDT.Homogenization

/-- **Generic homogenization principle.** Two integer sequences
satisfying the same affine update modulo `n` differ by a sequence
satisfying the homogeneous update. This is the algebraic core of
Lemma D.10. -/
theorem homogenization_principle
    (n : ℤ) (M u c : ℕ → ℤ) (k : ℕ)
    (hM : M (k + 1) ≡ 3 * M k + c k [ZMOD n])
    (hu : u (k + 1) ≡ 3 * u k + c k [ZMOD n]) :
    M (k + 1) - u (k + 1) ≡ 3 * (M k - u k) [ZMOD n] := by
  have hsub := hM.sub hu
  have hgoal :
      (3 * M k + c k) - (3 * u k + c k) = 3 * (M k - u k) := by ring
  rw [hgoal] at hsub
  exact hsub

/-- **Iterated homogeneous update.** If `Mtilde_{k+1} ≡ 3 Mtilde_k (mod n)`
holds at every step, then `Mtilde_{k+m} ≡ 3^m Mtilde_k (mod n)`. -/
theorem homogenized_iterate
    (n : ℤ) (Mtilde : ℕ → ℤ) (k : ℕ)
    (hstep : ∀ j, Mtilde (j + 1) ≡ 3 * Mtilde j [ZMOD n]) :
    ∀ m, Mtilde (k + m) ≡ 3 ^ m * Mtilde k [ZMOD n] := by
  intro m
  induction m with
  | zero =>
      have : (Mtilde (k + 0) : ℤ) = Mtilde k := by simp
      rw [this]
      simpa using (Int.ModEq.refl (Mtilde k))
  | succ m ih =>
      have hk : Mtilde (k + m + 1) ≡ 3 * Mtilde (k + m) [ZMOD n] := hstep (k + m)
      have hkm : 3 * Mtilde (k + m) ≡ 3 * (3 ^ m * Mtilde k) [ZMOD n] :=
        ih.mul_left 3
      have htrans : Mtilde (k + m + 1) ≡ 3 * (3 ^ m * Mtilde k) [ZMOD n] :=
        hk.trans hkm
      have heq' : (3 : ℤ) * (3 ^ m * Mtilde k) = 3 ^ (m + 1) * Mtilde k := by
        rw [pow_succ]; ring
      have hidx : k + (m + 1) = k + m + 1 := by ring
      rw [hidx]
      rwa [heq'] at htrans

/-- **Period bound from the order of `3`.** If `3 ^ P ≡ 1 (mod n)`
and `Mtilde` satisfies the homogeneous update, then `Mtilde` is periodic
with period dividing `P`. -/
theorem homogenized_periodic_of_order_dvd
    (n : ℤ) (Mtilde : ℕ → ℤ) (P : ℕ)
    (hstep : ∀ j, Mtilde (j + 1) ≡ 3 * Mtilde j [ZMOD n])
    (hord : (3 : ℤ) ^ P ≡ 1 [ZMOD n]) :
    ∀ k, Mtilde (k + P) ≡ Mtilde k [ZMOD n] := by
  intro k
  have hiter : Mtilde (k + P) ≡ 3 ^ P * Mtilde k [ZMOD n] :=
    homogenized_iterate n Mtilde k hstep P
  have hone : (3 : ℤ) ^ P * Mtilde k ≡ 1 * Mtilde k [ZMOD n] :=
    hord.mul_right (Mtilde k)
  have : Mtilde (k + P) ≡ 1 * Mtilde k [ZMOD n] := hiter.trans hone
  simpa using this

/-- Touch condition translates between affine and homogenized
representations: `3 M_k + 5 ≡ 0 (mod n)` iff
`3 Mtilde_k + (3 u_k + 5) ≡ 0 (mod n)`, where `Mtilde_k = M_k − u_k`. This
is the algebraic core of Lemma D.1.b (touch condition preservation
under homogenization). -/
theorem touch_iff_homogenized (n : ℤ) (M u : ℕ → ℤ) (k : ℕ) :
    (3 * M k + 5 ≡ 0 [ZMOD n]) ↔
    (3 * (M k - u k) + (3 * u k + 5) ≡ 0 [ZMOD n]) := by
  have heq : 3 * (M k - u k) + (3 * u k + 5) = 3 * M k + 5 := by ring
  rw [heq]

end Collatz.SEDT.Homogenization
