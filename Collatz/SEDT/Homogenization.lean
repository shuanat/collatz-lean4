/-
Homogenization of affine congruence recurrences (generic algebra).

If `M_{k+1} ≡ 3 M_k + c_k` and `u_{k+1} ≡ 3 u_k + c_k (mod n)`, then
`M̃ = M − u` satisfies `M̃_{k+1} ≡ 3 M̃_k`, hence `M̃_{k+m} ≡ 3^m M̃_k`, and
`M̃` is `P`-periodic mod `n` whenever `3^P ≡ 1 (mod n)`.

These are generic statements about integer sequences. In the paper they are
applied to the auxiliary sequence `(N_k)` of `AffineNumerator` (paper Lemma
D.10); no orbit sequence satisfying the hypotheses is constructed here, and
paper Lemma D.10 as an orbit statement is not formalized.
-/

import Mathlib.Tactic
import Mathlib.Data.Int.ModEq

namespace Collatz.SEDT.Homogenization

/-- Two integer sequences satisfying the same affine update modulo `n` differ by
a sequence satisfying the homogeneous update `x_{k+1} ≡ 3 x_k`. -/
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

end Collatz.SEDT.Homogenization
