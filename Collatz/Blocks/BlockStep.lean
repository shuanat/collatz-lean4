/-
Block step (paper Lemma 2.13 and the parameter of Definition 2.12), for
positive odd `x`.

Setting: `x + 1 = 2^α · y` with `y` odd and `α ≥ 1` (so `x` is odd,
`α = depth₋(x)`). `T = collatz_step`, `e = step_type`,
`σ = ν₂(3^α y − 1) = (3^α * y - 1).factorization 2`.

* (a) `T^k(x) + 1 = 3^k · 2^{α−k} · y` for `0 ≤ k ≤ α − 1`, and `e(T^k x) = 1`
  for `k ≤ α − 2`;
* (b) `T^{α−1}(x) = 2 · 3^{α−1} y − 1`, `depth₋(T^{α−1} x) = 1`,
  `e(T^{α−1} x) = 1 + σ`, `σ ≥ 1`;
* (c) `T^α(x) = (3^α y − 1) / 2^σ`;
* (d) the block values increase strictly.

The paper states the lemma for all odd integers `x ≠ −1`; here `x` is a natural
number (the map `collatz_step` is defined on `ℕ`), so only the positive case is
formalized. Status: proved.
-/
import Collatz.Foundations.OddPart

namespace Collatz.Blocks

open Collatz.Foundations

/-- One `e = 1` step in multiplicative form: if `z + 1 = 2^{j+2} q` with `q` odd,
then `e(z) = 1` and `T(z) + 1 = 2^{j+1} · (3q)`. -/
theorem step_of_add_one_eq_two_pow_mul {z j q : ℕ} (hq : Odd q)
    (h : z + 1 = 2 ^ (j + 2) * q) :
    step_type z = 1 ∧ collatz_step z + 1 = 2 ^ (j + 1) * (3 * q) := by
  have hA : 2 ^ (j + 2) * q = 4 * (2 ^ j * q) := by ring
  have hB : 2 ^ (j + 1) * (3 * q) = 6 * (2 ^ j * q) := by ring
  have hA1 : 1 ≤ 2 ^ j * q := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (pow_ne_zero j two_ne_zero) hq.pos.ne')
  rw [hA] at h
  rw [hB]
  generalize 2 ^ j * q = A at h hA1 ⊢
  have h3 : 3 * z + 1 = 2 ^ 1 * (6 * A - 1) := by rw [pow_one]; omega
  have hodd : Odd (6 * A - 1) := ⟨3 * A - 1, by omega⟩
  refine ⟨step_type_eq_of_three_mul_add_one_eq hodd h3, ?_⟩
  rw [collatz_step_eq_of_three_mul_add_one_eq hodd h3]
  omega

/-- Lemma 2.13(a), values: if `x + 1 = 2^α y` with `y` odd, then
`T^k(x) + 1 = 3^k · 2^{α−k} · y` for every `k` with `k + 1 ≤ α`. -/
theorem iterate_add_one_of_lt {x α y : ℕ} (hy : Odd y) (hx : x + 1 = 2 ^ α * y) :
    ∀ k, k + 1 ≤ α → (collatz_step^[k] x) + 1 = 3 ^ k * 2 ^ (α - k) * y := by
  intro k
  induction k with
  | zero => intro _; simp [hx]
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have hform : collatz_step^[k] x + 1 = 2 ^ ((α - k - 2) + 2) * (3 ^ k * y) := by
      rw [hprev, show α - k - 2 + 2 = α - k by omega]; ring
    have hq : Odd (3 ^ k * y) := (Odd.pow (by decide : Odd 3)).mul hy
    obtain ⟨_, hstep⟩ := step_of_add_one_eq_two_pow_mul hq hform
    rw [Function.iterate_succ_apply', hstep,
      show α - k - 2 + 1 = α - (k + 1) by omega]
    ring

/-- Lemma 2.13(a), exponents: if `x + 1 = 2^α y` with `y` odd, then
`e(T^k x) = 1` for every `k` with `k + 2 ≤ α`. -/
theorem step_type_iterate_eq_one {x α y : ℕ} (hy : Odd y) (hx : x + 1 = 2 ^ α * y) :
    ∀ k, k + 2 ≤ α → step_type (collatz_step^[k] x) = 1 := by
  intro k hk
  have hprev := iterate_add_one_of_lt hy hx k (by omega)
  have hform : collatz_step^[k] x + 1 = 2 ^ ((α - k - 2) + 2) * (3 ^ k * y) := by
    rw [hprev, show α - k - 2 + 2 = α - k by omega]; ring
  exact (step_of_add_one_eq_two_pow_mul ((Odd.pow (by decide : Odd 3)).mul hy) hform).1

/-- Lemma 2.13(d): for positive `x` with `x + 1 = 2^α y`, `y` odd, the block
values increase strictly: `T^k x < T^{k+1} x` for `k + 2 ≤ α`. -/
theorem iterate_lt_iterate_succ {x α y : ℕ} (hy : Odd y) (hx : x + 1 = 2 ^ α * y) :
    ∀ k, k + 2 ≤ α → collatz_step^[k] x < collatz_step^[k + 1] x := by
  intro k hk
  have h1 := iterate_add_one_of_lt hy hx k (by omega)
  have h2 := iterate_add_one_of_lt hy hx (k + 1) (by omega)
  have hpow : 3 ^ k * 2 ^ (α - k) * y = 2 * (3 ^ k * 2 ^ (α - (k + 1)) * y) := by
    rw [show α - k = (α - (k + 1)) + 1 by omega, pow_succ]; ring
  have hpow' : 3 ^ (k + 1) * 2 ^ (α - (k + 1)) * y = 3 * (3 ^ k * 2 ^ (α - (k + 1)) * y) := by
    rw [pow_succ]; ring
  have hpos : 0 < 3 ^ k * 2 ^ (α - (k + 1)) * y := by
    have := hy.pos; positivity
  rw [hpow] at h1
  rw [hpow'] at h2
  omega

/-- Lemma 2.13(b), last value: `T^{α−1}(x) + 1 = 2 · 3^{α−1} · y`
(for `x + 1 = 2^α y`, `y` odd, `α ≥ 1`). -/
theorem iterate_pred_add_one {x α y : ℕ} (hy : Odd y) (hα : 1 ≤ α)
    (hx : x + 1 = 2 ^ α * y) :
    collatz_step^[α - 1] x + 1 = 2 * 3 ^ (α - 1) * y := by
  rw [iterate_add_one_of_lt hy hx (α - 1) (by omega), show α - (α - 1) = 1 by omega]
  ring

/-- Lemma 2.13(b): `depth₋(T^{α−1}(x)) = 1`. -/
theorem depth_minus_iterate_pred {x α y : ℕ} (hy : Odd y) (hα : 1 ≤ α)
    (hx : x + 1 = 2 ^ α * y) :
    depth_minus (collatz_step^[α - 1] x) = 1 := by
  have h := iterate_pred_add_one hy hα hx
  have hodd : Odd (3 ^ (α - 1) * y) := (Odd.pow (by decide : Odd 3)).mul hy
  exact depth_minus_eq_of_add_one_eq hodd (by rw [h, pow_one, mul_assoc])

/-- Auxiliary: `3 · T^{α−1}(x) + 1 = 2 · (3^α y − 1)` and `3^α y ≥ 3`. -/
lemma three_mul_iterate_pred_add_one {x α y : ℕ} (hy : Odd y) (hα : 1 ≤ α)
    (hx : x + 1 = 2 ^ α * y) :
    3 * collatz_step^[α - 1] x + 1 = 2 * (3 ^ α * y - 1) ∧ 3 ≤ 3 ^ α * y := by
  have h := iterate_pred_add_one hy hα hx
  have hpow : 3 ^ α * y = 3 * (3 ^ (α - 1) * y) := by
    rw [show α = (α - 1) + 1 by omega, pow_succ]; simp only [Nat.add_sub_cancel]; ring
  have hpos : 1 ≤ 3 ^ (α - 1) * y := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) hy.pos.ne')
  rw [hpow]
  rw [show 2 * 3 ^ (α - 1) * y = 2 * (3 ^ (α - 1) * y) by ring] at h
  generalize 3 ^ (α - 1) * y = B at h hpos ⊢
  omega

/-- Lemma 2.13(b): `σ = ν₂(3^α y − 1) ≥ 1`. -/
theorem one_le_block_sigma {α y : ℕ} (hy : Odd y) (hα : 1 ≤ α) :
    1 ≤ (3 ^ α * y - 1).factorization 2 := by
  have hodd : Odd (3 ^ α * y) := (Odd.pow (by decide : Odd 3)).mul hy
  have h3 : 3 ≤ 3 ^ α * y := by
    have : 3 ≤ 3 ^ α := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ α := Nat.pow_le_pow_right (by norm_num) hα
    nlinarith [hy.pos]
  obtain ⟨c, hc⟩ := hodd
  have hdvd : 2 ∣ 3 ^ α * y - 1 := ⟨c, by omega⟩
  exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega) hdvd

/-- Lemma 2.13(b),(c) in factored form: `3 · T^{α−1}(x) + 1 = 2^{1+σ} · x'`
with `x' = (3^α y − 1)/2^σ` odd, `σ = ν₂(3^α y − 1)`. -/
lemma three_mul_iterate_pred_add_one_eq_two_pow_mul {x α y : ℕ} (hy : Odd y)
    (hα : 1 ≤ α) (hx : x + 1 = 2 ^ α * y) :
    3 * collatz_step^[α - 1] x + 1 =
        2 ^ (1 + (3 ^ α * y - 1).factorization 2) *
          ((3 ^ α * y - 1) / 2 ^ (3 ^ α * y - 1).factorization 2) ∧
      Odd ((3 ^ α * y - 1) / 2 ^ (3 ^ α * y - 1).factorization 2) := by
  obtain ⟨h1, h3⟩ := three_mul_iterate_pred_add_one hy hα hx
  obtain ⟨hN, hodd⟩ := two_pow_factorization_mul_odd_part (N := 3 ^ α * y - 1) (by omega)
  refine ⟨?_, hodd⟩
  rw [h1, pow_add, pow_one, mul_assoc, hN]

/-- Lemma 2.13(b): `e(T^{α−1}(x)) = 1 + σ` with `σ = ν₂(3^α y − 1)`. -/
theorem step_type_iterate_pred {x α y : ℕ} (hy : Odd y) (hα : 1 ≤ α)
    (hx : x + 1 = 2 ^ α * y) :
    step_type (collatz_step^[α - 1] x) = 1 + (3 ^ α * y - 1).factorization 2 := by
  obtain ⟨h, hodd⟩ := three_mul_iterate_pred_add_one_eq_two_pow_mul hy hα hx
  exact step_type_eq_of_three_mul_add_one_eq hodd h

/-- Lemma 2.13(c): the next block starts at `T^α(x) = (3^α y − 1) / 2^σ`,
`σ = ν₂(3^α y − 1)`. -/
theorem iterate_block_length {x α y : ℕ} (hy : Odd y) (hα : 1 ≤ α)
    (hx : x + 1 = 2 ^ α * y) :
    collatz_step^[α] x = (3 ^ α * y - 1) / 2 ^ (3 ^ α * y - 1).factorization 2 := by
  obtain ⟨h, hodd⟩ := three_mul_iterate_pred_add_one_eq_two_pow_mul hy hα hx
  have hα' : α = (α - 1) + 1 := by omega
  conv_lhs => rw [hα', Function.iterate_succ_apply']
  exact collatz_step_eq_of_three_mul_add_one_eq hodd h

/-- Lemma 2.13(c) multiplied out: `2^σ · T^α(x) = 3^α y − 1`. -/
theorem two_pow_sigma_mul_iterate_block_length {x α y : ℕ} (hy : Odd y) (hα : 1 ≤ α)
    (hx : x + 1 = 2 ^ α * y) :
    2 ^ (3 ^ α * y - 1).factorization 2 * collatz_step^[α] x = 3 ^ α * y - 1 := by
  rw [iterate_block_length hy hα hx]
  exact Nat.mul_div_cancel' (Nat.ordProj_dvd _ 2)

/-- Converse of Lemma 2.13 (used in Proposition H.7): if the orbit of an odd `x`
starts with `α − 1` steps with `e = 1` followed by a step with `e ≥ 2`, then
`depth₋(x) = α`. -/
theorem depth_minus_eq_of_block_exponents {x α : ℕ} (hx : Odd x) (hα : 1 ≤ α)
    (h1 : ∀ k, k + 2 ≤ α → step_type (collatz_step^[k] x) = 1)
    (h2 : 2 ≤ step_type (collatz_step^[α - 1] x)) :
    depth_minus x = α := by
  obtain ⟨y, hy, hxy⟩ := exists_odd_add_one_eq_two_pow_depth_mul x
  have hd : 1 ≤ depth_minus x := depth_minus_odd_pos hx
  rcases lt_trichotomy (depth_minus x) α with hlt | heq | hgt
  · exfalso
    have he1 := h1 (depth_minus x - 1) (by omega)
    have he2 := step_type_iterate_pred hy hd hxy
    have hσ := one_le_block_sigma (α := depth_minus x) hy hd
    omega
  · exact heq
  · exfalso
    have he := step_type_iterate_eq_one hy hxy (α - 1) (by omega)
    omega

end Collatz.Blocks
