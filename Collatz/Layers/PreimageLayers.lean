/-
Preimage layers of the odd map (paper §3, Definitions 2.3 and 2.5,
Proposition 3.1, Lemma 3.4, Lemma 3.5.a, Proposition 3.5, Corollary 3.5.b).

`T = collatz_step` is the odd-to-odd map, `e = step_type`. Odd natural numbers
are automatically `≥ 1`, so "odd `m : ℕ`" is the paper's "odd `m ≥ 1`".

* `preimage_layer n = {m odd : T m = n}` (paper `S_n`).
* `layer_base_exp n` is the paper's `k₀(n)` (1 if `n ≡ 2 (mod 3)`, 2 otherwise;
  only used for `3 ∤ n`), and `layer_elem n t = (2^{k₀(n)+2t} n − 1)/3` is
  `m(n,t)`.

Status: elementary, classical, proved here in full. Nothing in this file is
used by any convergence statement, and nothing here says where an individual
orbit goes.
-/
import Collatz.Foundations.OddPart

namespace Collatz.Layers

open Collatz.Foundations

/-- Preimage layer `S_n = {m : m odd, T(m) = n}` (paper Definition 2.3). -/
def preimage_layer (n : ℕ) : Set ℕ := {m | Odd m ∧ collatz_step m = n}

/-- Minimal base exponent `k₀(n)` (paper Lemma 3.5.a): `1` if `n ≡ 2 (mod 3)`,
otherwise `2`. The paper defines it only for `3 ∤ n`, where "otherwise" means
`n ≡ 1 (mod 3)`. -/
def layer_base_exp (n : ℕ) : ℕ := if n % 3 = 2 then 1 else 2

/-- Layer coordinate `m(n,t) = (2^{k₀(n)+2t} · n − 1) / 3` (paper Definition 2.5).
Meaningful for odd `n` with `3 ∤ n`. -/
def layer_elem (n t : ℕ) : ℕ := (2 ^ (layer_base_exp n + 2 * t) * n - 1) / 3

/-! ## Arithmetic modulo 3 -/

/-- `2^k mod 3` is `1` for even `k` and `2` for odd `k`. -/
lemma two_pow_mod_three (k : ℕ) : 2 ^ k % 3 = if k % 2 = 0 then 1 else 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs with h1 h2 h2 <;> omega

lemma one_le_layer_base_exp (n : ℕ) : 1 ≤ layer_base_exp n := by
  unfold layer_base_exp; split_ifs <;> omega

/-- Lemma 3.5.a: for `3 ∤ n` and `k ≥ 1`, `2^k · n ≡ 1 (mod 3)` iff
`k = k₀(n) + 2t` for some `t ≥ 0`. In particular `k₀(n)` is the least such
`k ≥ 1`. -/
theorem two_pow_mul_mod_three_eq_one_iff {n : ℕ} (hn3 : ¬ 3 ∣ n) {k : ℕ} (hk : 1 ≤ k) :
    2 ^ k * n % 3 = 1 ↔ ∃ t, k = layer_base_exp n + 2 * t := by
  have hn : n % 3 ≠ 0 := fun h => hn3 (Nat.dvd_of_mod_eq_zero h)
  rw [Nat.mul_mod, two_pow_mod_three]
  unfold layer_base_exp
  constructor
  · intro h
    split_ifs at h ⊢ <;>
      first
        | omega
        | exact ⟨(k - 2) / 2, by omega⟩
        | exact ⟨(k - 1) / 2, by omega⟩
  · rintro ⟨t, rfl⟩
    split_ifs with h1 h2 h2 <;> omega

lemma two_pow_layer_mul_mod_three {n : ℕ} (hn3 : ¬ 3 ∣ n) (t : ℕ) :
    2 ^ (layer_base_exp n + 2 * t) * n % 3 = 1 :=
  (two_pow_mul_mod_three_eq_one_iff hn3
    (le_trans (one_le_layer_base_exp n) (Nat.le_add_right _ _))).2 ⟨t, rfl⟩

/-! ## Basic identities for `m(n,t)` -/

/-- `3 · m(n,t) + 1 = 2^{k₀(n)+2t} · n` for `3 ∤ n`. -/
theorem three_mul_layer_elem_add_one {n : ℕ} (hn3 : ¬ 3 ∣ n) (t : ℕ) :
    3 * layer_elem n t + 1 = 2 ^ (layer_base_exp n + 2 * t) * n := by
  have h := two_pow_layer_mul_mod_three hn3 t
  unfold layer_elem
  generalize 2 ^ (layer_base_exp n + 2 * t) * n = A at h ⊢
  omega

/-- Proposition 3.5 / Remark 3.5.c: for `3 ∤ n` (oddness of `n` is not needed),
`m(n,t)` is odd (hence `≥ 1`). -/
theorem odd_layer_elem {n : ℕ} (hn3 : ¬ 3 ∣ n) (t : ℕ) : Odd (layer_elem n t) := by
  have h := three_mul_layer_elem_add_one hn3 t
  have h2 : 2 ∣ 2 ^ (layer_base_exp n + 2 * t) * n :=
    dvd_mul_of_dvd_left (dvd_pow_self 2
      (by have := one_le_layer_base_exp n; omega)) n
  rw [← h] at h2
  obtain ⟨c, hc⟩ := h2
  exact Nat.odd_iff.2 (by omega)

/-- Proposition 3.5: for odd `n` with `3 ∤ n` and every `t`, `0 < m(n,t)`. -/
theorem layer_elem_pos {n : ℕ} (hn3 : ¬ 3 ∣ n) (t : ℕ) : 0 < layer_elem n t :=
  (odd_layer_elem hn3 t).pos

/-- Proposition 3.5: for odd `n` with `3 ∤ n`, `T(m(n,t)) = n`. -/
theorem collatz_step_layer_elem {n : ℕ} (hn : Odd n) (hn3 : ¬ 3 ∣ n) (t : ℕ) :
    collatz_step (layer_elem n t) = n :=
  collatz_step_eq_of_three_mul_add_one_eq hn (three_mul_layer_elem_add_one hn3 t)

/-- Proposition 3.5: for odd `n` with `3 ∤ n`, `e(m(n,t)) = k₀(n) + 2t`. -/
theorem step_type_layer_elem {n : ℕ} (hn : Odd n) (hn3 : ¬ 3 ∣ n) (t : ℕ) :
    step_type (layer_elem n t) = layer_base_exp n + 2 * t :=
  step_type_eq_of_three_mul_add_one_eq hn (three_mul_layer_elem_add_one hn3 t)

/-- Lemma 3.5.d(b), first claim: for odd `n` with `3 ∤ n`,
`e(m(n,t)) = 1` iff `t = 0` and `n ≡ 2 (mod 3)`. -/
theorem step_type_layer_elem_eq_one_iff {n t : ℕ} (hn : Odd n) (hn3 : ¬ 3 ∣ n) :
    step_type (layer_elem n t) = 1 ↔ t = 0 ∧ n % 3 = 2 := by
  rw [step_type_layer_elem hn hn3]
  unfold layer_base_exp
  split_ifs with h <;> omega

/-- Proposition 3.5: `m(n,t+1) = 4 · m(n,t) + 1` for `3 ∤ n`. -/
theorem layer_elem_succ {n : ℕ} (hn3 : ¬ 3 ∣ n) (t : ℕ) :
    layer_elem n (t + 1) = 4 * layer_elem n t + 1 := by
  have h0 := three_mul_layer_elem_add_one hn3 t
  have h1 := three_mul_layer_elem_add_one hn3 (t + 1)
  have hpow : 2 ^ (layer_base_exp n + 2 * (t + 1)) * n =
      4 * (2 ^ (layer_base_exp n + 2 * t) * n) := by
    rw [show layer_base_exp n + 2 * (t + 1) = (layer_base_exp n + 2 * t) + 2 by ring,
      pow_add]
    ring
  rw [hpow, ← h0] at h1
  omega

/-- For `3 ∤ n` and `t ≥ 1`, `m(n,t) ≡ 1 (mod 4)`; equivalently (for odd
`m(n,t)`) `depth₋(m(n,t)) = 1` and `e(m(n,t)) ≥ 2`. -/
theorem layer_elem_mod_four {n : ℕ} (hn3 : ¬ 3 ∣ n) {t : ℕ} (ht : 1 ≤ t) :
    layer_elem n t % 4 = 1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht
  rw [layer_elem_succ hn3 s]
  omega

/-- `t ↦ m(n,t)` is strictly increasing (for `3 ∤ n`). -/
theorem layer_elem_strictMono {n : ℕ} (hn3 : ¬ 3 ∣ n) : StrictMono (layer_elem n) :=
  strictMono_nat_of_lt_succ fun t => by rw [layer_elem_succ hn3 t]; omega

/-! ## Every odd `m` lies on a layer -/

/-- `T(m)` is never divisible by `3` (for every natural `m`): `3m + 1 = 2^{e(m)} T(m)`. -/
theorem not_three_dvd_collatz_step (m : ℕ) : ¬ 3 ∣ collatz_step m := by
  intro h
  have h2 := two_pow_step_type_mul_collatz_step m
  have h3 : 3 ∣ 3 * m + 1 := h2 ▸ dvd_mul_of_dvd_right h _
  omega

/-- Link between the residue of `T(m)` modulo 3 and the parity of `e(m)`:
`T(m) ≡ 2 (mod 3)` iff `e(m)` is odd. Holds for every natural `m`
(the paper states it for odd `m`). -/
theorem collatz_step_mod_three_eq_two_iff (m : ℕ) :
    collatz_step m % 3 = 2 ↔ Odd (step_type m) := by
  have h2 := two_pow_step_type_mul_collatz_step m
  have h1 : 2 ^ step_type m * collatz_step m % 3 = 1 := by rw [h2]; omega
  have hn3 := not_three_dvd_collatz_step m
  have hn : collatz_step m % 3 ≠ 0 := fun h => hn3 (Nat.dvd_of_mod_eq_zero h)
  rw [Nat.mul_mod, two_pow_mod_three] at h1
  rw [Nat.odd_iff]
  split_ifs at h1 <;> omega

/-- For odd `m`, with `n = T(m)` and `e = e(m)`: `k₀(n) ≤ e` and `e − k₀(n)` is
even, so `e = k₀(n) + 2t` with `t = (e − k₀(n))/2`. -/
theorem layer_base_exp_add_two_mul_eq_step_type {m : ℕ} (hm : Odd m) :
    layer_base_exp (collatz_step m) +
        2 * ((step_type m - layer_base_exp (collatz_step m)) / 2) = step_type m := by
  have he : 1 ≤ step_type m := step_type_odd_pos hm
  have h2 := two_pow_step_type_mul_collatz_step m
  have h1 : 2 ^ step_type m * collatz_step m % 3 = 1 := by rw [h2]; omega
  obtain ⟨t, ht⟩ := (two_pow_mul_mod_three_eq_one_iff
    (not_three_dvd_collatz_step m) he).1 h1
  omega

/-- Corollary 3.5.b, inverse map: every odd `m` equals `m(T(m), t)` with
`t = (e(m) − k₀(T(m)))/2`. -/
theorem layer_elem_collatz_step {m : ℕ} (hm : Odd m) :
    layer_elem (collatz_step m)
        ((step_type m - layer_base_exp (collatz_step m)) / 2) = m := by
  unfold layer_elem
  rw [layer_base_exp_add_two_mul_eq_step_type hm, two_pow_step_type_mul_collatz_step]
  omega

/-! ## Partition and bijections -/

/-- Proposition 3.1 (partition): every odd `m` lies in exactly one layer `S_n`
with `n` odd and `3 ∤ n`, namely `n = T(m)`. -/
theorem existsUnique_preimage_layer {m : ℕ} (hm : Odd m) :
    ∃! n, Odd n ∧ ¬ 3 ∣ n ∧ m ∈ preimage_layer n :=
  ⟨collatz_step m, ⟨collatz_step_is_odd, not_three_dvd_collatz_step m, hm, rfl⟩,
    fun _ ⟨_, _, _, h⟩ => h.symm⟩

/-- Proposition 3.1 / Lemma 3.4: `S_n = ∅` when `3 ∣ n` (for every `n`). -/
theorem preimage_layer_eq_empty_of_three_dvd {n : ℕ} (h : 3 ∣ n) :
    preimage_layer n = ∅ := by
  ext m
  simp only [preimage_layer, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
    not_and]
  intro _ hm
  exact not_three_dvd_collatz_step m (hm ▸ h)

/-- Proposition 3.5: for odd `n` with `3 ∤ n`, the image of `t ↦ m(n,t)` is
exactly `S_n`. -/
theorem range_layer_elem {n : ℕ} (hn : Odd n) (hn3 : ¬ 3 ∣ n) :
    Set.range (layer_elem n) = preimage_layer n := by
  ext m
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨odd_layer_elem hn3 t, collatz_step_layer_elem hn hn3 t⟩
  · rintro ⟨hm, rfl⟩
    exact ⟨_, layer_elem_collatz_step hm⟩

/-- Proposition 3.5 (parametric bijection): for odd `n` with `3 ∤ n`,
`t ↦ m(n,t)` is a bijection from `ℕ` onto `S_n`. -/
theorem layer_elem_bijOn {n : ℕ} (hn : Odd n) (hn3 : ¬ 3 ∣ n) :
    Set.BijOn (layer_elem n) Set.univ (preimage_layer n) := by
  refine ⟨fun t _ => ⟨odd_layer_elem hn3 t, collatz_step_layer_elem hn hn3 t⟩,
    (layer_elem_strictMono hn3).injective.injOn, ?_⟩
  intro m hm
  rw [← range_layer_elem hn hn3] at hm
  obtain ⟨t, rfl⟩ := hm
  exact ⟨t, trivial, rfl⟩

/-- Lemma 3.4: for odd `n`, `S_n` is empty iff `3 ∣ n`; for `3 ∤ n` it is
infinite. -/
theorem preimage_layer_eq_empty_iff {n : ℕ} (hn : Odd n) :
    preimage_layer n = ∅ ↔ 3 ∣ n := by
  refine ⟨fun h => ?_, preimage_layer_eq_empty_of_three_dvd⟩
  by_contra hn3
  have hmem : layer_elem n 0 ∈ preimage_layer n :=
    ⟨odd_layer_elem hn3 0, collatz_step_layer_elem hn hn3 0⟩
  rw [h] at hmem
  exact hmem

/-- Lemma 3.4: for odd `n` with `3 ∤ n`, `S_n` is infinite. -/
theorem preimage_layer_infinite {n : ℕ} (hn : Odd n) (hn3 : ¬ 3 ∣ n) :
    (preimage_layer n).Infinite := by
  rw [← range_layer_elem hn hn3]
  exact Set.infinite_range_of_injective (layer_elem_strictMono hn3).injective

/-- Corollary 3.5.b: `(n,t) ↦ m(n,t)` is a bijection from
`{(n,t) : n odd, 3 ∤ n}` onto the odd natural numbers. -/
theorem layer_elem_pair_bijOn :
    Set.BijOn (fun p : ℕ × ℕ => layer_elem p.1 p.2)
      {p | Odd p.1 ∧ ¬ 3 ∣ p.1} {m | Odd m} := by
  refine ⟨fun p hp => odd_layer_elem hp.2 p.2, ?_, ?_⟩
  · rintro ⟨n, t⟩ ⟨hn, hn3⟩ ⟨n', t'⟩ ⟨hn', hn3'⟩ h
    simp only at hn hn3 hn' hn3' h
    have hnn : n = n' := by
      rw [← collatz_step_layer_elem hn hn3 t, ← collatz_step_layer_elem hn' hn3' t', h]
    subst hnn
    rw [(layer_elem_strictMono hn3).injective h]
  · intro m hm
    exact ⟨(collatz_step m, (step_type m - layer_base_exp (collatz_step m)) / 2),
      ⟨collatz_step_is_odd, not_three_dvd_collatz_step m⟩, layer_elem_collatz_step hm⟩

end Collatz.Layers
