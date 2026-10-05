/-
Block form of the cycle equation (paper Proposition H.7), positive case.

* `block_start_equation` — identity (H.7.2) between consecutive block starts:
  if `x + 1 = 2^α y` (`y` odd, `α ≥ 1`), `σ = ν₂(3^α y − 1)` and
  `T^α(x) + 1 = 2^{α'} y'`, then `2^{σ+α'} y' = 3^α y + 2^σ − 1`.
* `RealizesOneBlock α σ x` — the one-block pattern `((α, σ))` is realized by
  the odd number `x`: the first `α` exponents of the orbit of `x` are
  `1, …, 1, σ + 1` (`α − 1` ones) and `T^α(x) = x`.
* `realizesOneBlock_add_one_mul` — Proposition H.7(a) for one block:
  `(x + 1) · D = 2^α (2^σ − 1)` with `D = 2^{α+σ} − 3^α`; equivalently
  `y · D = C(w) = 2^σ − 1` and `x = 2^α (2^σ − 1)/D − 1`.
* `exists_realizesOneBlock_iff` — Proposition H.7(c): for `α, σ ≥ 1`, a positive
  odd `x` realizing `((α, σ))` exists iff `D > 0` and `D ∣ 2^σ − 1`
  (paper: `D ∣ 2^{s−1} − 1` with `s = σ + 1`).

Status: proved. This is an equivalent reformulation of the one-block cycle
condition; it excludes no cycle. The pattern `((1,1))` is realized by `x = 1`
(trivial cycle), see `Collatz/Tests/ResidualSanity.lean`.

* `RealizesBlockPattern α σ k x`, `blockPatternC` (= `C(w)`) and
  `realizesBlockPattern_block_equation` — Proposition H.7(a) for `k` blocks:
  `y₁ · D = C(w)`, `D > 0`, `D ∣ C(w)`, `(x + 1) · D = 2^{α₁} C(w)`.

Not formalized: the converse direction of H.7(b) for `k ≥ 2` (existence of a
realizer from `D > 0 ∧ D ∣ C(w)`, rotations `w^{[l]}`), and the negative-integer
case H.7(d) (`collatz_step` is defined on `ℕ`).
-/
import Collatz.Blocks.BlockStep

namespace Collatz.CycleExclusion

open Collatz.Foundations Collatz.Blocks

/-- Proposition H.7, identity (H.7.2) between consecutive block starts of a
positive odd orbit: if `x + 1 = 2^α y` with `y` odd and `α ≥ 1`,
`σ = ν₂(3^α y − 1)`, and the next block start `T^α(x)` satisfies
`T^α(x) + 1 = 2^{α'} y'`, then `2^{σ+α'} · y' = 3^α y + 2^σ − 1`.
(The identity holds for any such factorization of `T^α(x) + 1`; the paper uses
the one with `y'` odd, `α' = depth₋(T^α x)`.) -/
theorem block_start_equation {x α y α' y' : ℕ} (hy : Odd y) (hα : 1 ≤ α)
    (hx : x + 1 = 2 ^ α * y) (hx' : collatz_step^[α] x + 1 = 2 ^ α' * y') :
    2 ^ ((3 ^ α * y - 1).factorization 2 + α') * y' =
      3 ^ α * y + 2 ^ (3 ^ α * y - 1).factorization 2 - 1 := by
  have h := two_pow_sigma_mul_iterate_block_length hy hα hx
  obtain ⟨_, h3⟩ := three_mul_iterate_pred_add_one hy hα hx
  rw [pow_add, mul_assoc, ← hx', mul_add, mul_one, h]
  generalize 2 ^ (3 ^ α * y - 1).factorization 2 = P
  generalize 3 ^ α * y = M at h3 ⊢
  omega

/-- The odd number `x` realizes the one-block pattern `((α, σ))`
(paper Proposition H.7 with `k = 1`): the first `α` exponents of its orbit are
`α − 1` ones followed by `σ + 1`, and `T^α(x) = x`. -/
def RealizesOneBlock (α σ x : ℕ) : Prop :=
  Odd x ∧ (∀ k, k + 2 ≤ α → step_type (collatz_step^[k] x) = 1) ∧
    step_type (collatz_step^[α - 1] x) = σ + 1 ∧ collatz_step^[α] x = x

/-- Core of Proposition H.7(a) for one block: a realizer `x` of `((α, σ))`
has `x + 1 = 2^α y` with `y` odd and `y · (2^{α+σ} − 3^α) = 2^σ − 1`. -/
theorem realizesOneBlock_odd_part {α σ x : ℕ} (hα : 1 ≤ α) (hσ : 1 ≤ σ)
    (h : RealizesOneBlock α σ x) :
    ∃ y, Odd y ∧ x + 1 = 2 ^ α * y ∧
      (y : ℤ) * (2 ^ (α + σ) - 3 ^ α) = 2 ^ σ - 1 := by
  obtain ⟨hx, h1, h2, hper⟩ := h
  have hd := depth_minus_eq_of_block_exponents hx hα h1 (by omega)
  obtain ⟨y, hy, hxy⟩ := exists_odd_add_one_eq_two_pow_depth_mul x
  rw [hd] at hxy
  have hs := step_type_iterate_pred hy hα hxy
  have hν : (3 ^ α * y - 1).factorization 2 = σ := by omega
  have heq := block_start_equation (α' := α) (y' := y) hy hα hxy (by rw [hper]; exact hxy)
  rw [hν] at heq
  obtain ⟨_, h3⟩ := three_mul_iterate_pred_add_one hy hα hxy
  have heqN : 2 ^ (σ + α) * y + 1 = 3 ^ α * y + 2 ^ σ := by
    have : 1 ≤ 2 ^ σ := Nat.one_le_two_pow
    omega
  have heqZ : ((2 ^ (σ + α) * y + 1 : ℕ) : ℤ) = ((3 ^ α * y + 2 ^ σ : ℕ) : ℤ) := by
    rw [heqN]
  push_cast at heqZ
  refine ⟨y, hy, hxy, ?_⟩
  rw [add_comm α σ]
  linear_combination heqZ

/-- Proposition H.7(a), one block: if `x` realizes `((α, σ))` (`α, σ ≥ 1`), then
`(x + 1) · (2^{α+σ} − 3^α) = 2^α · (2^σ − 1)`, i.e. `x = 2^α (2^σ − 1)/D − 1`
with `D = 2^{α+σ} − 3^α`. Uniqueness of the realizer is
`realizesOneBlock_unique`. -/
theorem realizesOneBlock_add_one_mul {α σ x : ℕ} (hα : 1 ≤ α) (hσ : 1 ≤ σ)
    (h : RealizesOneBlock α σ x) :
    ((x : ℤ) + 1) * (2 ^ (α + σ) - 3 ^ α) = 2 ^ α * (2 ^ σ - 1) := by
  obtain ⟨y, _, hxy, hyD⟩ := realizesOneBlock_odd_part hα hσ h
  have hxZ : (x : ℤ) + 1 = 2 ^ α * y := by exact_mod_cast hxy
  rw [hxZ]
  linear_combination (2 : ℤ) ^ α * hyD

/-- Proposition H.7(c) (one-block cycle criterion), positive case: for
`α, σ ≥ 1`, there is a (positive) odd natural number `x` whose orbit starts with
`α − 1` steps with `e = 1`, then one step with `e = σ + 1`, and returns to `x`
after these `α` steps, if and only if `D = 2^{α+σ} − 3^α > 0` and
`D ∣ 2^σ − 1`. -/
theorem exists_realizesOneBlock_iff {α σ : ℕ} (hα : 1 ≤ α) (hσ : 1 ≤ σ) :
    (∃ x, RealizesOneBlock α σ x) ↔
      0 < (2 : ℤ) ^ (α + σ) - 3 ^ α ∧ ((2 : ℤ) ^ (α + σ) - 3 ^ α) ∣ 2 ^ σ - 1 := by
  have h2σ : (2 : ℤ) ≤ 2 ^ σ := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ σ := pow_le_pow_right₀ (by norm_num) hσ
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, _, hyD⟩ := realizesOneBlock_odd_part hα hσ hx
    have hy0 : (0 : ℤ) < y := by exact_mod_cast hy.pos
    refine ⟨?_, ⟨y, by rw [← hyD]; ring⟩⟩
    by_contra hD
    push_neg at hD
    have : (y : ℤ) * (2 ^ (α + σ) - 3 ^ α) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hy0.le hD
    linarith
  · rintro ⟨hD, c, hc⟩
    have hc0 : 0 < c := by
      by_contra hc0
      push_neg at hc0
      have : ((2 : ℤ) ^ (α + σ) - 3 ^ α) * c ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hD.le hc0
      linarith
    obtain ⟨y, rfl⟩ := Int.eq_ofNat_of_zero_le hc0.le
    have hy1 : 1 ≤ y := by exact_mod_cast hc0
    -- `y` is odd because `y · D = 2^σ − 1` is odd.
    have hoddZ : Odd ((2 : ℤ) ^ σ - 1) := by
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hσ
      exact ⟨2 ^ s - 1, by rw [pow_succ]; ring⟩
    rw [hc] at hoddZ
    have hy : Odd y := by exact_mod_cast (Int.odd_mul.1 hoddZ).2
    -- The realizer `x = 2^α y − 1`.
    have h2y : 1 ≤ 2 ^ α * y := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h3y : 1 ≤ 3 ^ α * y := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hxy : (2 ^ α * y - 1) + 1 = 2 ^ α * y := by omega
    have hx : Odd (2 ^ α * y - 1) := by
      obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hα
      have h2 : 2 ^ (a + 1) * y = 2 * (2 ^ a * y) := by ring
      rw [h2] at h2y ⊢
      exact ⟨2 ^ a * y - 1, by omega⟩
    have hN : 3 ^ α * y - 1 = 2 ^ σ * (2 ^ α * y - 1) := by
      zify [h3y, h2y]
      linear_combination hc
    have hν : (3 ^ α * y - 1).factorization 2 = σ := by
      rw [hN]; exact factorization_two_pow_mul_of_odd σ hx
    refine ⟨2 ^ α * y - 1, hx, step_type_iterate_eq_one hy hxy, ?_, ?_⟩
    · rw [step_type_iterate_pred hy hα hxy, hν]; ring
    · rw [iterate_block_length hy hα hxy, hν, hN]
      exact Nat.mul_div_cancel_left _ (pow_pos two_pos σ)

/-- Proposition H.7(a)/(c), uniqueness: for `α, σ ≥ 1` at most one odd natural
number realizes the one-block pattern `((α, σ))`. -/
theorem realizesOneBlock_unique {α σ x x' : ℕ} (hα : 1 ≤ α) (hσ : 1 ≤ σ)
    (h : RealizesOneBlock α σ x) (h' : RealizesOneBlock α σ x') : x = x' := by
  have e1 := realizesOneBlock_add_one_mul hα hσ h
  have e2 := realizesOneBlock_add_one_mul hα hσ h'
  have hD : (0 : ℤ) < 2 ^ (α + σ) - 3 ^ α :=
    ((exists_realizesOneBlock_iff hα hσ).1 ⟨x, h⟩).1
  have : ((x : ℤ) + 1) = (x' : ℤ) + 1 :=
    mul_right_cancel₀ hD.ne' (e1.trans e2.symm)
  exact_mod_cast (by linarith : (x : ℤ) = x')

/-! ## `k` blocks: Proposition H.7(a)

A block pattern `w = ((α₁,σ₁),…,(α_k,σ_k))` is encoded 0-indexed by two
functions `α σ : ℕ → ℕ`, of which only the values at `i < k` are used. -/

/-- `p = α₀ + ⋯ + α_{k−1}`, the length of the exponent word of the first `k`
blocks; `blockPatternLength α i` is also the index at which block `i` starts. -/
def blockPatternLength (α : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, α i

/-- `S = Σ_{i<k} (α_i + σ_i)`, the sum of the exponent word. -/
def blockPatternExpSum (α σ : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (α i + σ i)

/-- Partial sums `τ₀ + ⋯ + τ_{i−1}` with `τ_j = σ_j + α_{j+1}` (0-indexed). -/
def blockTauSum (α σ : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, (σ j + α (j + 1))

/-- `C(w)` of Proposition H.7, 0-indexed:
`C = Σ_{i<k} 3^{α_{i+1}+⋯+α_{k−1}} · 2^{τ₀+⋯+τ_{i−1}} · (2^{σ_i} − 1)`. -/
def blockPatternC (α σ : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k,
    3 ^ (∑ j ∈ Finset.Ico (i + 1) k, α j) * 2 ^ blockTauSum α σ i * (2 ^ σ i - 1)

/-- The odd number `x` realizes the pattern given by `α σ` and `k` (paper
Proposition H.7): for each `i < k`, the exponents at indices
`P_i, …, P_i + α_i − 2` (`P_i = α₀ + ⋯ + α_{i−1}`) equal `1` and the exponent at
index `P_i + α_i − 1` equals `σ_i + 1`; and `T^p(x) = x`. This is "the first `p`
exponents of the orbit of `x` form the exponent word of `w`, and `T^p(x) = x`".
The definition matches the paper only when all `α_i ≥ 1` (a block pattern has
`α_i, σ_i ≥ 1`); for `α_i = 0` the truncated `α_i − 1 = 0` changes its meaning.
All theorems below assume `α_i, σ_i ≥ 1` for `i < k`. -/
def RealizesBlockPattern (α σ : ℕ → ℕ) (k x : ℕ) : Prop :=
  Odd x ∧
    (∀ i < k,
      (∀ j, j + 2 ≤ α i → step_type (collatz_step^[blockPatternLength α i + j] x) = 1) ∧
        step_type (collatz_step^[blockPatternLength α i + (α i - 1)] x) = σ i + 1) ∧
    collatz_step^[blockPatternLength α k] x = x

/-- Recursion for `C`: `C_{k+1} = 3^{α_k} C_k + 2^{τ₀+⋯+τ_{k−1}} (2^{σ_k} − 1)`. -/
lemma blockPatternC_succ (α σ : ℕ → ℕ) (k : ℕ) :
    blockPatternC α σ (k + 1) =
      3 ^ α k * blockPatternC α σ k + 2 ^ blockTauSum α σ k * (2 ^ σ k - 1) := by
  unfold blockPatternC
  rw [Finset.sum_range_succ, Finset.Ico_self, Finset.sum_empty, pow_zero, one_mul,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [Finset.sum_Ico_succ_top (by omega : j + 1 ≤ k), pow_add]
  ring

/-- `C(w) > 0` when `σ_{k−1} ≥ 1` (here: `k = m + 1`). -/
theorem blockPatternC_pos (α σ : ℕ → ℕ) (m : ℕ) (hσ : 1 ≤ σ m) :
    0 < blockPatternC α σ (m + 1) := by
  rw [blockPatternC_succ]
  have h1 : 2 ≤ 2 ^ σ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ σ m := Nat.pow_le_pow_right (by norm_num) hσ
  have h2 : 0 < 2 ^ blockTauSum α σ m * (2 ^ σ m - 1) :=
    Nat.mul_pos (pow_pos two_pos _) (by omega)
  omega

/-- Telescoping of (H.7.2) along the first `m + 1` block starts (pure algebra):
if `2^{σ_i + α_{i+1}} y_{i+1} = 3^{α_i} y_i + (2^{σ_i} − 1)` for `i < m`, then
`2^{τ₀+⋯+τ_{i−1}} y_i = 3^{α₀+⋯+α_{i−1}} y₀ + C_i` for `i ≤ m`. -/
lemma block_telescope (α σ y : ℕ → ℕ) (m : ℕ)
    (hrec : ∀ i, i < m →
      2 ^ (σ i + α (i + 1)) * y (i + 1) = 3 ^ α i * y i + (2 ^ σ i - 1)) :
    ∀ i ≤ m, 2 ^ blockTauSum α σ i * y i =
      3 ^ blockPatternLength α i * y 0 + blockPatternC α σ i := by
  intro i
  induction i with
  | zero => intro _; simp [blockTauSum, blockPatternLength, blockPatternC]
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have h2 := hrec i (by omega)
    have hT : blockTauSum α σ (i + 1) = blockTauSum α σ i + (σ i + α (i + 1)) :=
      Finset.sum_range_succ _ _
    have hP : blockPatternLength α (i + 1) = blockPatternLength α i + α i :=
      Finset.sum_range_succ _ _
    rw [blockPatternC_succ, hT, hP, pow_add, mul_assoc, h2, pow_add]
    calc 2 ^ blockTauSum α σ i * (3 ^ α i * y i + (2 ^ σ i - 1))
        = 3 ^ α i * (2 ^ blockTauSum α σ i * y i) +
            2 ^ blockTauSum α σ i * (2 ^ σ i - 1) := by ring
      _ = 3 ^ α i * (3 ^ blockPatternLength α i * y 0 + blockPatternC α σ i) +
            2 ^ blockTauSum α σ i * (2 ^ σ i - 1) := by rw [h1]
      _ = 3 ^ blockPatternLength α i * 3 ^ α i * y 0 +
            (3 ^ α i * blockPatternC α σ i + 2 ^ blockTauSum α σ i * (2 ^ σ i - 1)) := by
          ring

/-- Proposition H.7(a), natural-number form: if the odd number `x` realizes the
block pattern `((α_i, σ_i))_{i<k}` with `k ≥ 1` and all `α_i, σ_i ≥ 1`, then
`x + 1 = 2^{α₀} y` with `y` odd and `2^S · y = 3^p · y + C(w)`. -/
theorem realizesBlockPattern_two_pow_mul {α σ : ℕ → ℕ} {k x : ℕ} (hk : 1 ≤ k)
    (hα : ∀ i < k, 1 ≤ α i) (hσ : ∀ i < k, 1 ≤ σ i)
    (h : RealizesBlockPattern α σ k x) :
    ∃ y, Odd y ∧ x + 1 = 2 ^ α 0 * y ∧
      2 ^ blockPatternExpSum α σ k * y =
        3 ^ blockPatternLength α k * y + blockPatternC α σ k := by
  obtain ⟨hx, hblk, hper⟩ := h
  -- block starts `z i = T^{P_i}(x)`
  set z : ℕ → ℕ := fun i => collatz_step^[blockPatternLength α i] x with hz
  have hzodd : ∀ i, Odd (z i) := fun i => odd_iterates_of_odd hx _
  have hiter : ∀ i j, collatz_step^[blockPatternLength α i + j] x =
      collatz_step^[j] (z i) := by
    intro i j
    rw [add_comm, Function.iterate_add_apply]
  have hznext : ∀ i, collatz_step^[α i] (z i) = z (i + 1) := by
    intro i
    simp only [hz]
    rw [← Function.iterate_add_apply]
    congr 1
    rw [blockPatternLength, blockPatternLength, Finset.sum_range_succ]
    ring
  choose y hy using fun i => exists_odd_add_one_eq_two_pow_depth_mul (z i)
  have hdepth : ∀ i < k, depth_minus (z i) = α i := by
    intro i hi
    obtain ⟨h1, h2⟩ := hblk i hi
    refine depth_minus_eq_of_block_exponents (hzodd i) (hα i hi)
      (fun j hj => by rw [← hiter]; exact h1 j hj) ?_
    rw [← hiter, h2]
    have := hσ i hi
    omega
  have hzy : ∀ i < k, z i + 1 = 2 ^ α i * y i := by
    intro i hi
    rw [← hdepth i hi]
    exact (hy i).2
  have hν : ∀ i < k, (3 ^ α i * y i - 1).factorization 2 = σ i := by
    intro i hi
    have hs := step_type_iterate_pred (hy i).1 (hα i hi) (hzy i hi)
    have h2 := (hblk i hi).2
    rw [hiter] at h2
    omega
  -- identity (H.7.2) for each block
  have hrec : ∀ i < k, ∀ a' y', z (i + 1) + 1 = 2 ^ a' * y' →
      2 ^ (σ i + a') * y' = 3 ^ α i * y i + (2 ^ σ i - 1) := by
    intro i hi a' y' h'
    have heq := block_start_equation (hy i).1 (hα i hi) (hzy i hi)
      (by rw [hznext]; exact h')
    rw [hν i hi] at heq
    rw [heq]
    have : 1 ≤ 2 ^ σ i := Nat.one_le_two_pow
    omega
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have htel := block_telescope α σ y m
    (fun i hi => hrec i (by omega) (α (i + 1)) (y (i + 1)) (hzy (i + 1) (by omega)))
    m le_rfl
  have hz0 : z 0 = x := by simp [hz, blockPatternLength]
  have hwrap := hrec m (by omega) (α 0) (y 0)
    (by rw [show z (m + 1) = x from hper, ← hz0]; exact hzy 0 (by omega))
  refine ⟨y 0, (hy 0).1, by rw [← hz0]; exact hzy 0 (by omega), ?_⟩
  have hS : blockPatternExpSum α σ (m + 1) = blockTauSum α σ m + (σ m + α 0) := by
    unfold blockPatternExpSum blockTauSum
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_range_succ' α,
      Finset.sum_range_succ σ]
    ring
  have hP : blockPatternLength α (m + 1) = blockPatternLength α m + α m :=
    Finset.sum_range_succ _ _
  rw [hS, hP, blockPatternC_succ, pow_add, mul_assoc, hwrap, pow_add]
  calc 2 ^ blockTauSum α σ m * (3 ^ α m * y m + (2 ^ σ m - 1))
      = 3 ^ α m * (2 ^ blockTauSum α σ m * y m) +
          2 ^ blockTauSum α σ m * (2 ^ σ m - 1) := by ring
    _ = 3 ^ α m * (3 ^ blockPatternLength α m * y 0 + blockPatternC α σ m) +
          2 ^ blockTauSum α σ m * (2 ^ σ m - 1) := by rw [htel]
    _ = 3 ^ blockPatternLength α m * 3 ^ α m * y 0 +
          (3 ^ α m * blockPatternC α σ m + 2 ^ blockTauSum α σ m * (2 ^ σ m - 1)) := by
        ring

/-- Proposition H.7(a) (block equation), positive case: if the odd number `x`
realizes the block pattern `w = ((α_i, σ_i))_{i<k}` (`k ≥ 1`, all `α_i, σ_i ≥ 1`),
write `x + 1 = 2^{α₀} y` (`y` odd) and `D = 2^S − 3^p`. Then `y · D = C(w)`,
hence `D > 0`, `D ∣ C(w)` and `(x + 1) · D = 2^{α₀} · C(w)`, i.e.
`x = 2^{α₀} C(w)/D − 1`. -/
theorem realizesBlockPattern_block_equation {α σ : ℕ → ℕ} {k x : ℕ} (hk : 1 ≤ k)
    (hα : ∀ i < k, 1 ≤ α i) (hσ : ∀ i < k, 1 ≤ σ i)
    (h : RealizesBlockPattern α σ k x) :
    ∃ y : ℕ, Odd y ∧ x + 1 = 2 ^ α 0 * y ∧
      (y : ℤ) * (2 ^ blockPatternExpSum α σ k - 3 ^ blockPatternLength α k) =
        blockPatternC α σ k ∧
      0 < (2 : ℤ) ^ blockPatternExpSum α σ k - 3 ^ blockPatternLength α k ∧
      ((2 : ℤ) ^ blockPatternExpSum α σ k - 3 ^ blockPatternLength α k) ∣
        (blockPatternC α σ k : ℤ) ∧
      ((x : ℤ) + 1) * (2 ^ blockPatternExpSum α σ k - 3 ^ blockPatternLength α k) =
        2 ^ α 0 * blockPatternC α σ k := by
  obtain ⟨y, hy, hxy, hN⟩ := realizesBlockPattern_two_pow_mul hk hα hσ h
  have hZ : ((2 ^ blockPatternExpSum α σ k * y : ℕ) : ℤ) =
      ((3 ^ blockPatternLength α k * y + blockPatternC α σ k : ℕ) : ℤ) := by rw [hN]
  push_cast at hZ
  have hyD : (y : ℤ) * (2 ^ blockPatternExpSum α σ k - 3 ^ blockPatternLength α k) =
      blockPatternC α σ k := by linear_combination hZ
  have hy0 : (0 : ℤ) < y := by exact_mod_cast hy.pos
  have hC : (0 : ℤ) < blockPatternC α σ k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact_mod_cast blockPatternC_pos α σ m (hσ m (by omega))
  refine ⟨y, hy, hxy, hyD, ?_, ⟨y, by rw [← hyD]; ring⟩, ?_⟩
  · by_contra hD
    push_neg at hD
    have : (y : ℤ) * (2 ^ blockPatternExpSum α σ k - 3 ^ blockPatternLength α k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hy0.le hD
    linarith
  · have hxZ : (x : ℤ) + 1 = 2 ^ α 0 * y := by exact_mod_cast hxy
    rw [hxZ]
    linear_combination (2 : ℤ) ^ α 0 * hyD

/-- Consistency of the two encodings: realizing the `k = 1` pattern `((α₀, σ₀))`
is the same as `RealizesOneBlock α₀ σ₀`. -/
theorem realizesBlockPattern_one_iff (α σ : ℕ → ℕ) (x : ℕ) :
    RealizesBlockPattern α σ 1 x ↔ RealizesOneBlock (α 0) (σ 0) x := by
  simp only [RealizesBlockPattern, RealizesOneBlock, blockPatternLength,
    Finset.range_one, Finset.sum_singleton, Nat.lt_one_iff, forall_eq,
    Finset.range_zero, Finset.sum_empty, zero_add, and_assoc]

/-- For one block, `C(((α₀, σ₀))) = 2^{σ₀} − 1` (paper H.7(c)). -/
theorem blockPatternC_one (α σ : ℕ → ℕ) : blockPatternC α σ 1 = 2 ^ σ 0 - 1 := by
  simp [blockPatternC, blockTauSum]

end Collatz.CycleExclusion
