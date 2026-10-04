/-
Collatz Conjecture: SEDT Deep Formalization — Multibit Bonus
(Appendix D.2 algebraic core)

This module implements the **algebraic core** of Corollary D.2.

The mathematical content of D.2 reduces, after the homogenization
(Lemma D.10) and touch-residue (Lemma D.1.b) layers are applied,
to the following purely combinatorial identities inside one period
of length `Q_{t+U} = 2^U · Q_t`:

  *  Inside one period there are exactly `2^U` t-touches, indexed by
     `j ∈ Finset.range (2^U)`.

  *  The "bonus ≥ u" condition at the j-th touch is equivalent to
     `2 ^ u ∣ j` (modulo the index `j = 0`).

  *  The number of `j ∈ range (2 ^ U)` divisible by `2 ^ u` equals
     `2 ^ (U - u)` for `u ≤ U`.

  *  Consequently the cumulative bonus over one period equals

       `∑_{u=1}^{U} 2 ^ (U - u)  =  2 ^ U - 1`,

     yielding the average `(2 ^ U - 1) / 2 ^ U = 1 - 2^{-U}`.

The orbit-side input "inside one `Q_{t+U}`-period there are exactly
`2^U` t-touches indexed by `j ∈ range (2^U)`" is supplied by the
homogenization / touch-residue layer; the present file delivers the
clean integer identities used to extract the bound.
-/

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Collatz.SEDT.MultibitBonus

open Finset

/-!
## Geometric sums of powers of two
-/

/-- **Geometric sum of powers of two.** `∑_{u=0}^{n-1} 2^u + 1 = 2^n`. -/
theorem geom_sum_two (n : ℕ) :
    (∑ u ∈ range n, 2 ^ u) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ]
      have hassoc : (∑ u ∈ range n, 2 ^ u) + 2 ^ n + 1
              = (∑ u ∈ range n, 2 ^ u) + 1 + 2 ^ n := by ring
      rw [hassoc, ih, pow_succ]
      ring

/-- **Geometric sum, reindexed.**
`∑_{u ∈ range U} 2 ^ u = ∑_{u ∈ range U} 2 ^ (U - 1 - u)`. -/
theorem geom_sum_two_reindexed (U : ℕ) :
    (∑ u ∈ range U, 2 ^ u) = (∑ u ∈ range U, 2 ^ (U - 1 - u)) := by
  rw [← Finset.sum_range_reflect (fun u => 2 ^ u) U]

/-- **Reindexed geometric sum.** `∑_{u ∈ range U} 2^(U - 1 - u) + 1 = 2^U`. -/
theorem multibit_period_bonus_total (U : ℕ) :
    (∑ u ∈ range U, 2 ^ (U - 1 - u)) + 1 = 2 ^ U := by
  rw [← geom_sum_two_reindexed]
  exact geom_sum_two U

/-!
## Counting cosets at successive 2-adic refinement levels
-/

/-- **Coset count.** Among `j ∈ range (2 ^ U)`, exactly `2 ^ (U - u)`
of them are divisible by `2 ^ u`, provided `u ≤ U`. -/
theorem card_filter_dvd_pow_two (U u : ℕ) (h : u ≤ U) :
    ((range (2 ^ U)).filter (fun j => 2 ^ u ∣ j)).card = 2 ^ (U - u) := by
  have hpow_pos : 0 < 2 ^ u := pow_pos (by norm_num : (0 : ℕ) < 2) u
  have hsum_eq : u + (U - u) = U := by omega
  have hpow_eq : 2 ^ u * 2 ^ (U - u) = 2 ^ U := by
    rw [← pow_add, hsum_eq]
  have himg :
      ((range (2 ^ U)).filter (fun j => 2 ^ u ∣ j))
        = (range (2 ^ (U - u))).image (fun i => 2 ^ u * i) := by
    ext j
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hjlt, k, hk⟩
      refine ⟨k, ?_, hk.symm⟩
      have hkmul : 2 ^ u * k < 2 ^ U := by rw [← hk]; exact hjlt
      have hbound : 2 ^ u * k < 2 ^ u * 2 ^ (U - u) := by
        rw [hpow_eq]; exact hkmul
      exact Nat.lt_of_mul_lt_mul_left hbound
    · rintro ⟨i, hilt, hij⟩
      refine ⟨?_, i, hij.symm⟩
      have hlt : 2 ^ u * i < 2 ^ u * 2 ^ (U - u) :=
        (Nat.mul_lt_mul_left hpow_pos).mpr hilt
      rw [hpow_eq] at hlt
      rw [← hij]; exact hlt
  rw [himg]
  rw [Finset.card_image_of_injective _
        (fun a b (h : 2 ^ u * a = 2 ^ u * b) =>
          Nat.eq_of_mul_eq_mul_left hpow_pos h)]
  exact Finset.card_range _

/-!
## Bonus distribution over one period

We model one `Q_{t+U}`-period of t-touches abstractly as the index
set `range (2 ^ U)`. The bonus function `bonus j := min (ν₂ j) U`,
with the convention `ν₂ 0 := U` (since the touch at `j = 0` lies in
all 2-adic refinements up to level `t + U`), encodes the multibit
contribution. The complementary identity

  bonus j = #{u : 1 ≤ u ≤ U ∧ 2^u ∣ j}     (with j = 0 capped at U)

lets us swap the order of summation and reduce to the coset count.
-/

/-- **Bonus function on one period.** `periodBonus U j := min (ν₂ j) U`,
with the convention that `ν₂ 0 = U`. -/
def periodBonus (U j : ℕ) : ℕ :=
  if j = 0 then U else min (Nat.factorization j 2) U

/-- **Bonus by levels.** Bonus = number of refinement levels at which
the touch persists. -/
theorem periodBonus_eq_card_levels (U j : ℕ) (hj : j < 2 ^ U) :
    periodBonus U j = ((range U).filter (fun u => 2 ^ (u + 1) ∣ j)).card := by
  unfold periodBonus
  by_cases h0 : j = 0
  · subst h0
    have hall : ∀ u ∈ range U, 2 ^ (u + 1) ∣ (0 : ℕ) := fun _ _ => dvd_zero _
    rw [if_pos rfl]
    have : ((range U).filter (fun u => 2 ^ (u + 1) ∣ (0 : ℕ))) = range U := by
      apply Finset.filter_eq_self.mpr
      exact hall
    rw [this, Finset.card_range]
  · rw [if_neg h0]
    -- show min ν₂(j) U = #{u < U : 2^(u+1) ∣ j}
    have hjpos : 0 < j := Nat.pos_of_ne_zero h0
    -- nu := ν₂(j), counted only up to U
    set ν := Nat.factorization j 2 with hν
    have hpow_dvd : ∀ u : ℕ, (2 ^ u ∣ j) ↔ u ≤ ν := by
      intro u
      have h2 : (2 : ℕ).Prime := Nat.prime_two
      constructor
      · intro hdvd
        rw [hν]
        exact (Nat.Prime.pow_dvd_iff_le_factorization h2 (Nat.pos_iff_ne_zero.mp hjpos)).mp hdvd
      · intro hle
        rw [hν] at hle
        exact (Nat.Prime.pow_dvd_iff_le_factorization h2 (Nat.pos_iff_ne_zero.mp hjpos)).mpr hle
    have hfilter_eq :
        ((range U).filter (fun u => 2 ^ (u + 1) ∣ j))
          = (range U).filter (fun u => u + 1 ≤ ν) := by
      apply Finset.filter_congr
      intro u _
      exact hpow_dvd (u + 1)
    rw [hfilter_eq]
    -- now count u < U with u + 1 ≤ ν, i.e. u < min ν U
    have hcard :
        ((range U).filter (fun u => u + 1 ≤ ν)).card = min ν U := by
      have heq :
          (range U).filter (fun u => u + 1 ≤ ν) = range (min ν U) := by
        ext u
        simp only [mem_filter, mem_range, lt_min_iff]
        omega
      rw [heq, Finset.card_range]
    rw [hcard]

/-- **Total bonus over one period equals `2^U - 1`.**
The cumulative bonus over the index set `range (2^U)` of one
`Q_{t+U}`-period equals `2^U - 1`, by Fubini/double-counting:

  `∑_{j < 2^U} #{u < U : 2^(u+1) ∣ j}
    = ∑_{u < U} #{j < 2^U : 2^(u+1) ∣ j}
    = ∑_{u < U} 2^(U - u - 1)
    = 2^U - 1.` -/
theorem multibit_period_total_bonus (U : ℕ) :
    (∑ j ∈ range (2 ^ U), periodBonus U j) + 1 = 2 ^ U := by
  -- Step 1: rewrite each bonus as the level-count.
  have hsum_eq :
      (∑ j ∈ range (2 ^ U), periodBonus U j)
        = ∑ j ∈ range (2 ^ U),
            ((range U).filter (fun u => 2 ^ (u + 1) ∣ j)).card := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    exact periodBonus_eq_card_levels U j hj
  -- Step 2: turn each card into a sum of 1's, then swap order.
  have hsum_swap :
      ∑ j ∈ range (2 ^ U),
          ((range U).filter (fun u => 2 ^ (u + 1) ∣ j)).card
        = ∑ u ∈ range U,
          ((range (2 ^ U)).filter (fun j => 2 ^ (u + 1) ∣ j)).card := by
    -- Use card-as-indicator-sum and swap.
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hsum_eq, hsum_swap]
  -- Step 3: each inner card equals 2 ^ (U - (u + 1)).
  have hinner :
      ∀ u ∈ range U,
        ((range (2 ^ U)).filter (fun j => 2 ^ (u + 1) ∣ j)).card
          = 2 ^ (U - (u + 1)) := by
    intro u hu
    rw [mem_range] at hu
    exact card_filter_dvd_pow_two U (u + 1) (by omega)
  rw [Finset.sum_congr rfl hinner]
  -- Step 4: reindex to obtain the geometric sum and apply
  -- `multibit_period_bonus_total`.
  have hcongr :
      (∑ u ∈ range U, 2 ^ (U - (u + 1)))
        = (∑ u ∈ range U, 2 ^ (U - 1 - u)) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [mem_range] at hu
    congr 1
    omega
  rw [hcongr]
  exact multibit_period_bonus_total U

/-- **Average bonus per touch ≥ `1 - 2^{-U}` (integer form).**
Multiplying through by `2 ^ U`, the statement
`average ≥ 1 - 2^{-U}` becomes the clean integer inequality
`(∑ bonuses) · 2 ^ U ≥ (2 ^ U - 1) · 2 ^ U`, which holds with
equality on a single complete period. Stated here as an equality
on one period:

  `∑_{j < 2^U} periodBonus U j = 2 ^ U - 1`. -/
theorem multibit_period_bonus_eq (U : ℕ) :
    ∑ j ∈ range (2 ^ U), periodBonus U j = 2 ^ U - 1 := by
  have h := multibit_period_total_bonus U
  have h2U_pos : 0 < 2 ^ U := pow_pos (by norm_num : (0 : ℕ) < 2) U
  omega

end Collatz.SEDT.MultibitBonus
