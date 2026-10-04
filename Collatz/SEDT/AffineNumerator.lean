/-
Collatz Conjecture: SEDT Deep Formalization — Affine Numerator (Appendix D foundations)

This module is the first concrete brick of the multi-session proof project that
aims to close `AperiodicSelectedLongEpochResidual` and `AperiodicFillDriftResidual`
without axioms. See `c:\Users\anato\.cursor\plans\sedt_deep_formalization_d8eaf9c1.plan.md`.

Content of this file:

* Definition of the algebraic numerator from Appendix D.0:

    `N_k_int r₀ k = 3^(k+1) * (r₀ + 2) - 5 * 2^k`

  working in `ℤ` to avoid `Nat`-subtraction underflow at small `k`.

* The exact recurrence (Sublemma D.8):

    `N_k_int r₀ (k+1) = 3 * N_k_int r₀ k + 5 * 2^k`

  proved by `ring` after expanding the definition.

* Strict positivity for any `r₀ ≥ 1`:

    `0 < N_k_int r₀ k`

  proved by induction on `k` from `9 * 3^k > 5 * 2^k` for `k ≥ 0` and
  `(r₀ + 2) ≥ 3`.

These are real proved theorems with **no `sorry`**, **no `axiom`**, **no `admit`**,
and they do not depend on any open SEDT residual. They are the algebraic
foundation on top of which the Appendix D / E machinery (case-split on `d_k`,
`+5` shift formula, touch residue, tail homogenization, multibit bonus, linear
surplus) will be built in subsequent sessions.
-/

import Mathlib.Tactic

namespace Collatz.SEDT.AffineNumerator

open Int

/-- The exact algebraic numerator of Appendix D.0:
`N_k(r₀) := 3^(k+1) (r₀ + 2) - 5 · 2^k`, working in `ℤ` to avoid `Nat`
subtraction underflow at small `k`. -/
def N_k_int (r₀ : ℤ) (k : ℕ) : ℤ :=
  3 ^ (k + 1) * (r₀ + 2) - 5 * (2 : ℤ) ^ k

@[simp] lemma N_k_int_zero (r₀ : ℤ) :
    N_k_int r₀ 0 = 3 * (r₀ + 2) - 5 := by
  simp [N_k_int]

/-- Concrete sanity check at `r₀ = 1`, `k = 0` (matches `3*1 + 1 = 4`). -/
example : N_k_int 1 0 = 4 := by
  simp [N_k_int]

/-- Concrete sanity check at `r₀ = 1`, `k = 1`. -/
example : N_k_int 1 1 = 17 := by
  simp [N_k_int]

/-- **Sublemma D.8 (recurrence).** The algebraic numerator satisfies the
exact integer recurrence `N_{k+1} = 3 N_k + 5 · 2^k`. This is the
foundational identity from Appendix D.0 / D.8. -/
theorem N_k_int_recurrence (r₀ : ℤ) (k : ℕ) :
    N_k_int r₀ (k + 1) = 3 * N_k_int r₀ k + 5 * (2 : ℤ) ^ k := by
  unfold N_k_int
  have h3 : (3 : ℤ) ^ (k + 1 + 1) = 3 * 3 ^ (k + 1) := by
    rw [pow_succ]; ring
  have h2 : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by
    rw [pow_succ]; ring
  rw [h3, h2]; ring

/-- Auxiliary integer inequality: for every natural `k`, `5 · 2^k < 9 · 3^k`.
This is the slack used to keep `N_k_int r₀ k` strictly positive when
`r₀ ≥ 1`. -/
lemma five_pow_two_lt_nine_pow_three_int (k : ℕ) :
    (5 : ℤ) * 2 ^ k < 9 * 3 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
      have h2 : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have h3 : (3 : ℤ) ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ]; ring
      have h2pos : (0 : ℤ) ≤ 2 ^ k := by positivity
      have h3pos : (0 : ℤ) ≤ 3 ^ k := by positivity
      calc
        (5 : ℤ) * 2 ^ (k + 1)
            = 2 * (5 * 2 ^ k) := by rw [h2]; ring
        _ < 2 * (9 * 3 ^ k) := by
              have h2pos' : (0 : ℤ) < 2 := by norm_num
              exact (mul_lt_mul_iff_of_pos_left h2pos').2 ih
        _ ≤ 3 * (9 * 3 ^ k) := by
              have : (2 : ℤ) * (9 * 3 ^ k) ≤ 3 * (9 * 3 ^ k) := by
                have h9pos : (0 : ℤ) ≤ 9 * 3 ^ k := by positivity
                nlinarith [h9pos]
              exact this
        _ = 9 * 3 ^ (k + 1) := by rw [h3]; ring

/-- **Strict positivity.** For any starting odd value `r₀ ≥ 1` (in `ℤ`),
the affine numerator stays strictly positive at every index `k`. The
proof bounds `3^(k+1) (r₀+2) ≥ 9 · 3^k > 5 · 2^k`. -/
theorem N_k_int_pos (r₀ : ℤ) (hr : 1 ≤ r₀) (k : ℕ) :
    0 < N_k_int r₀ k := by
  unfold N_k_int
  have hr2 : (3 : ℤ) ≤ r₀ + 2 := by linarith
  have h3pow_pos : (0 : ℤ) < 3 ^ k := by positivity
  have hslack : (5 : ℤ) * 2 ^ k < 9 * 3 ^ k :=
    five_pow_two_lt_nine_pow_three_int k
  have hexp : (3 : ℤ) ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ]; ring
  have hlower : (9 : ℤ) * 3 ^ k ≤ 3 ^ (k + 1) * (r₀ + 2) := by
    rw [hexp]
    have : (3 : ℤ) * 3 ^ k * 3 ≤ 3 * 3 ^ k * (r₀ + 2) := by
      have h3kpos : (0 : ℤ) ≤ 3 * 3 ^ k := by positivity
      exact mul_le_mul_of_nonneg_left hr2 h3kpos
    linarith [this]
  linarith [hslack, hlower]

/-- The natural number underlying `N_k_int r₀ k` for `r₀ ≥ 1`. This is the
quantity on which `d_k`, `M_k` and the rest of Appendix D's bookkeeping
will eventually be defined in subsequent sessions. -/
noncomputable def N_k_nat (r₀ : ℤ) (k : ℕ) : ℕ := (N_k_int r₀ k).toNat

lemma N_k_nat_eq (r₀ : ℤ) (hr : 1 ≤ r₀) (k : ℕ) :
    (N_k_nat r₀ k : ℤ) = N_k_int r₀ k := by
  have hpos := (N_k_int_pos r₀ hr k).le
  simp [N_k_nat, Int.toNat_of_nonneg hpos]

/-- Strict positivity at the natural-number level. -/
lemma N_k_nat_pos (r₀ : ℤ) (hr : 1 ≤ r₀) (k : ℕ) : 0 < N_k_nat r₀ k := by
  have h : 0 < N_k_int r₀ k := N_k_int_pos r₀ hr k
  have heq : ((N_k_nat r₀ k : ℕ) : ℤ) = N_k_int r₀ k := N_k_nat_eq r₀ hr k
  have : (0 : ℤ) < (N_k_nat r₀ k : ℤ) := by rw [heq]; exact h
  exact_mod_cast this

lemma N_k_nat_ne_zero (r₀ : ℤ) (hr : 1 ≤ r₀) (k : ℕ) : N_k_nat r₀ k ≠ 0 :=
  (N_k_nat_pos r₀ hr k).ne'

/-- **Sublemma D.8 — recurrence at the natural-number level.** Lifts
`N_k_int_recurrence` through `Int.toNat`, using strict positivity. -/
lemma N_k_nat_recurrence (r₀ : ℤ) (hr : 1 ≤ r₀) (k : ℕ) :
    N_k_nat r₀ (k + 1) = 3 * N_k_nat r₀ k + 5 * 2 ^ k := by
  have hint : N_k_int r₀ (k + 1) = 3 * N_k_int r₀ k + 5 * (2 : ℤ) ^ k :=
    N_k_int_recurrence r₀ k
  have eL : ((N_k_nat r₀ (k + 1) : ℕ) : ℤ) = N_k_int r₀ (k + 1) :=
    N_k_nat_eq r₀ hr (k + 1)
  have eR : ((N_k_nat r₀ k : ℕ) : ℤ) = N_k_int r₀ k :=
    N_k_nat_eq r₀ hr k
  have hcast : ((N_k_nat r₀ (k + 1) : ℕ) : ℤ)
      = ((3 * N_k_nat r₀ k + 5 * 2 ^ k : ℕ) : ℤ) := by
    rw [eL, hint]
    push_cast
    rw [eR]
  exact_mod_cast hcast

/-- The 2-adic valuation `d_k(r₀)` of the affine numerator. For
`r₀ ≥ 1` this is well-defined since `N_k_nat r₀ k > 0`. -/
noncomputable def d_k (r₀ : ℤ) (k : ℕ) : ℕ :=
  (N_k_nat r₀ k).factorization 2

/-- The odd part `M_k(r₀)` of the affine numerator: by definition
`N_k_nat = 2^{d_k} * M_k`. -/
noncomputable def M_k (r₀ : ℤ) (k : ℕ) : ℕ :=
  N_k_nat r₀ k / 2 ^ d_k r₀ k

/-- Decomposition `N_k_nat = 2^{d_k} * M_k`. -/
lemma N_k_nat_decomp (r₀ : ℤ) (k : ℕ) :
    2 ^ d_k r₀ k * M_k r₀ k = N_k_nat r₀ k :=
  Nat.ordProj_mul_ordCompl_eq_self _ 2

/-- The odd part is positive when `r₀ ≥ 1`. -/
lemma M_k_pos (r₀ : ℤ) (hr : 1 ≤ r₀) (k : ℕ) : 0 < M_k r₀ k :=
  Nat.ordCompl_pos 2 (N_k_nat_ne_zero r₀ hr k)

/-- The odd part is genuinely odd. -/
lemma M_k_odd (r₀ : ℤ) (hr : 1 ≤ r₀) (k : ℕ) : Odd (M_k r₀ k) := by
  have hne : N_k_nat r₀ k ≠ 0 := N_k_nat_ne_zero r₀ hr k
  have h2 : ¬ (2 ∣ M_k r₀ k) :=
    Nat.not_dvd_ordCompl Nat.prime_two hne
  rcases Nat.even_or_odd (M_k r₀ k) with he | ho
  · exact absurd (even_iff_two_dvd.mp he) h2
  · exact ho

/-- Helper: factorization of `2^d * m` at prime 2 when `m` is odd
and positive. -/
lemma factorization_two_of_pow_mul_odd (d : ℕ) {m : ℕ}
    (hm : 0 < m) (hodd : Odd m) :
    (2 ^ d * m).factorization 2 = d := by
  have hm0 : m ≠ 0 := hm.ne'
  have hpd : (2 ^ d : ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Nat.factorization_mul hpd hm0, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (Odd.not_two_dvd_nat hodd),
      Nat.add_zero]

/-- **Sublemma D.8, case `d_k < k` (sub-diagonal).** The 2-adic
valuation is preserved by the recurrence:

  `d_{k+1} = d_k`  whenever `d_k < k`.

Algebraically: `N_{k+1} = 2^{d_k} (3 M_k + 5 · 2^{k - d_k})` and the
inner factor is odd because `3 M_k` is odd and `5 · 2^{k-d_k}` is
even (using `k - d_k ≥ 1`). -/
theorem d_k_succ_of_lt (r₀ : ℤ) (hr : 1 ≤ r₀) {k : ℕ}
    (h : d_k r₀ k < k) :
    d_k r₀ (k + 1) = d_k r₀ k := by
  set d := d_k r₀ k with hd_def
  set M := M_k r₀ k with hM_def
  have hMod : Odd M := M_k_odd r₀ hr k
  have hMpos : 0 < M := M_k_pos r₀ hr k
  have hdec : 2 ^ d * M = N_k_nat r₀ k := N_k_nat_decomp r₀ k
  have hrec : N_k_nat r₀ (k + 1) = 3 * N_k_nat r₀ k + 5 * 2 ^ k :=
    N_k_nat_recurrence r₀ hr k
  have hkd : d ≤ k := h.le
  have hpow_split : (2 : ℕ) ^ k = 2 ^ d * 2 ^ (k - d) := by
    rw [← pow_add, Nat.add_sub_of_le hkd]
  have hsplit : N_k_nat r₀ (k + 1) = 2 ^ d * (3 * M + 5 * 2 ^ (k - d)) := by
    rw [hrec, ← hdec, hpow_split]; ring
  have hgt : 0 < k - d := Nat.sub_pos_of_lt h
  have h2_even : Even ((2 : ℕ) ^ (k - d)) := by
    rw [Nat.even_pow]
    exact ⟨even_two, hgt.ne'⟩
  have hMul_even : Even (5 * 2 ^ (k - d)) := h2_even.mul_left 5
  have h3M_odd : Odd (3 * M) := Odd.mul (by decide : Odd 3) hMod
  have hodd_sum : Odd (3 * M + 5 * 2 ^ (k - d)) :=
    Odd.add_even h3M_odd hMul_even
  have hpos_sum : 0 < 3 * M + 5 * 2 ^ (k - d) := by
    have : 0 < 3 * M := by positivity
    omega
  show (N_k_nat r₀ (k + 1)).factorization 2 = d
  rw [hsplit]
  exact factorization_two_of_pow_mul_odd d hpos_sum hodd_sum

/-- **Sublemma D.8, case `d_k > k` (super-diagonal).** The next
2-adic valuation lands exactly at the diagonal index `k`:

  `d_{k+1} = k`  whenever `k < d_k`.

Algebraically: `N_{k+1} = 2^k (3 · 2^{d_k - k} M_k + 5)` and the
inner factor is odd because `3 · 2^{d_k - k} M_k` is even and `5`
is odd. -/
theorem d_k_succ_of_gt (r₀ : ℤ) (hr : 1 ≤ r₀) {k : ℕ}
    (h : k < d_k r₀ k) :
    d_k r₀ (k + 1) = k := by
  set d := d_k r₀ k with hd_def
  set M := M_k r₀ k with hM_def
  have hMod : Odd M := M_k_odd r₀ hr k
  have hMpos : 0 < M := M_k_pos r₀ hr k
  have hdec : 2 ^ d * M = N_k_nat r₀ k := N_k_nat_decomp r₀ k
  have hrec : N_k_nat r₀ (k + 1) = 3 * N_k_nat r₀ k + 5 * 2 ^ k :=
    N_k_nat_recurrence r₀ hr k
  have hkd : k ≤ d := h.le
  have hpow_split : (2 : ℕ) ^ d = 2 ^ k * 2 ^ (d - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkd]
  have hsplit : N_k_nat r₀ (k + 1) = 2 ^ k * (3 * 2 ^ (d - k) * M + 5) := by
    rw [hrec, ← hdec, hpow_split]; ring
  have hgt : 0 < d - k := Nat.sub_pos_of_lt h
  have h2_even : Even ((2 : ℕ) ^ (d - k)) := by
    rw [Nat.even_pow]
    exact ⟨even_two, hgt.ne'⟩
  have h3pow_even : Even (3 * 2 ^ (d - k) * M) :=
    (h2_even.mul_left 3).mul_right M
  have h5_odd : Odd 5 := by decide
  have hodd_sum : Odd (3 * 2 ^ (d - k) * M + 5) := by
    rw [Nat.add_comm]
    exact Odd.add_even h5_odd h3pow_even
  have hpos_sum : 0 < 3 * 2 ^ (d - k) * M + 5 := by positivity
  show (N_k_nat r₀ (k + 1)).factorization 2 = k
  rw [hsplit]
  exact factorization_two_of_pow_mul_odd k hpos_sum hodd_sum

/-- **Sublemma D.8, diagonal case `d_k = k`.** The next 2-adic
valuation jumps by the `+5`-shift contribution:

  `d_{k+1} = k + ν₂(3 M_k + 5)`.

Algebraically: `N_{k+1} = 2^k (3 M_k + 5)`, and the residual jump
is read off via `factorization_mul`. -/
theorem d_k_succ_of_eq (r₀ : ℤ) (hr : 1 ≤ r₀) {k : ℕ}
    (h : d_k r₀ k = k) :
    d_k r₀ (k + 1) = k + (3 * M_k r₀ k + 5).factorization 2 := by
  set M := M_k r₀ k with hM_def
  have hMod : Odd M := M_k_odd r₀ hr k
  have hMpos : 0 < M := M_k_pos r₀ hr k
  have hdec : 2 ^ d_k r₀ k * M = N_k_nat r₀ k := N_k_nat_decomp r₀ k
  rw [h] at hdec
  have hrec : N_k_nat r₀ (k + 1) = 3 * N_k_nat r₀ k + 5 * 2 ^ k :=
    N_k_nat_recurrence r₀ hr k
  have hsplit : N_k_nat r₀ (k + 1) = 2 ^ k * (3 * M + 5) := by
    rw [hrec, ← hdec]; ring
  have hpos_sum : 0 < 3 * M + 5 := by positivity
  have hpk : ((2 : ℕ) ^ k : ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
  show (N_k_nat r₀ (k + 1)).factorization 2
      = k + (3 * M + 5).factorization 2
  rw [hsplit, Nat.factorization_mul hpk hpos_sum.ne',
      Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two]

/-- **Lemma D.1 Part A — `+5` shift formula at the orbit (`M`) level.**
On the diagonal `d_k = k`, the next normalized odd part satisfies the
canonical `+5` recurrence

  `M_{k+1} = (3 M_k + 5) / 2^{ν₂(3 M_k + 5)}`,

i.e. it is the odd part of `3 M_k + 5`. This is the precise
formulation used as input to the touch-residue lemma (Part B). -/
theorem M_k_succ_of_eq (r₀ : ℤ) (hr : 1 ≤ r₀) {k : ℕ}
    (h : d_k r₀ k = k) :
    M_k r₀ (k + 1)
      = (3 * M_k r₀ k + 5) / 2 ^ (3 * M_k r₀ k + 5).factorization 2 := by
  set M := M_k r₀ k with hM_def
  set e := (3 * M + 5).factorization 2 with he_def
  have hMod : Odd M := M_k_odd r₀ hr k
  have hMpos : 0 < M := M_k_pos r₀ hr k
  have hpos_sum : 0 < 3 * M + 5 := by positivity
  have hdec_k : 2 ^ d_k r₀ k * M = N_k_nat r₀ k := N_k_nat_decomp r₀ k
  rw [h] at hdec_k
  have hrec : N_k_nat r₀ (k + 1) = 3 * N_k_nat r₀ k + 5 * 2 ^ k :=
    N_k_nat_recurrence r₀ hr k
  have hN1 : N_k_nat r₀ (k + 1) = 2 ^ k * (3 * M + 5) := by
    rw [hrec, ← hdec_k]; ring
  have hd1 : d_k r₀ (k + 1) = k + e := d_k_succ_of_eq r₀ hr h
  have hdec_k1 : 2 ^ d_k r₀ (k + 1) * M_k r₀ (k + 1) = N_k_nat r₀ (k + 1) :=
    N_k_nat_decomp r₀ (k + 1)
  rw [hd1, pow_add, hN1] at hdec_k1
  have hp2k : (0 : ℕ) < 2 ^ k := by positivity
  have hp2e_pos : (0 : ℕ) < 2 ^ e := by positivity
  have heq : 2 ^ k * (2 ^ e * M_k r₀ (k + 1)) = 2 ^ k * (3 * M + 5) := by
    rw [← mul_assoc]; exact hdec_k1
  have hcancel : 2 ^ e * M_k r₀ (k + 1) = 3 * M + 5 :=
    Nat.eq_of_mul_eq_mul_left hp2k heq
  rw [show (3 * M + 5) = 2 ^ e * M_k r₀ (k + 1) from hcancel.symm,
      Nat.mul_div_cancel_left _ hp2e_pos]

/-! ### Lemma D.1 Part B — Touch residue

The condition `ν₂(3 M_k + 5) ≥ t`, i.e. `2^t ∣ 3 M_k + 5`, depends only
on the residue class of `M_k` modulo `2^t`. Moreover, for every level
`t` there is a unique solution residue `s_t < 2^t` (constructed by
Hensel lifting). -/

/-- **Lemma D.1 Part B — equivalence form.** The 2-adic touch
condition `2^t ∣ 3 M + 5` depends only on `M mod 2^t`. -/
theorem touch_residue_iff_modEq (t : ℕ) {M M' : ℕ}
    (h : M ≡ M' [MOD 2 ^ t]) :
    (2 ^ t ∣ 3 * M + 5) ↔ (2 ^ t ∣ 3 * M' + 5) := by
  have h3 : 3 * M ≡ 3 * M' [MOD 2 ^ t] := h.mul_left 3
  have h5 : 3 * M + 5 ≡ 3 * M' + 5 [MOD 2 ^ t] := h3.add_right 5
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨h5.symm.trans, h5.trans⟩

/-- **Lemma D.1 Part B — existence (Hensel lifting).** For every level
`t`, there exists a residue `s < 2^t` such that `2^t ∣ 3 s + 5`.

This is the canonical "touch residue": every `M ≡ s (mod 2^t)`
triggers a length-`t` touch, and conversely every touch lies in this
residue class (by `touch_residue_iff_modEq`). -/
theorem exists_touch_residue (t : ℕ) :
    ∃ s : ℕ, s < 2 ^ t ∧ 2 ^ t ∣ (3 * s + 5) := by
  induction t with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ t ih =>
      obtain ⟨s, hslt, c, hc⟩ := ih
      have hpow_succ : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by
        rw [pow_succ]; ring
      have hslt' : s < 2 ^ (t + 1) := by
        rw [hpow_succ]; omega
      rcases Nat.even_or_odd c with hcE | hcO
      · -- `c` even: `s` already lifts.
        obtain ⟨c', hc'⟩ := hcE
        refine ⟨s, hslt', c', ?_⟩
        rw [hpow_succ, hc, hc']; ring
      · -- `c` odd: shift by `2^t`.
        obtain ⟨c', hc'⟩ := hcO
        refine ⟨s + 2 ^ t, ?_, c' + 2, ?_⟩
        · rw [hpow_succ]; omega
        · have hexpand : 3 * (s + 2 ^ t) + 5 = (c + 3) * 2 ^ t := by
            have hsum : 3 * s + 5 + 3 * 2 ^ t = (c + 3) * 2 ^ t := by
              rw [hc]; ring
            linarith [hsum]
          rw [hexpand, hc', hpow_succ]; ring

/-! ### Sublemma D.10 — algebraic carry brick (Wave 2A substep E.2)

Paper Sublemma D.10 (`appendices/pdf-content/D-leverage.md` L466–L472) states that
on a plateau of the minimal term in `S_k`, for any fixed `t ≥ 1`,
`M_{k+1} ≡ 3 M_k + c_k (mod 2^t)` with `c_k := 5 · 2^{k - d_k} (mod 2^t)`,
periodic of period dividing `2^{t-2}`.

The paper proof reduces `N_{k+1} = 2^{d_k} (3 M_k + 5 · 2^{k - d_k})` modulo
`2^{d_k + t}` and divides by `2^{d_k}`, valid for `d_k ≤ k`. On the algebraic
side this splits cleanly into two cases:

* `d_k < k` (sub-diagonal): the inner factor `3 M_k + 5 · 2^{k - d_k}` is
  already odd, so it *equals* `M_{k+1}` exactly, and the `Int.ModEq` form
  follows trivially.
* `d_k > k` (super-diagonal): the analogous inner factor `3 · 2^{d_k-k} M_k + 5`
  is odd and equals `M_{k+1}` exactly.

The diagonal case `d_k = k` is handled by `M_k_succ_of_eq` above and
*does not* admit a simple linear-with-carry `Int.ModEq` form — it carries
the `+5`-shift jump captured separately by `d_k_succ_of_eq`.

Periodicity of the carry `(c_k)` and the orbit-side connection (plateau
of the minimal term in `S_k`) are *not* part of this brick: they require
plateau control that the algebraic numerator alone does not see.
-/

/-- **Sublemma D.10 (sub-diagonal branch, exact form).** When the
2-adic valuation lags behind the index (`d_k r₀ k < k`), the next
normalized odd part satisfies the **exact** linear-with-carry equality

  `M_{k+1} = 3 M_k + 5 · 2^{k - d_k}`

at the natural-number level, with carry `c_k := 5 · 2^{k - d_k}` reading
off the slack between `k` and `d_k`. -/
theorem M_k_succ_of_lt (r₀ : ℤ) (hr : 1 ≤ r₀) {k : ℕ}
    (h : d_k r₀ k < k) :
    M_k r₀ (k + 1) = 3 * M_k r₀ k + 5 * 2 ^ (k - d_k r₀ k) := by
  set d := d_k r₀ k with hd_def
  set M := M_k r₀ k with hM_def
  have hdec : 2 ^ d * M = N_k_nat r₀ k := N_k_nat_decomp r₀ k
  have hrec : N_k_nat r₀ (k + 1) = 3 * N_k_nat r₀ k + 5 * 2 ^ k :=
    N_k_nat_recurrence r₀ hr k
  have hkd : d ≤ k := h.le
  have hpow_split : (2 : ℕ) ^ k = 2 ^ d * 2 ^ (k - d) := by
    rw [← pow_add, Nat.add_sub_of_le hkd]
  have hsplit : N_k_nat r₀ (k + 1) = 2 ^ d * (3 * M + 5 * 2 ^ (k - d)) := by
    rw [hrec, ← hdec, hpow_split]; ring
  have hd1 : d_k r₀ (k + 1) = d := d_k_succ_of_lt r₀ hr h
  have hdec_k1 : 2 ^ d_k r₀ (k + 1) * M_k r₀ (k + 1) = N_k_nat r₀ (k + 1) :=
    N_k_nat_decomp r₀ (k + 1)
  rw [hd1, hsplit] at hdec_k1
  have hp2d : (0 : ℕ) < 2 ^ d := by positivity
  exact Nat.eq_of_mul_eq_mul_left hp2d hdec_k1

/-- **Sublemma D.10 (super-diagonal branch, exact form).** When the
2-adic valuation is ahead of the index (`k < d_k r₀ k`), the next
normalized odd part satisfies the **exact** equality

  `M_{k+1} = 3 · 2^{d_k - k} · M_k + 5`

at the natural-number level. Here the leading term is even and the
constant `5` is odd, so the sum is odd as required. -/
theorem M_k_succ_of_gt (r₀ : ℤ) (hr : 1 ≤ r₀) {k : ℕ}
    (h : k < d_k r₀ k) :
    M_k r₀ (k + 1) = 3 * 2 ^ (d_k r₀ k - k) * M_k r₀ k + 5 := by
  set d := d_k r₀ k with hd_def
  set M := M_k r₀ k with hM_def
  have hdec : 2 ^ d * M = N_k_nat r₀ k := N_k_nat_decomp r₀ k
  have hrec : N_k_nat r₀ (k + 1) = 3 * N_k_nat r₀ k + 5 * 2 ^ k :=
    N_k_nat_recurrence r₀ hr k
  have hkd : k ≤ d := h.le
  have hpow_split : (2 : ℕ) ^ d = 2 ^ k * 2 ^ (d - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkd]
  have hsplit : N_k_nat r₀ (k + 1) = 2 ^ k * (3 * 2 ^ (d - k) * M + 5) := by
    rw [hrec, ← hdec, hpow_split]; ring
  have hd1 : d_k r₀ (k + 1) = k := d_k_succ_of_gt r₀ hr h
  have hdec_k1 : 2 ^ d_k r₀ (k + 1) * M_k r₀ (k + 1) = N_k_nat r₀ (k + 1) :=
    N_k_nat_decomp r₀ (k + 1)
  rw [hd1, hsplit] at hdec_k1
  have hp2k : (0 : ℕ) < 2 ^ k := by positivity
  exact Nat.eq_of_mul_eq_mul_left hp2k hdec_k1

/-- **Sublemma D.10 — algebraic `Int.ModEq` carry brick (sub-diagonal
branch).** Lifting `M_k_succ_of_lt` to integer congruences: at every
level `t ≥ 0`,

  `M_{k+1} ≡ 3 M_k + 5 · 2^{k - d_k}  (mod 2^t)`,

i.e. the next odd part agrees with `3 M_k` plus the algebraic carry
`c_k := 5 · 2^{k - d_k}` modulo `2^t`. This is the Lean-formalized
honest leaf of paper Sublemma D.10 on the sub-diagonal branch.

Periodicity of `(c_k)` and the orbit-side plateau hypothesis remain
open as separate bricks; this theorem captures the algebraic recurrence
form only. -/
theorem M_k_ModEq_succ_of_lt (r₀ : ℤ) (hr : 1 ≤ r₀) {k t : ℕ}
    (h : d_k r₀ k < k) :
    ((M_k r₀ (k + 1) : ℤ))
      ≡ 3 * (M_k r₀ k : ℤ) + 5 * (2 : ℤ) ^ (k - d_k r₀ k)
        [ZMOD ((2 : ℤ) ^ t)] := by
  have heq : M_k r₀ (k + 1) = 3 * M_k r₀ k + 5 * 2 ^ (k - d_k r₀ k) :=
    M_k_succ_of_lt r₀ hr h
  have hcast : ((M_k r₀ (k + 1) : ℤ))
      = 3 * (M_k r₀ k : ℤ) + 5 * (2 : ℤ) ^ (k - d_k r₀ k) := by
    exact_mod_cast heq
  rw [hcast]

end Collatz.SEDT.AffineNumerator
