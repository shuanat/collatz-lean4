/-
Collatz Conjecture: paper Definition F.0.1 (revised) ⇒ late-window touchCount = 1
**(Wave 2F bridge).**

This module realises the elementary algebraic bridge derived in Wave 2D
`collatz-verification/research/wave2-d10b-empirical/REPORT-reverse-engineering.md`
§2: under the **revised** paper Definition F.0.1 admissibility predicate
`Collatz.Mixing.AdmissibleTailF01 t Mentry v` (Wave 2E), the count of late-regime
window touches over the canonical period `Q_t t = 2^(t-2)` equals exactly `1`.

Concretely, given the per-plateau-anchored algebraic data
`(Mentry, v : ZMod (2^t))` and the admissibility witness
`∃ n, s_t = 3^n · (v + 3^t · Mentry)`, the equation

    3^j · (v + 3^t · Mentry) = s_t   in `ZMod (2^t)`

has **exactly one** solution `j ∈ [0, Q_t t)`. The proof is the elementary
§2 algebra:

* `s_t` is a unit in `ZMod (2^t)` (`Collatz.OrdFact.isUnit_natCast_s_t`,
  since `s_t = -5 · 3⁻¹` and both `-5` and `3⁻¹` are units modulo `2^t`).
* Hence `v + 3^t · Mentry` is a unit (`isUnit_of_mul_isUnit_right` applied
  to the admissibility equation).
* Therefore `3^j · w = 3^n · w ⇒ 3^j = 3^n` (via `IsUnit.mul_right_cancel`
  on the right factor `w`).
* Since `orderOf (3 : ZMod (2^t)) = Q_t t` (paper Lemma B.2,
  `Collatz.OrdFact.orderOf_three_eq_pow_two`), the map `j ↦ 3^j` is
  injective on `[0, Q_t t)` (`pow_injOn_Iio_orderOf`).
* The unique solution is the witness `n` provided by
  `AdmissibleTailF01_witness_lt_Qt`, hence the filter equals `{n}` and its
  cardinality is `1`.

This is the **algebraic-core biconditional** (admissibility ⇒ touchCount = 1)
on the algebraic data `(Mentry, v)`. The remaining orbit-side bridge — tying
`Mentry := M 0 - u 0` and `v := u t` from `LocalAffinePairSemantics` and
deriving `one_touch_per_period_input` from `admissible` — additionally requires
encoding the late-regime `c_k = 0 (k ≥ t)` flush guard; that is queued as a
separate orbit-side residual (`R-OrbitSideAdmissibleDensity`) and not closed
in this module.

No `sorry`, no `axiom`, no proxy. Every theorem below is intended to be
axiom-clean (`#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`).
-/

import Mathlib.Tactic
import Mathlib.GroupTheory.OrderOfElement
import Collatz.Epochs.Core
import Collatz.Epochs.OrdFact
import Collatz.Mixing.AdmissibleTail
import Collatz.Mixing.TouchFrequencyLocal
import Collatz.SEDT.Homogenization
import Collatz.SEDT.TouchDensity

namespace Collatz.Mixing

open Collatz.Epochs

/-- **Wave 2F bridge — admissibility ⇒ exactly 1 touch in the late-regime
window.**

Given the per-plateau algebraic data `(Mentry, v : ZMod (2^t))` (paper
notation: `Mentry := M_{k_start} mod 2^t`, `v := u_{k_start + t} mod 2^t`)
and the revised Wave 2D paper Definition F.0.1 admissibility predicate
`AdmissibleTailF01 t Mentry v`, the touch count over the canonical period
`Q_t t = 2^(t-2)` equals exactly `1`. The proof is the elementary algebra
of `wave2-d10b-empirical/REPORT-reverse-engineering.md` §2:

    M_{k_start + t + j} ≡ 3^j · (v + 3^t · Mentry)  (mod 2^t),

so a touch at offset `j` is `3^j · (v + 3^t · Mentry) = s_t`, which has
exactly one `j ∈ [0, Q_t t)` because `3` has order `Q_t t = 2^(t-2)` in
`(ZMod (2^t))ˣ` (paper Lemma B.2). -/
theorem AdmissibleTailF01.touch_count_eq_one {t : ℕ} (ht : 3 ≤ t)
    {Mentry v : ZMod (2 ^ t)}
    (hadm : AdmissibleTailF01 t Mentry v) :
    ((Finset.range (Q_t t)).filter
        (fun j => (3 : ZMod (2 ^ t)) ^ j *
                    (v + (3 : ZMod (2 ^ t)) ^ t * Mentry)
                  = ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t)))).card = 1 := by
  obtain ⟨n, hn_lt_Q, hn_eq⟩ := AdmissibleTailF01_witness_lt_Qt ht hadm
  have hu_s : IsUnit ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t)) :=
    Collatz.OrdFact.isUnit_natCast_s_t (by omega : 2 ≤ t)
  have hu_w : IsUnit (v + (3 : ZMod (2 ^ t)) ^ t * Mentry) := by
    have hu_prod :
        IsUnit ((3 : ZMod (2 ^ t)) ^ n *
          (v + (3 : ZMod (2 ^ t)) ^ t * Mentry)) := by
      rw [← hn_eq]; exact hu_s
    exact isUnit_of_mul_isUnit_right hu_prod
  have horder : orderOf (3 : ZMod (2 ^ t)) = Q_t t := by
    show orderOf (3 : ZMod (2 ^ t)) = 2 ^ (t - 2)
    exact Collatz.OrdFact.orderOf_three_eq_pow_two ht
  have hfilter :
      (Finset.range (Q_t t)).filter
        (fun j => (3 : ZMod (2 ^ t)) ^ j *
                    (v + (3 : ZMod (2 ^ t)) ^ t * Mentry)
                  = ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t))) = {n} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hn_lt_Q, hn_eq.symm⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hj_lt, hj_eq⟩ := hj
      have h_eq_w :
          (3 : ZMod (2 ^ t)) ^ j *
              (v + (3 : ZMod (2 ^ t)) ^ t * Mentry) =
            (3 : ZMod (2 ^ t)) ^ n *
              (v + (3 : ZMod (2 ^ t)) ^ t * Mentry) :=
        hj_eq.trans hn_eq
      have h_pow : (3 : ZMod (2 ^ t)) ^ j = (3 : ZMod (2 ^ t)) ^ n :=
        hu_w.mul_right_cancel h_eq_w
      have h_inj :
          (Set.Iio (orderOf (3 : ZMod (2 ^ t)))).InjOn
            ((3 : ZMod (2 ^ t)) ^ ·) := pow_injOn_Iio_orderOf
      have hj_in : j ∈ Set.Iio (orderOf (3 : ZMod (2 ^ t))) := by
        rw [Set.mem_Iio, horder]; exact hj_lt
      have hn_in : n ∈ Set.Iio (orderOf (3 : ZMod (2 ^ t))) := by
        rw [Set.mem_Iio, horder]; exact hn_lt_Q
      exact h_inj hj_in hn_in h_pow
  rw [hfilter, Finset.card_singleton]

/-- **Expanded form of the Wave 2F bridge (paper §2.2 notation).**

The same conclusion as `AdmissibleTailF01.touch_count_eq_one`, but with the
touch indicator written in the un-factored form
`v · 3^j + 3^t · Mentry · 3^j = s_t` matching the paper §2.2 derivation
verbatim. The two filters are pointwise equal because
`v · 3^j + 3^t · Mentry · 3^j = 3^j · (v + 3^t · Mentry)` in any
commutative ring. -/
theorem AdmissibleTailF01.touch_count_eq_one_expanded {t : ℕ} (ht : 3 ≤ t)
    {Mentry v : ZMod (2 ^ t)}
    (hadm : AdmissibleTailF01 t Mentry v) :
    ((Finset.range (Q_t t)).filter
        (fun j => v * (3 : ZMod (2 ^ t)) ^ j
                  + (3 : ZMod (2 ^ t)) ^ t * Mentry * (3 : ZMod (2 ^ t)) ^ j
                  = ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t)))).card = 1 := by
  have hpoint : ∀ j : ℕ,
      (v * (3 : ZMod (2 ^ t)) ^ j
        + (3 : ZMod (2 ^ t)) ^ t * Mentry * (3 : ZMod (2 ^ t)) ^ j) =
      (3 : ZMod (2 ^ t)) ^ j *
        (v + (3 : ZMod (2 ^ t)) ^ t * Mentry) := by
    intro j; ring
  have hfilter_eq :
      (Finset.range (Q_t t)).filter
          (fun j => v * (3 : ZMod (2 ^ t)) ^ j
                    + (3 : ZMod (2 ^ t)) ^ t * Mentry * (3 : ZMod (2 ^ t)) ^ j
                    = ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t))) =
      (Finset.range (Q_t t)).filter
          (fun j => (3 : ZMod (2 ^ t)) ^ j *
                      (v + (3 : ZMod (2 ^ t)) ^ t * Mentry)
                    = ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t))) := by
    apply Finset.filter_congr
    intro j _
    rw [hpoint j]
  rw [hfilter_eq]
  exact AdmissibleTailF01.touch_count_eq_one ht hadm

/-! ## Wave 2G — orbit-faithful local algebraic-stack bridge with flush guard

The lemmas below close the **local** orbit-side direction of the
biconditional `revised F.0.1 ⇔ late-window touchCount = 1`: given the
algebraic data of a `LocalAffinePairSemantics` (paper Lemma D.10.b)
extended with the late-regime flush guard `c_k ≡ 0 (k ≥ t)` and the
natural identifications `Mentry := M 0 - u 0`, `v := u t`, the orbit-side
predicate `selected_segment_tail_touch m t i` has exactly one touch per
canonical `Q_t`-window. This converts `one_touch_per_period_input` from a
free honest input into a *derived* consequence of `admissible` + the
flush guard. The remaining open piece is the orbit-side **density**
target on actual Collatz orbits (`R-OrbitSideAdmissibleDensity`). -/

/-- Bridge between integer modular equality and the corresponding `ZMod`
equation, for a positive natural modulus `m`. -/
private lemma zmod_intCast_eq_iff_int_modEq {m : ℕ} [NeZero m] (a b : ℤ) :
    ((a : ZMod m) = (b : ZMod m)) ↔ a ≡ b [ZMOD (m : ℤ)] := by
  rw [Int.modEq_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero, eq_comm]

/-- **Single-step shift invariance of `touchCount` for periodic predicates.**
For a `P`-periodic decidable predicate `f`, shifting the index by `1`
preserves the touch count over a full period. -/
private lemma touchCount_shift_succ_of_periodic
    {f : ℕ → Prop} [DecidablePred f] (P : ℕ)
    (hper : ∀ k, f (k + P) ↔ f k) (s : ℕ) :
    Collatz.SEDT.TouchDensity.touchCount (fun k => f (s + 1 + k)) P =
      Collatz.SEDT.TouchDensity.touchCount (fun k => f (s + k)) P := by
  rcases P with _ | P'
  · simp [Collatz.SEDT.TouchDensity.touchCount]
  · unfold Collatz.SEDT.TouchDensity.touchCount
    rw [Finset.sum_range_succ (fun k => if f (s + 1 + k) then (1 : ℕ) else 0) P',
        Finset.sum_range_succ' (fun k => if f (s + k) then (1 : ℕ) else 0) P']
    have hsumeq :
        ∑ k ∈ Finset.range P', (if f (s + 1 + k) then (1 : ℕ) else 0) =
        ∑ k ∈ Finset.range P', (if f (s + (k + 1)) then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      have heq : s + 1 + k = s + (k + 1) := by ring
      rw [heq]
    rw [hsumeq]
    have hbdy : f (s + 1 + P') ↔ f (s + 0) := by
      have heq : s + 1 + P' = s + (P' + 1) := by ring
      rw [heq, Nat.add_zero]
      exact hper s
    by_cases hf : f (s + 1 + P')
    · rw [if_pos hf, if_pos (hbdy.mp hf)]
    · rw [if_neg hf, if_neg (fun h => hf (hbdy.mpr h))]

/-- **Iterated shift invariance of `touchCount` for periodic predicates.** -/
private lemma touchCount_shift_eq_of_periodic
    {f : ℕ → Prop} [DecidablePred f] (P : ℕ)
    (hper : ∀ k, f (k + P) ↔ f k) (s : ℕ) :
    Collatz.SEDT.TouchDensity.touchCount (fun k => f (s + k)) P =
      Collatz.SEDT.TouchDensity.touchCount f P := by
  induction s with
  | zero =>
    unfold Collatz.SEDT.TouchDensity.touchCount
    apply Finset.sum_congr rfl
    intro k _
    simp only [Nat.zero_add]
  | succ s ih =>
    rw [touchCount_shift_succ_of_periodic P hper s, ih]

/-- **Wave 2G algebraic-stack bridge — orbit-faithful `touchCount = 1` from
admissibility plus the late-regime flush guard.**

Given the local affine pair data `(M, u, c)` on an admissible-tail
window of the Collatz orbit (paper Lemma D.10.b minimal honest interface
plus the **flush guard** `c k ≡ 0 (k ≥ t)` and the natural identifications
`Mentry := M 0 - u 0 (mod 2^t)`, `v := u t (mod 2^t)`), the revised paper
Definition F.0.1 admissibility predicate `AdmissibleTailF01 t Mentry v`
algebraically forces

    Collatz.SEDT.TouchDensity.touchCount
      (selected_segment_tail_touch m t i) (Q_t t) = 1.

Proof outline (Wave 2D §2 algebra applied to the orbit-realised data):

1. `Mtilde k := M k - u k` satisfies `Mtilde (k+1) ≡ 3 * Mtilde k (mod 2^t)`
   by `homogenization_principle`. Hence
   `Mtilde k ≡ 3^k * Mtilde 0 (mod 2^t)` by `homogenized_iterate`.
2. `Q_t`-periodicity of `Mtilde` from `3^(Q_t) ≡ 1 (mod 2^t)` and
   `homogenized_periodic_of_order_dvd`. Combined with `uPeriodic` this gives
   `Q_t`-periodicity of `M`.
3. By `realized` and the cast bridge, `selected_segment_tail_touch m t i`
   is `Q_t`-periodic.
4. From the **flush guard** for `k ≥ t`, `u (k+1) ≡ 3 * u k (mod 2^t)`,
   so `u (t + j) ≡ 3^j * u t (mod 2^t)` by `homogenized_iterate` again.
5. Combining (1) + (4) yields `M (t + j) ≡ 3^j * (u t + 3^t * (M 0 - u 0))
   (mod 2^t)`, which after the identifications `Mentry`, `v` casts to
   `(M (t + j) : ZMod (2^t)) = 3^j * (v + 3^t * Mentry)`.
6. Hence the touch indicator `selected_segment_tail_touch m t i (t + j)`
   is pointwise equivalent to `3^j * (v + 3^t * Mentry) = s_t` in
   `ZMod (2^t)`, and `touchCount_shift_eq_of_periodic` translates the
   touch count over the canonical window `[0, Q_t)` into the count over
   `[t, t + Q_t)`, which equals `1` by
   `AdmissibleTailF01.touch_count_eq_one`. -/
theorem AdmissibleTailF01.touch_count_eq_one_of_realized
    {m t i : ℕ} (ht : 3 ≤ t)
    (M u c : ℕ → ℤ)
    (affineUpdateM : ∀ k, M (k + 1) ≡ 3 * M k + c k [ZMOD ((2 : ℤ) ^ t)])
    (affineUpdateU : ∀ k, u (k + 1) ≡ 3 * u k + c k [ZMOD ((2 : ℤ) ^ t)])
    (uPeriodic : ∀ k, u (k + Collatz.Epochs.Q_t t) ≡ u k [ZMOD ((2 : ℤ) ^ t)])
    (realized : ∀ k,
      ((Collatz.Epochs.selected_segment_value m (i + k) : ℕ) : ℤ) ≡ M k
        [ZMOD ((2 : ℤ) ^ t)])
    (flushGuard : ∀ k, t ≤ k → c k ≡ 0 [ZMOD ((2 : ℤ) ^ t)])
    {Mentry v : ZMod (2 ^ t)}
    (Mentry_eq : Mentry = ((M 0 - u 0 : ℤ) : ZMod (2 ^ t)))
    (v_eq : v = ((u t : ℤ) : ZMod (2 ^ t)))
    (admissible : AdmissibleTailF01 t Mentry v) :
    Collatz.SEDT.TouchDensity.touchCount
      (Collatz.Mixing.selected_segment_tail_touch m t i)
      (Collatz.Epochs.Q_t t) = 1 := by
  set n : ℤ := (2 : ℤ) ^ t with hndef
  have hntpos : (0 : ℕ) < 2 ^ t := pow_pos (by decide) _
  haveI : NeZero ((2 : ℕ) ^ t) := ⟨Nat.pos_iff_ne_zero.mp hntpos⟩
  have hncastNat : ((2 ^ t : ℕ) : ℤ) = n := by
    show ((2 ^ t : ℕ) : ℤ) = (2 : ℤ) ^ t
    push_cast
    rfl
  -- Step A: Mtilde k := M k - u k satisfies Mtilde(k+1) ≡ 3 * Mtilde k.
  let Mtilde : ℕ → ℤ := fun k => M k - u k
  have hMtildeStep : ∀ k, Mtilde (k + 1) ≡ 3 * Mtilde k [ZMOD n] := by
    intro k
    exact Collatz.SEDT.Homogenization.homogenization_principle
      n M u c k (affineUpdateM k) (affineUpdateU k)
  -- Step A': Mtilde m ≡ 3^m * Mtilde 0.
  have hMtildeIter : ∀ m, Mtilde m ≡ 3 ^ m * Mtilde 0 [ZMOD n] := by
    intro m
    have h := Collatz.SEDT.Homogenization.homogenized_iterate
      n Mtilde 0 hMtildeStep m
    simpa using h
  -- Step B: Q_t-periodicity of Mtilde.
  have hord : (3 : ℤ) ^ (Collatz.Epochs.Q_t t) ≡ 1 [ZMOD n] :=
    Collatz.OrdFact.three_pow_Qt_modEq_one ht
  have hMtildePer :
      ∀ k, Mtilde (k + Collatz.Epochs.Q_t t) ≡ Mtilde k [ZMOD n] :=
    Collatz.SEDT.Homogenization.homogenized_periodic_of_order_dvd
      n Mtilde (Collatz.Epochs.Q_t t) hMtildeStep hord
  -- Step C: M-periodicity via Mtilde-periodicity + uPeriodic.
  have hMPer : ∀ k, M (k + Collatz.Epochs.Q_t t) ≡ M k [ZMOD n] := by
    intro k
    have hMt := hMtildePer k
    have hu : u (k + Collatz.Epochs.Q_t t) ≡ u k [ZMOD n] := uPeriodic k
    have hsum :
        Mtilde (k + Collatz.Epochs.Q_t t) + u (k + Collatz.Epochs.Q_t t) ≡
          Mtilde k + u k [ZMOD n] := hMt.add hu
    have heqL : Mtilde (k + Collatz.Epochs.Q_t t) + u (k + Collatz.Epochs.Q_t t)
                  = M (k + Collatz.Epochs.Q_t t) := by simp [Mtilde]
    have heqR : Mtilde k + u k = M k := by simp [Mtilde]
    rw [heqL, heqR] at hsum
    exact hsum
  -- Step C': Q_t-periodicity of selected_segment_tail_touch.
  have hPredPer :
      ∀ k, Collatz.Mixing.selected_segment_tail_touch m t i
              (k + Collatz.Epochs.Q_t t) ↔
            Collatz.Mixing.selected_segment_tail_touch m t i k := by
    intro k
    have hRk : ((Collatz.Epochs.selected_segment_value m (i + k) : ℕ) : ℤ) ≡
                  M k [ZMOD n] := realized k
    have hRkQ :
        ((Collatz.Epochs.selected_segment_value m
            (i + (k + Collatz.Epochs.Q_t t)) : ℕ) : ℤ) ≡
              M (k + Collatz.Epochs.Q_t t) [ZMOD n] :=
      realized (k + Collatz.Epochs.Q_t t)
    have hint :
        ((Collatz.Epochs.selected_segment_value m
            (i + (k + Collatz.Epochs.Q_t t)) : ℕ) : ℤ) ≡
          ((Collatz.Epochs.selected_segment_value m (i + k) : ℕ) : ℤ)
            [ZMOD n] :=
      (hRkQ.trans (hMPer k)).trans hRk.symm
    have hintNat :
        ((Collatz.Epochs.selected_segment_value m
            (i + (k + Collatz.Epochs.Q_t t)) : ℕ) : ℤ) ≡
          ((Collatz.Epochs.selected_segment_value m (i + k) : ℕ) : ℤ)
            [ZMOD ((2 ^ t : ℕ) : ℤ)] := by
      rw [hncastNat]; exact hint
    have hNat :
        Collatz.Epochs.selected_segment_value m
            (i + (k + Collatz.Epochs.Q_t t)) ≡
          Collatz.Epochs.selected_segment_value m (i + k) [MOD 2 ^ t] := by
      exact_mod_cast hintNat
    have hmod :
        Collatz.Epochs.selected_segment_value m
            (i + (k + Collatz.Epochs.Q_t t)) % 2 ^ t =
          Collatz.Epochs.selected_segment_value m (i + k) % 2 ^ t := hNat
    constructor
    · intro hk
      show Collatz.Epochs.selected_segment_t_touch m (i + k) t
      have hkres :
          Collatz.Epochs.selected_segment_value m
              (i + (k + Collatz.Epochs.Q_t t)) % 2 ^ t =
            Collatz.Epochs.s_t t := hk
      rw [hmod] at hkres
      exact hkres
    · intro hk
      show Collatz.Epochs.selected_segment_t_touch m
        (i + (k + Collatz.Epochs.Q_t t)) t
      have hkres :
          Collatz.Epochs.selected_segment_value m (i + k) % 2 ^ t =
            Collatz.Epochs.s_t t := hk
      rw [← hmod] at hkres
      exact hkres
  -- Step D: late-regime u iteration `u (t + j) ≡ 3^j * u t [ZMOD n]`.
  have huLateIter : ∀ j, u (t + j) ≡ 3 ^ j * u t [ZMOD n] := by
    intro j
    have hu'Step : ∀ k, (fun k => u (t + k)) (k + 1) ≡
                          3 * (fun k => u (t + k)) k [ZMOD n] := by
      intro k
      show u (t + (k + 1)) ≡ 3 * u (t + k) [ZMOD n]
      have hidx : t + (k + 1) = t + k + 1 := by ring
      rw [hidx]
      have hAffU : u (t + k + 1) ≡ 3 * u (t + k) + c (t + k) [ZMOD n] :=
        affineUpdateU (t + k)
      have hcZero : c (t + k) ≡ 0 [ZMOD n] :=
        flushGuard (t + k) (Nat.le_add_right t k)
      have hRHS : 3 * u (t + k) + c (t + k) ≡ 3 * u (t + k) + 0 [ZMOD n] :=
        (Int.ModEq.refl _).add hcZero
      have hAffU' : u (t + k + 1) ≡ 3 * u (t + k) + 0 [ZMOD n] :=
        hAffU.trans hRHS
      have hadd0 : (3 : ℤ) * u (t + k) + 0 = 3 * u (t + k) := by ring
      rw [hadd0] at hAffU'
      exact hAffU'
    have hu'Iter := Collatz.SEDT.Homogenization.homogenized_iterate
      n (fun k => u (t + k)) 0 hu'Step j
    -- hu'Iter : (fun k => u (t + k)) (0 + j) ≡ 3^j * (fun k => u (t + k)) 0
    show u (t + j) ≡ 3 ^ j * u t [ZMOD n]
    simpa using hu'Iter
  -- Step E: late-regime M formula.
  have hMLate : ∀ j,
      M (t + j) ≡ 3 ^ j * (u t + 3 ^ t * (M 0 - u 0)) [ZMOD n] := by
    intro j
    have hMid : M (t + j) = Mtilde (t + j) + u (t + j) := by simp [Mtilde]
    have h1 : Mtilde (t + j) ≡ 3 ^ (t + j) * Mtilde 0 [ZMOD n] :=
      hMtildeIter (t + j)
    have h2 : u (t + j) ≡ 3 ^ j * u t [ZMOD n] := huLateIter j
    have h3 : Mtilde (t + j) + u (t + j) ≡
                3 ^ (t + j) * Mtilde 0 + 3 ^ j * u t [ZMOD n] := h1.add h2
    have hcalc :
        (3 : ℤ) ^ (t + j) * Mtilde 0 + 3 ^ j * u t =
          3 ^ j * (u t + 3 ^ t * Mtilde 0) := by
      have hpw : (3 : ℤ) ^ (t + j) = 3 ^ j * 3 ^ t := by rw [pow_add]; ring
      rw [hpw]; ring
    have hMtilde0 : Mtilde 0 = M 0 - u 0 := by simp [Mtilde]
    rw [hMtilde0] at hcalc
    rw [hcalc] at h3
    rw [hMid]
    exact h3
  -- Step F: ZMod transfer of the late-regime M formula.
  have hMLateZMod : ∀ j,
      ((M (t + j) : ℤ) : ZMod (2 ^ t)) =
        (3 : ZMod (2 ^ t)) ^ j *
          (v + (3 : ZMod (2 ^ t)) ^ t * Mentry) := by
    intro j
    have hModEq := hMLate j
    rw [← hncastNat] at hModEq
    have hZ1 :
        ((M (t + j) : ℤ) : ZMod (2 ^ t)) =
          (((3 : ℤ) ^ j * (u t + 3 ^ t * (M 0 - u 0)) : ℤ) :
            ZMod (2 ^ t)) :=
      (zmod_intCast_eq_iff_int_modEq _ _).mpr hModEq
    rw [hZ1]
    push_cast
    rw [Mentry_eq, v_eq]
    push_cast
    ring
  -- Step G: predicate equivalence at offset `t + j`.
  have hst_lt : Collatz.Epochs.s_t t < 2 ^ t := by
    unfold Collatz.Epochs.s_t
    split_ifs with h
    · exact ZMod.val_lt _
    · exact Nat.two_pow_pos t
  have hPredAt : ∀ j,
      Collatz.Mixing.selected_segment_tail_touch m t i (t + j) ↔
      (3 : ZMod (2 ^ t)) ^ j *
            (v + (3 : ZMod (2 ^ t)) ^ t * Mentry) =
          ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t)) := by
    intro j
    -- Rewrite `selected_segment_tail_touch m t i (t + j)` definitionally.
    show Collatz.Epochs.selected_segment_value m (i + (t + j)) % 2 ^ t =
            Collatz.Epochs.s_t t ↔ _
    -- Bridge `((sv : ℕ) : ZMod (2^t)) = (M (t+j) : ZMod (2^t))` via `realized`.
    have hReal :
        ((Collatz.Epochs.selected_segment_value m (i + (t + j)) : ℕ) : ℤ) ≡
            M (t + j) [ZMOD n] := realized (t + j)
    rw [← hncastNat] at hReal
    have hZ_real :
        (((Collatz.Epochs.selected_segment_value m (i + (t + j)) : ℕ) : ℤ) :
            ZMod (2 ^ t)) =
          ((M (t + j) : ℤ) : ZMod (2 ^ t)) :=
      (zmod_intCast_eq_iff_int_modEq _ _).mpr hReal
    have hbridge :
        ((Collatz.Epochs.selected_segment_value m (i + (t + j)) : ℕ) :
            ZMod (2 ^ t)) =
          (3 : ZMod (2 ^ t)) ^ j *
            (v + (3 : ZMod (2 ^ t)) ^ t * Mentry) := by
      have hZ_real' :
          ((Collatz.Epochs.selected_segment_value m (i + (t + j)) : ℕ) :
              ZMod (2 ^ t)) =
            ((M (t + j) : ℤ) : ZMod (2 ^ t)) := by
        have := hZ_real
        push_cast at this
        exact this
      rw [hZ_real', hMLateZMod j]
    -- Convert `% 2^t = s_t t` to a `ZMod (2^t)` equation, then apply hbridge.
    constructor
    · intro hk
      have hkNat :
          Collatz.Epochs.selected_segment_value m (i + (t + j)) ≡
            Collatz.Epochs.s_t t [MOD 2 ^ t] := by
        unfold Nat.ModEq
        rw [hk, Nat.mod_eq_of_lt hst_lt]
      have hZk :
          ((Collatz.Epochs.selected_segment_value m (i + (t + j)) : ℕ) :
              ZMod (2 ^ t)) =
            ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t)) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hkNat
      rw [hbridge] at hZk
      exact hZk
    · intro hk
      have hZk :
          ((Collatz.Epochs.selected_segment_value m (i + (t + j)) : ℕ) :
              ZMod (2 ^ t)) =
            ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t)) := by
        rw [hbridge]; exact hk
      have hkNat :
          Collatz.Epochs.selected_segment_value m (i + (t + j)) ≡
            Collatz.Epochs.s_t t [MOD 2 ^ t] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp hZk
      have h_eq : Collatz.Epochs.selected_segment_value m (i + (t + j))
                    % 2 ^ t = Collatz.Epochs.s_t t % 2 ^ t := hkNat
      rw [Nat.mod_eq_of_lt hst_lt] at h_eq
      exact h_eq
  -- Step H: shift `touchCount` by `t`, then identify with the bridge filter.
  rw [← touchCount_shift_eq_of_periodic (Collatz.Epochs.Q_t t) hPredPer t]
  unfold Collatz.SEDT.TouchDensity.touchCount
  rw [Finset.sum_boole]
  have hfilter_eq :
      ((Finset.range (Collatz.Epochs.Q_t t)).filter
          (fun k => Collatz.Mixing.selected_segment_tail_touch m t i
                      (t + k))) =
      ((Finset.range (Collatz.Epochs.Q_t t)).filter
          (fun j => (3 : ZMod (2 ^ t)) ^ j *
                      (v + (3 : ZMod (2 ^ t)) ^ t * Mentry) =
                    ((Collatz.Epochs.s_t t : ℕ) : ZMod (2 ^ t)))) := by
    apply Finset.filter_congr
    intro j _
    exact hPredAt j
  rw [hfilter_eq]
  exact_mod_cast AdmissibleTailF01.touch_count_eq_one ht admissible

end Collatz.Mixing
