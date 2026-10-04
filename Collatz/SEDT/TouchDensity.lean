/-
Counting lemmas for periodic predicates (generic).

For a `P`-periodic decidable predicate `f` with `c = touchCount f P`:
`touchCount f (q·P) = q·c` and `(L/P)·c ≤ touchCount f L ≤ (L/P + 1)·c`.

These are correct and generic. In the paper (Lemma D.4) they are applied with
`f k := (M_k ≡ s_t mod 2^t)` for the auxiliary sequence `(M_k)`, which is
eventually `Q_t`-periodic; touches of actual Collatz orbits are **not** known
to be periodic, and no orbit-level touch-density statement is proved here.
-/

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Collatz.SEDT.TouchDensity

open Finset BigOperators

/-- Number of `k < L` satisfying decidable predicate `f`. -/
def touchCount (f : ℕ → Prop) [DecidablePred f] (L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range L, if f k then 1 else 0

@[simp] lemma touchCount_zero (f : ℕ → Prop) [DecidablePred f] :
    touchCount f 0 = 0 := by
  simp [touchCount]

lemma touchCount_succ (f : ℕ → Prop) [DecidablePred f] (L : ℕ) :
    touchCount f (L + 1) = touchCount f L + (if f L then 1 else 0) := by
  unfold touchCount
  rw [Finset.sum_range_succ]

/-- Touch count is monotone in the length. -/
lemma touchCount_mono (f : ℕ → Prop) [DecidablePred f] {a b : ℕ} (h : a ≤ b) :
    touchCount f a ≤ touchCount f b := by
  unfold touchCount
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.sum_range_add]
  exact Nat.le_add_right _ _

/-- Touch count over `[0, n + m)` splits as touch count over `[0, n)`
plus touch count over `[n, n + m)`. -/
lemma touchCount_add (f : ℕ → Prop) [DecidablePred f] (n m : ℕ) :
    touchCount f (n + m) = touchCount f n + ∑ k ∈ Finset.range m, if f (n + k) then 1 else 0 := by
  unfold touchCount
  rw [Finset.sum_range_add]

/-- Iterated periodicity: `f (k + q · P) ↔ f k`. -/
lemma f_periodic_iter (f : ℕ → Prop) (P : ℕ)
    (hper : ∀ k, f (k + P) ↔ f k) (q k : ℕ) :
    f (k + q * P) ↔ f k := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hk : k + (q + 1) * P = (k + q * P) + P := by ring
      rw [hk, hper, ih]

/-- **Touch count over `q · P` blocks.** For a `P`-periodic decidable
predicate, the touch count over `q` consecutive periods equals
`q · c` where `c = touchCount f P`. -/
theorem touchCount_full_blocks
    (f : ℕ → Prop) [DecidablePred f] (P : ℕ)
    (hper : ∀ k, f (k + P) ↔ f k) (q : ℕ) :
    touchCount f (q * P) = q * touchCount f P := by
  induction q with
  | zero => simp
  | succ q ih =>
      have heq : (q + 1) * P = q * P + P := by ring
      rw [heq, touchCount_add, ih]
      have hsum :
          (∑ k ∈ Finset.range P, if f (q * P + k) then 1 else 0)
            = touchCount f P := by
        unfold touchCount
        apply Finset.sum_congr rfl
        intro k _
        have : f (q * P + k) ↔ f k := by
          have heqk : q * P + k = k + q * P := by ring
          rw [heqk]
          exact f_periodic_iter f P hper q k
        simp [this]
      rw [hsum]
      ring

/-- **Touch density lower bound (Lemma D.4 algebraic core).** For a
`P`-periodic predicate, the touch count over `[0, L)` is at least
`(L / P) · c`. -/
theorem touchCount_lower_bound
    (f : ℕ → Prop) [DecidablePred f] (P : ℕ) (hP : 0 < P)
    (hper : ∀ k, f (k + P) ↔ f k) (L : ℕ) :
    (L / P) * touchCount f P ≤ touchCount f L := by
  have hdiv : (L / P) * P ≤ L := Nat.div_mul_le_self L P
  have hblocks : touchCount f ((L / P) * P) = (L / P) * touchCount f P :=
    touchCount_full_blocks f P hper (L / P)
  calc (L / P) * touchCount f P
      = touchCount f ((L / P) * P) := hblocks.symm
    _ ≤ touchCount f L := touchCount_mono f hdiv

/-- **Touch density upper bound (Lemma D.4 algebraic core).** For a
`P`-periodic predicate, the touch count over `[0, L)` is at most
`(L / P + 1) · c`. -/
theorem touchCount_upper_bound
    (f : ℕ → Prop) [DecidablePred f] (P : ℕ) (hP : 0 < P)
    (hper : ∀ k, f (k + P) ↔ f k) (L : ℕ) :
    touchCount f L ≤ (L / P + 1) * touchCount f P := by
  have hLle : L ≤ (L / P + 1) * P := by
    have h1 : L = (L / P) * P + L % P := by
      have h := Nat.div_add_mod L P
      have hcomm : P * (L / P) = (L / P) * P := Nat.mul_comm _ _
      omega
    have h2 : L % P < P := Nat.mod_lt L hP
    calc L = (L / P) * P + L % P := h1
      _ ≤ (L / P) * P + P := by omega
      _ = (L / P + 1) * P := by ring
  have hblocks : touchCount f ((L / P + 1) * P) = (L / P + 1) * touchCount f P :=
    touchCount_full_blocks f P hper (L / P + 1)
  calc touchCount f L
      ≤ touchCount f ((L / P + 1) * P) := touchCount_mono f hLle
    _ = (L / P + 1) * touchCount f P := hblocks

/-- **Boundary discrepancy form.** The touch count differs from
`(L / P) · c` by at most `c`. -/
theorem touchCount_discrepancy
    (f : ℕ → Prop) [DecidablePred f] (P : ℕ) (hP : 0 < P)
    (hper : ∀ k, f (k + P) ↔ f k) (L : ℕ) :
    (L / P) * touchCount f P ≤ touchCount f L
      ∧ touchCount f L ≤ (L / P) * touchCount f P + touchCount f P := by
  refine ⟨touchCount_lower_bound f P hP hper L, ?_⟩
  have hub := touchCount_upper_bound f P hP hper L
  have : (L / P + 1) * touchCount f P = (L / P) * touchCount f P + touchCount f P := by
    ring
  linarith

end Collatz.SEDT.TouchDensity
