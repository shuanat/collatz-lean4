/-
Collatz Conjecture: S7.1.A.1 — Pure group-theoretic core for paper Lemma G.5c
(boxed Q_t-block phase uniqueness).

This module proves the **paper-faithful pure group-theoretic content** of
Lemma G.5c (good phase uniqueness on a t-epoch tail), separated cleanly from
the orbit-side application (which is blocked on the foundational replatform of
`Collatz/Epochs/{Structure,PhaseClasses,...}.lean` and is surfaced as
`EpochTailGeometryResidual` in `Collatz/Epochs/G/Residuals.lean`).

The pure statement is:

  In `ZMod (2^t)` for `t ≥ 3`, the equation
    `(3 : ZMod (2^t)) ^ j₁ = (3 : ZMod (2^t)) ^ j₂`
  is equivalent to `j₁ ≡ j₂ [MOD Q_t t]`, where `Q_t t = 2^(t-2)` is the
  multiplicative order of 3 modulo 2^t (paper Lemma B.2).

Hence the solutions of the touch-equation `3^j * x = y` for fixed `x, y` (with
`x` a unit) form a single residue class modulo `Q_t t`. This is exactly the
algebraic content of paper G.5c; the orbit-side application is the assertion
that on every t-epoch tail this residue class is realized, which is encoded as
the `EpochTailGeometryResidual` open math residual (paper G.1+G.2+G.4+G.5b
jointly).

Implementation note: the canonical paper Lemma B.2 (`orderOf (3 : ZMod (2^t))
= 2^(t-2)` for `t ≥ 3`) is consumed via import from `Collatz.Epochs.OrdFact`
(`Collatz.OrdFact.orderOf_three_eq_pow_two`). S7.0.A housekeeping fixed the
Mathlib API drift in `OrdFact.lean` (replaced stale `decide`/`simp` tactics
with `orderOf_eq_prime` / `map_natCast` / `orderOf_pow'` based proofs), so
the inline copy that S7.1 carried as a workaround has been removed.

Paper-correspondence:
- `phase_uniqueness_pure_mod_Qt`: paper Appendix G, Lemma G.5c (pure form);
  paper Appendix B, Lemma B.2 (via `Collatz.OrdFact.orderOf_three_eq_pow_two`).
-/

import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Collatz.Epochs.Core
import Collatz.Epochs.OrdFact

namespace Collatz.Epochs.G

open Collatz.Epochs

set_option maxHeartbeats 400000

/-- **Paper Lemma B.2 (re-export).** The multiplicative order of `3` modulo
`2^t` is exactly `2^(t-2)` for `t ≥ 3`. Thin alias forwarding to the
authoritative proof in `Collatz.Epochs.OrdFact`. -/
theorem orderOf_three_ZMod_pow_two {t : ℕ} (ht : 3 ≤ t) :
    orderOf (3 : ZMod (2 ^ t)) = 2 ^ (t - 2) :=
  Collatz.OrdFact.orderOf_three_eq_pow_two ht

/-- Auxiliary: `IsOfFinOrder (3 : ZMod (2^t))` for `t ≥ 3`. Derived from
`orderOf_three_ZMod_pow_two` via `orderOf_pos_iff`. -/
private lemma isOfFinOrder_three_ZMod_pow_two {t : ℕ} (ht : 3 ≤ t) :
    IsOfFinOrder (3 : ZMod (2 ^ t)) := by
  rw [← orderOf_pos_iff, orderOf_three_ZMod_pow_two ht]
  exact pow_pos (by decide) _

/-- **S7.1.A.1 — Pure group-theoretic G.5c uniqueness (paper Lemma G.5c, pure
form).**

For every `t ≥ 3`, two non-negative powers of `(3 : ZMod (2^t))` agree iff
their exponents are congruent modulo `Q_t t = 2^(t-2)`. This is the algebraic
core of paper Appendix G, Lemma G.5c: the orbit-side application is the
additional content blocked on the (open) epoch-tail geometry residual. -/
theorem phase_uniqueness_pure_mod_Qt {t : ℕ} (ht : 3 ≤ t) (j₁ j₂ : ℕ) :
    (3 : ZMod (2 ^ t)) ^ j₁ = (3 : ZMod (2 ^ t)) ^ j₂ ↔
      j₁ ≡ j₂ [MOD Collatz.Epochs.Q_t t] := by
  have hfin : IsOfFinOrder (3 : ZMod (2 ^ t)) := isOfFinOrder_three_ZMod_pow_two ht
  have hord : orderOf (3 : ZMod (2 ^ t)) = Collatz.Epochs.Q_t t := by
    rw [orderOf_three_ZMod_pow_two ht]
    rfl
  rw [hfin.pow_eq_pow_iff_modEq, hord]

/-- **Multiplicative form of `phase_uniqueness_pure_mod_Qt`.**

If `(3^j₁) * x = (3^j₂) * x` and `x` is a unit in `ZMod (2^t)`, then
`j₁ ≡ j₂ [MOD Q_t t]`. The cancellation by `x` is performed via right-
multiplication by `x⁻¹` (rather than via a non-existent `IsRightCancelMulZero`
instance for `ZMod (2^t)`, which has zero divisors). -/
theorem phase_uniqueness_pure_mod_Qt_mul {t : ℕ} (ht : 3 ≤ t)
    (j₁ j₂ : ℕ) (x : (ZMod (2 ^ t))ˣ)
    (h : (3 : ZMod (2 ^ t)) ^ j₁ * (x : ZMod (2 ^ t)) =
         (3 : ZMod (2 ^ t)) ^ j₂ * (x : ZMod (2 ^ t))) :
    j₁ ≡ j₂ [MOD Collatz.Epochs.Q_t t] := by
  have hxinv : (x : ZMod (2 ^ t)) * ((↑x⁻¹ : ZMod (2 ^ t))) = 1 := by
    rw [← Units.val_mul]
    simp
  have h' : (3 : ZMod (2 ^ t)) ^ j₁ = (3 : ZMod (2 ^ t)) ^ j₂ := by
    have hmul :
        (3 : ZMod (2 ^ t)) ^ j₁ * ((x : ZMod (2 ^ t)) * (↑x⁻¹ : ZMod (2 ^ t)))
          = (3 : ZMod (2 ^ t)) ^ j₂ * ((x : ZMod (2 ^ t)) * (↑x⁻¹ : ZMod (2 ^ t)))
        := by
      rw [← mul_assoc, ← mul_assoc, h]
    rwa [hxinv, mul_one, mul_one] at hmul
  exact (phase_uniqueness_pure_mod_Qt ht j₁ j₂).1 h'

end Collatz.Epochs.G
