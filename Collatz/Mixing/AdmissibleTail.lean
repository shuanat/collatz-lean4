/-
Collatz Conjecture: Paper Definition F.0.1 — admissible-tail predicate
(**Wave 2E revision**, route α₃).

This module formalises the **algebraic core** of paper Definition F.0.1 in
its **revised** form derived in Wave 2D. The previous "single-residue coset
test on the homogenized entry residue" form (canonical paper F.0.1) was
empirically shown to score at a 47% empirical hit rate (matches a 50/50
baseline) on the late-window touchCount-equals-1 question; the Wave 2D
reverse-engineering report identifies the **exact** algebraic predicate
that is biconditionally equivalent to "exactly one touch in the late-regime
window" on every plateau.

  Reference: `collatz-verification/research/wave2-d10b-empirical/REPORT-
  reverse-engineering.md`, especially §2 (the elementary derivation) and
  §5.2 (the recommended Lean form).

The revised predicate is

    AdmissibleTailF01 t M_entry v
      ⇔  ∃ n : ℕ, (s_t t) = (3 : ZMod (2^t)) ^ n * (v + 3^t * M_entry)

where

* `M_entry := (M_{k_start}) mod 2^t` is the algebraic numerator residue at
  the plateau entry (before the late-regime flush window of length `t`),
* `v := (u_{k_start + t}) mod 2^t` is the per-plateau-anchored homogenizer
  freeze value at the late-regime entry (purely multiplicative-by-3 from
  there onwards),
* `s_t t = -5 · 3⁻¹ (mod 2^t)` is the paper touch residue
  (`Collatz.Epochs.s_t`),
* `⟨3⟩ ⊂ (ZMod (2^t))ˣ` is the cyclic subgroup of order
  `Q_t t = 2^(t-2)` (paper Lemma B.2 / `Collatz.OrdFact.three_pow_Qt_eq_one_zmod`).

In paper-style coset notation the predicate reads

    s_t · (v + 3^t · M_entry)⁻¹  ∈  ⟨3⟩

(both forms are equivalent because `⟨3⟩` is closed under inversion).

The predicate is exposed in the **paper-faithful, orbit-agnostic** form: it
takes only the algebraic data `M_entry, v : ZMod (2^t)` and only fixes the
algebraic shape of the revised F.0.1 coset condition. The orbit-side
supplier (Wave 3) will instantiate `M_entry` and `v` from the actual
Collatz orbit at the plateau entry — concretely from
`(LocalAffinePairSemantics.M 0 - LocalAffinePairSemantics.u 0)` and
`LocalAffinePairSemantics.u t`, projected into `ZMod (2^t)`.

This file introduces:
* `Collatz.Mixing.IsPowerOfThree` — membership in `⟨3⟩` viewed at the level
  of residues in `ZMod (2^t)`,
* `Collatz.Mixing.AdmissibleTailF01` — the revised F.0.1 predicate,
* `AdmissibleTailF01_iff_exists_pow` — `Iff.rfl` unfolding,
* `AdmissibleTailF01_witness_lt_Qt` — period-reduction of the witnessing
  exponent to `[0, Q_t t)` using `Collatz.OrdFact.three_pow_Qt_eq_one_zmod`.

A bridge to "late-window touchCount = 1" (Wave 2D §2 algebra) is documented
here at the algebraic level; its full Lean discharge requires connecting
`M_entry`/`v` to the actual orbit semantics in
`Collatz.Mixing.TouchFrequencyHomogenization` and is tracked as a separate
formal-first task (see Wave 2E summary). No `sorry`, no `axiom`, no proxy
stubs are introduced here — every theorem below is intended to be
axiom-clean.
-/

import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Collatz.Epochs.Core
import Collatz.Epochs.OrdFact

namespace Collatz.Mixing

/-- Membership in the cyclic subgroup `⟨3⟩` of `(ZMod (2^t))ˣ`, expressed at
the level of residues: `x` is a power of `3` iff there exists `n : ℕ` with
`(3 : ZMod (2^t)) ^ n = x`.

For `t ≥ 3`, `⟨3⟩` is exactly the order-`Q_t t` (= `2^(t-2)`) cyclic subgroup
of `(ZMod (2^t))ˣ` (paper Lemma B.2 / `Collatz.OrdFact.orderOf_three_eq_pow_two`),
so any `x : ZMod (2^t)` satisfying `IsPowerOfThree` is automatically a unit. -/
def IsPowerOfThree {t : ℕ} (x : ZMod (2 ^ t)) : Prop :=
  ∃ n : ℕ, (3 : ZMod (2 ^ t)) ^ n = x

/-- **Paper Definition F.0.1 (revised, Wave 2E) — admissibility predicate
(algebraic core).**

A plateau is *F.0.1-admissible at level `t`* iff the algebraic invariant
`v + 3^t · M_entry` lies in the coset `s_t · ⟨3⟩` of `(ZMod (2^t))ˣ`, where
`M_entry := M_{k_start} mod 2^t`, `v := u_{k_start + t} mod 2^t` is the
late-regime per-plateau homogenizer freeze value, and
`s_t := -5 · 3⁻¹ mod 2^t`.

Equivalently, in paper-style notation,
    `s_t · (v + 3^t · M_entry)⁻¹ ∈ ⟨3⟩`.

Wave 2D (`REPORT-reverse-engineering.md` §2) proves that this predicate is
biconditionally equivalent to "the late-regime window
`[k_start + t, k_start + t + Q_t)` contains exactly one touch
`M_k ≡ s_t (mod 2^t)`" on every eligible plateau, and ablations confirm
that the previous canonical paper F.0.1 (a coset test on `M_entry` alone,
ignoring `v` and the `3^t`-rotation) is at the random baseline.

This is the **paper-faithful, orbit-agnostic** form: the orbit-side
supplier (future Wave 3 of `R-D10b`) instantiates `M_entry` and `v` from
the real Collatz orbit at the plateau entry; here we only fix the
algebraic shape of the revised F.0.1 coset condition. -/
def AdmissibleTailF01 (t : ℕ) (Mentry v : ZMod (2 ^ t)) : Prop :=
  ∃ n : ℕ, (Collatz.Epochs.s_t t : ZMod (2 ^ t)) =
    (3 : ZMod (2 ^ t)) ^ n * (v + (3 : ZMod (2 ^ t)) ^ t * Mentry)

/-- **Power-form characterization (Wave 2E revision).** Direct unfolding of
`AdmissibleTailF01`: an admissible plateau is exactly the data of a
natural number `n` exhibiting

    `s_t = 3^n · (v + 3^t · M_entry)`   in `ZMod (2^t)`.

This makes the revised F.0.1 paper condition explicitly equivalent to the
`s_t · (v + 3^t · M_entry)⁻¹ ∈ ⟨3⟩` paper-style statement. -/
theorem AdmissibleTailF01_iff_exists_pow (t : ℕ) (Mentry v : ZMod (2 ^ t)) :
    AdmissibleTailF01 t Mentry v ↔
      ∃ n : ℕ, (Collatz.Epochs.s_t t : ZMod (2 ^ t)) =
        (3 : ZMod (2 ^ t)) ^ n * (v + (3 : ZMod (2 ^ t)) ^ t * Mentry) :=
  Iff.rfl

/-- **Period bound on the witnessing exponent (Wave 2E revision).**

If `t ≥ 3` and `AdmissibleTailF01 t Mentry v` holds, the witnessing exponent
`n` in the power-form equation can always be chosen in the canonical range
`[0, Q_t t)`. The reduction uses the order fact
`Collatz.OrdFact.three_pow_Qt_eq_one_zmod` (paper Lemma B.2):
`(3 : ZMod (2^t))^(Q_t t) = 1`. -/
theorem AdmissibleTailF01_witness_lt_Qt {t : ℕ} (ht : 3 ≤ t)
    {Mentry v : ZMod (2 ^ t)} (h : AdmissibleTailF01 t Mentry v) :
    ∃ n : ℕ, n < Collatz.Epochs.Q_t t ∧
      (Collatz.Epochs.s_t t : ZMod (2 ^ t)) =
        (3 : ZMod (2 ^ t)) ^ n * (v + (3 : ZMod (2 ^ t)) ^ t * Mentry) := by
  obtain ⟨n, hn⟩ := h
  have hQt_pos : 0 < Collatz.Epochs.Q_t t := by
    show 0 < 2 ^ (t - 2)
    exact pow_pos (by decide) _
  refine ⟨n % Collatz.Epochs.Q_t t, Nat.mod_lt _ hQt_pos, ?_⟩
  have hperiod : (3 : ZMod (2 ^ t)) ^ (Collatz.Epochs.Q_t t) = 1 :=
    Collatz.OrdFact.three_pow_Qt_eq_one_zmod ht
  -- Reduce `3^n` to `3^(n % Q_t t)` by the period identity.
  have hpow :
      (3 : ZMod (2 ^ t)) ^ n =
        (3 : ZMod (2 ^ t)) ^ (n % Collatz.Epochs.Q_t t) := by
    conv_lhs =>
      rw [show n = Collatz.Epochs.Q_t t * (n / Collatz.Epochs.Q_t t)
                    + n % Collatz.Epochs.Q_t t from
            (Nat.div_add_mod n (Collatz.Epochs.Q_t t)).symm]
    rw [pow_add, pow_mul, hperiod, one_pow, one_mul]
  rw [hn, hpow]

end Collatz.Mixing
