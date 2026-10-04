/-
Admissible-tail predicate (algebraic form of paper Definition F.0.1, revised).

Status (2026-10 review). Everything in this module is a statement about
residues in `ZMod (2^t)`; it does **not** mention the Collatz orbit. In the paper
the data `M_entry`, `v` come from the auxiliary sequence
`a_k = 3^{k+1}(r₀ + 2) − 5·2^k` (and its odd parts), which is *not* the orbit
numerator for `k ≥ 1` (see `Collatz/SEDT/AffineNumerator.lean`). Hence the
predicate and the counting lemma built on it
(`AdmissibleTailF01.touch_count_eq_one` in `AdmissibleTailBridge.lean`) are true
algebra about that auxiliary data only; no statement about touches on actual
orbits follows from them.

The predicate is

    AdmissibleTailF01 t M_entry v  ⇔  ∃ n, s_t = 3^n · (v + 3^t · M_entry)  in ZMod (2^t),

i.e. `v + 3^t · M_entry` lies in the coset `s_t · ⟨3⟩` of `(ZMod (2^t))ˣ`, where
`⟨3⟩` has order `Q_t = 2^{t−2}` for `t ≥ 3` (`Collatz.OrdFact.orderOf_three_eq_pow_two`).

Contents:
* `selected_segment_tail_touch` — the orbit touch predicate `T^[i+k] m ≡ s_t`
  (mod `2^t`) in local coordinates (used by `AdmissibleTailBridge` and
  `AggregateTouchRate`);
* `IsPowerOfThree`, `AdmissibleTailF01`;
* `AdmissibleTailF01_iff_exists_pow` (`Iff.rfl`);
* `AdmissibleTailF01_witness_lt_Qt` — the exponent can be reduced below `Q_t`.
-/

import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Collatz.Epochs.Core
import Collatz.Epochs.OrdFact

namespace Collatz.Mixing

/-- Touch predicate on the orbit of `m` in local coordinates starting at time
`i`: `selected_segment_tail_touch m t i k ↔ T^[i+k] m ≡ s_t (mod 2^t)`. -/
def selected_segment_tail_touch (m t i : ℕ) (k : ℕ) : Prop :=
  Collatz.Epochs.selected_segment_t_touch m (i + k) t

instance selected_segment_tail_touch_decidable (m t i : ℕ) :
    DecidablePred (selected_segment_tail_touch m t i) := by
  intro k
  dsimp [selected_segment_tail_touch, Collatz.Epochs.selected_segment_t_touch,
    Collatz.Epochs.is_t_touch]
  infer_instance

/-- `x` is a power of `3` in `ZMod (2^t)`. For `t ≥ 3`, `⟨3⟩` has order
`Q_t t = 2^(t-2)` (`Collatz.OrdFact.orderOf_three_eq_pow_two`). -/
def IsPowerOfThree {t : ℕ} (x : ZMod (2 ^ t)) : Prop :=
  ∃ n : ℕ, (3 : ZMod (2 ^ t)) ^ n = x

/-- Admissibility predicate (algebraic form of the revised Definition F.0.1):
`v + 3^t · Mentry ∈ s_t · ⟨3⟩` in `ZMod (2^t)`. A statement about two residues;
in the paper they are read off the auxiliary sequence `(a_k)`, not off the
Collatz orbit (see the module docstring). -/
def AdmissibleTailF01 (t : ℕ) (Mentry v : ZMod (2 ^ t)) : Prop :=
  ∃ n : ℕ, (Collatz.Epochs.s_t t : ZMod (2 ^ t)) =
    (3 : ZMod (2 ^ t)) ^ n * (v + (3 : ZMod (2 ^ t)) ^ t * Mentry)

/-- Unfolding of `AdmissibleTailF01` (`Iff.rfl`). -/
theorem AdmissibleTailF01_iff_exists_pow (t : ℕ) (Mentry v : ZMod (2 ^ t)) :
    AdmissibleTailF01 t Mentry v ↔
      ∃ n : ℕ, (Collatz.Epochs.s_t t : ZMod (2 ^ t)) =
        (3 : ZMod (2 ^ t)) ^ n * (v + (3 : ZMod (2 ^ t)) ^ t * Mentry) :=
  Iff.rfl

/-- For `t ≥ 3`, the witnessing exponent can be chosen in `[0, Q_t)`, because
`3^{Q_t} = 1` in `ZMod (2^t)` (`Collatz.OrdFact.three_pow_Qt_eq_one_zmod`). -/
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
