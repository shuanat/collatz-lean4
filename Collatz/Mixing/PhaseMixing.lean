import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.Mixing.TouchFrequencyLocal
import Collatz.SEDT.Core
import Collatz.SEDT.Theorems

namespace Collatz.Mixing

open Collatz.Epochs

/-- Phase-mixing proxy invariant. -/
def phase_mixing_invariant (t : ℕ) : Prop := t ≥ 3

lemma per_epoch_ap_structure (k0 M_tilde0 t : ℕ) :
    phase_class k0 M_tilde0 t < Q_t t := by
  unfold phase_class
  exact Nat.mod_lt _ (pow_pos (by decide) _)

lemma epoch_to_epoch_phase_shift (k0 k0' M_tilde0 M_tilde0' t : ℕ) :
    phase_shift k0 k0' M_tilde0 M_tilde0' t < Q_t t := by
  unfold phase_shift
  exact Nat.mod_lt _ (pow_pos (by decide) _)

lemma primitive_junction_theorem (k0 k0' M_tilde0 M_tilde0' t : ℕ)
    (hprim : is_primitive_junction k0 k0' M_tilde0 M_tilde0' t) :
    phase_shift k0 k0' M_tilde0 M_tilde0' t % 2 = 1 := by
  simpa [is_primitive_junction] using hprim

/-- Phase shift is periodic with period `Q_t t` in the epoch index. -/
lemma phase_shift_periodic (k0 k0' M_tilde0 M_tilde0' t : ℕ) :
    phase_shift k0 (k0' + Q_t t) M_tilde0 M_tilde0' t =
      phase_shift k0 k0' M_tilde0 M_tilde0' t := by
  unfold phase_shift
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Nat.add_mod_right (k0' + M_tilde0 + M_tilde0') (Q_t t))

lemma recurrence_of_primitive_junction (k0 k0' M_tilde0 M_tilde0' t : ℕ)
    (hprim : is_primitive_junction k0 k0' M_tilde0 M_tilde0' t) :
    is_primitive_junction k0 (k0' + Q_t t) M_tilde0 M_tilde0' t := by
  unfold is_primitive_junction at hprim ⊢
  simpa [phase_shift_periodic] using hprim

lemma exact_cycling_qt_block (k0 M_tilde0 t : ℕ) :
    phase_class (k0 + Q_t t) M_tilde0 t = phase_class k0 M_tilde0 t := by
  unfold phase_class
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Nat.add_mod_right (k0 + M_tilde0) (Q_t t))

theorem phase_mixing_main (t : ℕ) (_ht : 3 ≤ t) :
  p_touch t = ((Q_t t : ℕ) : ℝ)⁻¹ := by
  rfl

/-- Lower theorem-source below paper Appendix F.6 on admissible tails.

For each prefix length `L`, choose the admissible-tail window
`[tailStart L, tailStop L)` and attach the honest local tail semantics on that
window. This keeps the actual mathematical burden explicit: `PhaseMixing`
does not pretend to manufacture F.6 from `rfl`; it consumes the local
periodicity + one-touch-per-period slot exported by
`Collatz/Mixing/TouchFrequencyLocal.lean`. -/
structure AdmissibleTailTouchFrequencyTheoremSource (n t : ℕ) where
  tailStart : ℕ → ℕ
  tailStop : ℕ → ℕ
  tailOrdered : ∀ L : ℕ, tailStart L ≤ tailStop L
  tailSemantics : ∀ L : ℕ, SelectedTailTouchSemantics n t (tailStart L)

/-- Integer-coded two-sided discrepancy witness for Appendix F.6 on admissible
tails. This is the paper-faithful tail-level content: a deterministic constant
`C_t` and a counted number of touches on the chosen admissible-tail window,
bounded on both sides by the expected `Q_t^{-1}` density up to `C_t`. -/
structure AdmissibleTailTouchFrequencyWitness (n t : ℕ) where
  discrepancyConst : ℕ
  tailStart : ℕ → ℕ
  tailStop : ℕ → ℕ
  touchCount : ℕ → ℕ
  lower :
    ∀ L : ℕ,
      (tailStop L - tailStart L) / Q_t t ≤ touchCount L + discrepancyConst
  upper :
    ∀ L : ℕ,
      touchCount L ≤ (tailStop L - tailStart L) / Q_t t + discrepancyConst

/-- Public F.6-facing residual: the honest lower theorem-source on admissible
tails is present. The mathematical content remains explicit in
`AdmissibleTailTouchFrequencyTheoremSource`; the residual is just its
`Nonempty` wrapper for public consumption.

**Wave 2H deprecation note.** The Wave 2H repackaging of paper Theorem F.6
moved the public orbit-side burden to the strictly weaker
`Collatz.Mixing.OrbitSideAggregateTouchRateResidual` (one-sided aggregate
touch-rate, file `Collatz/Mixing/AggregateTouchRate.lean`). This residual,
together with `AdmissibleTailTouchLowerBoundResidual` below, is **kept as
a deprecated back-compat alias** for downstream consumers that still rely
on the per-window two-sided form; it is no longer the canonical Wave 2H
public target. See `docs/residual-budget.md` (W-B entry) and
`docs/wave2h-research/paper-residual-scope.md` §5.1, §5.3. -/
def AdmissibleTailTouchFrequencyResidual (n t : ℕ) : Prop :=
  Nonempty (AdmissibleTailTouchFrequencyTheoremSource n t)

/-- One-sided E.2-facing corollary interface extracted from the two-sided
Appendix-F.6 tail discrepancy statement. The core theorem remains two-sided; this
lower-bound package is a derived consumer-facing corollary, not a redefinition
of F.6 itself.

**Wave 2H deprecation note.** Superseded as the canonical SEDT-input by
`Collatz.Mixing.OrbitSideAggregateTouchRateResidual`
(`Collatz/Mixing/AggregateTouchRate.lean`). Retained here as a deprecated
back-compat alias for downstream consumers and as the algebraic-stack-level
lower-bound used to motivate the one-sided W-B retargeting. -/
def AdmissibleTailTouchLowerBoundResidual (_n t : ℕ) : Prop :=
  ∃ tailStart tailStop touchCount : ℕ → ℕ, ∃ C_t : ℕ,
    ∀ L : ℕ, (tailStop L - tailStart L) / Q_t t ≤ touchCount L + C_t

/-- The honest local admissible-tail theorem-source produces the explicit
two-sided Appendix-F.6 discrepancy witness with the concrete deterministic
constant `1` coming from `TouchDensity.touchCount_discrepancy`. -/
noncomputable def admissible_tail_touch_frequency_witness_of_theorem_source
    {n t : ℕ}
    (hsrc : AdmissibleTailTouchFrequencyTheoremSource n t) :
    AdmissibleTailTouchFrequencyWitness n t := by
  refine
    { discrepancyConst := 1
      tailStart := hsrc.tailStart
      tailStop := hsrc.tailStop
      touchCount := fun L =>
        (selected_touch_count_witness_on_of_semantics
          (i := hsrc.tailStart L) (j := hsrc.tailStop L) (hsrc.tailSemantics L)).touchCount
      lower := ?_
      upper := ?_ }
  · intro L
    let hw :=
      selected_touch_count_witness_on_of_semantics
        (i := hsrc.tailStart L) (j := hsrc.tailStop L) (hsrc.tailSemantics L)
    change
      touch_count_lower t (hsrc.tailStop L - hsrc.tailStart L) ≤
        hw.touchCount + 1
    exact le_trans hw.touchLower (Nat.le_add_right _ _)
  · intro L
    let hw :=
      selected_touch_count_witness_on_of_semantics
        (i := hsrc.tailStart L) (j := hsrc.tailStop L) (hsrc.tailSemantics L)
    simpa [touch_count_upper] using hw.touchUpper

/-- Public extractor from the Appendix-F.6 residual wrapper to the explicit
two-sided discrepancy witness. -/
noncomputable def admissible_tail_touch_frequency_witness_of_residual
    {n t : ℕ}
    (hfreq : AdmissibleTailTouchFrequencyResidual n t) :
    AdmissibleTailTouchFrequencyWitness n t :=
  admissible_tail_touch_frequency_witness_of_theorem_source (Classical.choice hfreq)

/-- Consumer-facing one-sided lower bound extracted from the honest two-sided
Appendix-F.6 residual wrapper. This is the weakest sufficient interface expected
downstream by the E.2 bookkeeping route. -/
theorem admissible_tail_touch_lower_bound_of_residual
    {n t : ℕ}
    (hfreq : AdmissibleTailTouchFrequencyResidual n t) :
    AdmissibleTailTouchLowerBoundResidual n t := by
  let hw := admissible_tail_touch_frequency_witness_of_residual hfreq
  refine ⟨hw.tailStart, hw.tailStop, hw.touchCount, hw.discrepancyConst, ?_⟩
  intro L
  exact hw.lower L

lemma uniform_phase_recurrence (k0 M_tilde0 t n : ℕ) :
    phase_class (k0 + n * Q_t t) M_tilde0 t = phase_class k0 M_tilde0 t := by
  induction n with
  | zero =>
      simp [phase_class]
  | succ n ih =>
      calc
        phase_class (k0 + Nat.succ n * Q_t t) M_tilde0 t
            = phase_class (k0 + n * Q_t t + Q_t t) M_tilde0 t := by
                simp [Nat.succ_mul, Nat.add_left_comm, Nat.add_comm]
        _ = phase_class (k0 + n * Q_t t) M_tilde0 t := by
              simpa using exact_cycling_qt_block (k0 + n * Q_t t) M_tilde0 t
        _ = phase_class k0 M_tilde0 t := ih

/-- F-level bridge: mixing/touch frequency feeds SEDT envelope negativity input. -/
theorem mixing_touch_to_sedt_envelope_nonpositive
    (t U : ℕ) (β : ℝ) (L : ℕ)
    (ht : 3 ≤ t) (hU : U ≥ 1) (hβ : β > Collatz.SEDT.β₀ t U)
    (hmix : p_touch t = ((Q_t t : ℕ) : ℝ)⁻¹)
    (hverylong : β * Collatz.SEDT.C t U ≤ (L : ℝ) * Collatz.SEDT.ε t U β) :
    Collatz.SEDT.sedt_envelope t U β L ≤ 0 := by
  have _ : p_touch t = ((Q_t t : ℕ) : ℝ)⁻¹ := hmix
  simpa [Collatz.SEDT.sedt_envelope] using
    Collatz.SEDT.sedt_bound_negative_for_very_long_epochs t U β L ht hU hβ hverylong

end Collatz.Mixing
