import Collatz.Epochs.NumeratorCarry
import Collatz.SEDT.TouchDensity

namespace Collatz.Mixing

open Collatz.Epochs

/-- Touch predicate on the translated selected window `[i, i + L)` of the actual
orbit. The local index `k` is measured from the left endpoint `i`. -/
def selected_segment_tail_touch (m t i : ℕ) (k : ℕ) : Prop :=
  Collatz.Epochs.selected_segment_t_touch m (i + k) t

instance selected_segment_tail_touch_decidable (m t i : ℕ) :
    DecidablePred (selected_segment_tail_touch m t i) := by
  intro k
  dsimp [selected_segment_tail_touch, Collatz.Epochs.selected_segment_t_touch,
    Collatz.Epochs.is_t_touch]
  infer_instance

/-- Minimal honest local semantic slot below paper Appendix F.6 on one selected
admissible tail. It records exactly the two inputs consumed by
`TouchDensity.touchCount_discrepancy`: `Q_t`-periodicity of the translated touch
predicate and the fact that one `Q_t`-block contains exactly one touch.

**Wave 2H scope note.** This structure is now used **only as an internal
algebraic-stack input** for the deprecated two-sided F.6 path
(`AdmissibleTailTouchFrequencyResidual` / `AdmissibleTailTouchLowerBoundResidual`
in `PhaseMixing.lean`). The Wave 2H public orbit-side residual
(`Collatz.Mixing.OrbitSideAggregateTouchRateResidual` in
`Collatz/Mixing/AggregateTouchRate.lean`) does **not** require the per-period
`one_touch_per_period` field on the actual orbit; it is one-sided and
aggregate. The Wave 2G internal lemma
`LocalAffinePairSemantics.one_touch_per_period`
(`Collatz/Mixing/TouchFrequencyHomogenization.lean`) remains the algebraic
supplier for this structure on plateau-anchored data, but is no longer
exposed as the orbit-side public obligation. -/
structure SelectedTailTouchSemantics (m t i : ℕ) where
  periodic :
    ∀ k : ℕ,
      selected_segment_tail_touch m t i (k + Q_t t) ↔
        selected_segment_tail_touch m t i k
  one_touch_per_period :
    Collatz.SEDT.TouchDensity.touchCount
      (selected_segment_tail_touch m t i) (Q_t t) = 1

/-- Actual selected-segment touch-count witness: unlike the older stable wrapper,
this object remembers the counted value itself and the fact that it is the
`TouchDensity.touchCount` of the translated actual-orbit touch predicate. -/
structure SelectedTouchCountWitnessOn (m t i j : ℕ) where
  touchCount : ℕ
  touchCount_eq :
    touchCount =
      Collatz.SEDT.TouchDensity.touchCount
        (selected_segment_tail_touch m t i) (j - i)
  touchLower : touch_count_lower t (j - i) ≤ touchCount
  touchUpper : touchCount ≤ touch_count_upper t (j - i)

/-- The local semantic slot immediately yields the honest finite-window
touch-count witness on the selected segment. The proof is the real algebraic D.4
counting theorem specialized to period `Q_t` and one touch per period. -/
def selected_touch_count_witness_on_of_semantics
    {m t i j : ℕ}
    (hsem : SelectedTailTouchSemantics m t i) :
    SelectedTouchCountWitnessOn m t i j := by
  refine
    { touchCount :=
        Collatz.SEDT.TouchDensity.touchCount
          (selected_segment_tail_touch m t i) (j - i)
      touchCount_eq := rfl
      touchLower := ?_
      touchUpper := ?_ }
  ·
    have hQtPos : 0 < Q_t t := by
      unfold Q_t
      exact pow_pos (by decide) _
    have hdisc :=
      Collatz.SEDT.TouchDensity.touchCount_discrepancy
        (selected_segment_tail_touch m t i) (Q_t t) hQtPos hsem.periodic (j - i)
    rcases hdisc with ⟨hlow, _⟩
    simpa [touch_count_lower, hsem.one_touch_per_period] using hlow
  ·
    have hQtPos : 0 < Q_t t := by
      unfold Q_t
      exact pow_pos (by decide) _
    have hdisc :=
      Collatz.SEDT.TouchDensity.touchCount_discrepancy
        (selected_segment_tail_touch m t i) (Q_t t) hQtPos hsem.periodic (j - i)
    rcases hdisc with ⟨_, hupp⟩
    simpa [touch_count_lower, touch_count_upper, hsem.one_touch_per_period] using hupp

/-- Forget the actual-count equation when only the older stable wrapper is
needed higher in the carry/depth stack. -/
def SelectedTouchCountWitnessOn.toSelectedTouchCountWitness
    {m t i j : ℕ}
    (hw : SelectedTouchCountWitnessOn m t i j) :
    SelectedTouchCountWitness t i j :=
  { touchCount := hw.touchCount
    touchLower := hw.touchLower
    touchUpper := hw.touchUpper }

/-- Compatibility wrapper: the honest local tail semantics produce the legacy
stable touch-count witness type used by the upper carry/depth packages. -/
def selected_touch_count_witness_of_tail_semantics
    {m t i j : ℕ}
    (hsem : SelectedTailTouchSemantics m t i) :
    SelectedTouchCountWitness t i j :=
  (selected_touch_count_witness_on_of_semantics (j := j) hsem).toSelectedTouchCountWitness

end Collatz.Mixing
