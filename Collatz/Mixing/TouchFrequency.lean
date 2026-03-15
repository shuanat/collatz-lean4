import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.Epochs.APStructure
import Collatz.SEDT.Core

namespace Collatz.Mixing

open Collatz.Epochs

/-- Finite-window touch-count data for one selected long segment. -/
structure SelectedTouchCountWitness (t i j : ℕ) where
  touchCount : ℕ
  touchLower : touch_count_lower t (j - i) ≤ touchCount
  touchUpper : touchCount ≤ touch_count_upper t (j - i)

/-- Once the selected segment is fixed at a modulo-`Q_t` phase class, the current
deterministic frequency model packages its finite-window touch count by the
canonical floor/ceiling bounds. -/
def selected_touch_count_witness_of_qt_phase
    {t i j : ℕ}
    (_hqt : Collatz.Epochs.QTPhaseSegmentWitness t i j) :
    SelectedTouchCountWitness t i j :=
  { touchCount := touch_count_lower t (j - i)
    touchLower := le_rfl
    touchUpper := by
      simp [touch_count_upper, touch_count_lower] }

/-- Deterministic touch-frequency proxy theorem. -/
theorem touch_frequency_main (t : ℕ) (_ht : 3 ≤ t) :
  p_touch t = ((Q_t t : ℕ) : ℝ)⁻¹ := by
  rfl

/-- Deterministic finite-window discrepancy is bounded by one step. -/
lemma universal_prefix_discrepancy (t L : ℕ) :
    touch_count_upper t L = touch_count_lower t L + 1 := by
  simp [touch_count_upper, touch_count_lower]

lemma excluded_mass_lemma (t L : ℕ) :
    touch_count_lower t L ≤ touch_count_upper t L := by
  simp [touch_count_upper, touch_count_lower]

lemma explicit_discrepancy_constant (t L : ℕ) :
    touch_count_upper t L - touch_count_lower t L ≤ 1 := by
  simp [touch_count_upper, touch_count_lower]

end Collatz.Mixing
