import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.Mixing

open Collatz.Epochs

/-- Deterministic touch-frequency proxy theorem. -/
theorem touch_frequency_main (t : ℕ) (_ht : 3 ≤ t) :
  p_touch t = ((Q_t t + 1 : ℕ) : ℝ)⁻¹ := by
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
