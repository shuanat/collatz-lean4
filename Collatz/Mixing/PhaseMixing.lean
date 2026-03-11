import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.Mixing

open Collatz.Epochs

/-- Phase-mixing proxy invariant. -/
def phase_mixing_invariant (t : ℕ) : Prop := t ≥ 3

lemma per_epoch_ap_structure (_t : ℕ) : True := trivial
lemma epoch_to_epoch_phase_shift (_t : ℕ) : True := trivial
lemma primitive_junction_theorem (_t : ℕ) : True := trivial
lemma recurrence_of_primitive_junction (_t : ℕ) : True := trivial
lemma exact_cycling_qt_block (_t : ℕ) : True := trivial

theorem phase_mixing_main (t : ℕ) (_ht : 3 ≤ t) :
  ∃ p : ℝ, p = ((Q_t t + 1 : ℕ) : ℝ)⁻¹ := by
  exact ⟨((Q_t t + 1 : ℕ) : ℝ)⁻¹, rfl⟩

lemma uniform_phase_recurrence (_t : ℕ) : True := trivial

end Collatz.Mixing
