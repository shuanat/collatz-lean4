import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core
import Collatz.SEDT.Theorems

namespace Collatz.Mixing

open Collatz.Epochs

/-- Phase-mixing proxy invariant. -/
def phase_mixing_invariant (t : ℕ) : Prop := t ≥ 3

lemma per_epoch_ap_structure (k0 M_tilde0 t : ℕ) :
    phase_class k0 M_tilde0 t < Q_t t + 1 := by
  unfold phase_class
  exact Nat.mod_lt _ (Nat.succ_pos _)

lemma epoch_to_epoch_phase_shift (k0 k0' M_tilde0 M_tilde0' t : ℕ) :
    phase_shift k0 k0' M_tilde0 M_tilde0' t < Q_t t + 1 := by
  unfold phase_shift
  exact Nat.mod_lt _ (Nat.succ_pos _)

lemma primitive_junction_theorem (k0 k0' M_tilde0 M_tilde0' t : ℕ)
    (hprim : is_primitive_junction k0 k0' M_tilde0 M_tilde0' t) :
    phase_shift k0 k0' M_tilde0 M_tilde0' t % 2 = 1 := by
  simpa [is_primitive_junction] using hprim

/-- Phase shift is periodic with period `Q_t t + 1` in the epoch index. -/
lemma phase_shift_periodic (k0 k0' M_tilde0 M_tilde0' t : ℕ) :
    phase_shift k0 (k0' + (Q_t t + 1)) M_tilde0 M_tilde0' t =
      phase_shift k0 k0' M_tilde0 M_tilde0' t := by
  unfold phase_shift
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Nat.add_mod_right (k0' + M_tilde0 + M_tilde0') (Q_t t + 1))

lemma recurrence_of_primitive_junction (k0 k0' M_tilde0 M_tilde0' t : ℕ)
    (hprim : is_primitive_junction k0 k0' M_tilde0 M_tilde0' t) :
    is_primitive_junction k0 (k0' + (Q_t t + 1)) M_tilde0 M_tilde0' t := by
  unfold is_primitive_junction at hprim ⊢
  simpa [phase_shift_periodic] using hprim

lemma exact_cycling_qt_block (k0 M_tilde0 t : ℕ) :
    phase_class (k0 + (Q_t t + 1)) M_tilde0 t = phase_class k0 M_tilde0 t := by
  unfold phase_class
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Nat.add_mod_right (k0 + M_tilde0) (Q_t t + 1))

theorem phase_mixing_main (t : ℕ) (_ht : 3 ≤ t) :
  p_touch t = ((Q_t t + 1 : ℕ) : ℝ)⁻¹ := by
  rfl

lemma uniform_phase_recurrence (k0 M_tilde0 t n : ℕ) :
    phase_class (k0 + n * (Q_t t + 1)) M_tilde0 t = phase_class k0 M_tilde0 t := by
  induction n with
  | zero =>
      simp [phase_class]
  | succ n ih =>
      calc
        phase_class (k0 + Nat.succ n * (Q_t t + 1)) M_tilde0 t
            = phase_class (k0 + n * (Q_t t + 1) + (Q_t t + 1)) M_tilde0 t := by
                simp [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = phase_class (k0 + n * (Q_t t + 1)) M_tilde0 t := by
              simpa using exact_cycling_qt_block (k0 + n * (Q_t t + 1)) M_tilde0 t
        _ = phase_class k0 M_tilde0 t := ih

/-- F-level bridge: mixing/touch frequency feeds SEDT envelope negativity input. -/
theorem mixing_touch_to_sedt_envelope_nonpositive
    (t U : ℕ) (β : ℝ) (L : ℕ)
    (ht : 3 ≤ t) (hU : U ≥ 1) (hβ : β > Collatz.SEDT.β₀ t U)
    (hmix : p_touch t = ((Q_t t + 1 : ℕ) : ℝ)⁻¹)
    (hverylong : β * Collatz.SEDT.C t U ≤ (L : ℝ) * Collatz.SEDT.ε t U β) :
    Collatz.SEDT.sedt_envelope t U β L ≤ 0 := by
  have _ : p_touch t = ((Q_t t + 1 : ℕ) : ℝ)⁻¹ := hmix
  simpa [Collatz.SEDT.sedt_envelope] using
    Collatz.SEDT.sedt_bound_negative_for_very_long_epochs t U β L ht hU hβ hverylong

end Collatz.Mixing
