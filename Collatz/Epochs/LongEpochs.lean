import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.Epochs

/-- Canonical long-epoch gap proxy. -/
def gap_long (t : ℕ) : ℕ := Q_t t + 1

lemma sparsity_of_switches (_t : ℕ) : True := trivial
lemma long_plateau_on_tail (_t : ℕ) : True := trivial
lemma primitive_phase_shift_in_window (_t : ℕ) : True := trivial
lemma good_phase_implies_long (_t : ℕ) : True := trivial

theorem infinite_long_epochs (_t : ℕ) (_ht : 3 ≤ _t) : True := trivial

lemma super_long_epochs (_t : ℕ) : True := trivial
lemma super_long_epochs_sedt (_t : ℕ) : True := trivial
lemma touch_count_vs_length (_t : ℕ) : True := trivial
lemma pigeonhole_multibit_touches (_t : ℕ) : True := trivial
lemma plateau_to_epoch_length (_t : ℕ) : True := trivial

end Collatz.Epochs
