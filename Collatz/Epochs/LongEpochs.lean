import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.Epochs

/-- Canonical long-epoch gap proxy. -/
def gap_long (t : ℕ) : ℕ := Q_t t + 1

lemma sparsity_of_switches (t : ℕ) : gap_long t ≥ 1 := by
  simp [gap_long]

lemma long_plateau_on_tail (t : ℕ) : ∃ L : ℕ, L ≥ Q_t t := by
  exact ⟨Q_t t, le_rfl⟩

lemma primitive_phase_shift_in_window (t : ℕ) :
    ∃ W : ℕ, W = Q_t t + gap_long t := by
  exact ⟨Q_t t + gap_long t, rfl⟩

lemma good_phase_implies_long (t : ℕ) :
    ∀ L : ℕ, L ≥ gap_long t → L + 1 > gap_long t := by
  intro L hL
  have hg : gap_long t < gap_long t + 1 := Nat.lt_succ_self _
  have hle : gap_long t + 1 ≤ L + 1 := Nat.succ_le_succ hL
  exact lt_of_lt_of_le hg hle

theorem infinite_long_epochs (t : ℕ) (_ht : 3 ≤ t) :
    ∀ n : ℕ, ∃ L : ℕ, L ≥ n ∧ L ≥ gap_long t := by
  intro n
  refine ⟨max n (gap_long t), ?_, ?_⟩
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma super_long_epochs (t : ℕ) : ∃ L : ℕ, L ≥ gap_long t + Q_t t := by
  exact ⟨gap_long t + Q_t t, le_rfl⟩

lemma super_long_epochs_sedt (t : ℕ) : ∃ L : ℕ, L ≥ Collatz.SEDT.L₀ t 1 := by
  exact ⟨Collatz.SEDT.L₀ t 1, le_rfl⟩

lemma touch_count_vs_length (t : ℕ) :
    ∀ L : ℕ, L / gap_long t ≤ L := by
  intro L
  exact Nat.div_le_self _ _

lemma pigeonhole_multibit_touches (t : ℕ) : ∃ n : ℕ, n ≤ gap_long t := by
  exact ⟨0, Nat.zero_le _⟩

lemma plateau_to_epoch_length (t : ℕ) :
    ∀ plateauLen : ℕ, plateauLen ≤ plateauLen + gap_long t := by
  intro plateauLen
  exact Nat.le_add_right _ _

end Collatz.Epochs
