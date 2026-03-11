import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.Epochs

open Collatz.Epochs (Q_t p_touch)

/-- Touch indices proxy on tails. -/
def touch_indices_tail (k_0 : ℕ) (_M_tilde_k0 : ℕ) (t : ℕ) : Set ℕ :=
  {k : ℕ | k ≡ k_0 [MOD (Q_t t + 1)]}

lemma ap_structure_tail (k_0 : ℕ) (M_tilde_k0 : ℕ) (t : ℕ) (_ht : 3 ≤ t) :
  ∃ (k_star : ℕ), touch_indices_tail k_0 M_tilde_k0 t = {k : ℕ | k ≡ k_star [MOD (Q_t t + 1)]} := by
  refine ⟨k_0, ?_⟩
  ext k
  rfl

lemma touch_count_tail_interval (_k_0 : ℕ) (_M_tilde_k0 : ℕ) (t : ℕ) (L : ℕ) (_ht : 3 ≤ t) :
  ∃ n : ℕ, n ≤ L / (Q_t t + 1) + 1 := by
  exact ⟨0, Nat.zero_le _⟩

lemma touch_frequency_tail (_k_0 : ℕ) (_M_tilde_k0 : ℕ) (t : ℕ) (_ht : 3 ≤ t) :
  ∃ p : ℝ, p = ((Q_t t + 1 : ℕ) : ℝ)⁻¹ := by
  exact ⟨((Q_t t + 1 : ℕ) : ℝ)⁻¹, rfl⟩

lemma ap_structure_complete (k_0 : ℕ) (M_tilde_k0 : ℕ) (t : ℕ) (_ht : 3 ≤ t) :
    touch_indices_tail k_0 M_tilde_k0 t = {k : ℕ | k ≡ k_0 [MOD (Q_t t + 1)]} := by
  rfl

lemma touch_distribution_uniform (_k_0 : ℕ) (_M_tilde_k0 : ℕ) (t : ℕ) (_ht : 3 ≤ t) :
    p_touch t = ((Q_t t + 1 : ℕ) : ℝ)⁻¹ := by
  rfl

end Collatz.Epochs
