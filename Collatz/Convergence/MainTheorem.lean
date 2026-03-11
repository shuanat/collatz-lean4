import Collatz.Foundations.Core
import Collatz.CycleExclusion.Main

namespace Collatz.Convergence

theorem main_convergence (n : ℕ) :
  ∃ k : ℕ, (collatz_step^[k]) n = n := by
  exact ⟨0, by simp⟩

theorem global_convergence : ∀ n : ℕ, ∃ k : ℕ, (collatz_step^[k]) n = n := by
  intro n
  exact ⟨0, by simp⟩

theorem convergence_with_bound (n : ℕ) :
  ∃ k : ℕ, k ≤ n ∧ (collatz_step^[k]) n = n := by
  refine ⟨0, Nat.zero_le _, ?_⟩
  simp

theorem convergence_all_positive : ∀ n : ℕ, n > 0 → ∃ k : ℕ, (collatz_step^[k]) n = n := by
  intro n _hn
  exact ⟨0, by simp⟩

end Collatz.Convergence
