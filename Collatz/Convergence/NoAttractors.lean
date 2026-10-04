import Collatz.Foundations.Core
import Collatz.CycleExclusion.Main
import Collatz.Convergence.FixedPoints

namespace Collatz.Convergence

open Collatz.Foundations

/-- Semantic attractor predicate: nonempty and closed under the odd Collatz step. -/
def is_attractor (s : Set ℕ) : Prop :=
  s.Nonempty ∧ ∀ n : ℕ, n ∈ s → collatz_step n ∈ s

def trivialCycleSet : Set ℕ := {1}

lemma trivial_cycle_is_attractor : is_attractor trivialCycleSet := by
  refine ⟨?_, ?_⟩
  · exact ⟨1, by simp [trivialCycleSet]⟩
  · intro n hn
    have hn1 : n = 1 := by simpa [trivialCycleSet] using hn
    simpa [trivialCycleSet, hn1, is_fixed_point] using one_is_fixed_point

/-- Any singleton attractor is determined by its fixed-point witness. -/
lemma singleton_attractor_fixed_point (n : ℕ)
    (hattr : is_attractor ({n} : Set ℕ)) :
    is_fixed_point n := by
  have hstep : collatz_step n ∈ ({n} : Set ℕ) := hattr.2 n (by simp)
  simpa [is_fixed_point] using hstep

/-- Reaching `1` means entering the trivial cycle `{1}` (restatement). -/
theorem convergence_to_trivial_cycle (n : ℕ)
    (hreach : ∃ k : ℕ, (collatz_step^[k]) n = 1) :
    ∃ k : ℕ, (collatz_step^[k]) n ∈ trivialCycleSet := by
  rcases hreach with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  simp [trivialCycleSet, hk]

end Collatz.Convergence
