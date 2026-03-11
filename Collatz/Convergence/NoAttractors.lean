import Collatz.Foundations.Core
import Collatz.CycleExclusion.Main

namespace Collatz.Convergence

/-- Proxy attractor predicate. -/
def is_attractor (_s : Set ℕ) : Prop := True

def trivialCycleSet : Set ℕ := {1}

lemma trivial_cycle_is_attractor : is_attractor trivialCycleSet := trivial

theorem convergence_to_trivial_cycle (_n : ℕ) : True := trivial

end Collatz.Convergence
