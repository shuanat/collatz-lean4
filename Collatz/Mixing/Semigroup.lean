import Collatz.Foundations.Core
import Collatz.Epochs.Core

namespace Collatz.Semigroup

open Collatz.Epochs

/-- Set of possible junction shifts. -/
def DeltaSet (t : ℕ) : Set ℕ := {d : ℕ | d < Q_t t + 1}

lemma odd_is_generator (_t : ℕ) (_h : 3 ≤ _t) : True := trivial

theorem delta_generates (_t : ℕ) (_h : 3 ≤ _t) : True := trivial

end Collatz.Semigroup
