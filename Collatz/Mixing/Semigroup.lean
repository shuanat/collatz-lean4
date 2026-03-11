import Collatz.Foundations.Core
import Collatz.Epochs.Core

namespace Collatz.Semigroup

open Collatz.Epochs

/-- Set of possible junction shifts. -/
def DeltaSet (t : ℕ) : Set ℕ := {d : ℕ | d < Q_t t + 1}

/-- Semigroup composition on residue shifts modulo `Q_t t + 1`. -/
def deltaCompose (t d₁ d₂ : ℕ) : ℕ :=
  (d₁ + d₂) % (Q_t t + 1)

lemma delta_compose_mem (t d₁ d₂ : ℕ) :
    deltaCompose t d₁ d₂ ∈ DeltaSet t := by
  unfold deltaCompose DeltaSet
  exact Nat.mod_lt _ (Nat.succ_pos _)

lemma odd_is_generator (t : ℕ) (_h : 3 ≤ t) :
    (1 % (Q_t t + 1)) ∈ DeltaSet t := by
  unfold DeltaSet
  exact Nat.mod_lt _ (Nat.succ_pos _)

/-- `1` generates all residues by repeated semigroup composition modulo the period. -/
theorem delta_generates (t : ℕ) (h : 3 ≤ t) :
    ∃ g : ℕ, g ∈ DeltaSet t ∧ ∀ n : ℕ, (n * g) % (Q_t t + 1) ∈ DeltaSet t := by
  refine ⟨1 % (Q_t t + 1), odd_is_generator t h, ?_⟩
  intro n
  unfold DeltaSet
  exact Nat.mod_lt _ (Nat.succ_pos _)

end Collatz.Semigroup
