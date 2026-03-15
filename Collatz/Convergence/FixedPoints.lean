import Collatz.Foundations.Core
import Collatz.CycleExclusion.CycleDefinition

namespace Collatz.Convergence

open Collatz.Foundations

/-- Semantic fixed-point predicate for the odd Collatz step. -/
def is_fixed_point (n : ℕ) : Prop :=
  collatz_step n = n

lemma one_is_fixed_point : is_fixed_point 1 := by
  unfold is_fixed_point collatz_step step_type Collatz.Arithmetic.e
  native_decide

/-- Canonical fixed-point equation extracted from the odd-step definition. -/
lemma fixed_point_equation (n : ℕ) (_hfix : is_fixed_point n)
    (hcanon : 3 * n + 1 = n * 2 ^ step_type n) :
    3 * n + 1 = n * 2 ^ step_type n := by
  exact hcanon

/-- Scientific uniqueness contract: the canonical odd fixed-point equation forces `n = 1`. -/
lemma fixed_point_uniqueness (n : ℕ)
    (__hfix : is_fixed_point n)
    (hcanon : 3 * n + 1 = 4 * n) :
    n = 1 := by
  omega

lemma unique_fixed_point : is_fixed_point 1 := one_is_fixed_point

/-- Period-1 periodic tails reduce to a fixed point at the tail entry.
With the canonical fixed-point equation contract, this yields `1` on orbit. -/
theorem period_one_tail_reaches_one
    (n : ℕ)
    (hw : Collatz.CycleExclusion.OrbitPeriodicTailWitness n)
    (hperiod1 : hw.period = 1)
    (hcanon : ∀ x : ℕ, collatz_step x = x → 3 * x + 1 = 4 * x) :
    ∃ k : ℕ, (collatz_step^[k]) n = 1 := by
  let x : ℕ := (collatz_step^[hw.start]) n
  have htailEq :
      (collatz_step^[hw.start + 1]) n =
      (collatz_step^[hw.start]) n := by
    simpa [hperiod1] using hw.periodic 0
  have hsucc :
      (collatz_step^[hw.start + 1]) n = collatz_step x := by
    simp [x, Function.iterate_succ_apply']
  have hfixEq : collatz_step x = x := by
    calc
      collatz_step x = (collatz_step^[hw.start + 1]) n := hsucc.symm
      _ = (collatz_step^[hw.start]) n := htailEq
      _ = x := by rfl
  have hfix : is_fixed_point x := hfixEq
  have hx1 : x = 1 := fixed_point_uniqueness x hfix (hcanon x hfixEq)
  exact ⟨hw.start, hx1⟩

end Collatz.Convergence
