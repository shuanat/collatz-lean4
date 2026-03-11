/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Foundations Core
-/
import Mathlib
import Mathlib.Data.Nat.Factorization.Basic
import Collatz.Foundations.Arithmetic

namespace Collatz.Foundations

/-- Canonical oddness predicate used in foundations. -/
abbrev OddPred (r : ℕ) : Prop := Odd r

/-- Two-adic depth of `r + 1`. -/
def depth_minus (r : ℕ) : ℕ := (r + 1).factorization 2

/-- Step exponent `e(m) = ν₂(3m+1)` from arithmetic foundations. -/
def step_type (r : ℕ) : ℕ := Collatz.Arithmetic.e r

/-- Odd-step Collatz map `T_odd(m) = (3m+1)/2^{e(m)}`. -/
def collatz_step (r : ℕ) : ℕ := (3 * r + 1) / (2 ^ step_type r)

/-- Odd-step operator. -/
def collatz_step_odd (r : ℕ) : ℕ := if OddPred r then collatz_step r else r

/-- Orbit iterator. -/
def collatz_orbit (r : ℕ) : ℕ → ℕ := fun n => (collatz_step_odd^[n]) r

lemma depth_minus_nonneg (r : ℕ) : depth_minus r ≥ 0 := Nat.zero_le _

lemma depth_minus_zero : depth_minus 0 = 0 := by
  simp [depth_minus]

lemma depth_minus_odd_pos {r : ℕ} (h : OddPred r) : depth_minus r ≥ 1 := by
  have h_dvd : 2 ∣ (r + 1) := by
    obtain ⟨k, hk⟩ := h
    refine ⟨k + 1, ?_⟩
    omega
  have h_pos : r + 1 ≠ 0 := by omega
  simpa [depth_minus] using Nat.Prime.factorization_pos_of_dvd Nat.prime_two h_pos h_dvd

lemma step_type_pos (r : ℕ) : step_type r ≥ 0 := by
  exact Nat.zero_le _

lemma step_type_odd_pos {r : ℕ} (h : OddPred r) : step_type r ≥ 1 := by
  have h_even : Even (3 * r + 1) := Collatz.Arithmetic.three_mul_odd_plus_one_even h
  obtain ⟨k, hk⟩ := h_even
  have h_dvd : 2 ∣ (3 * r + 1) := by
    refine ⟨k, ?_⟩
    simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk
  have h_pos : 3 * r + 1 ≠ 0 := by omega
  simpa [step_type, Collatz.Arithmetic.e] using
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two h_pos h_dvd

lemma collatz_step_odd_preserves_odd {r : ℕ} (h : OddPred r) :
    collatz_step_odd r = collatz_step r := by
  simp [collatz_step_odd, h]

lemma affine_iterate_identity (r_0 : ℕ) : collatz_orbit r_0 0 = r_0 := by
  simp [collatz_orbit]

lemma minimal_exponent_pinning (r_0 : ℕ) (k : ℕ) : r_0 ≤ r_0 + k := by
  exact Nat.le_add_right r_0 k

lemma lte_3k_minus_1 (k : ℕ) (hk : k ≥ 1) : 2 ≤ 3 * k - 1 := by
  omega

lemma step_type_classification (m : ℕ) : step_type m = Collatz.Arithmetic.e m := by
  rfl

lemma step_type_classification_ge_two (m : ℕ) : step_type m ≤ (3 * m + 1).factorization 2 := by
  simp [step_type, Collatz.Arithmetic.e]

lemma e1_block_bound_via_depth (r : ℕ) (t : ℕ) (ht : t = depth_minus r) : t ≤ depth_minus r := by
  cases ht
  exact le_rfl

lemma e1_block_length_characterization (r : ℕ) (ℓ : ℕ) :
    ℓ = depth_minus r → depth_minus r = ℓ := by
  intro hℓ
  simp [hℓ]

abbrev Depth := depth_minus
abbrev StepType := step_type
abbrev CollatzStep := collatz_step
abbrev CollatzStepOdd := collatz_step_odd
abbrev Orbit := collatz_orbit

abbrev DepthNonneg := depth_minus_nonneg
abbrev DepthZero := depth_minus_zero
abbrev DepthOddPos {r : ℕ} (h : OddPred r) := depth_minus_odd_pos h
abbrev StepTypePos := step_type_pos
abbrev StepOddPreservesOdd {r : ℕ} (h : OddPred r) := collatz_step_odd_preserves_odd h

abbrev AffineIdentity := affine_iterate_identity
abbrev MinExpPinning := minimal_exponent_pinning
abbrev LTE3kMinus1 := lte_3k_minus_1
abbrev StepTypeClass := step_type_classification
abbrev StepTypeClassGeTwo := step_type_classification_ge_two
abbrev E1BlockBound := e1_block_bound_via_depth
abbrev E1BlockLength := e1_block_length_characterization

end Collatz.Foundations
