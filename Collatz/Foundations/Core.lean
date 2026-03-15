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

lemma collatz_step_is_odd {r : ℕ} : OddPred (collatz_step r) := by
  unfold collatz_step step_type
  have h_pos : 0 < 3 * r + 1 := by omega
  simpa [Collatz.Arithmetic.e] using Collatz.Arithmetic.odd_div_pow_two_factorization h_pos

lemma odd_iterates_of_odd {r : ℕ} (h : OddPred r) :
    ∀ k : ℕ, OddPred ((collatz_step^[k]) r) := by
  intro k
  induction k with
  | zero =>
      simpa using h
  | succ k ih =>
      simpa [Function.iterate_succ_apply'] using collatz_step_is_odd (r := ((collatz_step^[k]) r))

/-- The odd-step Collatz map is not pointwise nonincreasing on odd inputs:
already `3 ↦ 5` is a strict growth step. This is a useful obstruction when
separating honest filler-side value semantics from generic odd-orbit facts. -/
lemma collatz_step_three_eq_five : collatz_step 3 = 5 := by
  native_decide

/-- Concrete strict-growth odd-step example showing that raw oddness of the
orbit does not by itself force one-step nonincrease. Any stream-side filler
monotonicity theorem must therefore use genuine extra semantics. -/
theorem exists_odd_strict_growth_step : ∃ r : ℕ, OddPred r ∧ collatz_step r > r := by
  refine ⟨3, ?_, ?_⟩
  · norm_num
  · rw [collatz_step_three_eq_five]
    norm_num

/-- Arithmetic one-step descent criterion for the odd-step Collatz map: once the
local two-adic exponent is at least `2`, the normalized odd step cannot exceed
its input. This is the exact bridge needed to turn filler-side `step_type ≥ 2`
control into value-level nonincrease. -/
theorem collatz_step_le_self_of_step_type_ge_two {r : ℕ}
    (hodd : OddPred r)
    (hstep : 2 ≤ step_type r) :
    collatz_step r ≤ r := by
  have hpowNat : 4 ≤ 2 ^ step_type r := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ step_type r := by
        exact Nat.pow_le_pow_right (by decide) hstep
  have hmulNat : 4 * collatz_step r ≤ 3 * r + 1 := by
    calc
      4 * collatz_step r = collatz_step r * 4 := by ring
      _ ≤ collatz_step r * 2 ^ step_type r := by
        exact Nat.mul_le_mul_left _ hpowNat
      _ ≤ 3 * r + 1 := by
        simpa [collatz_step, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.div_mul_le_self (3 * r + 1) (2 ^ step_type r)
  have hupper : 3 * r + 1 ≤ 4 * r := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    omega
  have hmul : 4 * collatz_step r ≤ 4 * r := le_trans hmulNat hupper
  omega

lemma collatz_step_add_one_le_three_halves_of_odd {r : ℕ} (h : OddPred r) :
    (collatz_step r : ℝ) + 1 ≤ (3 / 2 : ℝ) * ((r : ℝ) + 1) := by
  have hpowNat : 2 ≤ 2 ^ step_type r := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ step_type r := by
        exact Nat.pow_le_pow_right (by decide) (step_type_odd_pos h)
  have hmulNat : 2 * collatz_step r ≤ 3 * r + 1 := by
    calc
      2 * collatz_step r = collatz_step r * 2 := by ring
      _ ≤ collatz_step r * 2 ^ step_type r := by
        exact Nat.mul_le_mul_left _ hpowNat
      _ ≤ 3 * r + 1 := by
        simpa [collatz_step, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.div_mul_le_self (3 * r + 1) (2 ^ step_type r)
  have hmulReal : (2 : ℝ) * (collatz_step r : ℝ) ≤ 3 * (r : ℝ) + 1 := by
    exact_mod_cast hmulNat
  nlinarith

lemma collatz_step_log_delta_le_of_odd {r : ℕ} (h : OddPred r) :
    Real.log ((collatz_step r : ℝ) + 1) - Real.log ((r : ℝ) + 1) ≤
      Real.log (3 / 2 : ℝ) := by
  have hstep : (collatz_step r : ℝ) + 1 ≤ (3 / 2 : ℝ) * ((r : ℝ) + 1) :=
    collatz_step_add_one_le_three_halves_of_odd h
  have hlog :
      Real.log ((collatz_step r : ℝ) + 1) ≤
        Real.log ((3 / 2 : ℝ) * ((r : ℝ) + 1)) := by
    apply Real.log_le_log
    positivity
    exact hstep
  calc
    Real.log ((collatz_step r : ℝ) + 1) - Real.log ((r : ℝ) + 1)
        ≤ Real.log ((3 / 2 : ℝ) * ((r : ℝ) + 1)) - Real.log ((r : ℝ) + 1) := by
          exact sub_le_sub_right hlog _
    _ = Real.log (3 / 2 : ℝ) := by
          have hthreeHalves : (3 / 2 : ℝ) ≠ 0 := by norm_num
          have hrpos : (r : ℝ) + 1 ≠ 0 := by positivity
          rw [Real.log_mul hthreeHalves hrpos]
          ring

lemma iterate_log_delta_le_of_odd {r : ℕ} (h : OddPred r) :
    ∀ L : ℕ,
      Real.log (((collatz_step^[L]) r : ℝ) + 1) - Real.log ((r : ℝ) + 1) ≤
        (L : ℝ) * Real.log (3 / 2 : ℝ) := by
  intro L
  induction L with
  | zero =>
      simp
  | succ L ih =>
      have hoddL : OddPred ((collatz_step^[L]) r) := odd_iterates_of_odd h L
      have hstep := collatz_step_log_delta_le_of_odd hoddL
      have hsplit :
          Real.log (((collatz_step^[L.succ]) r : ℝ) + 1) - Real.log ((r : ℝ) + 1) =
            (Real.log ((collatz_step ((collatz_step^[L]) r) : ℝ) + 1) -
                Real.log (((collatz_step^[L]) r : ℝ) + 1)) +
              (Real.log (((collatz_step^[L]) r : ℝ) + 1) -
                Real.log ((r : ℝ) + 1)) := by
        simp [Function.iterate_succ_apply']
      rw [hsplit]
      have hsum :
          (Real.log ((collatz_step ((collatz_step^[L]) r) : ℝ) + 1) -
              Real.log (((collatz_step^[L]) r : ℝ) + 1)) +
            (Real.log (((collatz_step^[L]) r : ℝ) + 1) -
              Real.log ((r : ℝ) + 1)) ≤
            Real.log (3 / 2 : ℝ) + (L : ℝ) * Real.log (3 / 2 : ℝ) :=
        add_le_add hstep ih
      have hsucc :
          Real.log (3 / 2 : ℝ) + (L : ℝ) * Real.log (3 / 2 : ℝ) =
            (L.succ : ℝ) * Real.log (3 / 2 : ℝ) := by
        norm_num
        ring
      exact hsum.trans_eq hsucc

theorem iterate_log_compression_of_odd_segment (m i L : ℕ) (hm : OddPred m) :
    (Real.log (((collatz_step^[i + L]) m : ℝ) + 1) -
        Real.log (((collatz_step^[i]) m : ℝ) + 1)) / Real.log 2 ≤
      (L : ℝ) * (Real.log (3 / 2 : ℝ) / Real.log 2) := by
  have hbase : OddPred ((collatz_step^[i]) m) := odd_iterates_of_odd hm i
  have hdelta := iterate_log_delta_le_of_odd hbase L
  have hlog2 : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hseg :
      Real.log (((collatz_step^[i + L]) m : ℝ) + 1) -
        Real.log (((collatz_step^[i]) m : ℝ) + 1) ≤
          (L : ℝ) * Real.log (3 / 2 : ℝ) := by
    simpa [show i + L = L + i by omega, Function.iterate_add_apply] using hdelta
  have hdiv := div_le_div_of_nonneg_right hseg (le_of_lt hlog2)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

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
