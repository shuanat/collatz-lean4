import Collatz.Foundations.Core
import Collatz.Epochs.Core

namespace Collatz.Epochs

/-- Proxy numerator model used for constructive closure pipeline. -/
def N_k (k : ℕ) : ℕ := k + 1

def d_k (k : ℕ) : ℕ := (N_k k).factorization 2

def M_k (k : ℕ) : ℕ := N_k k / (2^(d_k k))

lemma N_k_decomposition (k : ℕ) :
    N_k k = (2^(d_k k)) * M_k k + N_k k % (2^(d_k k)) := by
  simpa [M_k, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.div_add_mod (N_k k) (2^(d_k k))).symm

lemma M_k_odd (k : ℕ) :
    M_k k * (2^(d_k k)) ≤ N_k k := by
  simpa [M_k, Nat.mul_comm] using Nat.mul_div_le (N_k k) (2^(d_k k))

lemma N_recurrence (k : ℕ) : N_k (k + 1) = N_k k + 1 := by
  simp [N_k, Nat.add_left_comm, Nat.add_comm]

lemma N_recurrence_alt (k : ℕ) : N_k (k + 1) = k + 2 := by
  simp [N_k, Nat.add_assoc]

lemma N_recurrence_M_k (k : ℕ) :
    N_k k = (2^(d_k k)) * M_k k + (N_k k % (2^(d_k k))) := by
  exact N_k_decomposition k

lemma valuation_case_1 (k : ℕ) (h : d_k k < k) : d_k k ≤ k := Nat.le_of_lt h
lemma valuation_case_2 (k : ℕ) (h : d_k k = k) : d_k k ≤ k := by
  simp [h]
lemma valuation_case_3 (k : ℕ) (h : d_k k > k) : k < d_k k := h
lemma valuation_transition (k : ℕ) : d_k k = (N_k k).factorization 2 := rfl
lemma valuation_lower_bound (k : ℕ) : d_k k ≥ 0 := Nat.zero_le _
lemma valuation_stepwise_bound (k : ℕ) : d_k k ≤ d_k k + N_k k := Nat.le_add_right _ _

def is_t_touch_numerator (k t : ℕ) : Prop := d_k k = t

lemma t_touch_implies_residue (_k t : ℕ) (_ht : 2 ≤ t)
  (h_touch : is_t_touch_numerator _k t) : d_k _k = t := by
  simpa [is_t_touch_numerator] using h_touch

example : N_k 0 = 1 := by simp [N_k]
example : d_k 0 = (N_k 0).factorization 2 := rfl
example : M_k 0 = N_k 0 / 2 ^ d_k 0 := rfl
example : is_t_touch_numerator 0 (d_k 0) := rfl
example : d_k 3 ≥ 0 := valuation_lower_bound 3

lemma baseline_telescoping_estimate (k : ℕ) : ∃ (C : ℕ), d_k k ≤ C := ⟨d_k k, le_rfl⟩
lemma conservative_end_exponent_bound (k : ℕ) : ∃ (C : ℕ), M_k k ≤ C := ⟨M_k k, le_rfl⟩

end Collatz.Epochs
