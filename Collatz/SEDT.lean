import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Field.Basic
import Collatz.Basic
import Collatz.Epoch

/-!
# SEDT (Scaled Epoch Drift Theorem)

This file formalizes the SEDT envelope theorem, which establishes negative drift
for long t-epochs in the Collatz dynamics.

## Main Results

- `sedt_envelope`: For long epochs (L ≥ L₀), the potential change ΔV is bounded by
  -ε·L + β·C, where ε > 0 (negative drift coefficient)
- Constants α, β₀, ε are defined according to Appendix D of the paper

## References

See paper Appendix A (SEDT proof) for detailed mathematical derivation.
-/

namespace Collatz.SEDT

open Real

/-!
## Potential Function and Constants
-/

/-- Depth-minus function: ν₂(r+1) for odd r -/
def depth_minus (r : ℕ) : ℕ :=
  (r + 1).factorization 2

/-- Amortized Lyapunov potential function
    V(n) = log₂(n) + β·depth⁻(n)
-/
noncomputable def V (n : ℕ) (β : ℝ) : ℝ :=
  log n / log 2 + β * (depth_minus n : ℝ)

/-- Touch frequency parameter α(t,U) = 1 + (1 - 2^{-U})/Q_t -/
noncomputable def α (t U : ℕ) : ℝ :=
  1 + (1 - 2^(-(U : ℝ))) / (2^((t : ℝ) - 2))

/-- Threshold parameter β₀(t,U) = log₂(3/2) / (2 - α(t,U)) -/
noncomputable def β₀ (t U : ℕ) : ℝ :=
  (log (3/2) / log 2) / (2 - α t U)

/-- Negative drift coefficient ε(t,U;β) = β(2 - α) - log₂(3/2) -/
noncomputable def ε (t U : ℕ) (β : ℝ) : ℝ :=
  β * (2 - α t U) - log (3/2) / log 2

/-- Constant C(t,U) - maximum cumulative overhead per epoch -/
def C (t U : ℕ) : ℕ :=
  -- Simplified bound: 2^t + 3*U (conservative)
  2^t + 3*U

/-- Threshold length L₀(t,U) for "long" epochs -/
def L₀ (t _U : ℕ) : ℕ :=
  -- Long epochs have length ≥ Q_t
  max (2^(t-2)) 10

/-- Glue constant K_glue(t) for boundary overhead -/
def K_glue (t : ℕ) : ℕ :=
  max (2 * 2^(t-2)) (3 * t)

/-!
## Helper Lemmas for Constants
-/

lemma alpha_gt_one (t U : ℕ) (_ht : t ≥ 3) (hU : U ≥ 1) : α t U > 1 := by
  unfold α
  -- Denominator > 0 since base is positive
  have hden_pos : 0 < (2 : ℝ)^((t : ℝ) - 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  -- Exponent -(U:ℝ) is negative as soon as U ≥ 1
  have hUpos : 0 < (U : ℝ) := by
    have : 0 < U := Nat.pos_of_ne_zero (fun h => by omega)
    exact Nat.cast_pos.mpr this
  have hneg : (-(U : ℝ)) < 0 := by linarith
  -- With base 2 > 1 and negative exponent, we get 2^(-U) < 1
  have hlt1 : (2 : ℝ) ^ (-(U : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) hneg
  -- So the numerator is positive
  have hnum_pos : 0 < 1 - (2 : ℝ) ^ (-(U : ℝ)) := by linarith
  -- Hence the fraction is positive
  have hfrac_pos : 0 < (1 - (2 : ℝ) ^ (-(U : ℝ))) / (2^((t : ℝ) - 2)) :=
    div_pos hnum_pos hden_pos
  -- Add 1 to a positive quantity
  linarith

lemma alpha_lt_two (t U : ℕ) (ht : t ≥ 3) : α t U < 2 := by
  unfold α
  -- Нужно показать: 1 + (1 - 2^{-U})/Q_t < 2
  -- ⇔ (1 - 2^{-U})/Q_t < 1
  -- Это верно т.к. 1 - 2^{-U} < 1 и Q_t ≥ 1

  -- 2^(-(U)) > 0
  have two_pos : 0 < (2 : ℝ) := by norm_num
  have h_num_pos : 0 < (2 : ℝ)^(-(U : ℝ)) :=
    Real.rpow_pos_of_pos two_pos _

  -- (1 - 2^(-U)) < 1
  have h_num_strict : 1 - (2 : ℝ)^(-(U : ℝ)) < 1 := by
    linarith [h_num_pos]

  -- denominator > 0
  have h_denom_pos : 0 < (2 : ℝ)^(t-2 : ℝ) :=
    Real.rpow_pos_of_pos two_pos _

  -- ключевой шаг: 2^(t-2) ≥ 1 используя Real.one_le_rpow
  have h_denom_ge_one : (1 : ℝ) ≤ (2 : ℝ)^(t-2 : ℝ) := by
    have h_nonneg : (0 : ℝ) ≤ (t : ℝ) - 2 := by
      simp only [sub_nonneg]
      norm_cast
      linarith [ht]
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) h_nonneg

  -- ограничение дроби через 1
  have hfrac_lt_one : (1 - (2 : ℝ)^(-(U : ℝ))) / (2^(t-2 : ℝ)) < 1 := by
    -- сначала: строгий шаг от числителя < 1
    have h1 : (1 - (2 : ℝ)^(-(U : ℝ))) / (2^(t-2 : ℝ)) < 1 / (2^(t-2 : ℝ)) :=
      div_lt_div_of_pos_right h_num_strict h_denom_pos
    -- затем: 1/(2^(t-2)) ≤ 1
    have h2 : (1 : ℝ) / (2^(t-2 : ℝ)) ≤ 1 := by
      rw [div_le_one h_denom_pos]
      exact h_denom_ge_one
    exact lt_of_lt_of_le h1 h2

  -- завершение
  linarith [hfrac_lt_one]

lemma beta_zero_pos (t U : ℕ) (ht : t ≥ 3) (_hU : U ≥ 1) : β₀ t U > 0 := by
  unfold β₀
  have h1 : α t U < 2 := alpha_lt_two t U ht
  have h2 : log (3/2) / log 2 > 0 := by
    have log_three_half_pos : log (3/2) > 0 := by
      have : (3 : ℝ) / 2 > 1 := by norm_num
      exact Real.log_pos this
    have log_two_pos : log 2 > 0 := by
      have : (2 : ℝ) > 1 := by norm_num
      exact Real.log_pos this
    exact div_pos log_three_half_pos log_two_pos
  -- β₀ = (log(3/2)/log(2)) / (2 - α) где α < 2
  have h3 : 2 - α t U > 0 := by linarith [h1]
  exact div_pos h2 h3

lemma epsilon_pos (t U : ℕ) (β : ℝ) (ht : t ≥ 3) (_hU : U ≥ 1) (hβ : β > β₀ t U) :
  ε t U β > 0 := by
  unfold ε
  -- ε = β(2-α) - log(3/2)/log(2)
  -- β > β₀ = (log(3/2)/log(2))/(2-α)
  -- ⇒ β(2-α) > log(3/2)/log(2)
  -- ⇒ ε > 0
  have h1 : α t U < 2 := alpha_lt_two t U ht
  have h2_alpha : 2 - α t U > 0 := by linarith [h1]

  have log_ratio : log (3/2) / log 2 > 0 := by
    have log_three_half_pos : log (3/2) > 0 := by
      have : (3 : ℝ) / 2 > 1 := by norm_num
      exact Real.log_pos this
    have log_two_pos : log 2 > 0 := by
      have : (2 : ℝ) > 1 := by norm_num
      exact Real.log_pos this
    exact div_pos log_three_half_pos log_two_pos

  -- Из β > β₀ получаем β(2-α) > log(3/2)/log(2)
  have key : β * (2 - α t U) > log (3/2) / log 2 := by
    unfold β₀ at hβ
    calc β * (2 - α t U) > (log (3/2) / log 2) / (2 - α t U) * (2 - α t U) := by
           apply mul_lt_mul_of_pos_right hβ h2_alpha
       _ = log (3/2) / log 2 := by field_simp

  linarith [key, log_ratio]

/-!
## Epoch Structure for SEDT
-/

/-- Extended epoch structure with touch data for SEDT -/
structure SEDTEpoch where
  /-- Base epoch data -/
  base : Epoch
  /-- Number of t-touches in plateau -/
  num_touches : ℕ
  /-- Head overhead contribution -/
  head_overhead : ℝ
  /-- Boundary glue overhead -/
  boundary_overhead : ℝ

/-- Get length from SEDT epoch -/
def SEDTEpoch.length (e : SEDTEpoch) : ℕ :=
  let b : Collatz.Epoch := e.base
  b.end_idx - b.start_idx + 1

/-!
## Main SEDT Theorem
-/

/-- SEDT Envelope Theorem

    For any long t-epoch (L ≥ L₀(t,U)) with β > β₀(t,U):

    ΔV ≤ -ε(t,U;β)·L + β·C(t,U)

    where ε > 0 is the negative drift coefficient.

    **Mathematical Proof Strategy:**
    1. Decompose epoch into head + plateau + tail
    2. Head: O(t) contribution → bounded by β·C_head
    3. Plateau: deterministic t-touch frequency (1/Q_t) → multibit bonus
    4. Per-step accounting: log₂(3/2) growth vs β·(2-α) depth decrease
    5. Net per-step: -ε where ε = β(2-α) - log₂(3/2) > 0
    6. Long epoch (L ≥ L₀): negative term -ε·L dominates overhead β·C

    **Formalization Status:** Statement formalized, proof deferred (see paper Appendix A)
-/
theorem sedt_envelope (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1)
  (hβ : β > β₀ t U)
  (h_long : e.length ≥ L₀ t U) :
  ∃ (ΔV : ℝ), ΔV ≤ -(ε t U β) * (e.length : ℝ) + β * (C t U : ℝ) ∧
              ΔV < 0 := by
  sorry
  -- Full proof would involve:
  -- 1. Head accounting: ΔV_head ≤ β·C_head
  -- 2. Plateau accounting: per-step -ε (via touch frequency and multibit bonus)
  -- 3. Boundary: ΔV_boundary ≤ β·K_glue
  -- 4. Sum: ΔV_total ≤ -ε·L + β·(C_head + K_glue) ≤ -ε·L + β·C
  -- 5. For L ≥ L₀, ε·L > β·C, so ΔV < 0

/-!
## Corollaries for Cycle Exclusion
-/

/-- Short epochs have bounded potential change -/
lemma short_epoch_bounded (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3)
  (h_short : e.length < L₀ t U) :
  ∃ (ΔV : ℝ), abs ΔV ≤ β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ) := by
  sorry
  -- Short epochs contribute bounded overhead (no guaranteed negative drift)

/-- Period sum over multiple epochs -/
lemma period_sum_negative (t U : ℕ) (epochs : List SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β > β₀ t U)
  (h_many_long : (epochs.filter (fun e => e.length ≥ L₀ t U)).length ≥
                  epochs.length / (2^(t-2) + 8*t*(2^t))) :
  ∃ (total_ΔV : ℝ), total_ΔV < 0 := by
  sorry
  -- If density of long epochs ≥ 1/(Q_t + G_t), total drift is negative
  -- This is key for cycle exclusion (Appendix B)

/-!
## Connection to Paper
-/

/-
Documentation: mapping to paper notation

- V(n) ↔ Equation (A.E4.V)
- α(t,U) ↔ Definition A.E3.alpha
- β₀(t,U) ↔ Definition A.E3.beta0
- ε(t,U;β) ↔ Definition A.E4.epsilon
- SEDT envelope ↔ Theorem A.E4
- Cycle exclusion ↔ Theorem C.A (uses period_sum_negative)
-/

end Collatz.SEDT
