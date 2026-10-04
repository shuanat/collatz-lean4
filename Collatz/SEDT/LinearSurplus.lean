/-
Collatz Conjecture: SEDT Deep Formalization — Linear Surplus
(Appendix D.5 algebraic core)

This module implements the **algebraic core** of Proposition D.5
(Linear Surplus on long t-epochs).

**Setup.**  Fix abstract parameters `P, U ≥ 1` modeling
`P = Q_t = 2^{t-2}` and the refinement depth `U`.
On a tail of length `L`, three input estimates are available:

* (Touch Density, Lemma D.4)
    `N · P + P · P ≥ L`           (i.e. `N ≥ L/P − P` rearranged)

* (Multibit Bonus, Corollary D.2 / period-level identity)
    `B · 2^U ≥ N · (2^U − 1)`     (average bonus per touch ≥ 1 − 2^{−U})

Here `N` is the number of t-touches and `B` is the cumulative
multibit bonus on the tail.

**Conclusion.**  Cross-multiplying gives the clean integer
*linear surplus* inequality

    `B · 2^U · P ≥ (2^U − 1) · L − (2^U − 1) · P · P`,

equivalently `e*(L) ≥ (α − 1) · L − C` with

    `α − 1 = (1 − 2^{−U}) / Q_t,  C = (1 − 2^{−U}) · Q_t`.

The orbit-side estimates `N · P + P² ≥ L` and `B · 2^U ≥ N · (2^U − 1)`
are supplied by `TouchDensity.lean` and `MultibitBonus.lean`
respectively (after the periodicity layer is closed); the present
module assembles them into the final linear bound.
-/

import Mathlib.Tactic

namespace Collatz.SEDT.LinearSurplus

/-- **Abstract linear surplus combiner.**

Given:
  *  `P U L N B : ℕ` with `P ≥ 1` and `U ≥ 1`,
  *  Touch density: `N * P + P * P ≥ L`,
  *  Multibit bonus: `B * 2 ^ U ≥ N * (2 ^ U - 1)`,

then the cumulative bonus satisfies the linear surplus bound

    `B * 2 ^ U * P + (2 ^ U - 1) * P * P ≥ (2 ^ U - 1) * L`.

This is the integer-arithmetic form of

    `e*(L) ≥ (1 − 2^{−U}) · (L / Q_t − Q_t)`,

cross-multiplied through by `Q_t` and `2^U`. -/
theorem linear_surplus
    (P U L N B : ℕ) (hP : 1 ≤ P) (hU : 1 ≤ U)
    (hTouch : N * P + P * P ≥ L)
    (hBonus : B * 2 ^ U ≥ N * (2 ^ U - 1)) :
    B * 2 ^ U * P + (2 ^ U - 1) * P * P ≥ (2 ^ U - 1) * L := by
  -- multiply touch density by `(2^U - 1)`
  have h1 : (2 ^ U - 1) * (N * P + P * P) ≥ (2 ^ U - 1) * L :=
    Nat.mul_le_mul_left _ hTouch
  -- multiply bonus by `P`
  have h2 : B * 2 ^ U * P ≥ N * (2 ^ U - 1) * P :=
    Nat.mul_le_mul_right _ hBonus
  -- chain the estimates
  have hexpand : (2 ^ U - 1) * (N * P + P * P)
                  = N * (2 ^ U - 1) * P + (2 ^ U - 1) * P * P := by ring
  rw [hexpand] at h1
  -- B * 2^U * P + (2^U - 1)*P*P ≥ N * (2^U - 1) * P + (2^U - 1)*P*P ≥ (2^U-1)*L
  have h3 : B * 2 ^ U * P + (2 ^ U - 1) * P * P
              ≥ N * (2 ^ U - 1) * P + (2 ^ U - 1) * P * P :=
    Nat.add_le_add_right h2 _
  exact le_trans h1 h3

/-- **Long-tail regime.** When `L ≥ 2 * P * P`, the boundary loss
`(2^U - 1) * P * P` is at most `(2^U - 1) * L / 2`, hence

    `B * 2^U * P ≥ (2^U - 1) * L / 2`.

This is the simplest "linear in L" reformulation; for a sharper
constant one keeps `(2^U - 1) * P * P` as an additive correction
(matching the paper's `C(t, U) ≤ (1 - 2^{-U}) Q_t`). -/
theorem linear_surplus_long
    (P U L N B : ℕ) (hP : 1 ≤ P) (hU : 1 ≤ U)
    (hLong : L ≥ 2 * P * P)
    (hTouch : N * P + P * P ≥ L)
    (hBonus : B * 2 ^ U ≥ N * (2 ^ U - 1)) :
    2 * (B * 2 ^ U * P) ≥ (2 ^ U - 1) * L := by
  have hcore := linear_surplus P U L N B hP hU hTouch hBonus
  -- Abstract the nonlinear monomials so omega can finish.
  set X := B * 2 ^ U * P
  set Y := (2 ^ U - 1) * P * P
  set Z := (2 ^ U - 1) * L
  -- From `hLong : L ≥ 2 * P * P`, multiply by `(2^U - 1)`:
  have hPL : 2 * Y ≤ Z := by
    have : (2 ^ U - 1) * (2 * P * P) ≤ (2 ^ U - 1) * L :=
      Nat.mul_le_mul_left _ hLong
    have heq : (2 ^ U - 1) * (2 * P * P) = 2 * Y := by
      simp only [Y]; ring
    rw [heq] at this
    exact this
  -- `hcore : X + Y ≥ Z` (after abstraction).
  have hcore' : Z ≤ X + Y := hcore
  omega

end Collatz.SEDT.LinearSurplus
