/-
Linear-surplus combiner (generic integer inequality).

For naturals `P, U ≥ 1` and `L, N, B`:
if `N·P + P·P ≥ L` and `B·2^U ≥ N·(2^U − 1)`, then
`B·2^U·P + (2^U − 1)·P·P ≥ (2^U − 1)·L`.

Status (2026-10 review). This is a correct *lower* bound on `B` in terms of `L`.
It does **not** discharge the depth-bookkeeping residual of the former SEDT
chain, which required an *upper* bound on the orbit's multibit gain
(`multibit_gain_on_orbit ≤ budget`, see `OrbitDepth`). Moreover the two
hypotheses are not established for Collatz orbits: in the paper they come from
the auxiliary sequence `(N_k)` (`TouchDensity`, `MultibitBonus`). The paper's
use of this bound inside the proof of E.2 (a lower bound substituted where an
upper bound is needed) is one of the errors behind the withdrawal of E.2.
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

Equivalently `B ≥ (1 − 2^{−U}) · (L / P − P)` (a lower bound on `B`). -/
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

Again a lower bound on `B`. -/
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
