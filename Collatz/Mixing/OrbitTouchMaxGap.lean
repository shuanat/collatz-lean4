/-
Collatz Conjecture: Wave 2J Pass-2c (B1) — typed orbit-side max-gap
residual and discharge of `R-OrbitSideAggregateTouchRate` from it.

# Background

Wave 2J explored an alternative orbit-side route to
`R-OrbitSideAggregateTouchRate` (defined in
`Collatz/Mixing/AggregateTouchRate.lean`) that **bypasses** the
primitive-junction route from Wave 2H Phase B
(`Collatz/Mixing/OrbitAdmissibleSupplyFromF3.lean`) and its open
dependencies on `R-F3-Recurrence` and the structural lemma F.4.1.

The route under investigation is the **deterministic max-gap** of
consecutive `t`-touches along an orbit (variant B1(ii) in
`research/wave2j-pass2c-b1-maxgap/STATEMENT.md` §2.2): there exist
universal constants `C` and a per-`t` threshold `K_t(n)` such that any
two consecutive `t`-touches `i < j` past `K_t(n)` satisfy
`j − i ≤ C · Q_t`. Variant B1(ii) is strictly weaker than B1(i)
(absolute linear) and stronger than the polylog variant B1(iii). It is
the smallest variant that yields W-B with a `t`-uniform `ε` (cf.
`STATEMENT.md` §2.3 for why polylog forces `ε(t)`).

Stage 3.D verdict (`research/wave2j-pass2c-b1-maxgap/ATTEMPT.md`):
**`BLOCKED`.** Each of four standard analytical branches reaches an
explicit obstruction:

* Krasikov–Lagarias touch-carrier patterns are too sparse on a single
  orbit segment to force a touch within `C · Q_t` steps.
* No effective spectral gap is known for the 2-adic Collatz transfer
  operator, blocking Erdős–Turán + character-sum approaches.
* Recurrence-shift pigeonhole alphabet is `2^{2t}`, too large by a
  factor of 40–100 relative to the empirical bound `25 · Q_t`.
* Tao 2019 entropy gives only a density-1 statement; eliminating the
  exceptional set is itself Collatz-hard.

Empirical support for B1(ii) remains **strong** (Stage 3.B):
1.1 M observed gaps across 16K orbits, `t ∈ {3..12}`, never exceed
`25 · Q_t`; `max/Q_t` is monotonically decreasing in `t`. So B1(ii)
is mathematically plausible but **currently unproven**, and we encode
it as an honest typed open math residual.

# Why land this stub even with `BLOCKED` Stage 3.D

The typed residual + bridge theorem are pure bookkeeping (axiom-clean,
no new sorries beyond those already inside the residual itself). They
serve as **alternative entry points** if any of the four blocked
analytical branches re-opens (cf. `ATTEMPT.md` §8 for the four
unblocking conditions). Landing the stub now records the
formal-first design of the alternative route and avoids re-doing the
type-design work in a future wave.

This module is **independent** of `Collatz/Mixing/OrbitAdmissibleSupplyFromF3.lean`:
it provides a **second** discharge route for
`R-OrbitSideAggregateTouchRate` that does not consume
`PrimitiveJunctionRecurrenceWitness` and does not depend on F.3 or
F.4.1.

# Module contents

* `OrbitTouchMaxGapWitness n` — typed witness for B1(ii) along the
  actual Collatz orbit of `n`: a universal constant `C`, a per-`t`
  threshold `K_t`, a per-`t` strictly mono sequence of touches starting
  past `K_t`, with consecutive gaps `≤ C · Q_t`, and the W-B aggregate
  inequality recorded as a witness field.

* `OrbitTouchMaxGapResidual n` — the typed residual
  `1 ≤ n → ¬ orbit_eventually_periodic n → Nonempty (witness)`. **OPEN
  MATH RESIDUAL** per `unconditional-discipline.mdc` rule 1; encodes
  the B1(ii) conjecture from `research/wave2j-pass2c-b1-maxgap/STATEMENT.md`.

* `orbitSideAggregateTouchRate_of_orbitTouchMaxGap` — the discharge:
  `R-OrbitTouchMaxGap ⇒ R-OrbitSideAggregateTouchRate`. Bookkeeping-only
  proof; introduces no new axioms.

# What this module does *not* do

It does not prove B1(ii), it does not weaken
`R-OrbitSideAggregateTouchRate`, and it does not remove the existing
F.3-route discharge (`OrbitAdmissibleSupplyFromF3.lean`). The two
routes coexist as alternative orbit-side suppliers of
`R-OrbitSideAggregateTouchRate`; downstream consumers can choose
either witness depending on which open math is closed first.

# Discipline anchors

* `unconditional-discipline.mdc` rule 1: every public residual carries
  either a paper-citation or an explicit `OPEN MATH RESIDUAL` marker.
  `OrbitTouchMaxGapResidual` is OPEN MATH and points to
  `research/wave2j-pass2c-b1-maxgap/STATEMENT.md` §2.2 + `ATTEMPT.md`
  for the obstruction map.
* `formal-first-proof-policy.mdc`: the typed shape is the formal
  contract; the analytical proof attempt under it is documented
  externally rather than forced into a Lean script.
* `residual-audit-discipline.mdc`: tracked in `docs/residual-budget.md`
  as `R-OrbitTouchMaxGap` (added by Wave 2J Stage 4).
* `unconditional-discipline.mdc` rule 3: the typed witness fields
  match the empirical bound shape and **do not over-strengthen** the
  paper claim — `count_lower` is the W-B inequality (the orbit-side
  obligation that already lives on the public frontier), and the
  gap-form fields encode the *mechanism* by which B1(ii) is supposed
  to deliver `count_lower`. The witness shape mirrors
  `OrbitAdmissibleTouchSupplyWitness`, with the F.3 paper-trace field
  removed (since the max-gap route is independent of F.3).
-/

import Collatz.Mixing.AggregateTouchRate

namespace Collatz.Mixing

open Collatz.Epochs

/--
**Typed orbit-side max-gap witness (Wave 2J Pass-2c).**

For an odd start `n` whose Collatz orbit is the focus, this structure
records the **structural conclusion** of the B1(ii) max-gap conjecture
(`research/wave2j-pass2c-b1-maxgap/STATEMENT.md` §2.2): along the actual
Collatz orbit of `n` there is a per-level family of `t`-touches whose
consecutive recurrence gap is uniformly bounded against `Q_t`, and
consequently the aggregate W-B inequality holds with a `t`-uniform
`ε`-witness.

The fields decompose as:

* `C` — universal max-gap constant; consecutive touches differ by at
  most `C · Q_t`. Empirical fit (Stage 3.B): `C = 25` is consistent with
  16K orbits up to `t = 12` (1.1 M observed gaps).
* `C_pos` — `0 < C` (so the gap bound is non-trivial).
* `epsNum`, `epsDen` — `t`-uniform W-B factors `(epsNum, epsDen)`,
  both positive; `ε := epsNum / epsDen`. Bridge bookkeeping
  (`STATEMENT.md` §3) yields `epsNum = 1`, `epsDen = 4 · C`.
* `L_star : ℕ → ℕ` — per-`t` threshold beyond which the W-B inequality
  bites (combines the gap threshold and a slack term;
  `STATEMENT.md` §3 step 5).
* `K : ℕ → ℕ` — per-`t` orbit-dependent threshold past which the gap
  bound holds. The `K t` argument captures B1(ii)'s strictly weaker
  scope versus B1(i): short orbit prefixes may have anomalously long
  gaps before settling into the `≤ C · Q_t` regime.
* `touchAt : ℕ → ℕ → ℕ` — `touchAt t m` is the orbit-step index of
  the `m`-th `t`-touch past `K t`.
* `touchAt_isTouch` — each anchor is a real `selected_segment_t_touch`
  on the orbit of `n` at level `t`.
* `touchAt_strict_mono` — anchors are strictly increasing.
* `touchAt_above_K` — the first anchor occurs at index `≥ K t`.
* `touchAt_gap` — consecutive anchors are within distance `C · Q_t`.
* `touchAt_start` — the first anchor occurs by index `K t + C · Q_t`
  (paper-trace: a touch must exist within one max-gap of `K t`).
* `count_lower` — the W-B aggregate inequality holds for every
  `t ≥ 3` and every `L ≥ L_star t`.

The `count_lower` field is **recorded directly** as part of the
witness shape (rather than derived inside this structure from the
gap data) for two reasons:

1. *Pattern alignment.* This mirrors `OrbitAdmissibleTouchSupplyWitness`
   in `OrbitAdmissibleSupplyFromF3.lean`, keeping a uniform witness
   shape across the two alternative routes to
   `R-OrbitSideAggregateTouchRate`.
2. *Honest scope.* The gap-to-count derivation is a pure combinatorial
   counting argument (cf. `STATEMENT.md` §3 sketch); it is decoupled
   from the open math content of B1(ii) itself. Recording `count_lower`
   as a field keeps the typed residual shape *exactly* what the public
   frontier consumes, without adding a counting-lemma layer between the
   open math and the W-B residual. -/
structure OrbitTouchMaxGapWitness (n : ℕ) where
  /-- Universal max-gap constant. -/
  C : ℕ
  C_pos : 0 < C
  /-- Universal ε-witness numerator. -/
  epsNum : ℕ
  /-- Universal ε-witness denominator. -/
  epsDen : ℕ
  epsNum_pos : 0 < epsNum
  epsDen_pos : 0 < epsDen
  /-- Per-level orbit-dependent gap-threshold. -/
  K : ℕ → ℕ
  /-- Per-level threshold beyond which the W-B inequality bites. -/
  L_star : ℕ → ℕ
  /-- m-th `t`-touch past `K t` along the orbit of n. -/
  touchAt : ℕ → ℕ → ℕ
  touchAt_isTouch :
    ∀ t, 3 ≤ t → ∀ m, selected_segment_t_touch n (touchAt t m) t
  touchAt_strict_mono :
    ∀ t, 3 ≤ t → ∀ m, touchAt t m < touchAt t (m + 1)
  touchAt_above_K :
    ∀ t, 3 ≤ t → K t ≤ touchAt t 0
  touchAt_start :
    ∀ t, 3 ≤ t → touchAt t 0 ≤ K t + C * Q_t t
  touchAt_gap :
    ∀ t, 3 ≤ t → ∀ m, touchAt t (m + 1) ≤ touchAt t m + C * Q_t t
  /-- The W-B aggregate inequality, recorded directly as a witness
  field (the gap-to-count bookkeeping is documented in
  `research/wave2j-pass2c-b1-maxgap/STATEMENT.md` §3 and is a pure
  combinatorial counting argument independent of the B1(ii) open
  math). -/
  count_lower :
    ∀ t, 3 ≤ t → ∀ L, L_star t ≤ L →
      epsDen * orbit_aggregate_touch_count n t L * Q_t t
        ≥ epsNum * L

/--
**`R-OrbitTouchMaxGap` (Wave 2J Pass-2c).**

For an odd start `n ≥ 1` whose Collatz orbit is *not* eventually
periodic, the residual asserts existence of an orbit-side max-gap
witness in the sense above. The qualifiers `1 ≤ n` and
`¬ orbit_eventually_periodic n` are inherited from
`OrbitSideAggregateTouchRateResidual` and serve the same purpose
(cf. the docstring of `OrbitSideAggregateTouchRateResidual` in
`Collatz/Mixing/AggregateTouchRate.lean`).

Status (per `unconditional-discipline.mdc` rule 1 and
`residual-audit-discipline.mdc`):

**OPEN MATH RESIDUAL.** This residual encodes the B1(ii) conjecture
from `research/wave2j-pass2c-b1-maxgap/STATEMENT.md` §2.2. Stage 3.D
(`research/wave2j-pass2c-b1-maxgap/ATTEMPT.md`) records `BLOCKED`
verdict on the proof attempt, with four explicit obstructions. The
residual is retained as an alternative entry point for future waves
should any of the obstructions be lifted (cf. `ATTEMPT.md` §8).

Tracked in `docs/residual-budget.md` as `R-OrbitTouchMaxGap` (added by
Wave 2J Stage 4).
-/
def OrbitTouchMaxGapResidual (n : ℕ) : Prop :=
  1 ≤ n →
  ¬ Collatz.CycleExclusion.orbit_eventually_periodic n →
  Nonempty (OrbitTouchMaxGapWitness n)

/--
**Wave 2J Pass-2c discharge.**

`R-OrbitTouchMaxGap ⇒ R-OrbitSideAggregateTouchRate`.

Conceptually, the typed max-gap witness *contains* the W-B inequality
as the field `count_lower`; the proof is therefore a pure unpacking.
Bookkeeping form: `(epsNum, epsDen, L_star)` from the witness become
the ε-witness factors and threshold for the W-B residual.

This theorem is bookkeeping-only and introduces no new axioms (only
`propext`, `Classical.choice`, `Quot.sound` are used, transitively from
the imported modules).

This is the **second** discharge route for
`R-OrbitSideAggregateTouchRate`, alongside
`orbitSideAggregateTouchRate_of_admissibleTouchSupply` from
`Collatz/Mixing/OrbitAdmissibleSupplyFromF3.lean`. The two routes are
independent and can be lifted in either order. -/
theorem orbitSideAggregateTouchRate_of_orbitTouchMaxGap
    {n : ℕ}
    (hres : OrbitTouchMaxGapResidual n) :
    OrbitSideAggregateTouchRateResidual n := by
  intro hn hper
  obtain ⟨w⟩ := hres hn hper
  refine ⟨w.epsNum, w.epsDen, w.epsNum_pos, w.epsDen_pos, w.L_star, ?_⟩
  intro t ht L hL
  exact w.count_lower t ht L hL

end Collatz.Mixing
