/-
Collatz Conjecture: Wave 2H W-B — orbit-side aggregate touch-rate
residual (`R-OrbitSideAggregateTouchRate`).

This module introduces the **strictly weaker** orbit-side residual
that supersedes `R-OrbitSideAdmissibleDensity` for the SEDT route
(paper Theorem F.6 (revised, Wave 2H aggregate); cf.
`docs/wave2h-research/paper-residual-scope.md` §3.1, §5.1).

The repackaging is purely additive at this stage:

* The previous algebraic-stack pipeline
  (`AdmissibleTailF01.touch_count_eq_one_of_realized` →
  `LocalAffinePairSemantics.one_touch_per_period` →
  `selectedTailTouchSemantics_of_localAffinePair` →
  `AdmissibleTailTouchFrequencyTheoremSource` /
  `AdmissibleTailTouchFrequencyResidual` /
  `AdmissibleTailTouchLowerBoundResidual`) is **kept unchanged** as
  the algebraic-stack supplier and historical compatibility layer.

* This module defines `OrbitSideAggregateTouchRateResidual` —
  the new public orbit-side hypothesis.

* The strictness ordering "previous residual is strictly stronger"
  is documented at the paper / ledger level
  (`docs/wave2h-research/paper-residual-scope.md` §5.3 and
  `docs/residual-budget.md`); no Lean-level "old ⇒ new" wrapper is
  produced here, since the canonical identification
  "admissible-tail discrepancy on the orbit prefix `[0, L)`
  equals the orbit-aggregate count on `[0, L)`" is itself an honest
  mathematical claim, not a definitional unfolding. Forcing such a
  wrapper would either smuggle the open math piece via a `sorry`
  or restate `R-OrbitSideAdmissibleDensity` at orbit level — both
  forbidden by `unconditional-discipline.mdc`.

* The aggregate count uses the existing per-orbit touch predicate
  `selected_segment_t_touch n · t` directly, with no re-anchoring,
  so the new residual is bit-for-bit a statement about the actual
  Collatz orbit of `n`.

Per `unconditional-discipline.mdc`: the residual is explicit, the
aggregate count uses the actual orbit (no homogenization, no plateau
anchoring), `ε > 0` is encoded as a positive rational
`epsNum / epsDen` to stay axiom-clean inside `ℕ` (no `ℝ`).

**Wave 2H Phase 3 — orbit-side qualifier.** The paper W-B statement
(`Theorem F.6 (revised, Wave 2H aggregate)`) is asserted only for
*infinite* (non-eventually-periodic) odd Collatz orbits with
`n ≥ 1`. Without that qualifier, the residual would be mathematically
inconsistent: on any orbit converging to `1` we have `m_k = 1` for all
sufficiently large `k`, hence `1 mod 2^t = 1 ≠ s_t t` for every
`t ≥ 4` (since `s_t t = 9` from `t = 4` onward). Therefore
`N_t(L)` is bounded by a constant `T(n)` on a converging orbit at
`t ≥ 4`, which contradicts `N_t(L) ≥ ε · L / Q_t` for large `L`.

We follow the **curried-implication** design:
`OrbitSideAggregateTouchRateResidual n :=`
`  1 ≤ n → ¬ orbit_eventually_periodic n → ∃ ε > 0, …`
so that:

* the residual remains a `ℕ → Prop` predicate (no signature change at
  the type level — existing call sites still typecheck);
* the residual is *vacuously satisfied* on `n = 0` and on every
  eventually-periodic orbit (which is mathematically the correct
  scope for the orbit-side W-B statement);
* the consumer extractor `orbit_aggregate_touch_count_lower_of_residual`
  takes both qualifiers explicitly and returns the unguarded
  existential, exposing the same surface as before.

The aperiodicity predicate is the existing `Collatz.CycleExclusion.
orbit_eventually_periodic`, defined in
`Collatz/CycleExclusion/Main.lean:69`.
-/

import Collatz.Epochs.Core
import Collatz.Epochs.NumeratorCarry
import Collatz.SEDT.TouchDensity
import Collatz.Mixing.PhaseMixing
import Collatz.Mixing.TouchFrequencyLocal
import Collatz.CycleExclusion.Main

namespace Collatz.Mixing

open Collatz.Epochs

/-- Orbit-side aggregate `t`-touch count over a prefix of length `L`
of the Collatz orbit of `n` (no homogenization, no plateau anchoring).
Counts indices `k < L` such that the orbit-realised touch predicate
`selected_segment_t_touch n k t` holds. We reuse the existing
`selected_segment_tail_touch n t 0` packaging so that the decidability
instance from `Collatz/Mixing/TouchFrequencyLocal.lean` is in scope; on
the raw indices the two predicates are definitionally equal. -/
def orbit_aggregate_touch_count (n t L : ℕ) : ℕ :=
  Collatz.SEDT.TouchDensity.touchCount
    (selected_segment_tail_touch n t 0) L

@[simp] lemma orbit_aggregate_touch_count_zero (n t : ℕ) :
    orbit_aggregate_touch_count n t 0 = 0 := by
  simp [orbit_aggregate_touch_count]

lemma orbit_aggregate_touch_count_mono
    (n t : ℕ) {a b : ℕ} (h : a ≤ b) :
    orbit_aggregate_touch_count n t a
      ≤ orbit_aggregate_touch_count n t b :=
  Collatz.SEDT.TouchDensity.touchCount_mono _ h

/--
**R-OrbitSideAggregateTouchRate (Wave 2H, W-B).**

For an odd start `n ≥ 1` whose Collatz orbit is *not* eventually
periodic (`¬ orbit_eventually_periodic n`), the predicate asserts the
existence of a positive rational lower-bound factor
`ε(n) = epsNum / epsDen > 0` and a per-`t` threshold `L_⋆(n, t)`
such that the aggregate `t`-touch count along the actual Collatz
orbit of `n` satisfies
`epsDen · N_t(L) · Q_t  ≥  epsNum · L`
for every `t ≥ 3` and every `L ≥ L_⋆(n, t)`.

Equivalently (passing to the rationals):
`N_t(L) ≥ ε · L / Q_t`.

**Why the curried `1 ≤ n → ¬ orbit_eventually_periodic n →` form?**
Without these qualifiers the residual is mathematically inconsistent
for every orbit converging to `1` at `t ≥ 4`: the orbit reaches
`m_k = 1`, so `1 mod 2^t = 1 ≠ s_t t = 9` (for `t ≥ 4`), hence
`N_t(L) ≤ T(n)` is bounded — contradicting any positive
`ε · L / Q_t` lower bound. Currying the qualifiers makes the
residual *vacuously satisfied* on `n = 0` and on every eventually
periodic orbit (which is mathematically correct for an orbit-side
W-B statement). It also keeps the type signature `ℕ → Prop` so that
existing consumers of the residual continue to typecheck without
changes.

**Strictly weaker** than:
* `R-OrbitSideAdmissibleDensity` (per-window `tc = 1` density);
* equidistribution of `m_k mod 2^t` along the orbit;
* Collatz convergence itself.

See `docs/residual-budget.md` and
`docs/wave2h-research/paper-residual-scope.md` §5.1, §5.3.
-/
def OrbitSideAggregateTouchRateResidual (n : ℕ) : Prop :=
  1 ≤ n →
  ¬ Collatz.CycleExclusion.orbit_eventually_periodic n →
  ∃ epsNum epsDen : ℕ,
    0 < epsNum ∧ 0 < epsDen ∧
    ∃ L_star : ℕ → ℕ,
      ∀ t : ℕ, 3 ≤ t →
        ∀ L : ℕ, L_star t ≤ L →
          epsDen * orbit_aggregate_touch_count n t L * Q_t t
            ≥ epsNum * L

/-- Honest extractor: the W-B residual *is* the aggregate lower-bound
inequality on a non-trivial, non-eventually-periodic Collatz orbit.
Provided as a distinct theorem so downstream modules do not need to
unfold the residual definition.

The two hypotheses `1 ≤ n` and `¬ orbit_eventually_periodic n`
discharge the curried qualifiers in the residual definition; on the
complement (n = 0 or eventually-periodic orbit) the residual is
vacuously satisfied and no aggregate lower bound can be extracted. -/
theorem orbit_aggregate_touch_count_lower_of_residual
    {n : ℕ}
    (hn : 1 ≤ n)
    (hper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n)
    (hres : OrbitSideAggregateTouchRateResidual n) :
    ∃ epsNum epsDen : ℕ,
      0 < epsNum ∧ 0 < epsDen ∧
      ∃ L_star : ℕ → ℕ,
        ∀ t : ℕ, 3 ≤ t →
          ∀ L : ℕ, L_star t ≤ L →
            epsDen * orbit_aggregate_touch_count n t L * Q_t t
              ≥ epsNum * L := hres hn hper

end Collatz.Mixing
