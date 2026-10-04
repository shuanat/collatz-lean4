/-
Orbit-side aggregate touch-rate hypothesis (research; not used by any theorem).

`orbit_aggregate_touch_count n t L` counts the times `k < L` at which the odd
orbit of `n` satisfies `T^[k] n ≡ s_t (mod 2^t)`.

`OrbitSideAggregateTouchRateResidual n` is an OPEN hypothesis about
non-eventually-periodic orbits: a positive lower bound on the aggregate touch
rate, uniformly in `t ≥ 3`. Status:

* It is guarded by `1 ≤ n` and `¬ orbit_eventually_periodic n`, hence vacuously
  true for every eventually periodic orbit (in particular for every orbit that
  reaches `1`). Without the guard it would be false on convergent orbits for
  `t ≥ 4`, because `s_t ≡ 9 (mod 16)` for `t ≥ 4` (`s_4 = s_5 = 9`, `s_6 = 41`),
  so the value `1` is not a touch and the count stays bounded.
* No theorem of this library consumes it; nothing here derives boundedness
  or convergence from it. (Under the random model the expected touch rate is
  `2^{1−t} = 1/(2 Q_t)`.)
* The former suppliers of this hypothesis (`OrbitAdmissibleSupplyFromF3`,
  `OrbitTouchMaxGap`, whose uniform-gap assumptions are heuristically false)
  were deleted in the 2026-10 clean-up.
-/

import Collatz.Mixing.AdmissibleTail
import Collatz.SEDT.TouchDensity
import Collatz.CycleExclusion.Main

namespace Collatz.Mixing

open Collatz.Epochs

/-- Number of times `k < L` with `T^[k] n ≡ s_t (mod 2^t)`. -/
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

/-- OPEN hypothesis (unused): for `n ≥ 1` with a non-eventually-periodic orbit
there are `ε = epsNum / epsDen > 0` and thresholds `L_star t` with
`epsDen · N_t(L) · Q_t ≥ epsNum · L` for all `t ≥ 3`, `L ≥ L_star t`, where
`N_t(L) = orbit_aggregate_touch_count n t L`. Vacuously true on eventually
periodic orbits. See the module docstring for its status. -/
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

/-- Unfolding of `OrbitSideAggregateTouchRateResidual` under its guards. -/
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
