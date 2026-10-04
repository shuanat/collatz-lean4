/-
Collatz Conjecture: Wave 2H Phase B (B.1.A + B.1.C + B.1.D) — typed
"primitive-junction admissibility supply" residual and discharge of
`R-OrbitSideAggregateTouchRate` from it.

# Background

Wave 2H Phase A produced `Collatz/Mixing/AggregateTouchRate.lean` with the
strictly weaker public orbit-side residual `R-OrbitSideAggregateTouchRate`
(the W-B form of paper Theorem F.6 (revised)). Phase B opens the route from
the F.3 / F.4 line of the paper to that residual.

Phase B.0 reconnaissance (`computational-reconnaissance.mdc`) produced two
verdicts that pin down the *form* of this module:

* **B.0.1 (`research/wave2h-f3-proof-audit/REPORT.md`).** The paper proof
  of Theorem F.3 in `paper/src/md/appendices/pdf-content/F-mixing.md` §F.7
  is **GAP-CONFIRMED**: Step F.7.5 (the 2-adic valuation contradiction) is
  invalid — `ν₂(S_k) = 0` unconditionally, so no contradiction can be
  produced from the exact closure equation; Step F.7.4 (the leap from
  finite-state periodicity to orbit-value periodicity) is invalid — even
  with a *richer* finite projection than the paper's (`n mod 2^t` × next
  head-window exponents) state collisions are abundant and orbit values
  diverge by up to `log₂ ratio = 42.55`. F.3 is therefore *not proven* in
  current paper form; only F.3' (window bound `W = 7 · Q_t`,
  computational-empirical, `F-mixing.md` line 17) is empirically validated.
  Consequence for Lean: `R-F3-Recurrence` cannot be discharged from a
  paper proof and must remain an *honest open math residual* on the
  public frontier.

* **B.0.2 (`research/wave2h-junction-admissibility/REPORT.md`).** The
  intended structural lemma "primitive junctions are F.0.1-admissible-tail
  anchors" cannot be empirically validated at the current scale: across
  270 seeds × 8 levels (`t ∈ {3..10}`), neither the algebraic-stack
  approach (Wave 2D `N_k = 3^{k+1}(r₀+2) − 5·2^k`) nor the real-orbit
  `e_i = t` epoch approach produces a single junction whose adjacent
  plateaus are F.0.1-admissible. The structural lemma is therefore *not*
  derivable in Lean from already-formalised pieces and must itself be
  encoded as an *honest typed open residual* — not as a derived theorem.

* **B.0.3 decision (Go with conservative form).** Encode the joint
  structural conclusion ("F.3 + structural lemma yield enough
  admissible-tail t-touches on the orbit to satisfy the W-B inequality")
  as a single *typed* open residual `R-PrimitiveJunctionAdmissibilitySupply`,
  with the typed F.3 witness (`PrimitiveJunctionRecurrenceWitness` from
  `Collatz/Epochs/G/F3ConditionalResiduals.lean`) as an explicit
  paper-trace field of the supply witness. The discharge to W-B is then
  axiom-clean and bookkeeping-only.

Paper-citation (anchored honestly):
* Theorem F.3 (Shumak Primitive Junction Theorem) — `F-mixing.md` §F.7
  (proof gap-confirmed in B.0.1, theorem itself remains the conjectured
  paper-trace).
* Theorem F.4 (recurrence consequence: bounded gap `G_t ≤ 8 t · 2^(κt)`)
  — `F-mixing.md` §F.4.
* Definition F.0.1 (admissible-tail predicate) — `F-mixing.md` §F.0.1.
* Lemma F.4.1 / F.4 corollary "primitive junctions are admissible-tail
  anchors" — *not* in current paper as a separate lemma; this is the new
  open structural residual produced by Phase B (paper-issue W2H-PI-B06).

# Module contents

* `OrbitAdmissibleTouchSupplyWitness n` — typed witness: bundles an
  underlying typed F.3 witness `f3` (paper-trace), a per-`t` admissible-
  tail anchor sequence `touchAt` along the actual Collatz orbit of `n`,
  per-`t` recurrence gap `gap` (universal scaling against `Q_t` so that
  `ε` is universal in `t`), and a `count_lower` field that records the
  W-B aggregate inequality directly from the gap data.

* `PrimitiveJunctionAdmissibilitySupplyResidual n` — the typed residual
  `1 ≤ n → ¬ orbit_eventually_periodic n → Nonempty (witness)`. Honest
  open math residual; shape-compatible with any future closure of F.3 +
  the structural lemma F.4.1.

* `orbitSideAggregateTouchRate_of_admissibleTouchSupply` — the discharge:
  `R-PrimitiveJunctionAdmissibilitySupply ⇒ R-OrbitSideAggregateTouchRate`.
  Bookkeeping-only proof; introduces no new axioms.

# What this module does *not* do

It does not prove F.3, it does not prove the structural lemma, and it
does not weaken `R-OrbitSideAggregateTouchRate`. It only changes which
*shape* of orbit-side input the public frontier consumes: instead of
quantifying over an opaque W-B inequality directly, the new public
frontier (`Collatz/Convergence/UnconditionalModuloOrbitWitnesses.lean`)
quantifies over an honest typed admissibility-supply witness whose
*content* (gap-bounded sequence of admissible-tail t-touches) is the
mathematical bridge promised by F.3 + F.4 + the structural lemma F.4.1.

# Discipline anchors

* `unconditional-discipline.mdc` rule 1: every public residual on the
  frontier carries either a paper-citation or an explicit
  `OPEN MATH RESIDUAL` marker. The supply residual is OPEN MATH.
* `formal-first-proof-policy.mdc`: the typed shape is the formal contract
  and the paper proof is reconstructed under it; we do *not* force the
  Lean target to match a flawed paper proof.
* `residual-audit-discipline.mdc`: residual entries (typed F.3 witness,
  primitive-junction admissibility supply, plus the W-B residual now
  conditionally formalized) tracked in `docs/residual-budget.md`
  (Phase B.2.C update).
-/

import Collatz.Mixing.AggregateTouchRate
import Collatz.Epochs.G.F3ConditionalResiduals

namespace Collatz.Mixing

open Collatz.Epochs

/--
**Typed orbit-side admissibility-supply witness (Wave 2H Phase B.1.A).**

For an odd start `n` whose Collatz orbit is the focus, this structure
records the *structural conclusion* of the F.3 / F.4 line plus the
"primitive junctions are admissible-tail anchors" structural lemma
(paper-issue W2H-PI-B06): along the actual Collatz orbit of `n` there is
a per-level family of admissible-tail t-touches whose recurrence gap is
uniformly bounded against `Q_t`, and consequently the aggregate W-B
inequality holds with a universal `ε`-witness.

The fields decompose as:

* `f3` — the underlying typed F.3 witness (paper-trace; see
  `PrimitiveJunctionRecurrenceWitness`).
* `epsNum`, `epsDen` — universal ε-witness factors `(epsNum, epsDen)`
  with both positive; `ε := epsNum / epsDen`.
* `L_star : ℕ → ℕ` — per-`t` threshold beyond which the W-B inequality
  bites.
* `gap : ℕ → ℕ` — per-`t` recurrence gap on the admissible-tail anchor
  sequence.
* `touchAt : ℕ → ℕ → ℕ` — `touchAt t m` is the orbit-step index of the
  m-th admissible-tail anchor at level `t`.
* `touchAt_isTouch` — each anchor is a real `selected_segment_t_touch`
  on the orbit of `n` at level `t`.
* `touchAt_strict_mono` — anchors are strictly increasing.
* `touchAt_gap` — consecutive anchors are within distance `gap t`.
* `touchAt_start` — the first anchor occurs by index `gap t`.
* `count_lower` — the W-B aggregate inequality holds for every
  `t ≥ 3` and every `L ≥ L_star t`.

The `count_lower` field is **not formally derived** from the gap data
inside this structure: B.0.2 demonstrated that the structural-lemma
content is itself an open mathematical question. We instead encode the
bookkeeping conclusion *as part of the witness shape*, so that the
witness is honest about what it asserts (and so that its existence
remains an open math residual). The gap-form fields are kept as
paper-trace: they describe the *mechanism* by which the structural
lemma is supposed to deliver `count_lower`. -/
structure OrbitAdmissibleTouchSupplyWitness (n : ℕ) where
  /-- Underlying typed F.3 witness (paper-trace; `t = 3` is a canonical
  level — paper F.4 carries gap bounds at every `t ≥ 3` simultaneously
  on the same orbit, so a single anchoring level suffices for the
  paper-trace). -/
  f3 : Collatz.Epochs.G.PrimitiveJunctionRecurrenceWitness n 3
  /-- Universal ε-witness numerator. -/
  epsNum : ℕ
  /-- Universal ε-witness denominator. -/
  epsDen : ℕ
  epsNum_pos : 0 < epsNum
  epsDen_pos : 0 < epsDen
  /-- Per-level threshold beyond which the W-B inequality bites. -/
  L_star : ℕ → ℕ
  /-- Per-level recurrence gap. -/
  gap : ℕ → ℕ
  gap_pos : ∀ t, 3 ≤ t → 0 < gap t
  /-- m-th admissible-tail anchor at level t along the orbit of n. -/
  touchAt : ℕ → ℕ → ℕ
  touchAt_isTouch :
    ∀ t, 3 ≤ t → ∀ m, selected_segment_t_touch n (touchAt t m) t
  touchAt_strict_mono :
    ∀ t, 3 ≤ t → ∀ m, touchAt t m < touchAt t (m + 1)
  touchAt_start :
    ∀ t, 3 ≤ t → touchAt t 0 < gap t
  touchAt_gap :
    ∀ t, 3 ≤ t → ∀ m, touchAt t (m + 1) ≤ touchAt t m + gap t
  /-- The W-B aggregate inequality, recorded directly as a witness
  field (since the bookkeeping deriving it from `gap` + `touchAt` data
  depends on the structural lemma F.4.1 — currently OPEN MATH per
  B.0.2). -/
  count_lower :
    ∀ t, 3 ≤ t → ∀ L, L_star t ≤ L →
      epsDen * orbit_aggregate_touch_count n t L * Q_t t
        ≥ epsNum * L

/--
**`R-PrimitiveJunctionAdmissibilitySupply` (Wave 2H Phase B.1.A).**

For an odd start `n ≥ 1` whose Collatz orbit is *not* eventually
periodic, the residual asserts existence of an admissibility-supply
witness in the sense above. The qualifiers
`1 ≤ n` and `¬ orbit_eventually_periodic n` are inherited from
`OrbitSideAggregateTouchRateResidual` and serve the same purpose:
without them the residual is mathematically inconsistent on orbits
converging to `1` (cf. the docstring of
`OrbitSideAggregateTouchRateResidual` in
`Collatz/Mixing/AggregateTouchRate.lean`).

Status (per `unconditional-discipline.mdc` rule 1 and
`residual-audit-discipline.mdc`):

**OPEN MATH RESIDUAL.** This residual is *not* discharged from any
already-formalised piece. It is the joint typed conclusion of:

* `R-F3-Recurrence` (paper Theorem F.3 — gap-confirmed unproven by
  B.0.1; encoded as `PrimitiveJunctionRecurrenceTypedResidual`) and
* the structural lemma F.4.1 "primitive junctions are admissible-tail
  anchors" (B.0.2 SCAFFOLDING-LIMITED; not currently in the paper as
  a separate lemma — paper-issue W2H-PI-B06).

Tracked in `docs/residual-budget.md` as
`R-PrimitiveJunctionAdmissibilitySupply` (added by Wave 2H Phase B.2.C).
-/
def PrimitiveJunctionAdmissibilitySupplyResidual (n : ℕ) : Prop :=
  1 ≤ n →
  ¬ Collatz.CycleExclusion.orbit_eventually_periodic n →
  Nonempty (OrbitAdmissibleTouchSupplyWitness n)

/--
**Wave 2H Phase B.1.D discharge.**

`R-PrimitiveJunctionAdmissibilitySupply ⇒ R-OrbitSideAggregateTouchRate`.

Conceptually, the typed admissibility-supply witness *contains* the W-B
inequality as the field `count_lower`; the proof is therefore a pure
unpacking. Bookkeeping form: `(epsNum, epsDen, L_star)` from the witness
become the ε-witness factors and threshold for the W-B residual.

This theorem is bookkeeping-only and introduces no new axioms (only
`propext`, `Classical.choice`, `Quot.sound` are used, transitively from
the imported modules).
-/
theorem orbitSideAggregateTouchRate_of_admissibleTouchSupply
    {n : ℕ}
    (hres : PrimitiveJunctionAdmissibilitySupplyResidual n) :
    OrbitSideAggregateTouchRateResidual n := by
  intro hn hper
  obtain ⟨w⟩ := hres hn hper
  refine ⟨w.epsNum, w.epsDen, w.epsNum_pos, w.epsDen_pos, w.L_star, ?_⟩
  intro t ht L hL
  exact w.count_lower t ht L hL

/-- **Wave 2H Phase B.1.D paper-trace alias.**

Same content as `orbitSideAggregateTouchRate_of_admissibleTouchSupply`,
with a name carrying the paper-trace tag `_of_F3_recurrence` to match
the public-frontier naming convention used in
`Collatz/Convergence/UnconditionalModuloOrbitWitnesses.lean`. The "F3
recurrence" in the name refers to the underlying `f3` field of the
admissibility-supply witness — i.e. to the paper-trace embedding of
the typed F.3 witness inside every supply witness. -/
theorem orbitSideAggregateTouchRate_of_F3_recurrence
    {n : ℕ}
    (hres : PrimitiveJunctionAdmissibilitySupplyResidual n) :
    OrbitSideAggregateTouchRateResidual n :=
  orbitSideAggregateTouchRate_of_admissibleTouchSupply hres

end Collatz.Mixing
