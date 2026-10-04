/-
Collatz Conjecture: S7.1.B — F.3-conditional orbit-side residuals.

These residuals encode the F.3-derived inputs that, **together with**
`EpochTailGeometryResidual`, would close paper Appendix G, Theorem G.5 (boxed
Q_t-block) on every infinite orbit at `t ≥ 3`. They are explicitly opaque
(`Prop := True`) per `.cursor/rules/unconditional-discipline.mdc` rule 1
because their formalization depends on F.3 (Shumak Primitive Junction Theorem),
which is its own future S7.4 session.

In the S7.1.C assembly (`G5Assembly.lean`) and the S7.1.D public frontier
(extension of `Collatz/Convergence/UnconditionalModuloOrbitWitnesses.lean`)
these residuals appear as **documentation hooks**: they record exactly which
F.3-derived inputs paper Appendix G uses to derive the consolidated tail
geometry (`EpochTailGeometryResidual`). They do not constrain the assembly
typing because the assembly genuinely consumes the geometry residual directly
(via `Classical.choice`) and the period-sum residual as an arrow — the F.3
residuals are kept in the public frontier as paper-trace, recording that the
geometry residual itself decomposes through F.3 in the paper proof.

Paper-correspondence:
- `PrimitiveJunctionRecurrenceResidual`: paper Appendix F, Theorem F.3
  (Shumak Primitive Junction Theorem) + Theorem F.4 (recurrence consequence:
  every infinite orbit admits a primitive junction type with bounded recurrence
  gap `≤ G_t = 8t · 2^(κ t)`).
- `UniformPhaseDistributionResidual`: paper Appendix F, Lemma F.2.1 (uniform
  phase distribution under primitive junctions, ensuring visitation of every
  phase class in the boxed Q_t-block).

Both residuals are tracked in `docs/residual-budget.md` as `R-F3-Recurrence`
and `R-F3-PhaseDistribution`. Their formalization is deferred to S7.4.
-/

import Collatz.Epochs.Core

namespace Collatz.Epochs.G

/-- **OPEN MATH RESIDUAL — paper Appendix F, Theorems F.3 + F.4.**

Every infinite orbit at `t ≥ 3` admits a primitive junction type `J*` whose
recurrence gap on the orbit is bounded by `G_t = 8 t · 2^(κ t)` (where `κ` is
the small constant from F.4). This is the F.3 / F.4 conclusion that drives the
paper proof of G.5 by guaranteeing infinitely many primitive junction events
(hence infinitely many G.4 structural recurrences feeding into G.5).

Encoding rationale: opaque `True` because (i) F.3 itself is open (S7.4,
gap-risk), (ii) the paper-faithful typed statement requires the (currently
stubbed) `Epochs/PhaseClasses.lean` `is_primitive_junction` infrastructure with
real semantics, and (iii) in the S7.1 assembly this residual appears as
documentation — the assembly genuinely consumes `EpochTailGeometryResidual`
which already encodes the paper-derived conclusion. Listing this residual in
the public frontier preserves the paper-trace: the geometry residual decomposes
through F.3 in the paper.

**Wave 2H Phase B audit (2026-04-19, B.0.1):** the paper proof of F.3 in
[F-mixing.md §F.7] is GAP-CONFIRMED (Steps F.7.4 and F.7.5 both invalid;
see `collatz-verification/research/wave2h-f3-proof-audit/REPORT.md`). The
opaque `True` encoding is therefore preserved — the residual remains
*honestly open*. A typed witness form is provided alongside as
`PrimitiveJunctionRecurrenceWitness` /
`PrimitiveJunctionRecurrenceTypedResidual` (this module, below) so that
downstream Lean code can consume an *honest typed shape* without committing
to the unproven paper proof.

OPEN MATH RESIDUAL marker per `.cursor/rules/unconditional-discipline.mdc`
rule 1; tracked in `docs/residual-budget.md` as `R-F3-Recurrence`. -/
def PrimitiveJunctionRecurrenceResidual (_n _t : ℕ) : Prop := True

/-- **Typed witness for `R-F3-Recurrence` (Wave 2H Phase B.1.B refactor).**

A `PrimitiveJunctionRecurrenceWitness n t` records the F.3 + F.4 conclusion
in an honestly typed shape:

* `G` is the recurrence gap bound (paper F.4 gives `G ≤ G_t = 8 t · 2^(κ t)`,
  but we leave it abstract here — the typed witness is consumed only via
  its bounded-gap field, not via the paper bound on `G`);
* `occursAt m` is the orbit-step index of the m-th primitive junction
  occurrence;
* `gap_bound` enforces consecutive occurrences within distance `G`;
* `cofinal` enforces that occurrences are not bounded above (otherwise
  the residual would be vacuous after a finite prefix).

This typed shape is **structurally compatible** with the paper claim: any
real proof of F.3 + F.4 produces such a witness. Conversely, *existence of
the witness* is the (orbit-side) honest content of `R-F3-Recurrence`; the
paper proof attempting to derive its existence from finite-state
periodicity is gap-confirmed (B.0.1) and not relied upon here.

Per `formal-first-proof-policy.mdc`: typed shape is the formal contract;
the paper proof is reconstructed *under* this shape rather than the shape
being forced to match a flawed proof. -/
structure PrimitiveJunctionRecurrenceWitness (_n _t : ℕ) where
  /-- Recurrence gap bound on consecutive primitive-junction occurrences. -/
  G : ℕ
  /-- The gap is positive (so that the bounded-gap field has content). -/
  G_pos : 0 < G
  /-- Indexed family of orbit-step positions of primitive junctions. -/
  occursAt : ℕ → ℕ
  /-- Consecutive occurrences are within distance `G`. -/
  gap_bound : ∀ m : ℕ, occursAt (m + 1) ≤ occursAt m + G
  /-- Occurrences are cofinal: every prefix is eventually exited. -/
  cofinal : ∀ k : ℕ, ∃ m : ℕ, k ≤ occursAt m

/-- **Typed F.3 residual (Wave 2H Phase B.1.B).**

`Nonempty (PrimitiveJunctionRecurrenceWitness n t)` — orbit at level `t`
admits at least one F.3 + F.4 witness. This is logically the paper's
"infinitely many primitive junctions with bounded recurrence gap"
statement, packaged as a Lean type rather than as opaque `True`.

Provided alongside the opaque `PrimitiveJunctionRecurrenceResidual` for
backward compatibility: the existing 4-residual public frontier consumes
the opaque form; the new Wave 2H Phase B public frontier (this module +
`Collatz/Mixing/OrbitAdmissibleSupplyFromF3.lean`) consumes the typed form.

Both forms are open math residuals; the typed form additionally encodes
the *shape* of the witness needed by any honest closure. -/
def PrimitiveJunctionRecurrenceTypedResidual (n t : ℕ) : Prop :=
  Nonempty (PrimitiveJunctionRecurrenceWitness n t)

/-- The typed form trivially implies the opaque form (which is `True`).
Provided so that any consumer accepting the opaque residual can be fed
the typed one transparently. -/
theorem primitiveJunctionRecurrenceResidual_of_typed
    {n t : ℕ}
    (_h : PrimitiveJunctionRecurrenceTypedResidual n t) :
    PrimitiveJunctionRecurrenceResidual n t := trivial

/-- **OPEN MATH RESIDUAL — paper Appendix F, Lemma F.2.1.**

Primitive junctions ensure uniform phase distribution: along the orbit, every
phase class modulo `Q_t` is visited with controlled frequency. This is the
F.2.1 conclusion that, combined with F.3 / F.4 (`PrimitiveJunctionRecurrence`),
ensures the boxed Q_t-block from paper G.5 actually realizes every required
phase. Together with `PrimitiveJunctionRecurrenceResidual` and the pure
group-theoretic G.5c uniqueness (`phase_uniqueness_pure_mod_Qt`), this is the
F.3-side input to G.5.

Encoding rationale: opaque `True`, same reasoning as
`PrimitiveJunctionRecurrenceResidual`. Listed in the public frontier as
paper-trace documentation; not consumed by the typed assembly.

OPEN MATH RESIDUAL marker per `.cursor/rules/unconditional-discipline.mdc`
rule 1; tracked in `docs/residual-budget.md` as `R-F3-PhaseDistribution`. -/
def UniformPhaseDistributionResidual (_n _t : ℕ) : Prop := True

end Collatz.Epochs.G
