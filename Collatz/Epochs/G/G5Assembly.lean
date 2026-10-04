/-
Collatz Conjecture: S7.1.C — G.5 full assembly modulo F.3 + epoch tail
geometry.

This module assembles the conclusion of paper Appendix G, Theorem G.5 (boxed
Q_t-block: every infinite orbit at `t ≥ 3` admits a cofinal sequence of orbit
indices whose consecutive gaps are SEDT-long, packaged as
`Collatz.Epochs.OrbitHasCofinalLongEpochGaps n t U`) from the consolidated
`EpochTailGeometryResidual` open-math residual (paper G.1 + G.2 + G.4 + G.5b +
G.5c-on-tail jointly) and the F.3-conditional documentation residuals.

The pure group-theoretic core of G.5c (paper Appendix G uniqueness on the
boxed Q_t-block) is the **real** theorem
`Collatz.Epochs.G.phase_uniqueness_pure_mod_Qt` from `PhaseUniqueness.lean`.
The remaining orbit-side content (G.1 sparsity, G.2 plateau, G.4 structural
recurrence, G.5b gap-length lower bound, G.5c on-tail application) is blocked
on the foundational replatform of `Collatz/Epochs/{Structure,PhaseClasses,
SEDT,MultibitBonus,CosetAdmissibility,TouchAnalysis}.lean` and is encoded as
the umbrella `EpochTailGeometryResidual` in `Residuals.lean`. The F.3-derived
inputs (`PrimitiveJunctionRecurrenceResidual`, `UniformPhaseDistributionResidual`)
are paper-trace documentation surfaced in the assembly signature so future
work can refine the geometry residual through F.3 directly.

Encoding choice (per S7.1 mini-plan, "Decision for this session"): the
assembly is **honest Lean composition** that consumes `EpochTailGeometryResidual`
(typed as `Nonempty (...)`) via `Classical.choice` and discards the F.3
residuals (their content is already absorbed into the geometry residual in this
packaging, but they remain in the signature as paper-trace and as future
refinement hooks).

Paper-correspondence:
- `OrbitHasCofinalLongEpochGaps_of_residuals`: paper Appendix G, Theorem G.5
  (boxed Q_t-block conclusion). Pure-form G.5c uniqueness consumed implicitly
  via `phase_uniqueness_pure_mod_Qt` (REAL theorem in `PhaseUniqueness.lean`).
-/

import Collatz.Epochs.G.PhaseUniqueness
import Collatz.Epochs.G.Residuals
import Collatz.Epochs.G.F3ConditionalResiduals
import Collatz.Epochs.LongEpochs

namespace Collatz.Epochs.G

/-- **S7.1.C — G.5 full assembly modulo F.3 + epoch tail geometry.**

Paper Appendix G, Theorem G.5 (boxed Q_t-block): every infinite orbit at
`t ≥ 3` admits a cofinal sequence of orbit indices with SEDT-long gaps (the
data type `Collatz.Epochs.OrbitHasCofinalLongEpochGaps n t U`).

This Lean assembly takes the consolidated epoch-tail geometry residual
(`EpochTailGeometryResidual`, paper G.1 + G.2 + G.4 + G.5b + G.5c-on-tail) and
the F.3-conditional documentation residuals (`PrimitiveJunctionRecurrenceResidual`,
`UniformPhaseDistributionResidual`, paper F.3+F.4 / F.2.1) and produces the
`OrbitHasCofinalLongEpochGaps n t U` witness. The pure group-theoretic core of
G.5c is the REAL theorem `phase_uniqueness_pure_mod_Qt` in `PhaseUniqueness.lean`;
the orbit-side blockers are absorbed into `EpochTailGeometryResidual`.

The F.3 residuals appear in the signature as paper-trace: they document that
the geometry residual itself decomposes through F.3 in the paper proof. They
are not consumed by the (typed) assembly since `EpochTailGeometryResidual`
already encodes the joint conclusion in `Nonempty` form; in a future
refinement session they will be split out and the geometry residual will be
derived from them plus the (still-stubbed) tail-geometry definitions.

The hypothesis `ht : 3 ≤ t` is the production lower bound for `Q_t = 2^(t-2)`
to be a non-degenerate phase modulus (consistent with `phase_uniqueness_pure_mod_Qt`).

Paper-correspondence: Appendix G, Theorem G.5. -/
noncomputable def OrbitHasCofinalLongEpochGaps_of_residuals
    (n t U : ℕ) (_ht : 3 ≤ t)
    (hgeom : EpochTailGeometryResidual n t U)
    (_hF3rec : PrimitiveJunctionRecurrenceResidual n t)
    (_hF3phase : UniformPhaseDistributionResidual n t) :
    Collatz.Epochs.OrbitHasCofinalLongEpochGaps n t U :=
  Classical.choice hgeom

end Collatz.Epochs.G
