/-
Collatz Conjecture: S7.1.A.2/A.3 — Paper-cited orbit-side residuals for the
G.5-modulo-F.3 assembly.

This module collects all OPEN MATH RESIDUAL definitions surfaced by the S7.1
mini-plan as Lean propositions. Per `.cursor/rules/unconditional-discipline.mdc`
each residual carries:

* an explicit `OPEN MATH RESIDUAL` marker,
* paper-citation,
* rationale for the chosen encoding (in particular: why the body is opaque /
  honest paper-trace).

The residuals here are explicitly listed in `docs/residual-budget.md`.

Three residuals are defined here:

1. `EpochTailGeometryResidual n t U`: consolidated umbrella for paper Appendix G
   Lemmas G.1 + G.2 + G.4 + G.5b + G.5c-on-tail. Encoded as the `Nonempty` of
   the existing `Collatz.Epochs.OrbitHasCofinalLongEpochGaps` structure.

   **S7.0.E formalized-conditional-on-aperiodicity (REAL theorem):**
   `epochTailGeometryResidual_of_aperiodic` discharges the residual for any
   `n` satisfying `¬ Collatz.CycleExclusion.orbit_eventually_periodic n`,
   via the existing real production chain
   `aperiodic_orbit_has_cofinal_gap_long_phase_returns` (sorry-free in
   `Collatz/Convergence/MainTheorem.lean` L320) +
   `orbit_has_cofinal_long_epoch_gaps_of_gap_long_phase_returns` +
   `canonical_gap_long_phase_returns_bridge` (sorry-free in
   `Collatz/Epochs/LongEpochs.lean`). Axiom-clean. Therefore R-EpochTailGeometry
   is no longer an OPEN MATH residual under aperiodicity assumption.

   The unconditional `EpochTailGeometryResidual n t U` (without aperiodicity)
   is mathematically false for periodic n (e.g., n = 1: no infinite tail);
   the unconditional residual signature is preserved for backward compatibility
   with the original S7.1 5-residual public frontier, but the (U2)-aligned
   refined frontier (S7.0.E) replaces it with explicit aperiodicity hypothesis
   and the real discharge theorem.

2. `PeriodSumTelescopingResidual n`: paper Appendix H period-sum telescoping
   step. Encoded as the implication
     (∀ β, bulk envelope) → OrbitHasCofinalLongEpochGaps n 3 1 →
       PeriodicConvergenceResidual n
   so that the assembly of the new public frontier is REAL Lean composition
   (no opaque `True`-arrow). The implication body itself is the open math
   content (the period-sum telescoping argument from paper H.main).

Paper-correspondence:
- `EpochTailGeometryResidual` ⇐ paper Appendix G (G.1, G.2, G.4, G.5b, G.5c
  on-tail jointly).
- `epochTailGeometryResidual_of_aperiodic` ⇐ paper Appendix G + the existing
  paper-faithful aperiodic phase-return / canonical bridge infrastructure.
- `PeriodSumTelescopingResidual` ⇐ paper Appendix H, Theorem H.main, the
  period-sum telescoping step, given G.5 long-epoch supply and bulk envelope.
-/

import Collatz.Epochs.LongEpochs
import Collatz.Convergence.MainTheorem

namespace Collatz.Epochs.G

/-- **OPEN MATH RESIDUAL — paper Appendix G (G.1, G.2, G.4, G.5b, G.5c-on-tail).**

Consolidated epoch-tail geometry residual: every infinite orbit at parameters
`(t, U)` admits a cofinal sequence of orbit indices whose consecutive gaps are
SEDT-long (data type `Collatz.Epochs.OrbitHasCofinalLongEpochGaps n t U`).

The full paper proof of this assertion goes through the joint deployment of
paper Appendix G Lemmas G.1 (sparsity of switches), G.2 (long plateau), G.4
(structural recurrence under primitive junctions), G.5b (gap-length lower
bound), and G.5c-on-tail (good phase uniqueness). The pure group-theoretic core
of G.5c is the real Lean theorem `phase_uniqueness_pure_mod_Qt`; the orbit-side
applications of G.1 + G.2 + G.4 + G.5b are blocked on the (currently stubbed)
foundational modules `Collatz/Epochs/{Structure,PhaseClasses,SEDT,MultibitBonus,
CosetAdmissibility,TouchAnalysis}.lean` whose replatform is a future S7.0
session.

Encoding rationale: the residual is encoded as `Nonempty` of the existing
`OrbitHasCofinalLongEpochGaps` structure (rather than `True`) because this is
the precise paper-content that the joint G-Lemmas would establish, and it
allows the G.5 assembly to be honest Lean composition (`Classical.choice` to
extract the witness). This is **not** a degenerate wrapper in the sense of
`unconditional-discipline.mdc` rule 2 — the body of the residual is the
genuine open mathematical assertion.

OPEN MATH RESIDUAL marker per `.cursor/rules/unconditional-discipline.mdc`
rule 1; tracked in `docs/residual-budget.md` as `R-EpochTailGeometry`. -/
def EpochTailGeometryResidual (n t U : ℕ) : Prop :=
  Nonempty (Collatz.Epochs.OrbitHasCofinalLongEpochGaps n t U)

/-- **REAL theorem (S7.0.E formal-first refinement, axiom-clean).**

Discharge of `EpochTailGeometryResidual n t U` for any orbit whose Collatz
trajectory is **not eventually periodic**, established via the existing
sorry-free production chain:

1. `aperiodic_orbit_has_cofinal_gap_long_phase_returns`
   (`Collatz/Convergence/MainTheorem.lean`, real `noncomputable def`):
   given aperiodicity, produces `OrbitHasCofinalGapLongPhaseReturns n t U`.
2. `canonical_gap_long_phase_returns_bridge`
   (`Collatz/Epochs/LongEpochs.lean`, real `def`):
   provides the canonical `GapLongPhaseReturnsBridge n t U`.
3. `orbit_has_cofinal_long_epoch_gaps_of_gap_long_phase_returns`
   (`Collatz/Epochs/LongEpochs.lean`, real `def`):
   composes the two into `OrbitHasCofinalLongEpochGaps n t U`.

The result is wrapped in `Nonempty` to match the residual's signature.

**Significance:** R-EpochTailGeometry is no longer an OPEN MATH residual
under the aperiodicity assumption — it is a REAL Lean theorem. The (U2)-
aligned 4-residual public frontier
`collatz_convergence_modulo_aperiodic_envelope_and_g5_aperiodic_and_f3_and_period_telescoping`
(see `Collatz/Convergence/UnconditionalModuloOrbitWitnesses.lean`) replaces
the unconditional `EpochTailGeometryResidual` hypothesis with an explicit
`¬ Collatz.CycleExclusion.orbit_eventually_periodic n` hypothesis and
discharges the residual internally via this theorem.

The original 5-residual frontier
`collatz_convergence_modulo_aperiodic_envelope_and_g5_modulo_f3_and_period_telescoping`
is preserved for backward compatibility.

Paper-correspondence: paper Appendix G consolidated content + paper-faithful
aperiodic phase-return / canonical bridge infrastructure already proved in
the Lean repository. -/
theorem epochTailGeometryResidual_of_aperiodic
    (n t U : ℕ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) :
    EpochTailGeometryResidual n t U := by
  refine ⟨?_⟩
  exact Collatz.Epochs.orbit_has_cofinal_long_epoch_gaps_of_gap_long_phase_returns
    (Collatz.Epochs.canonical_gap_long_phase_returns_bridge n t U)
    (Collatz.Convergence.aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)

/-- **OPEN MATH RESIDUAL — paper Appendix H, period-sum telescoping step
(H.main, telescoping sub-argument).**

Given (i) the bulk per-long-epoch SEDT envelope at production parameters
`(t, U) = (3, 1)` for every admissible `β`, and (ii) cofinal long-epoch supply
on the orbit (`OrbitHasCofinalLongEpochGaps n 3 1`, mathematically equivalent
to G.5 conclusion at production), the period-sum telescoping argument from
paper Appendix H concludes that no nontrivial periodic tail exists on the
orbit (`Collatz.Convergence.PeriodicConvergenceResidual n`).

This residual encodes exactly the paper telescoping mechanics that take
`Σ ΔV ≤ -ε P + O(1)` over one full period and derive a contradiction with
`Σ ΔV = 0` (forced by exact periodicity), for sufficiently long periods. It is
typed as an implication so the S7.1.D public frontier assembly is real Lean
composition.

Encoding rationale: the implication form is the cleanest paper-faithful
typing — it captures the **derivation step** that paper H.main performs given
its hypotheses. The body of the implication is the open math content
(formalization deferred to a future session, S7.5 candidate).

OPEN MATH RESIDUAL marker per `.cursor/rules/unconditional-discipline.mdc`
rule 1; tracked in `docs/residual-budget.md` as `R-PeriodSumTelescoping`. -/
def PeriodSumTelescopingResidual (n : ℕ) : Prop :=
  (∀ β : ℝ, Collatz.Convergence.canonical_aperiodic_orbit_epoch_sedt_envelope
              n 3 1 β) →
  Collatz.Epochs.OrbitHasCofinalLongEpochGaps n 3 1 →
  Collatz.Convergence.PeriodicConvergenceResidual n

end Collatz.Epochs.G
