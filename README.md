# Collatz Lean4 Formalization

Lean 4 workspace accompanying the Collatz/SEDT paper.

## Status (2026-10 review) — read first

**This library does not prove the Collatz conjecture.** Every convergence
theorem in it (conclusion `∃ k, T^[k] n = 1`, where `T = collatz_step` is the
odd-step map `n ↦ (3n+1)/2^{ν₂(3n+1)}`) is *conditional* on explicitly named
open hypotheses. A clean `#print axioms` list only certifies the absence of
`sorry`/`axiom`; it says nothing about the strength of the hypotheses.

Public endpoints (`Collatz/Convergence/MainTheorem.lean`):

| Theorem | Hypotheses (open unless stated) |
|---|---|
| `collatz_of_no_cycles_and_bounded` | `NoNontrivialCycles`; every odd orbit bounded. Exact reformulation: `collatz_iff_no_cycles_and_bounded` proves the converse. |
| `reaches_one_of_bounded_of_no_cycle_on_orbit` | `orbit_bounded n`; `NoNontrivialCycleOnOrbit n` |
| `CycleExclusion.reaches_one_of_periodic_of_no_cycle` | `orbit_eventually_periodic n`; `NoNontrivialCycleOnOrbit n` |
| `collatz_convergence_modulo_explicit_residuals` (and the compatibility alias `collatz_convergence_unconditional_modulo_explicit_residuals`, which is *not* unconditional) | `PeriodicConvergenceResidual n`; `AperiodicConvergenceResidual n` |
| `collatz_convergence`, `collatz_convergence_from_aperiodic_orbit_epoch_envelope` | periodic contract (= no nontrivial cycle on the orbit); single-`β` SEDT envelope / E.2 witness guarded by aperiodicity |

Facts proved without extra hypotheses:

- `false_of_orbit_epoch_sedt_envelope`: at dominant parameters the SEDT
  envelope cannot hold on any long-epoch stream of an odd orbit. Hence, for odd
  `n`, `AperiodicConvergenceResidual n` is *equivalent* to eventual periodicity
  of the orbit (`aperiodic_convergence_residual_iff_eventually_periodic`): the
  SEDT route contributes no information beyond "the orbit does not diverge".
- `no_pure_e1_cycle`: no cycle consists only of `e = 1` steps.
- `fixed_point_eq_one`: `T(x) = x ⇒ x = 1`.
- Orbit-level identities: `T(3) = 5`, the growth bound
  `iterate_log_compression_of_odd_segment`, `e(n) ≥ 2 ⇔ depth₋(n) = 1`, and the
  exact depth identity `SEDT.OrbitDepth.cumulative_depth_identity`.
- `Epochs.G.phase_uniqueness_pure_mod_Qt`, `OrdFact.orderOf_three_eq_pow_two`
  (`ord_{2^t}(3) = 2^{t−2}`), and algebraic lemmas in `SEDT/AffineNumerator`,
  `SEDT/{Homogenization,TouchDensity,MultibitBonus,LinearSurplus*}` and
  `Mixing/AdmissibleTail*`. These concern the auxiliary sequence
  `N_k = 3^{k+1}(r₀+2) − 5·2^k` (not the orbit numerator for `k ≥ 1`) or
  abstract periodic predicates; they are not statements about Collatz orbits and
  are not connected to the convergence endpoints.

Sanity guarantees:

- `Collatz/Tests/ResidualSanity.lean`: every hypothesis of every public
  convergence theorem holds for `n = 1`, each theorem is applied at `n = 1`, and
  every per-orbit residual holds for every `n` whose orbit reaches `1`.
- `Collatz/Tests/VacuityRegression.lean`: machine-checked reasons why earlier
  hypotheses were removed (period-`≤ 1` residual ⇔ aperiodicity; unsatisfiable
  `exclusion_premises`; `∀ β` envelope ⇔ eventual periodicity; orbit-independent
  "witness" structures).

What was removed in the 2026-10 fix: the unsatisfiable cycle-exclusion package
(`exclusion_premises`, `RepeatTrick`, `main_cycle_exclusion`, …), the old
`OrbitNoNontrivialPeriodicTail` (false for `n = 1`), the `∀ β` envelope
frontiers (jointly unsatisfiable with the periodic residual), trivially true
residuals (`PrimitiveJunctionRecurrenceResidual`,
`UniformPhaseDistributionResidual`, `EpochTailGeometryResidual`, typed F.3
residual, `PeriodSumTelescopingResidual`, `SEDTPeriodSumContradictionResidual`),
the fake G.5 assembly, and ~50 wrappers built on them
(`Convergence/UnconditionalModuloOrbitWitnesses.lean` was deleted).

Second clean-up pass (stage L2): the library shrank from ~18 000 to ~6 700 lines.
Deleted: placeholder lemmas carrying paper names (e.g. `sedt_full_bound_technical`,
`coercivity`, `coercivity_concatenation`, `period_sum_with_density_negative`,
`phase_mixing_main`, `touch_count_tail_interval`, `minimal_exponent_pinning`);
the toy definitions `Epochs.N_k := k + 1` and `Epochs.sedt_envelope := 0`; the
aperiodicity-guarded plumbing in `MainTheorem`, `Coercivity`, `LongEpochs`
(incl. `AperiodicSelectedLongEpochResidual`); `SEDT/{Axioms,Theorems,
DepthBookkeeping,AperiodicGainBridge}`, `Epochs/{APStructure,Homogenization,
NumeratorCarry,Aliases}`, `Mixing/{PhaseMixing,TouchFrequency*,Semigroup,
OrbitAdmissibleSupplyFromF3,OrbitTouchMaxGap}` and all of `Stratified/`,
`Utilities/`, `Examples/`. Residual structures that were trivially inhabited,
empty / false on every orbit reaching `1`, or heuristically false went with
them; see `../docs/residual-budget.md` §0.2–0.4.

## Production Entry

- `Collatz.lean`
- `Collatz/Production.lean`

## Build

```bash
lake build Collatz
lake build Collatz.Tests.ResidualSanity Collatz.Tests.VacuityRegression Collatz.Tests.AxiomCheck
```

## Documentation

- `Collatz/Documentation/PaperCodeMapping.lean`: paper label → Lean status
  (status table at the top; the long log below it is historical).
- `ACTIVE_FRONTIER.md`: status at the top; older milestone log is superseded.
- `../docs/residual-budget.md`: residual status table (satisfiable at `n = 1`?
  trivial? equivalent to what?).
- `SEMANTIC_HARDENING_PLAN.md`: historical; superseded.

## Notes

- `collatz_step` is the odd-step map; it is not the full mixed even/odd
  Collatz step.
- CI (`.github/workflows/lean.yml`) builds `Collatz` and the three test
  targets and rejects placeholder proofs, extra axioms and `native_decide` in
  the source tree. `grep -rn "sorry\|native_decide\|^axiom" Collatz` is empty.
