/-
Paper-code mapping for collatz-lean4.
-/

namespace Collatz.Documentation

/-!
## Status (2026-10 review) — authoritative

This library does **not** prove the Collatz conjecture, and no step of the
original paper chain `D.1 -> {E.2, F.6/F.7, G.5} -> H.main -> I.1` is
formalized as a theorem about Collatz orbits. In the corrected paper E.2, F.3/F.4,
G.5 and the proof of H.main are withdrawn; I.1 is replaced by a conditional
reformulation.

Public endpoints (`Collatz/Convergence/MainTheorem.lean`), all conditional on
OPEN hypotheses, all of whose hypotheses hold for `n = 1`
(`Collatz/Tests/ResidualSanity.lean`):

| Lean theorem | hypotheses | remark |
|---|---|---|
| `collatz_of_no_cycles_and_bounded` | `NoNontrivialCycles`, all odd orbits bounded | exact reformulation (`collatz_iff_no_cycles_and_bounded`) |
| `reaches_one_of_bounded_of_no_cycle_on_orbit` | `orbit_bounded n`, `NoNontrivialCycleOnOrbit n` | pointwise |
| `CycleExclusion.reaches_one_of_periodic_of_no_cycle` | `orbit_eventually_periodic n`, `NoNontrivialCycleOnOrbit n` | periodic branch |
| `collatz_convergence_modulo_explicit_residuals` (+ `_unconditional_` alias) | `PeriodicConvergenceResidual n`, `AperiodicConvergenceResidual n` | for odd `n` the second hypothesis ⇔ eventual periodicity |
| `collatz_convergence` | periodic contract, aperiodicity-guarded E.2 witness, single `β` | same remark |
| `collatz_convergence_from_aperiodic_orbit_epoch_envelope` | periodic contract, single-`β` envelope | same remark |

Paper label → Lean status:

- B.2 (`ord_{2^t}(3) = 2^{t−2}`): proved, `Collatz.OrdFact.orderOf_three_eq_pow_two`.
- Exact odd step `3m + 1 = 2^{e(m)} T(m)` and its converse: proved,
  `Foundations.two_pow_step_type_mul_collatz_step`,
  `Foundations.step_type_eq_of_three_mul_add_one_eq`,
  `Foundations.collatz_step_eq_of_three_mul_add_one_eq` (`Foundations/OddPart.lean`).
- §2 Def. 2.3 / 2.5 and §3 (preimage layers `S_n`, `k₀(n)`, `m(n,t)`): proved,
  `Collatz/Layers/PreimageLayers.lean` (`preimage_layer`, `layer_base_exp`,
  `layer_elem`). Prop. 3.1: `Layers.existsUnique_preimage_layer`,
  `Layers.not_three_dvd_collatz_step`; Lemma 3.4:
  `Layers.preimage_layer_eq_empty_iff`, `Layers.preimage_layer_infinite`;
  Lemma 3.5.a: `Layers.two_pow_mul_mod_three_eq_one_iff`; Prop. 3.5:
  `Layers.odd_layer_elem`, `Layers.collatz_step_layer_elem`,
  `Layers.step_type_layer_elem`, `Layers.layer_elem_succ`,
  `Layers.layer_elem_bijOn`; Cor. 3.5.b: `Layers.layer_elem_pair_bijOn`,
  `Layers.layer_elem_collatz_step`. Lemma 3.5.d: (a)
  `Layers.collatz_step_mod_three_eq_two_iff` (`T m ≡ 2 mod 3 ↔ e(m)` odd, all
  `m : ℕ`); (b) first sentence `Layers.step_type_layer_elem_eq_one_iff`
  (`e(m(n,t)) = 1 ↔ t = 0 ∧ n ≡ 2 mod 3`), second sentence
  `Layers.layer_elem_mod_four` (`m(n,t) ≡ 1 mod 4`, `t ≥ 1`); (c) (touches in
  layer coordinates): not formalized; (d)
  `Layers.layer_base_exp_add_two_mul_eq_step_type` (`e(m) = k₀(n) + 2t`,
  `t = (e(m) − k₀(n))/2`).
- Lemma 2.13 (block step), positive odd `x` only: proved,
  `Collatz/Blocks/BlockStep.lean` — (a) `Blocks.iterate_add_one_of_lt`,
  `Blocks.step_type_iterate_eq_one`; (b) `Blocks.iterate_pred_add_one`,
  `Blocks.depth_minus_iterate_pred`, `Blocks.step_type_iterate_pred`,
  `Blocks.one_le_block_sigma`; (c) `Blocks.iterate_block_length`;
  (d) `Blocks.iterate_lt_iterate_succ`; converse
  `Blocks.depth_minus_eq_of_block_exponents`.
- H.7 (block form of the cycle equation), positive case: proved parts in
  `Collatz/CycleExclusion/BlockEquation.lean` — (H.7.2)
  `CycleExclusion.block_start_equation`; (a) for `k` blocks
  `CycleExclusion.realizesBlockPattern_block_equation` (`y₁ D = C(w)`, `D > 0`,
  `D ∣ C(w)`); (c) `CycleExclusion.exists_realizesOneBlock_iff`,
  `CycleExclusion.realizesOneBlock_add_one_mul`,
  `CycleExclusion.realizesOneBlock_unique`. Not formalized: the converse
  of (b) for `k ≥ 2` (rotations), and (d) (negative integers). H.7 is an
  equivalent reformulation of the cycle condition; it excludes no cycle.
- C.4 / depth dynamics: proved on the orbit —
  `SEDT.OrbitBridge.step_type_ge_two_iff_depth_eq_one`,
  `SEDT.OrbitBridge.depth_minus_collatz_step_of_step_type_one`,
  `SEDT.OrbitDepth.cumulative_depth_identity`.
- D.0 / D.1 / D.8 / D.10 (numerator `N_k = 3^{k+1}(r₀+2) − 5·2^k`, `+5` formula,
  case split, homogenization): only correct algebra about this *auxiliary*
  sequence (`SEDT.AffineNumerator`, `SEDT.Homogenization`, base case `k = 0` in
  `SEDT.OrbitBridge`). `N_k` is not the orbit numerator for `k ≥ 1`
  (true identity: `2^k(3r_k+1) = 3^{k+1}(r₀+1) − 2^{k+1}` on an `e = 1` run).
- D.2 / D.4 / D.5 (multibit bonus, touch density, linear surplus): generic
  counting lemmas (`SEDT.MultibitBonus`, `SEDT.TouchDensity`,
  `SEDT.LinearSurplus`, `SEDT.LinearSurplusReal`) with explicit hypotheses that
  are not established for orbits; the surplus lemmas are *lower* bounds.
- E.1 / E.2 (SEDT): withdrawn. The envelope appears only as a hypothesis
  (`orbit_epoch_sedt_envelope`). Proved fact:
  `false_of_orbit_epoch_sedt_envelope` — at dominant parameters it is
  contradictory on every long-epoch stream of an odd orbit; the `∀ β` form is
  equivalent to eventual periodicity (`Tests/VacuityRegression.lean`).
- F.0.1 / F.6 (per plateau): `Mixing.AdmissibleTailF01.touch_count_eq_one` —
  algebra in `ZMod (2^t)` about auxiliary-sequence data; the window version
  `touch_count_eq_one_of_realized` has hypotheses that fail on every orbit
  reaching `1`.
- F.3 / F.4 (primitive junctions): withdrawn; nothing formalized
  (`Epochs.G.PrimitiveJunctionRecurrenceWitness` is orbit-independent and kept
  only for a regression test).
- F.6 aggregate / F.7: conjecture; `Mixing.OrbitSideAggregateTouchRateResidual`
  states an aggregate touch-rate hypothesis for non-eventually-periodic orbits;
  no theorem uses it.
- G.5 (long epochs): withdrawn; only the pure group-theoretic lemma
  `Epochs.G.phase_uniqueness_pure_mod_Qt`. `Epochs.LongEpochs` contains index
  bookkeeping only.
- H.main (cycle exclusion): withdrawn; appears as the open hypothesis
  `NoNontrivialCycleOnOrbit` / `NoNontrivialCycles`. Proved:
  `no_pure_e1_cycle`, `fixed_point_eq_one`.
- I.1: conditional endpoints above. Lemma I.2 (coercivity for every orbit) is
  the no-divergence conjecture and is not formalized; `Convergence.Coercivity`
  only sums an assumed per-epoch bound.

## Deletions in the 2026-10 clean-up

Removed because they were placeholders carrying paper names (statements that
restate their hypotheses, `∃ x, x ≤ x`, `rfl`-facts about toy definitions such as
`N_k := k + 1` or `sedt_envelope := 0`), trivially inhabited or unsatisfiable
residual structures, or conditional plumbing that only fed removed endpoints:

- modules `SEDT/Axioms`, `SEDT/Theorems`, `SEDT/DepthBookkeeping`,
  `SEDT/AperiodicGainBridge`, `Epochs/APStructure`, `Epochs/Homogenization`,
  `Epochs/NumeratorCarry`, `Epochs/Aliases`, `Mixing/PhaseMixing`,
  `Mixing/TouchFrequency`, `Mixing/TouchFrequencyLocal`,
  `Mixing/TouchFrequencyBridge`, `Mixing/TouchFrequencyHomogenization`,
  `Mixing/Semigroup`, `Mixing/OrbitAdmissibleSupplyFromF3`,
  `Mixing/OrbitTouchMaxGap`, all of `Stratified/`, `Utilities/`, `Examples/`;
- in `Convergence/MainTheorem` ~3200 lines of aperiodicity-guarded
  phase-return / filler / carry plumbing (including
  `AperiodicSelectedLongEpochResidual`), in `Convergence/Coercivity` the
  phase-return chain and the placeholders `coercivity`,
  `coercivity_concatenation`, in `Epochs/LongEpochs` ~3300 lines of filler /
  boundary plumbing and the toy sample block.

Residual structures removed with them (status at removal):
`LocalAffinePairResidual`, `AdmissibleTailLocalAffinePairResidual`,
`AdmissibleTailTouchFrequencyResidual` (false on every orbit reaching `1` for
`t ≥ 3`, trivially true at `t = 0`), `RawPrefixTouchFrequency*`,
`AdmissibleTailTouchLowerBoundResidual`, `AdmissibleTailTouchFrequencyWitness`
(trivially inhabited: free count function), `SelectedLongEpochBridge`
(empty at `(t, U) = (3, 1)` for every odd `m`), `phase_return_epoch_accounting_witness` (false for
odd `m` at `(3, 1, 4)`), `CanonicalAperiodicMultibitGainBound` (equivalent to
the depth bookkeeping bound, which forces `depth₋(start) ≥ (2−α)L − C + 1`),
`PrimitiveJunctionAdmissibilitySupplyResidual` and the orbit max-gap residual
(uniform touch-gap bounds, heuristically false).

## CI guardrails

`.github/workflows/lean.yml` builds `Collatz` and the three test targets
(`ResidualSanity`, `VacuityRegression`, `AxiomCheck`) and rejects placeholder
proofs and extra axioms in the listed chain files.
-/

end Collatz.Documentation
