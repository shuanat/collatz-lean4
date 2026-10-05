/-
Axiom check for the public surface of collatz-lean4.

Every declaration printed below must depend on at most the standard
kernel axioms `propext`, `Classical.choice`, `Quot.sound`. Run with
`lake env lean Collatz/Tests/AxiomCheck.lean` (or `lake build Collatz.Tests.AxiomCheck`).

A clean list only means that no placeholder proof, extra axiom or compiled
decision procedure leaked in.
It says nothing about the strength of the hypotheses: the convergence theorems
below are CONDITIONAL on open hypotheses. Satisfiability of those hypotheses at
`n = 1` is checked separately in `Collatz/Tests/ResidualSanity.lean`; facts about
removed (vacuous) hypotheses are in `Collatz/Tests/VacuityRegression.lean`.

Sections:

1. Conditional convergence endpoints (`Collatz/Convergence/MainTheorem.lean`)
   and the periodic-side layer (`Collatz/CycleExclusion/PeriodicTailBridge.lean`).
2. Proved unconditional lemmas used by them (coercivity contradiction, fixed
   point uniqueness, no pure e=1 cycles, the cycle/divergence equivalence).
3. Algebraic lemmas from `Foundations`, `Epochs`, `SEDT`, `Mixing` (not used by
   any convergence theorem; their status is stated in the module docstrings).
-/

import Collatz

open Collatz.Convergence

-- 1. Conditional convergence endpoints.
#print axioms Collatz.Convergence.collatz_of_no_cycles_and_bounded
#print axioms Collatz.Convergence.reaches_one_of_bounded_of_no_cycle_on_orbit
#print axioms Collatz.CycleExclusion.reaches_one_of_periodic_of_no_cycle
#print axioms Collatz.Convergence.collatz_convergence
#print axioms Collatz.Convergence.collatz_convergence_from_aperiodic_orbit_epoch_envelope
#print axioms Collatz.Convergence.collatz_convergence_modulo_explicit_residuals
#print axioms Collatz.Convergence.collatz_convergence_unconditional_modulo_explicit_residuals

-- 2. Proved lemmas (unconditional).
#print axioms Collatz.Convergence.collatz_iff_no_cycles_and_bounded
#print axioms Collatz.Convergence.false_of_orbit_epoch_sedt_envelope
#print axioms Collatz.Convergence.aperiodic_convergence_residual_iff_eventually_periodic
#print axioms Collatz.Convergence.orbit_bounded_of_reaches_one
#print axioms Collatz.Convergence.fixed_point_eq_one
#print axioms Collatz.CycleExclusion.collatz_step_one
#print axioms Collatz.CycleExclusion.no_pure_e1_cycle
#print axioms Collatz.CycleExclusion.orbit_no_nontrivial_periodic_tail_iff_no_cycle_on_orbit
#print axioms Collatz.CycleExclusion.no_cycle_on_orbit_of_no_nontrivial_cycles
#print axioms Collatz.CycleExclusion.no_cycle_on_orbit_of_reaches_one
#print axioms Collatz.CycleExclusion.cycle_of_periodic_tail_witness_valid
#print axioms Collatz.Epochs.G.phase_uniqueness_pure_mod_Qt

-- 3. Algebraic / research lemmas from Foundations, Epochs, SEDT, Mixing. None of
--    them is a hypothesis or ingredient of the convergence endpoints in
--    section 1. Lemmas about the auxiliary sequence `N_k` / `(Mentry, v)` say
--    nothing about Collatz orbits (see the module docstrings).
#print axioms Collatz.Foundations.collatz_step_three_eq_five
#print axioms Collatz.Foundations.iterate_log_compression_of_odd_segment
#print axioms Collatz.Foundations.collatz_step_le_self_of_step_type_ge_two

#print axioms Collatz.OrdFact.orderOf_three_eq_pow_two
#print axioms Collatz.OrdFact.three_pow_Qt_modEq_one
#print axioms Collatz.OrdFact.isUnit_three_zmod
#print axioms Collatz.OrdFact.isUnit_five_zmod
#print axioms Collatz.OrdFact.isUnit_three_inv_zmod
#print axioms Collatz.OrdFact.natCast_s_t_eq
#print axioms Collatz.OrdFact.isUnit_natCast_s_t

#print axioms Collatz.SEDT.OrbitDepth.cumulative_depth_identity
#print axioms Collatz.SEDT.OrbitBridge.step_type_ge_two_iff_depth_eq_one
#print axioms Collatz.SEDT.OrbitBridge.depth_minus_collatz_step_of_step_type_one
#print axioms Collatz.SEDT.AffineNumerator.N_k_int_recurrence
#print axioms Collatz.SEDT.AffineNumerator.M_k_succ_of_lt
#print axioms Collatz.SEDT.AffineNumerator.M_k_succ_of_gt
#print axioms Collatz.SEDT.AffineNumerator.M_k_ModEq_succ_of_lt
#print axioms Collatz.SEDT.TouchDensity.touchCount_discrepancy
#print axioms Collatz.SEDT.MultibitBonus.multibit_period_bonus_eq
#print axioms Collatz.SEDT.LinearSurplusReal.linear_surplus_real_budget

#print axioms Collatz.Mixing.AdmissibleTailF01_iff_exists_pow
#print axioms Collatz.Mixing.AdmissibleTailF01_witness_lt_Qt
#print axioms Collatz.Mixing.AdmissibleTailF01.touch_count_eq_one
#print axioms Collatz.Mixing.AdmissibleTailF01.touch_count_eq_one_expanded
#print axioms Collatz.Mixing.AdmissibleTailF01.touch_count_eq_one_of_realized

#print axioms Collatz.Mixing.OrbitSideAggregateTouchRateResidual
#print axioms Collatz.Mixing.orbit_aggregate_touch_count_lower_of_residual
#print axioms Collatz.Mixing.orbit_aggregate_touch_count_zero
#print axioms Collatz.Mixing.orbit_aggregate_touch_count_mono

-- 4. Elementary proved results (2026-10): exact odd step, preimage layers
--    (paper §3: Prop. 3.1, Lemma 3.4, Lemma 3.5.a, Prop. 3.5, Cor. 3.5.b), block step
--    (Lemma 2.13) and the block form of the cycle equation (Prop. H.7(a),(c)).
--    None of them is a hypothesis or ingredient of a convergence endpoint; H.7 is
--    an equivalent reformulation of the cycle condition and excludes no cycle.
#print axioms Collatz.Foundations.factorization_two_pow_mul_of_odd
#print axioms Collatz.Foundations.two_pow_factorization_mul_odd_part
#print axioms Collatz.Foundations.two_pow_step_type_mul_collatz_step
#print axioms Collatz.Foundations.step_type_eq_of_three_mul_add_one_eq
#print axioms Collatz.Foundations.collatz_step_eq_of_three_mul_add_one_eq
#print axioms Collatz.Foundations.depth_minus_eq_of_add_one_eq
#print axioms Collatz.Foundations.exists_odd_add_one_eq_two_pow_depth_mul
#print axioms Collatz.Layers.two_pow_mod_three
#print axioms Collatz.Layers.one_le_layer_base_exp
#print axioms Collatz.Layers.two_pow_mul_mod_three_eq_one_iff
#print axioms Collatz.Layers.two_pow_layer_mul_mod_three
#print axioms Collatz.Layers.three_mul_layer_elem_add_one
#print axioms Collatz.Layers.odd_layer_elem
#print axioms Collatz.Layers.layer_elem_pos
#print axioms Collatz.Layers.collatz_step_layer_elem
#print axioms Collatz.Layers.step_type_layer_elem
#print axioms Collatz.Layers.layer_elem_succ
#print axioms Collatz.Layers.layer_elem_mod_four
#print axioms Collatz.Layers.layer_elem_strictMono
#print axioms Collatz.Layers.not_three_dvd_collatz_step
#print axioms Collatz.Layers.collatz_step_mod_three_eq_two_iff
#print axioms Collatz.Layers.layer_base_exp_add_two_mul_eq_step_type
#print axioms Collatz.Layers.layer_elem_collatz_step
#print axioms Collatz.Layers.existsUnique_preimage_layer
#print axioms Collatz.Layers.preimage_layer_eq_empty_of_three_dvd
#print axioms Collatz.Layers.range_layer_elem
#print axioms Collatz.Layers.layer_elem_bijOn
#print axioms Collatz.Layers.preimage_layer_eq_empty_iff
#print axioms Collatz.Layers.preimage_layer_infinite
#print axioms Collatz.Layers.layer_elem_pair_bijOn
#print axioms Collatz.Layers.step_type_layer_elem_eq_one_iff
#print axioms Collatz.Blocks.step_of_add_one_eq_two_pow_mul
#print axioms Collatz.Blocks.iterate_add_one_of_lt
#print axioms Collatz.Blocks.step_type_iterate_eq_one
#print axioms Collatz.Blocks.iterate_lt_iterate_succ
#print axioms Collatz.Blocks.iterate_pred_add_one
#print axioms Collatz.Blocks.depth_minus_iterate_pred
#print axioms Collatz.Blocks.three_mul_iterate_pred_add_one
#print axioms Collatz.Blocks.one_le_block_sigma
#print axioms Collatz.Blocks.three_mul_iterate_pred_add_one_eq_two_pow_mul
#print axioms Collatz.Blocks.step_type_iterate_pred
#print axioms Collatz.Blocks.iterate_block_length
#print axioms Collatz.Blocks.two_pow_sigma_mul_iterate_block_length
#print axioms Collatz.Blocks.depth_minus_eq_of_block_exponents
#print axioms Collatz.CycleExclusion.block_start_equation
#print axioms Collatz.CycleExclusion.realizesOneBlock_odd_part
#print axioms Collatz.CycleExclusion.realizesOneBlock_add_one_mul
#print axioms Collatz.CycleExclusion.exists_realizesOneBlock_iff
#print axioms Collatz.CycleExclusion.blockPatternC_succ
#print axioms Collatz.CycleExclusion.blockPatternC_pos
#print axioms Collatz.CycleExclusion.block_telescope
#print axioms Collatz.CycleExclusion.realizesBlockPattern_two_pow_mul
#print axioms Collatz.CycleExclusion.realizesBlockPattern_block_equation
#print axioms Collatz.CycleExclusion.realizesBlockPattern_one_iff
#print axioms Collatz.CycleExclusion.blockPatternC_one
#print axioms Collatz.CycleExclusion.realizesOneBlock_unique
