import Collatz

/-!
# Residual sanity tests

Regression guard against vacuous frontiers: every hypothesis of every public
convergence theorem (conclusion `∃ k, T^[k] n = 1`) must be satisfiable at
`n = 1`, and the theorem must actually be applicable there. Additionally, all
per-orbit residuals are shown to hold for every `n` whose orbit reaches `1`
(so they are implied by the Collatz conjecture and cannot be inconsistent
with it).

Public convergence theorems covered:

* `Collatz.CycleExclusion.reaches_one_of_periodic_of_no_cycle`
* `Collatz.Convergence.reaches_one_of_bounded_of_no_cycle_on_orbit`
* `Collatz.Convergence.collatz_of_no_cycles_and_bounded` (global hypotheses;
  shown equivalent to the conclusion by `collatz_iff_no_cycles_and_bounded`)
* `Collatz.Convergence.collatz_convergence`
* `Collatz.Convergence.collatz_convergence_from_aperiodic_orbit_epoch_envelope`
* `Collatz.Convergence.collatz_convergence_modulo_explicit_residuals`
* `Collatz.Convergence.collatz_convergence_unconditional_modulo_explicit_residuals`

All proofs are ordinary kernel proofs.
-/

open Collatz.Foundations Collatz.CycleExclusion Collatz.Convergence

namespace Collatz.Tests.ResidualSanity

/-- `T(1) = 1`, proved by unfolding `ν₂(4) = 2`. -/
theorem step_one : collatz_step 1 = 1 := by
  have h4 : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_two]
  simp [collatz_step, step_type, Collatz.Arithmetic.e, h4]

theorem odd_one' : Odd (1 : ℕ) := odd_one

theorem periodic_one : orbit_eventually_periodic 1 := orbit_eventually_periodic_one

/-! ## Each residual holds at `n = 1` -/

theorem no_cycle_on_orbit_one' : NoNontrivialCycleOnOrbit 1 := no_cycle_on_orbit_one

theorem orbit_no_tail_one : OrbitNoNontrivialPeriodicTail 1 :=
  orbit_no_nontrivial_periodic_tail_one

theorem periodic_residual_one : PeriodicConvergenceResidual 1 := orbit_no_tail_one

theorem periodic_cycle_premises_residual_one : PeriodicCyclePremisesResidual 1 :=
  orbit_no_tail_one

theorem bridge_contract_one : periodic_orbit_bridge_contract 1 := orbit_no_tail_one

theorem aperiodic_residual_one : AperiodicConvergenceResidual 1 :=
  aperiodic_convergence_residual_of_eventually_periodic periodic_one

theorem bounded_one : orbit_bounded 1 := orbit_bounded_one

theorem params_exist : ∃ β : ℝ, sedt_dominant_parameters 3 1 β :=
  exists_sedt_dominant_parameters 3 1 (by decide) (by decide)

theorem envelope_one (β : ℝ) : canonical_aperiodic_orbit_epoch_sedt_envelope 1 3 1 β :=
  fun ha => absurd periodic_one ha

/-- The (Type-valued) aperiodic witness hypothesis of `collatz_convergence` at `n = 1`. -/
def witness_one (β : ℝ) :
    ∀ _ha : ¬ orbit_eventually_periodic 1, OrbitLongEpochE2Witness 1 3 1 β :=
  fun ha => absurd periodic_one ha

/-! ## Frontier sanity: each convergence theorem applies at `n = 1` -/

theorem frontier_periodic : ∃ k, (collatz_step^[k]) 1 = 1 :=
  reaches_one_of_periodic_of_no_cycle periodic_one no_cycle_on_orbit_one'

theorem frontier_bounded : ∃ k, (collatz_step^[k]) 1 = 1 :=
  reaches_one_of_bounded_of_no_cycle_on_orbit bounded_one no_cycle_on_orbit_one'

theorem frontier_collatz_convergence : ∃ k, (collatz_step^[k]) 1 = 1 := by
  obtain ⟨β, hp⟩ := params_exist
  exact collatz_convergence 1 3 1 β odd_one' bridge_contract_one (witness_one β) hp

theorem frontier_envelope : ∃ k, (collatz_step^[k]) 1 = 1 := by
  obtain ⟨β, hp⟩ := params_exist
  exact collatz_convergence_from_aperiodic_orbit_epoch_envelope 1 3 1 β odd_one' hp
    bridge_contract_one (envelope_one β)

theorem frontier_explicit_residuals : ∃ k, (collatz_step^[k]) 1 = 1 :=
  collatz_convergence_modulo_explicit_residuals 1 odd_one' periodic_residual_one
    aperiodic_residual_one

theorem frontier_explicit_residuals_alias : ∃ k, (collatz_step^[k]) 1 = 1 :=
  collatz_convergence_unconditional_modulo_explicit_residuals 1 odd_one'
    periodic_residual_one aperiodic_residual_one

/-- The global endpoint `collatz_of_no_cycles_and_bounded` has global hypotheses
(open conjectures). They are exactly equivalent to its conclusion, hence
consistent with it. -/
theorem frontier_global_equivalence :
    (∀ n : ℕ, Odd n → ∃ k : ℕ, (collatz_step^[k]) n = 1) ↔
      NoNontrivialCycles ∧ ∀ n : ℕ, Odd n → orbit_bounded n :=
  collatz_iff_no_cycles_and_bounded

/-- The instances at `x = 1` of the global hypotheses hold. -/
theorem global_hypotheses_at_one :
    (∀ p : ℕ, 0 < p → (collatz_step^[p]) 1 = 1 → (1 : ℕ) = 1) ∧ orbit_bounded 1 :=
  ⟨fun _ _ _ => rfl, bounded_one⟩

/-! ## Every convergent `n` satisfies all per-orbit residuals -/

theorem residuals_of_reaches_one {n k : ℕ} (h : (collatz_step^[k]) n = 1) :
    PeriodicConvergenceResidual n ∧ AperiodicConvergenceResidual n ∧
      orbit_bounded n ∧ NoNontrivialCycleOnOrbit n := by
  have hno : NoNontrivialCycleOnOrbit n := no_cycle_on_orbit_of_reaches_one h
  have hbdd : orbit_bounded n := orbit_bounded_of_reaches_one h
  exact ⟨(orbit_no_nontrivial_periodic_tail_iff_no_cycle_on_orbit n).2 hno,
    aperiodic_convergence_residual_of_eventually_periodic
      (orbit_eventually_periodic_of_bounded n hbdd),
    hbdd, hno⟩

end Collatz.Tests.ResidualSanity

#print axioms Collatz.Tests.ResidualSanity.step_one
#print axioms Collatz.Tests.ResidualSanity.frontier_collatz_convergence
#print axioms Collatz.Tests.ResidualSanity.frontier_envelope
#print axioms Collatz.Tests.ResidualSanity.frontier_explicit_residuals
#print axioms Collatz.Tests.ResidualSanity.residuals_of_reaches_one
