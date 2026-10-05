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

/-! ## Preimage layers, block step, block equation (paper §3, Lemma 2.13, Prop. H.7)

These are proved elementary statements, not conditional endpoints. The checks
below show that their hypotheses (`n` odd, `3 ∤ n`; `x + 1 = 2^α y` with `y` odd,
`α ≥ 1`; one-block / `k`-block realizers) are satisfiable, at the trivial
instance `1` and on the paper's tables, and that the cycle criterion is not
vacuous in either direction. -/

section LayersAndBlocks

open Collatz.Layers Collatz.Blocks

theorem odd_five : Odd (5 : ℕ) := ⟨2, by norm_num⟩
theorem odd_seven : Odd (7 : ℕ) := ⟨3, by norm_num⟩
theorem odd_eleven : Odd (11 : ℕ) := ⟨5, by norm_num⟩
theorem odd_thirteen : Odd (13 : ℕ) := ⟨6, by norm_num⟩

/-- Paper §3 "Check" table: `S₅ = 3, 13, 53, 213`; `S₇ = 9, 37, 149, 597`;
`S₁₁ = 7, 29, 117, 469`; `S₁₃ = 17, 69, 277, 1109`. -/
theorem layer_table :
    (layer_elem 5 0, layer_elem 5 1, layer_elem 5 2, layer_elem 5 3) = (3, 13, 53, 213) ∧
    (layer_elem 7 0, layer_elem 7 1, layer_elem 7 2, layer_elem 7 3) = (9, 37, 149, 597) ∧
    (layer_elem 11 0, layer_elem 11 1, layer_elem 11 2, layer_elem 11 3) =
      (7, 29, 117, 469) ∧
    (layer_elem 13 0, layer_elem 13 1, layer_elem 13 2, layer_elem 13 3) =
      (17, 69, 277, 1109) := by
  decide

/-- Trivial instance `n = 1` (`k₀(1) = 2`): `m(1,0) = 1` and `T(1) = 1`. -/
theorem layer_one : layer_elem 1 0 = 1 ∧ collatz_step (layer_elem 1 0) = 1 :=
  ⟨by decide, collatz_step_layer_elem odd_one (by decide) 0⟩

/-- `T(13) = 5` and `e(13) = 3`, obtained from Proposition 3.5 at `(n,t) = (5,1)`. -/
theorem collatz_step_thirteen : collatz_step 13 = 5 ∧ step_type 13 = 3 := by
  have h1 := collatz_step_layer_elem odd_five (by decide) 1
  have h2 := step_type_layer_elem odd_five (by decide) 1
  rw [show layer_elem 5 1 = 13 by decide] at h1 h2
  exact ⟨h1, by rw [h2]; decide⟩

/-- `T(29) = 11`, `e(29) = 3`: Proposition 3.5 at `(n,t) = (11,1)`. -/
theorem collatz_step_twentynine : collatz_step 29 = 11 ∧ step_type 29 = 3 := by
  have h1 := collatz_step_layer_elem odd_eleven (by decide) 1
  have h2 := step_type_layer_elem odd_eleven (by decide) 1
  rw [show layer_elem 11 1 = 29 by decide] at h1 h2
  exact ⟨h1, by rw [h2]; decide⟩

/-- Link fact on an instance: `T(13) = 5 ≡ 2 (mod 3)` and `e(13) = 3` is odd. -/
theorem link_thirteen : collatz_step 13 % 3 = 2 ∧ Odd (step_type 13) := by
  refine ⟨by rw [collatz_step_thirteen.1], ?_⟩
  exact (collatz_step_mod_three_eq_two_iff 13).1 (by rw [collatz_step_thirteen.1])

/-- `m(5,2) = 53 ≡ 1 (mod 4)`. -/
theorem layer_mod_four_instance : layer_elem 5 2 % 4 = 1 :=
  layer_elem_mod_four (by decide) (by norm_num)

/-- Lemma 3.4 instance: `9` has no odd preimage. -/
theorem no_preimage_nine : preimage_layer 9 = ∅ :=
  preimage_layer_eq_empty_of_three_dvd (by decide)

/-- Lemma 2.13 on the paper example `x = 7 = 2^3·1 − 1`: block `[7, 11, 17]`,
next block start `T^3(7) = (27 − 1)/2 = 13`. -/
theorem block_seven :
    collatz_step^[1] 7 = 11 ∧ collatz_step^[2] 7 = 17 ∧ collatz_step^[3] 7 = 13 := by
  have hy : Odd (1 : ℕ) := odd_one
  have hx : 7 + 1 = 2 ^ 3 * 1 := by norm_num
  have h1 := iterate_add_one_of_lt hy hx 1 (by norm_num)
  have h2 := iterate_add_one_of_lt hy hx 2 (by norm_num)
  have h3 := iterate_block_length hy (by norm_num) hx
  have h26 : (3 ^ 3 * 1 - 1 : ℕ).factorization 2 = 1 := by
    rw [show (3 ^ 3 * 1 - 1 : ℕ) = 2 ^ 1 * 13 by norm_num]
    exact factorization_two_pow_mul_of_odd 1 odd_thirteen
  rw [h26] at h3
  rw [show 3 ^ 1 * 2 ^ (3 - 1) * 1 = 12 by norm_num] at h1
  rw [show 3 ^ 2 * 2 ^ (3 - 2) * 1 = 18 by norm_num] at h2
  refine ⟨by omega, by omega, by rw [h3]; norm_num⟩

/-- `step_type 1 = 2` (`3·1 + 1 = 2^2·1`). -/
theorem step_type_one : step_type 1 = 2 :=
  step_type_eq_of_three_mul_add_one_eq odd_one (by norm_num)

/-- Proposition H.7(c), satisfiable instance: `x = 1` realizes the one-block
pattern `((1,1))` (trivial cycle). -/
theorem realizes_one_block_one : Collatz.CycleExclusion.RealizesOneBlock 1 1 1 :=
  ⟨odd_one, fun k hk => absurd hk (by omega), by simpa using step_type_one,
    by simpa using step_one⟩

/-- The criterion at `((1,1))`: `D = 1 > 0` and `D ∣ 1`. -/
theorem criterion_one_one :
    ∃ x, Collatz.CycleExclusion.RealizesOneBlock 1 1 x :=
  (Collatz.CycleExclusion.exists_realizesOneBlock_iff (by norm_num) (by norm_num)).2
    ⟨by norm_num, by norm_num⟩

/-- The criterion is not trivially true: `((1,2))` has `D = 5 ∤ 3`, and `((2,1))`
has `D = 8 − 9 < 0` (the pattern of the negative cycle `{−5, −7}`); neither is
realized by a positive odd integer. -/
theorem criterion_fails :
    (¬ ∃ x, Collatz.CycleExclusion.RealizesOneBlock 1 2 x) ∧
      ¬ ∃ x, Collatz.CycleExclusion.RealizesOneBlock 2 1 x := by
  constructor
  · rw [Collatz.CycleExclusion.exists_realizesOneBlock_iff (by norm_num) (by norm_num)]
    norm_num
  · rw [Collatz.CycleExclusion.exists_realizesOneBlock_iff (by norm_num) (by norm_num)]
    norm_num

/-- `C(w)` matches paper Remark H.7a on `w = ((4,1),(3,3))` (pattern of the
negative cycle `{−17, …, −91}`): `C(w) = 139`, `p = 7`, `S = 11`. -/
theorem blockC_remark_H7a :
    Collatz.CycleExclusion.blockPatternC (fun i => if i = 0 then 4 else 3)
        (fun i => if i = 0 then 1 else 3) 2 = 139 ∧
      Collatz.CycleExclusion.blockPatternLength (fun i => if i = 0 then 4 else 3) 2 = 7 ∧
      Collatz.CycleExclusion.blockPatternExpSum (fun i => if i = 0 then 4 else 3)
        (fun i => if i = 0 then 1 else 3) 2 = 11 := by
  decide

/-- Proposition H.7(a) for `k = 2`, satisfiable instance: `x = 1` realizes
`((1,1),(1,1))`; there `D = 2^4 − 3^2 = 7 = C(w)`. -/
theorem realizes_two_blocks_one :
    Collatz.CycleExclusion.RealizesBlockPattern (fun _ => 1) (fun _ => 1) 2 1 := by
  refine ⟨odd_one, fun i _ => ⟨fun j hj => by beta_reduce at hj; omega, ?_⟩, ?_⟩
  · rw [iterate_collatz_step_one]; exact step_type_one
  · exact iterate_collatz_step_one _

theorem block_equation_two_blocks_one :
    Collatz.CycleExclusion.blockPatternC (fun _ => 1) (fun _ => 1) 2 = 7 ∧
      ∃ y : ℕ, Odd y ∧ 1 + 1 = 2 ^ 1 * y ∧ (y : ℤ) * 7 = 7 := by
  refine ⟨by decide, ?_⟩
  obtain ⟨y, hy, hxy, hyD, -⟩ :=
    Collatz.CycleExclusion.realizesBlockPattern_block_equation (by norm_num)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl) realizes_two_blocks_one
  refine ⟨y, hy, hxy, ?_⟩
  have hC : Collatz.CycleExclusion.blockPatternC (fun _ => 1) (fun _ => 1) 2 = 7 := by
    decide
  have hS : Collatz.CycleExclusion.blockPatternExpSum (fun _ => 1) (fun _ => 1) 2 = 4 := by
    decide
  have hP : Collatz.CycleExclusion.blockPatternLength (fun _ => 1) 2 = 2 := by decide
  rw [hC, hS, hP] at hyD
  norm_num at hyD
  linarith

end LayersAndBlocks

end Collatz.Tests.ResidualSanity

#print axioms Collatz.Tests.ResidualSanity.step_one
#print axioms Collatz.Tests.ResidualSanity.frontier_collatz_convergence
#print axioms Collatz.Tests.ResidualSanity.frontier_envelope
#print axioms Collatz.Tests.ResidualSanity.frontier_explicit_residuals
#print axioms Collatz.Tests.ResidualSanity.residuals_of_reaches_one
#print axioms Collatz.Tests.ResidualSanity.layer_table
#print axioms Collatz.Tests.ResidualSanity.block_seven
#print axioms Collatz.Tests.ResidualSanity.criterion_fails
#print axioms Collatz.Tests.ResidualSanity.block_equation_two_blocks_one
