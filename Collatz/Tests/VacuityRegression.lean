import Collatz

/-!
# Vacuity regression facts

Machine-checked facts from the 2026-10 review that remain true after the fix.
They document why the old hypotheses were removed and guard against
reintroducing them.

1. The old periodic residual `∀ hw, hw.period ≤ 1` is equivalent to
   aperiodicity (periods are not minimal), hence false for `n = 1`.
2. The old H-level premise package `exclusion_premises` is unsatisfiable for
   every cycle.
3. The SEDT envelope assumed for *every* `β : ℝ` is equivalent to eventual
   periodicity by an elementary argument (affine dependence on `β`), so it is
   not a meaningful hypothesis; the public frontier now uses a single `β`.
4. The structures `PrimitiveJunctionRecurrenceWitness` and
   `OrbitHasCofinalLongEpochGaps` do not mention the orbit and are inhabited
   for every `n`.
5. The single-`β` envelope is also contradictory on every long-epoch stream of
   an odd orbit (`false_of_orbit_epoch_sedt_envelope`), so the aperiodic
   residual is equivalent to eventual periodicity.
-/

open Collatz.Foundations Collatz.CycleExclusion Collatz.Convergence

namespace Collatz.Tests.VacuityRegression

theorem iter_eq_one_after {n k : ℕ} (hk : (collatz_step^[k]) n = 1) (j : ℕ) :
    (collatz_step^[k + j]) n = 1 := by
  rw [show k + j = j + k by omega, Function.iterate_add_apply, hk, iterate_collatz_step_one]

theorem eventually_periodic_of_reaches_one {n k : ℕ}
    (hk : (collatz_step^[k]) n = 1) : orbit_eventually_periodic n :=
  ⟨k, 1, one_pos, fun m => by
    rw [show k + m + 1 = k + (m + 1) by omega, iter_eq_one_after hk, iter_eq_one_after hk]⟩

/-! ## 1. Old periodic residual -/

/-- The pre-fix definition of `OrbitNoNontrivialPeriodicTail`. -/
def OldOrbitNoNontrivialPeriodicTail (n : ℕ) : Prop :=
  ∀ hw : OrbitPeriodicTailWitness n, hw.period ≤ 1

theorem old_no_tail_iff_aperiodic (n : ℕ) :
    OldOrbitNoNontrivialPeriodicTail n ↔ ¬ orbit_eventually_periodic n := by
  constructor
  · rintro h ⟨k, p, hp, hper⟩
    have h2 : ∀ m, (collatz_step^[k + m + 2 * p]) n = (collatz_step^[k + m]) n := by
      intro m
      calc (collatz_step^[k + m + 2 * p]) n = (collatz_step^[k + (m + p) + p]) n := by
              congr 1; omega
        _ = (collatz_step^[k + (m + p)]) n := hper (m + p)
        _ = (collatz_step^[k + m + p]) n := by congr 1; omega
        _ = (collatz_step^[k + m]) n := hper m
    have := h ⟨k, 2 * p, by omega, h2⟩
    simp at this
    omega
  · intro h hw
    exact absurd ⟨hw.start, hw.period, hw.period_pos, hw.periodic⟩ h

theorem old_no_tail_one_false : ¬ OldOrbitNoNontrivialPeriodicTail 1 :=
  fun h => (old_no_tail_iff_aperiodic 1).1 h orbit_eventually_periodic_one

/-! ## 2. Old cycle-exclusion premises -/

/-- The pre-fix `exclusion_premises t c` with `R0 t = Q_t t + 1` inlined. -/
def OldExclusionPremises (t : ℕ) (c : Cycle) : Prop :=
  period_sum c = 0 ∧
    period_sum c = ((Collatz.Epochs.Q_t t + 1 : ℕ) : ℝ) - (Nat.succ c.len : ℝ) ∧
    Collatz.Epochs.Q_t t + 1 ≤ c.len

theorem old_exclusion_premises_empty (t : ℕ) (c : Cycle) : ¬ OldExclusionPremises t c := by
  rintro ⟨h0, h1, h2⟩
  have h2' : ((Collatz.Epochs.Q_t t + 1 : ℕ) : ℝ) ≤ (c.len : ℝ) := by exact_mod_cast h2
  push_cast at h1 h2'
  linarith

/-! ## 3. The `∀ β` envelope is equivalent to eventual periodicity -/

lemma coeff_nonpos (a D : ℝ) (h : ∀ β : ℝ, a + β * D ≤ 0) : D ≤ 0 := by
  by_contra hD
  push_neg at hD
  have h1 := h ((|a| + 1) / D)
  rw [div_mul_cancel₀ _ hD.ne'] at h1
  linarith [neg_abs_le a]

lemma alpha31 : Collatz.SEDT.α 3 1 = 5 / 4 := by
  unfold Collatz.SEDT.α Collatz.Epochs.Q_t; norm_num

lemma C31 : Collatz.SEDT.C 3 1 = 28 := by
  unfold Collatz.SEDT.C; norm_num

lemma L031 : Collatz.SEDT.L₀ 3 1 = 64 := by
  unfold Collatz.SEDT.L₀ Collatz.Epochs.Q_t; norm_num

/-- Per-epoch consequence of the `∀ β` envelope: depth drops by at least 20. -/
lemma depth_drop {n : ℕ} (s : Collatz.Epochs.OrbitLongEpochStream n 3 1)
    (henv : ∀ β : ℝ, orbit_epoch_sedt_envelope 3 1 β s) (j : ℕ) :
    (depth_minus (s.orbitVal (j + 1)) : ℝ) ≤ (depth_minus (s.orbitVal j) : ℝ) - 20 := by
  set v := s.orbitVal j
  set v' := s.orbitVal (j + 1)
  set L : ℝ := (s.epochLen j : ℝ)
  set d : ℝ := (depth_minus v : ℝ)
  set d' : ℝ := (depth_minus v' : ℝ)
  set a : ℝ := Real.log v' / Real.log 2 - Real.log v / Real.log 2 -
    (Real.log (3 / 2) / Real.log 2) * L
  set D : ℝ := (d' - d) + (2 - Collatz.SEDT.α 3 1) * L - Collatz.SEDT.C 3 1
  have hlin : ∀ β : ℝ, a + β * D ≤ 0 := by
    intro β
    have h := henv β j
    unfold orbit_epoch_sedt_envelope at h
    have heq : potential β v' - potential β v - Collatz.SEDT.sedt_envelope 3 1 β (s.epochLen j)
        = a + β * D := by
      simp only [potential, Collatz.SEDT.sedt_envelope, Collatz.SEDT.ε, a, D, d, d', L, v, v']
      ring
    have h' : potential β v' - potential β v ≤
        Collatz.SEDT.sedt_envelope 3 1 β (s.epochLen j) := h
    linarith
  have hD := coeff_nonpos a D hlin
  have hL : (64 : ℝ) ≤ L := by
    have := s.longEpoch j
    rw [L031] at this
    have h64 : ((64 : ℕ) : ℝ) ≤ (s.epochLen j : ℝ) := Nat.cast_le.mpr this
    simpa [L] using h64
  simp only [D, alpha31, C31] at hD
  linarith

/-- The `∀ β` form of the envelope is equivalent to eventual periodicity. -/
theorem forall_beta_envelope_iff_eventually_periodic (n : ℕ) :
    (∀ β : ℝ, canonical_aperiodic_orbit_epoch_sedt_envelope n 3 1 β) ↔
      orbit_eventually_periodic n := by
  constructor
  · intro henv
    by_contra haper
    let s := canonical_aperiodic_orbit_long_epoch_stream n 3 1 haper
    have hs : ∀ β : ℝ, orbit_epoch_sedt_envelope 3 1 β s := fun β => henv β haper
    have hdec : ∀ J : ℕ, (depth_minus (s.orbitVal J) : ℝ) ≤
        (depth_minus (s.orbitVal 0) : ℝ) - 20 * J := by
      intro J
      induction J with
      | zero => simp
      | succ J ih =>
          have := depth_drop s hs J
          push_cast
          linarith
    have h := hdec (depth_minus (s.orbitVal 0) + 1)
    have hnn : (0 : ℝ) ≤ (depth_minus (s.orbitVal (depth_minus (s.orbitVal 0) + 1)) : ℝ) :=
      Nat.cast_nonneg _
    push_cast at h
    have hd0 : (0 : ℝ) ≤ (depth_minus (s.orbitVal 0) : ℝ) := Nat.cast_nonneg _
    linarith
  · intro hper β haper
    exact absurd hper haper

/-! ## 4. Orbit-independent structures -/

theorem primitive_junction_witness_trivial (n t : ℕ) :
    Nonempty (Collatz.Epochs.G.PrimitiveJunctionRecurrenceWitness n t) :=
  ⟨Collatz.Epochs.G.PrimitiveJunctionRecurrenceWitness.trivial n t⟩

theorem cofinal_long_epoch_gaps_trivial (n t U : ℕ) :
    Nonempty (Collatz.Epochs.OrbitHasCofinalLongEpochGaps n t U) :=
  ⟨{ idx := fun j => j * (Collatz.SEDT.L₀ t U + 1)
     idxStrict := strictMono_nat_of_lt_succ (fun j => by rw [Nat.succ_mul]; omega)
     longGap := fun j => by rw [Nat.succ_mul]; omega }⟩

/-! ## 5. The single-`β` residual is equivalent to eventual periodicity -/

theorem aperiodic_residual_iff (n : ℕ) (hn : Odd n) :
    AperiodicConvergenceResidual n ↔ orbit_eventually_periodic n :=
  aperiodic_convergence_residual_iff_eventually_periodic hn

end Collatz.Tests.VacuityRegression

#print axioms Collatz.Tests.VacuityRegression.old_no_tail_iff_aperiodic
#print axioms Collatz.Tests.VacuityRegression.old_exclusion_premises_empty
#print axioms Collatz.Tests.VacuityRegression.forall_beta_envelope_iff_eventually_periodic
#print axioms Collatz.Tests.VacuityRegression.cofinal_long_epoch_gaps_trivial
