import Collatz.Foundations.Core
import Collatz.Foundations.Basic
import Collatz.Convergence.Coercivity
import Collatz.Convergence.FixedPoints
import Collatz.Convergence.NoAttractors
import Collatz.CycleExclusion.Main
import Collatz.CycleExclusion.PeriodicTailBridge
import Collatz.Epochs.LongEpochs

/-!
# Convergence layer: conditional endpoints

Nothing in this file proves the Collatz conjecture. The public convergence
theorems (all with conclusion `∃ k, T^[k] n = 1` for the odd-step map `T`) are
conditional on explicitly named OPEN hypotheses:

* periodic side: `NoNontrivialCycleOnOrbit n` (equivalently
  `OrbitNoNontrivialPeriodicTail n` = `PeriodicConvergenceResidual n`), or the
  global `NoNontrivialCycles`;
* aperiodic side: `orbit_bounded n`, or the SEDT-envelope residual
  `AperiodicConvergenceResidual n`.

Every hypothesis of every public convergence theorem holds for `n = 1`; this is
checked in `Collatz/Tests/ResidualSanity.lean`.

Main endpoints (end of this file):

* `collatz_of_no_cycles_and_bounded` — (no nontrivial cycles) + (all odd orbits
  bounded) ⇒ every odd orbit reaches `1`; the converse also holds
  (`collatz_iff_no_cycles_and_bounded`), so this is an exact reformulation.
* `reaches_one_of_bounded_of_no_cycle_on_orbit` — pointwise version.
* `collatz_convergence_modulo_explicit_residuals` — SEDT-conditional endpoint.
  For odd `n` the aperiodic residual is *equivalent* to eventual periodicity of
  the orbit (`aperiodic_convergence_residual_iff_eventually_periodic`), because
  the coercivity argument (`false_of_orbit_epoch_sedt_envelope`) shows that no
  long-epoch stream of an odd orbit satisfies the SEDT envelope at dominant
  parameters.

Supporting material: the pigeonhole lemmas (a bounded orbit is eventually
periodic; an aperiodic orbit is cofinally unbounded and has cofinal phase
returns modulo any `q > 0`) and the canonical long-epoch stream of an aperiodic
orbit on which the aperiodic residual is stated. The former ~3000 lines of
conditional plumbing on the phase-return skeleton (all guarded by
`¬ orbit_eventually_periodic n` and unused by the endpoints) were deleted in
the 2026-10 clean-up.
-/

namespace Collatz.Convergence

/-- Periodic-side hypothesis of `collatz_convergence`. It is exactly the open
per-orbit hypothesis `OrbitNoNontrivialPeriodicTail n` (no nontrivial cycle on
the orbit of `n`). The former second clause (fixed-point canonization) is a
theorem, `collatz_step_fixed_point_canonical`, and was dropped. -/
def periodic_orbit_bridge_contract (n : ℕ) : Prop :=
  Collatz.CycleExclusion.OrbitNoNontrivialPeriodicTail n

/-- **Open periodic residual.** No nontrivial cycle on the odd-step orbit of
`n`, in periodic-tail-witness form. Holds for `n = 1` and for every `n` whose
orbit reaches `1`. -/
abbrev PeriodicConvergenceResidual (n : ℕ) : Prop :=
  Collatz.CycleExclusion.OrbitNoNontrivialPeriodicTail n

/-- Odd starts stay in the odd-state Collatz subsystem under iteration. -/
lemma odd_iterates_of_odd (n : ℕ) (hn : Odd n) :
    ∀ k : ℕ, Odd ((Collatz.Foundations.collatz_step^[k]) n) := by
  intro k
  induction k with
  | zero =>
      simpa using hn
  | succ k ih =>
      simpa [Function.iterate_succ_apply', Collatz.T_odd] using Collatz.T_odd_odd_of_odd ih

/-- A repeated orbit value at times `k < k + p` forces an eventually periodic
tail for the deterministic odd-step Collatz dynamics. -/
lemma orbit_eventually_periodic_of_iterate_eq
    (n k p : ℕ)
    (hp : 0 < p)
    (hkp :
      (Collatz.Foundations.collatz_step^[k + p]) n =
        (Collatz.Foundations.collatz_step^[k]) n) :
    Collatz.CycleExclusion.orbit_eventually_periodic n := by
  refine ⟨k, p, hp, ?_⟩
  intro m
  have hm' :
      (Collatz.Foundations.collatz_step^[k + m + p]) n =
        (Collatz.Foundations.collatz_step^[k + m]) n := by
    calc
      (Collatz.Foundations.collatz_step^[k + m + p]) n
          = (Collatz.Foundations.collatz_step^[m])
              ((Collatz.Foundations.collatz_step^[k + p]) n) := by
                rw [show k + m + p = m + (k + p) by omega, Function.iterate_add_apply]
      _ = (Collatz.Foundations.collatz_step^[m])
            ((Collatz.Foundations.collatz_step^[k]) n) := by rw [hkp]
      _ = (Collatz.Foundations.collatz_step^[k + m]) n := by
            rw [show k + m = m + k by omega, Function.iterate_add_apply]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hm'

/-- Boundedness of a deterministic orbit forces eventual periodicity by the
finite pigeonhole principle. -/
lemma orbit_eventually_periodic_of_bounded
    (n : ℕ)
    (hbounded : orbit_bounded n) :
    Collatz.CycleExclusion.orbit_eventually_periodic n := by
  rcases hbounded with ⟨B, hB⟩
  let orbitVal : ℕ → ℕ := fun k => (Collatz.Foundations.collatz_step^[k]) n
  have hmem : ∀ k : ℕ, orbitVal k ∈ Set.Iic B := by
    intro k
    exact hB k
  obtain ⟨i, j, hij, hEq⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem (f := orbitVal) hmem (Set.finite_Iic B)
  have hp : 0 < j - i := Nat.sub_pos_of_lt hij
  have hij' : i + (j - i) = j := Nat.add_sub_of_le hij.le
  have hrepeat :
      (Collatz.Foundations.collatz_step^[i + (j - i)]) n =
        (Collatz.Foundations.collatz_step^[i]) n := by
    simpa [orbitVal, hij'] using hEq.symm
  exact orbit_eventually_periodic_of_iterate_eq n i (j - i) hp hrepeat

/-- Contrapositive form used by the aperiodic branch: a genuinely aperiodic
orbit cannot stay in a finite state set. -/
lemma aperiodic_orbit_unbounded
    (n : ℕ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) :
    ¬ orbit_bounded n := by
  intro hbounded
  exact haper (orbit_eventually_periodic_of_bounded n hbounded)

/-- Cofinal unboundedness along the odd-step orbit: after every time threshold,
the orbit eventually exceeds every prescribed value bound. -/
def orbit_cofinally_unbounded (n : ℕ) : Prop :=
  ∀ B N : ℕ, ∃ k : ℕ, k ≥ N ∧ (Collatz.Foundations.collatz_step^[k]) n > B

/-- Negation of boundedness upgrades to the cofinal form of unboundedness. -/
lemma orbit_cofinally_unbounded_of_not_bounded
    (n : ℕ)
    (hunbounded : ¬ orbit_bounded n) :
    orbit_cofinally_unbounded n := by
  intro B N
  let orbitVal : ℕ → ℕ := fun k => (Collatz.Foundations.collatz_step^[k]) n
  by_contra hcontra
  push_neg at hcontra
  let prefixBound : ℕ :=
    Finset.sum (Finset.range N) orbitVal
  have hbounded : orbit_bounded n := by
    refine ⟨prefixBound + B, ?_⟩
    intro k
    change orbitVal k ≤ prefixBound + B
    by_cases hk : k < N
    · have hk_mem : k ∈ Finset.range N := by
        simpa using hk
      have hprefix :
          orbitVal k ≤ prefixBound := by
        simpa [prefixBound] using
          (Finset.single_le_sum (fun i _ => Nat.zero_le (orbitVal i)) hk_mem)
      omega
    · have hk' : N ≤ k := le_of_not_gt hk
      have htail : orbitVal k ≤ B := hcontra k hk'
      omega
  exact hunbounded hbounded

/-- Aperiodicity therefore forces the orbit to exceed every bound arbitrarily
far out along the odd-step dynamics. -/
lemma aperiodic_orbit_cofinally_unbounded
    (n : ℕ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) :
    orbit_cofinally_unbounded n := by
  exact orbit_cofinally_unbounded_of_not_bounded n (aperiodic_orbit_unbounded n haper)

/-- From cofinal unboundedness one can extract arbitrarily long sequences of
large orbit values separated by at least a prescribed gap length. -/
lemma cofinally_unbounded_orbit_has_spaced_hits
    (n B N L : ℕ)
    (hunbounded : orbit_cofinally_unbounded n) :
    ∃ idx : ℕ → ℕ,
      idx 0 ≥ N ∧
      Monotone idx ∧
      (∀ j : ℕ, idx (j + 1) ≥ idx j + L) ∧
      (∀ j : ℕ, (Collatz.Foundations.collatz_step^[idx j]) n > B) := by
  let orbitVal : ℕ → ℕ := fun k => (Collatz.Foundations.collatz_step^[k]) n
  have hstep : ∀ M : ℕ, ∃ k : ℕ, k ≥ M ∧ orbitVal k > B := by
    intro M
    exact hunbounded B M
  classical
  choose next hnext_ge hnext_big using hstep
  let idx : ℕ → ℕ :=
    Nat.rec (motive := fun _ => ℕ) (next N) (fun _ prev => next (prev + L))
  refine ⟨idx, ?_, ?_, ?_, ?_⟩
  · simpa [idx] using hnext_ge N
  · refine monotone_nat_of_le_succ ?_
    intro j
    have hgapj : idx (j + 1) ≥ idx j + L := by
      simpa [idx] using hnext_ge (idx j + L)
    exact le_trans (Nat.le_add_right _ _) hgapj
  · intro j
    simpa [idx] using hnext_ge (idx j + L)
  · intro j
    cases j with
    | zero =>
        simpa [idx, orbitVal] using hnext_big N
    | succ j =>
        simpa [idx, orbitVal] using hnext_big (idx j + L)

/-- Phase-return form of cofinal unboundedness: for any fixed phase period `q`,
there are arbitrarily far-out large orbit values at two times in the same
residue class modulo `q`, with an arbitrarily large prescribed separation. -/
def orbit_has_cofinal_phase_returns (n q : ℕ) : Prop :=
  ∀ B N L : ℕ, ∃ i j : ℕ,
    N ≤ i ∧ i + L ≤ j ∧ i % q = j % q ∧
    (Collatz.Foundations.collatz_step^[i]) n > B ∧
    (Collatz.Foundations.collatz_step^[j]) n > B

/-- Strict variant of `orbit_has_cofinal_phase_returns`: the left return time
must lie strictly after the requested threshold. Since the original theorem is
uniform in `N`, this is obtained by the one-step shift `N ↦ N+1`, but keeping
it explicit matches the exact boundary geometry later needed for filler-event
construction. -/
def orbit_has_strictly_cofinal_phase_returns (n q : ℕ) : Prop :=
  ∀ B N L : ℕ, ∃ i j : ℕ,
    N < i ∧ i + L ≤ j ∧ i % q = j % q ∧
    (Collatz.Foundations.collatz_step^[i]) n > B ∧
    (Collatz.Foundations.collatz_step^[j]) n > B

lemma cofinally_unbounded_orbit_has_cofinal_phase_returns
    (n q : ℕ)
    (hq : 0 < q)
    (hunbounded : orbit_cofinally_unbounded n) :
    orbit_has_cofinal_phase_returns n q := by
  intro B N L
  rcases cofinally_unbounded_orbit_has_spaced_hits n B N L hunbounded with
    ⟨idx, hidx0, hmono, hgap, hbig⟩
  let residue : Fin (q + 1) → Fin q :=
    fun a => ⟨idx (a : ℕ) % q, Nat.mod_lt _ hq⟩
  have hcard : Fintype.card (Fin q) < Fintype.card (Fin (q + 1)) := by
    simp
  obtain ⟨a, b, hab_ne, hres⟩ := Fintype.exists_ne_map_eq_of_card_lt residue hcard
  have hmod :
      idx (a : ℕ) % q = idx (b : ℕ) % q := by
    exact congrArg Fin.val hres
  cases lt_or_gt_of_ne hab_ne with
  | inl hab =>
      refine ⟨idx (a : ℕ), idx (b : ℕ), ?_, ?_, ?_, hbig (a : ℕ), hbig (b : ℕ)⟩
      · exact le_trans hidx0 (hmono (Nat.zero_le _))
      · exact le_trans (hgap (a : ℕ)) (hmono (Nat.succ_le_of_lt hab))
      · exact hmod
  | inr hba =>
      refine ⟨idx (b : ℕ), idx (a : ℕ), ?_, ?_, ?_, hbig (b : ℕ), hbig (a : ℕ)⟩
      · exact le_trans hidx0 (hmono (Nat.zero_le _))
      · exact le_trans (hgap (b : ℕ)) (hmono (Nat.succ_le_of_lt hba))
      · exact hmod.symm

/-- The previous cofinal return theorem immediately strengthens to a strict
threshold form by requesting the non-strict statement one step later. -/
lemma cofinally_unbounded_orbit_has_strictly_cofinal_phase_returns
    (n q : ℕ)
    (hq : 0 < q)
    (hunbounded : orbit_cofinally_unbounded n) :
    orbit_has_strictly_cofinal_phase_returns n q := by
  intro B N L
  rcases cofinally_unbounded_orbit_has_cofinal_phase_returns n q hq hunbounded
      B (N + 1) L with ⟨i, j, hi, hij, hmod, hiBig, hjBig⟩
  refine ⟨i, j, ?_, hij, hmod, hiBig, hjBig⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self N) hi

lemma aperiodic_orbit_has_cofinal_phase_returns
    (n q : ℕ)
    (hq : 0 < q)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) :
    orbit_has_cofinal_phase_returns n q := by
  exact cofinally_unbounded_orbit_has_cofinal_phase_returns n q hq
    (aperiodic_orbit_cofinally_unbounded n haper)

/-- Strict threshold version of the previous aperiodic phase-return theorem. -/
lemma aperiodic_orbit_has_strictly_cofinal_phase_returns
    (n q : ℕ)
    (hq : 0 < q)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) :
    orbit_has_strictly_cofinal_phase_returns n q := by
  exact cofinally_unbounded_orbit_has_strictly_cofinal_phase_returns n q hq
    (aperiodic_orbit_cofinally_unbounded n haper)

/-- Epoch-side specialization of the phase-return skeleton: an aperiodic orbit
admits arbitrarily far-out returns aligned modulo the joint selected-segment
period, hence in particular modulo both `gap_long(t)` and `Q_t(t)`, with
separation already beating the SEDT threshold `L₀(t,U)`. -/
noncomputable def aperiodic_orbit_has_cofinal_gap_long_phase_returns
    (n t U : ℕ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) :
    Epochs.OrbitHasCofinalGapLongPhaseReturns n t U := by
  have hraw : Epochs.RawStrictCofinalGapLongPhaseReturns n t U := by
    intro N
    have hq : 0 < Epochs.selected_phase_period t := Epochs.selected_phase_period_pos t
    rcases aperiodic_orbit_has_strictly_cofinal_phase_returns n (Epochs.selected_phase_period t) hq haper 0 N
        (Collatz.SEDT.L₀ t U) with ⟨i, j, hiN, hij, hmod, _hiBig, _hjBig⟩
    exact ⟨i, j, hiN, hij, hmod⟩
  exact Epochs.orbit_has_cofinal_gap_long_phase_returns_of_raw_strict hraw

/-- The canonical long-epoch stream of an aperiodic orbit: the orbit values at
the left endpoints of the phase-return pairs chosen by
`aperiodic_orbit_has_cofinal_gap_long_phase_returns`. Consecutive indices are at
least `L₀(t, U)` apart. This is pure index bookkeeping; no drift property of the
stream is proved. -/
noncomputable def canonical_aperiodic_orbit_long_epoch_stream
    (n t U : ℕ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) :
    Epochs.OrbitLongEpochStream n t U :=
  Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps n t U
    ((Epochs.canonical_gap_long_phase_returns_bridge n t U)
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper))

/-- Hypothesis shape: if the orbit of `n` is not eventually periodic, the SEDT
envelope holds on its canonical long-epoch stream at `(t, U, β)`. Vacuously true
for eventually periodic orbits; for odd `n` and dominant parameters it is
equivalent to eventual periodicity (`false_of_orbit_epoch_sedt_envelope`). -/
def canonical_aperiodic_orbit_epoch_sedt_envelope
    (n t U : ℕ) (β : ℝ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    orbit_epoch_sedt_envelope t U β
      (canonical_aperiodic_orbit_long_epoch_stream n t U _ha)

/-! ## Aperiodic side: the coercivity contradiction -/

/-- **Coercivity contradiction (proved).** For odd `n`, no long-epoch stream of
the orbit of `n` satisfies the per-epoch SEDT envelope at dominant parameters:
summing the envelope drives the (nonnegative) potential below `0`.

Aperiodicity is *not* used. Consequently any hypothesis asserting the envelope
on a stream of an odd orbit is contradictory, and the residuals built from it
below are satisfiable only because they are guarded by
`¬ orbit_eventually_periodic n`. -/
theorem false_of_orbit_epoch_sedt_envelope
    {n t U : ℕ} {β : ℝ} (hn : Odd n)
    (hstream : Collatz.Epochs.OrbitLongEpochStream n t U)
    (henv : orbit_epoch_sedt_envelope t U β hstream)
    (hparams : sedt_dominant_parameters t U β) : False := by
  have ht : t ≥ 3 := hparams.1
  have hU : U ≥ 1 := hparams.2.1
  have hβgt : β > Collatz.SEDT.β₀ t U := hparams.2.2.1
  have hdom : sedt_dominance_condition t U β := hparams.2.2.2
  have hα : Collatz.SEDT.α t U < 2 := Collatz.SEDT.alpha_lt_two_of_ht_hU t U ht hU
  have hε : Collatz.SEDT.ε t U β > 0 := Collatz.SEDT.epsilon_pos t U β ht hU hα hβgt
  have hβ0pos : 0 < Collatz.SEDT.β₀ t U := Collatz.SEDT.beta_zero_pos t U hα
  have hβpos : 0 < β := by linarith
  have hβnonneg : 0 ≤ β := le_of_lt hβpos
  have hoddIter : ∀ k : ℕ, Odd ((Collatz.Foundations.collatz_step^[k]) n) :=
    odd_iterates_of_odd n hn
  have hstep : orbit_epoch_step_drift t U β hstream :=
    orbit_epoch_step_drift_of_sedt_envelope t U β hstream henv
  have hpack := stream_potential_linear_bound_of_dominance t U β hstream hε hβnonneg hstep hdom
  rcases hpack with ⟨εv, B, hεv, hupper, hthreshold⟩
  rcases orbitwise_absorbed_cofinal_negativity t U β εv B hstream hεv hthreshold 0 with
    ⟨J, _hJ, hneg⟩
  have horbit : hstream.orbitVal J = (Collatz.Foundations.collatz_step^[hstream.idx J]) n :=
    hstream.realizedOnOrbit J
  have hnonneg : 0 ≤ potential β ((Collatz.Foundations.collatz_step^[hstream.idx J]) n) :=
    potential_nonneg_of_odd β hβnonneg (hoddIter (hstream.idx J))
  have hupper' : potential β ((Collatz.Foundations.collatz_step^[hstream.idx J]) n) ≤
      -(εv) * (stream_prefix_total hstream J : ℝ) + B := by
    simpa [horbit] using hupper J
  have hle : potential β ((Collatz.Foundations.collatz_step^[hstream.idx J]) n) < 0 :=
    lt_of_le_of_lt hupper' hneg
  exact not_lt_of_ge hnonneg hle

/-- Witness form of `false_of_orbit_epoch_sedt_envelope`. The aperiodicity
argument is not used (kept for signature compatibility). -/
theorem aperiodic_tail_contradiction_from_coercivity
    (n t U : ℕ) (β : ℝ)
    (_haper : ¬Collatz.CycleExclusion.orbit_eventually_periodic n)
    (hw : OrbitLongEpochE2Witness n t U β)
    (hparams : sedt_dominant_parameters t U β)
    (hn : Odd n) : False :=
  false_of_orbit_epoch_sedt_envelope hn hw.toStream
    (by simpa [OrbitLongEpochE2Witness.toStream] using hw.envelope) hparams

/-! ## Periodic side and the cycle/divergence reformulation -/

/-- Pointwise endpoint: a bounded orbit without a nontrivial cycle reaches `1`.
Both hypotheses are open in general and hold for `n = 1`. -/
theorem reaches_one_of_bounded_of_no_cycle_on_orbit {n : ℕ}
    (hbdd : orbit_bounded n) (hno : Collatz.CycleExclusion.NoNontrivialCycleOnOrbit n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 :=
  Collatz.CycleExclusion.reaches_one_of_periodic_of_no_cycle
    (orbit_eventually_periodic_of_bounded n hbdd) hno

/-- Global endpoint: (no nontrivial cycles) + (every odd orbit bounded) ⇒ every
odd orbit reaches `1`. Both hypotheses are open conjectures; by
`collatz_iff_no_cycles_and_bounded` they are together equivalent to the
conclusion, so this is an exact reformulation, not a reduction to something
weaker. -/
theorem collatz_of_no_cycles_and_bounded
    (hcyc : Collatz.CycleExclusion.NoNontrivialCycles)
    (hbdd : ∀ n : ℕ, Odd n → orbit_bounded n) :
    ∀ n : ℕ, Odd n → ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 :=
  fun n hn => reaches_one_of_bounded_of_no_cycle_on_orbit (hbdd n hn)
    (Collatz.CycleExclusion.no_cycle_on_orbit_of_no_nontrivial_cycles hcyc n)

/-- An orbit that reaches `1` is bounded. -/
theorem orbit_bounded_of_reaches_one {n k₀ : ℕ}
    (h : (Collatz.Foundations.collatz_step^[k₀]) n = 1) : orbit_bounded n := by
  let orbitVal : ℕ → ℕ := fun i => (Collatz.Foundations.collatz_step^[i]) n
  refine ⟨Finset.sum (Finset.range (k₀ + 1)) orbitVal, fun k => ?_⟩
  have hle : ∀ i, i ≤ k₀ → orbitVal i ≤ Finset.sum (Finset.range (k₀ + 1)) orbitVal :=
    fun i hi => Finset.single_le_sum (fun j _ => Nat.zero_le (orbitVal j))
      (Finset.mem_range.2 (by omega))
  change orbitVal k ≤ _
  by_cases hk : k ≤ k₀
  · exact hle k hk
  · have h1 : orbitVal k = orbitVal k₀ := by
      change (Collatz.Foundations.collatz_step^[k]) n = (Collatz.Foundations.collatz_step^[k₀]) n
      rw [h, show k = (k - k₀) + k₀ by omega, Function.iterate_add_apply, h,
        Collatz.CycleExclusion.iterate_collatz_step_one]
    rw [h1]
    exact hle k₀ le_rfl

/-- `orbit_bounded 1`. -/
theorem orbit_bounded_one : orbit_bounded 1 :=
  orbit_bounded_of_reaches_one (k₀ := 0) rfl

/-- Converse of `collatz_of_no_cycles_and_bounded`. -/
theorem no_cycles_and_bounded_of_collatz
    (h : ∀ n : ℕ, Odd n → ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1) :
    Collatz.CycleExclusion.NoNontrivialCycles ∧ ∀ n : ℕ, Odd n → orbit_bounded n := by
  refine ⟨?_, fun n hn => ?_⟩
  · intro x hx p hp hxp
    obtain ⟨k₀, hk⟩ := h x hx
    simpa using
      Collatz.CycleExclusion.no_cycle_on_orbit_of_reaches_one hk 0 p hp (by simpa using hxp)
  · obtain ⟨k₀, hk⟩ := h n hn
    exact orbit_bounded_of_reaches_one hk

/-- The odd-step Collatz conjecture is equivalent to (no nontrivial cycles) ∧
(all odd orbits bounded). -/
theorem collatz_iff_no_cycles_and_bounded :
    (∀ n : ℕ, Odd n → ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1) ↔
      Collatz.CycleExclusion.NoNontrivialCycles ∧ ∀ n : ℕ, Odd n → orbit_bounded n :=
  ⟨no_cycles_and_bounded_of_collatz, fun h => collatz_of_no_cycles_and_bounded h.1 h.2⟩

/-! ## SEDT-conditional endpoints -/

/-- Conditional convergence at fixed parameters `(t, U, β)`.

* periodic branch: `periodic_orbit_bridge_contract n` (= no nontrivial cycle on
  the orbit, open);
* aperiodic branch: an `OrbitLongEpochE2Witness` for every proof of
  aperiodicity. For odd `n` this witness type is empty
  (`aperiodic_tail_contradiction_from_coercivity`), so the hypothesis is
  equivalent to eventual periodicity of the orbit of `n`.

All hypotheses hold for `n = 1`, `(t, U) = (3, 1)` and any `β` with
`sedt_dominant_parameters 3 1 β` (see `Tests/ResidualSanity.lean`). -/
theorem collatz_convergence
    (n t U : ℕ) (β : ℝ) (hn : Odd n)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicWitness :
      ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
        OrbitLongEpochE2Witness n t U β)
    (hparams : sedt_dominant_parameters t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  by_cases hper : Collatz.CycleExclusion.orbit_eventually_periodic n
  · exact Collatz.CycleExclusion.reaches_one_of_periodic_of_no_cycle hper
      ((Collatz.CycleExclusion.orbit_no_nontrivial_periodic_tail_iff_no_cycle_on_orbit n).1
        hperiodicContracts)
  · exact (aperiodic_tail_contradiction_from_coercivity n t U β hper
      (haperiodicWitness hper) hparams hn).elim

/-- Conditional convergence from the SEDT envelope on the canonical aperiodic
long-gap stream, at a *single* admissible `β`.

The former version assumed the envelope for every `β : ℝ`; since the potential
is affine in `β` on a `β`-independent stream, that hypothesis is equivalent to
eventual periodicity of the orbit by an elementary argument (see
`Tests/VacuityRegression.lean`) and was replaced. The single-`β` envelope is
still contradictory for aperiodic odd `n` (`false_of_orbit_epoch_sedt_envelope`),
so this theorem, too, only reduces convergence to "no nontrivial cycle" +
"eventually periodic". -/
theorem collatz_convergence_from_aperiodic_orbit_epoch_envelope
    (n t U : ℕ) (β : ℝ) (hn : Odd n)
    (hparams : sedt_dominant_parameters t U β)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicEnvelope : canonical_aperiodic_orbit_epoch_sedt_envelope n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  by_cases hper : Collatz.CycleExclusion.orbit_eventually_periodic n
  · exact Collatz.CycleExclusion.reaches_one_of_periodic_of_no_cycle hper
      ((Collatz.CycleExclusion.orbit_no_nontrivial_periodic_tail_iff_no_cycle_on_orbit n).1
        hperiodicContracts)
  · exact (false_of_orbit_epoch_sedt_envelope hn _ (haperiodicEnvelope hper) hparams).elim

/-- **Aperiodic residual (single `β`).** If the orbit of `n` is not eventually
periodic, then the SEDT envelope holds on its canonical long-gap stream at
production parameters `(t, U) = (3, 1)` for some dominant `β`.

Status: holds for `n = 1` and for every eventually periodic orbit (vacuously).
For odd `n` it is *equivalent* to `orbit_eventually_periodic n`
(`aperiodic_convergence_residual_iff_eventually_periodic`): it carries no
information beyond "the orbit of `n` does not diverge". -/
def AperiodicConvergenceResidual (n : ℕ) : Prop :=
  ∀ ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
    ∃ β : ℝ, sedt_dominant_parameters 3 1 β ∧
      orbit_epoch_sedt_envelope 3 1 β (canonical_aperiodic_orbit_long_epoch_stream n 3 1 ha)

theorem aperiodic_convergence_residual_of_eventually_periodic {n : ℕ}
    (h : Collatz.CycleExclusion.orbit_eventually_periodic n) :
    AperiodicConvergenceResidual n :=
  fun ha => absurd h ha

theorem eventually_periodic_of_aperiodic_convergence_residual {n : ℕ} (hn : Odd n)
    (h : AperiodicConvergenceResidual n) :
    Collatz.CycleExclusion.orbit_eventually_periodic n := by
  by_contra ha
  obtain ⟨β, hparams, henv⟩ := h ha
  exact false_of_orbit_epoch_sedt_envelope hn _ henv hparams

/-- For odd `n`, the aperiodic residual is exactly eventual periodicity. -/
theorem aperiodic_convergence_residual_iff_eventually_periodic {n : ℕ} (hn : Odd n) :
    AperiodicConvergenceResidual n ↔ Collatz.CycleExclusion.orbit_eventually_periodic n :=
  ⟨eventually_periodic_of_aperiodic_convergence_residual hn,
    aperiodic_convergence_residual_of_eventually_periodic⟩

/-- SEDT-conditional endpoint: `PeriodicConvergenceResidual n` (no nontrivial
cycle on the orbit) and `AperiodicConvergenceResidual n` (single-`β` SEDT
envelope on the canonical stream, guarded by aperiodicity) imply that the odd
orbit of `n` reaches `1`. Both hypotheses hold for `n = 1`; for odd `n` the
second is equivalent to eventual periodicity of the orbit. This is not an
unconditional result. -/
theorem collatz_convergence_modulo_explicit_residuals
    (n : ℕ) (hn : Odd n)
    (hperiodic : PeriodicConvergenceResidual n)
    (haperiodic : AperiodicConvergenceResidual n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 :=
  Collatz.CycleExclusion.reaches_one_of_periodic_of_no_cycle
    (eventually_periodic_of_aperiodic_convergence_residual hn haperiodic)
    ((Collatz.CycleExclusion.orbit_no_nontrivial_periodic_tail_iff_no_cycle_on_orbit n).1
      hperiodic)

/-- Same statement as `collatz_convergence_modulo_explicit_residuals`; the name
is kept for compatibility only. Despite the word "unconditional" in the name,
the theorem is conditional on two open hypotheses. -/
theorem collatz_convergence_unconditional_modulo_explicit_residuals
    (n : ℕ) (hn : Odd n)
    (hperiodic : PeriodicConvergenceResidual n)
    (haperiodic : AperiodicConvergenceResidual n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 :=
  collatz_convergence_modulo_explicit_residuals n hn hperiodic haperiodic

/-! ## Compatibility aliases -/

/-- Compatibility alias: after removal of the unsatisfiable `exclusion_premises`
package, the "cycle premises" residual is just `PeriodicConvergenceResidual`. -/
abbrev PeriodicCyclePremisesResidual (n : ℕ) : Prop :=
  PeriodicConvergenceResidual n

end Collatz.Convergence
