import Collatz.Foundations.Core
import Collatz.Foundations.Basic
import Collatz.Convergence.Coercivity
import Collatz.Convergence.FixedPoints
import Collatz.Convergence.NoAttractors
import Collatz.CycleExclusion.Main
import Collatz.Epochs.LongEpochs
import Collatz.Epochs.LongEpochs
import Collatz.Convergence.Coercivity

namespace Collatz.Convergence

/-- Entry into the trivial attractor is the exact bridge needed for strict I.1. -/
def enters_trivial_cycle (n : ℕ) : Prop :=
  ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n ∈ trivialCycleSet

/-- Periodic-side upstream package:
- period > 1 branch is bridged to an H-level cycle witness;
- period = 1 branch can be canonized to the fixed-point equation `3x+1=4x`. -/
def periodic_orbit_bridge_contract (n : ℕ) : Prop :=
  Collatz.CycleExclusion.periodic_tail_cycle_bridge n ∧
    (∀ x : ℕ, Collatz.Foundations.collatz_step x = x → 3 * x + 1 = 4 * x)

/-- Honest W6 bridge theorem: once an odd orbit enters `{1}`, it reaches 1. -/
theorem collatz_convergence_from_entry (n : ℕ) (_hn : Odd n)
    (hentry : enters_trivial_cycle n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  rcases hentry with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  exact hk

theorem main_convergence (n : ℕ) (hn : Odd n)
    (hentry : enters_trivial_cycle n) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_entry n hn hentry

theorem global_convergence :
    (∀ n : ℕ, Odd n → enters_trivial_cycle n) →
    ∀ n : ℕ, Odd n → ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  intro hentry n hn
  exact collatz_convergence_from_entry n hn (hentry n hn)

theorem convergence_with_bound (n : ℕ) (hn : Odd n)
    (hentry : enters_trivial_cycle n) :
    ∃ k : ℕ, k ≤ k ∧ (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  rcases collatz_convergence_from_entry n hn hentry with ⟨k, hk⟩
  exact ⟨k, le_rfl, hk⟩

theorem convergence_all_positive :
    ∀ n : ℕ, n > 0 → Odd n → enters_trivial_cycle n →
      ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  intro n _hnpos hnodd hentry
  exact collatz_convergence_from_entry n hnodd hentry

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

lemma aperiodic_orbit_has_cofinal_phase_returns
    (n q : ℕ)
    (hq : 0 < q)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) :
    orbit_has_cofinal_phase_returns n q := by
  exact cofinally_unbounded_orbit_has_cofinal_phase_returns n q hq
    (aperiodic_orbit_cofinally_unbounded n haper)

/-- Epoch-side specialization of the phase-return skeleton: an aperiodic orbit
admits arbitrarily far-out returns aligned modulo the joint selected-segment
period, hence in particular modulo both `gap_long(t)` and `Q_t(t)`, with
separation already beating the SEDT threshold `L₀(t,U)`. -/
noncomputable def aperiodic_orbit_has_cofinal_gap_long_phase_returns
    (n t U : ℕ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) :
    Epochs.OrbitHasCofinalGapLongPhaseReturns n t U := by
  have hraw : Epochs.RawCofinalGapLongPhaseReturns n t U := by
    intro N
    have hq : 0 < Epochs.selected_phase_period t := Epochs.selected_phase_period_pos t
    rcases aperiodic_orbit_has_cofinal_phase_returns n (Epochs.selected_phase_period t) hq haper 0 N
        (Collatz.SEDT.L₀ t U) with ⟨i, j, hiN, hij, hmod, _hiBig, _hjBig⟩
    exact ⟨i, j, hiN, hij, hmod⟩
  exact Epochs.orbit_has_cofinal_gap_long_phase_returns_of_raw hraw

/-- Honest canonical aperiodic phase-return witness: unlike the raw
`aperiodic_orbit_has_cofinal_gap_long_phase_returns` skeleton, this object is
built directly with the selected-segment semantic data actually used later in
the coercivity chain. In particular it carries paper-faithful D.1/E.1
bookkeeping on each chosen phase-return pair together with the honest
normalization-side correction control and the already reassembled canonical-gap
drift theorem needed downstream. -/
structure CanonicalAperiodicPhaseReturnWitness (n t U : ℕ) (β : ℝ) where
  leftIdx : ℕ → ℕ
  rightIdx : ℕ → ℕ
  leftStep : ∀ j : ℕ, leftIdx (j + 1) ≥ leftIdx j + 1
  rightStep : ∀ j : ℕ, rightIdx j < leftIdx (j + 1)
  longSep : ∀ j : ℕ, leftIdx j + Collatz.SEDT.L₀ t U ≤ rightIdx j
  selectedPhaseAligned :
    ∀ j : ℕ, leftIdx j % Epochs.selected_phase_period t = rightIdx j % Epochs.selected_phase_period t
  cofinalLeft : ∀ N : ℕ, ∃ j : ℕ, N ≤ leftIdx j
  carryPaper :
    ∀ j : ℕ, Epochs.SelectedPaperCarryArguments n t U (leftIdx j) (rightIdx j)
  correctionNonpositive :
    ∀ j : ℕ,
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[leftIdx j]) n)
        ((Collatz.Foundations.collatz_step^[rightIdx j]) n) ≤ 0
  fillEndpointNonincrease :
    ∀ j : ℕ,
      ((Collatz.Foundations.collatz_step^[leftIdx (j + 1)]) n) ≤
        ((Collatz.Foundations.collatz_step^[rightIdx j]) n)
  canonicalGapStep :
    sedt_dominant_parameters t U β →
      ∀ j : ℕ,
        potential β ((Collatz.Foundations.collatz_step^[leftIdx (j + 1)]) n) -
          potential β ((Collatz.Foundations.collatz_step^[leftIdx j]) n) ≤
            Collatz.SEDT.sedt_envelope t U β (leftIdx (j + 1) - leftIdx j)

/-- Forget the extra semantic fields of the honest canonical aperiodic witness
and recover the structured phase-return skeleton used by the coercivity layer. -/
def CanonicalAperiodicPhaseReturnWitness.toPhaseReturns
    {n t U : ℕ} {β : ℝ}
    (hw : CanonicalAperiodicPhaseReturnWitness n t U β) :
    Epochs.OrbitHasCofinalGapLongPhaseReturns n t U := by
  refine
    { leftIdx := hw.leftIdx
      rightIdx := hw.rightIdx
      leftStep := hw.leftStep
      rightStep := hw.rightStep
      longSep := hw.longSep
      selectedPhaseAligned := hw.selectedPhaseAligned
      phaseAligned := ?_
      qtPhaseAligned := ?_
      cofinalLeft := hw.cofinalLeft }
  · intro j
    have hle : hw.leftIdx j ≤ hw.rightIdx j := by
      exact le_trans (Nat.le_add_right _ _) (hw.longSep j)
    exact Epochs.gap_long_aligned_of_selected_phase_period t
      (hw.leftIdx j) (hw.rightIdx j) hle (hw.selectedPhaseAligned j)
  · intro j
    have hle : hw.leftIdx j ≤ hw.rightIdx j := by
      exact le_trans (Nat.le_add_right _ _) (hw.longSep j)
    exact Epochs.qt_phase_aligned_of_selected_phase_period t
      (hw.leftIdx j) (hw.rightIdx j) hle (hw.selectedPhaseAligned j)

/-- Orbit/epoch semantic package on the actual aperiodic phase-return skeleton.
This is the honest theorem-producing target below the repaired canonical witness:
the concrete selected pairs from
`aperiodic_orbit_has_cofinal_gap_long_phase_returns` carry exactly the local
selected-segment bookkeeping, the normalization-side correction control, and
the already reassembled canonical-gap drift theorem needed later in coercivity. -/
structure CanonicalAperiodicPhaseReturnSemantics
    (n t U : ℕ) (β : ℝ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) where
  carryPaper :
    ∀ j : ℕ,
      Epochs.SelectedPaperCarryArguments n t U
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).leftIdx j)
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).rightIdx j)
  correctionNonpositive :
    phase_return_potential_correction_nonpositive_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  fillEndpointNonincrease :
    phase_return_fill_endpoint_nonincrease_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  canonicalGapStep :
    canonical_phase_return_gap_step_sedt_on n t U β
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)

/-- Stepwise-aware actual-skeleton semantic package on the canonical aperiodic
phase-return skeleton. This is the honest lower stream-side object when the
filler content is available as raw value-level monotonicity on each
intermediate step, rather than only as endpoint order. The extra field is
genuinely semantic: `Collatz.Foundations.exists_odd_strict_growth_step` shows
that generic odd-step dynamics do not force one-step nonincrease. -/
structure CanonicalAperiodicPhaseReturnStepwiseSemantics
    (n t U : ℕ) (β : ℝ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) where
  carryPaper :
    ∀ j : ℕ,
      Epochs.SelectedPaperCarryArguments n t U
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).leftIdx j)
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).rightIdx j)
  correctionNonpositive :
    phase_return_potential_correction_nonpositive_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  fillStepwiseNonincrease :
    phase_return_fill_stepwise_nonincrease_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  canonicalGapStep :
    canonical_phase_return_gap_step_sedt_on n t U β
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)

/-- Lowest currently exposed actual-skeleton semantic package on the canonical
aperiodic phase-return skeleton: instead of directly carrying any residue or
drift statement on the filler, it only carries the exclusion that no filler
simple-step candidate is admitted. -/
structure CanonicalAperiodicPhaseReturnCandidateSelectionSemantics
    (n t U : ℕ) (β : ℝ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) where
  carryPaper :
    ∀ j : ℕ,
      Epochs.SelectedPaperCarryArguments n t U
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).leftIdx j)
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).rightIdx j)
  correctionNonpositive :
    phase_return_potential_correction_nonpositive_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  fillCandidateSelection :
    Epochs.FillerCandidateSelectionSemanticsOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  canonicalGapStep :
    canonical_phase_return_gap_step_sedt_on n t U β
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)

/-- Lowest currently exposed actual-skeleton semantic package on the canonical
aperiodic phase-return skeleton: instead of directly carrying any residue or
drift statement on the filler, it only carries the exclusion that no filler
simple-step candidate is admitted. -/
structure CanonicalAperiodicPhaseReturnCandidateExclusionSemantics
    (n t U : ℕ) (β : ℝ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) where
  carryPaper :
    ∀ j : ℕ,
      Epochs.SelectedPaperCarryArguments n t U
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).leftIdx j)
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).rightIdx j)
  correctionNonpositive :
    phase_return_potential_correction_nonpositive_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  fillCandidateExclusion :
    Epochs.GapLongPhaseReturnsFillerCandidateExclusionBridgeOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  canonicalGapStep :
    canonical_phase_return_gap_step_sedt_on n t U β
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)

/-- Even more atomic actual-skeleton semantic package on the canonical
aperiodic phase-return skeleton: instead of directly carrying filler-stepwise
monotonicity, it only assumes the arithmetic local source that no simple step
appears on the filler interval. -/
structure CanonicalAperiodicPhaseReturnNoSimpleStepSemantics
    (n t U : ℕ) (β : ℝ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) where
  carryPaper :
    ∀ j : ℕ,
      Epochs.SelectedPaperCarryArguments n t U
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).leftIdx j)
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).rightIdx j)
  correctionNonpositive :
    phase_return_potential_correction_nonpositive_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  fillNoSimpleStep :
    Epochs.GapLongPhaseReturnsFillerNoSimpleStepBridgeOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  canonicalGapStep :
    canonical_phase_return_gap_step_sedt_on n t U β
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)

/-- Even more atomic actual-skeleton semantic package on the canonical
aperiodic phase-return skeleton: instead of directly carrying filler-stepwise
monotonicity, it only assumes the arithmetic local source that every filler
orbit point has `step_type ≥ 2`. This is the narrowest stream-side semantic
package currently exposed below the stepwise layer. -/
structure CanonicalAperiodicPhaseReturnStepTypeTwoSemantics
    (n t U : ℕ) (β : ℝ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) where
  carryPaper :
    ∀ j : ℕ,
      Epochs.SelectedPaperCarryArguments n t U
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).leftIdx j)
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).rightIdx j)
  correctionNonpositive :
    phase_return_potential_correction_nonpositive_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  fillStepTypeTwo :
    Epochs.GapLongPhaseReturnsFillerStepTypeTwoBridgeOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  canonicalGapStep :
    canonical_phase_return_gap_step_sedt_on n t U β
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)

/-- Actual-skeleton carry-depth theorem source: each concrete selected
phase-return pair on the canonical aperiodic skeleton satisfies the localized
D.1/E.1 depth bookkeeping bound. This is the real mathematical source below
`carryPaper`. -/
def canonical_aperiodic_selected_long_epoch_bridge_on
    (n t U : ℕ) : Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.SelectedLongEpochBridgeOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Actual-skeleton carry-depth theorem source: each concrete selected
phase-return pair on the canonical aperiodic skeleton satisfies the localized
D.1/E.1 depth bookkeeping bound. This is the real mathematical source below
`carryPaper`. -/
def canonical_aperiodic_selected_portrait_enumeration_semantics
    (n t U : ℕ) : Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    ∀ j : ℕ,
      Epochs.SelectedPortraitEnumerationSemantics n t U
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j)
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j)

/-- Actual-skeleton selected-segment carry theorem source below the depth bridge:
once the portrait bonus is fixed on a concrete selected pair of the canonical
aperiodic skeleton, it must control the depth drop in the paper-faithful
`bonus - length` form. -/
def canonical_aperiodic_selected_depth_from_bonus_semantics
    (n t U : ℕ)
    (hportrait : canonical_aperiodic_selected_portrait_enumeration_semantics n t U) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    ∀ j : ℕ,
      let i := (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j
      let k := (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j
      ((Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[k]) n) : ℝ) -
          (Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[i]) n) : ℝ)) ≤
        (hportrait _ha j).cappedBonus - ((k - i : ℕ) : ℝ)

/-- Actual-skeleton carry-depth theorem source: each concrete selected
phase-return pair on the canonical aperiodic skeleton satisfies the localized
D.1/E.1 depth bookkeeping bound. This is the real mathematical source below
`carryPaper`. -/
def canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics
    (n t U : ℕ) : Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    ∀ j : ℕ,
      Epochs.SelectedDepthBookkeepingBridgeSemantics n t U
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j)
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j)

/-- Actual-skeleton carry-depth theorem source: each concrete selected
phase-return pair on the canonical aperiodic skeleton satisfies the localized
D.1/E.1 depth bookkeeping bound. This is the real mathematical source below
`carryPaper`. -/
def canonical_aperiodic_selected_carry_depth_semantics
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    ∀ j : ℕ,
      Epochs.SelectedCarryDepthSemantics n t U
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j)
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j)

/-- Actual-skeleton correction theorem source: on the canonical aperiodic
phase-return skeleton, the normalization correction is already known to be
nonpositive on every selected pair. -/
def canonical_aperiodic_phase_return_correction_nonpositive_on
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    phase_return_potential_correction_nonpositive_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Actual-skeleton canonical-gap theorem source: the full repaired local
canonical-gap `E.2` theorem holds on the concrete aperiodic phase-return
skeleton itself. -/
def canonical_aperiodic_phase_return_gap_step_sedt_on
    (n t U : ℕ) (β : ℝ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    canonical_phase_return_gap_step_sedt_on n t U β
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- More orbit-semantic stream-level source on the actual aperiodic skeleton:
the induced canonical long-gap stream already satisfies the orbitwise `E.2`
envelope. This is definitionally equivalent to the local canonical-gap theorem
on that same skeleton. -/
noncomputable def canonical_aperiodic_orbit_long_epoch_stream
    (n t U : ℕ)
    (haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n) :
    Epochs.OrbitLongEpochStream n t U :=
  Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps n t U
    ((Epochs.canonical_gap_long_phase_returns_bridge n t U)
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper))

/-- More orbit-semantic stream-level source on the actual aperiodic skeleton:
the induced canonical long-gap stream already satisfies the orbitwise `E.2`
envelope. This is definitionally equivalent to the local canonical-gap theorem
on that same skeleton. -/
def canonical_aperiodic_orbit_epoch_sedt_envelope
    (n t U : ℕ) (β : ℝ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    orbit_epoch_sedt_envelope t U β
      (canonical_aperiodic_orbit_long_epoch_stream n t U _ha)

/-- Honest actual-stream local accounting target: each epoch of the induced
canonical long-gap stream carries the exact logarithmic and depth-side local
E.1/E.2 bounds whose sum gives the native `SEDT` drift estimate. -/
def canonical_aperiodic_orbit_epoch_local_accounting_semantics
    (n t U : ℕ) (β : ℝ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    ∀ j : ℕ,
      Collatz.SEDT.local_log_drift_bound
        ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).orbitVal j)
        ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).orbitVal (j + 1))
        ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).epochLen j) ∧
      Collatz.SEDT.local_depth_drift_bound t U β
        ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).orbitVal j)
        ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).orbitVal (j + 1))
        ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).epochLen j)

/-- Honest actual-stream native `SEDT` target: each epoch of the induced
canonical long-gap stream satisfies the native `SEDT.potential_change`
envelope before normalization back to `Coercivity.potential`. -/
def canonical_aperiodic_orbit_epoch_native_sedt_semantics
    (n t U : ℕ) (β : ℝ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    ∀ j : ℕ,
      Collatz.SEDT.potential_change
        ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).orbitVal j)
        ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).orbitVal (j + 1))
        β ≤
          Collatz.SEDT.sedt_envelope t U β
            ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).epochLen j)

/-- Stream-level normalization target on the induced canonical long-gap stream:
to pass from native `SEDT.potential_change` to `Coercivity.potential`, the
correction term must already be nonpositive on each actual stream epoch. -/
def canonical_aperiodic_orbit_epoch_correction_nonpositive
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    ∀ j : ℕ,
      potential_change_correction
        ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).orbitVal j)
        ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).orbitVal (j + 1)) ≤ 0

/-- Lower stream normalization target on the induced canonical long-gap stream:
the endpoint values along each actual stream epoch should not increase. This is
the exact hypothesis needed to force the stream correction term to be
nonpositive. -/
def canonical_aperiodic_orbit_epoch_endpoint_nonincrease
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    ∀ j : ℕ,
      ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).orbitVal (j + 1)) ≤
        ((canonical_aperiodic_orbit_long_epoch_stream n t U _ha).orbitVal j)

/-- Lower filler-side endpoint target on the actual aperiodic phase-return
skeleton: between one selected pair end and the next canonical left endpoint,
the raw orbit value should also not increase. Together with the pair endpoint
order this is exactly what yields stream-level endpoint monotonicity. -/
def canonical_aperiodic_phase_return_fill_endpoint_nonincrease
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    phase_return_fill_endpoint_nonincrease_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Lower value-level filler source on the actual canonical aperiodic skeleton:
every individual Collatz step inside the filler segment is nonincreasing. This
is stronger than endpoint order, but remains a purely value-level statement,
free of `β` and potential normalization. -/
def canonical_aperiodic_phase_return_fill_stepwise_nonincrease
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    phase_return_fill_stepwise_nonincrease_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Even lower stream-side theorem source on the actual canonical aperiodic
skeleton: the chosen phase-return witness carries raw filler-stepwise
monotonicity as separate value-level semantics below coercivity. This matches
the new lower bridge in `Epochs.LongEpochs` and makes explicit that the
`choose`-based phase-return skeleton does not by itself provide filler control. -/
def canonical_aperiodic_phase_return_fill_stepwise_bridge
    (n t U : ℕ) : Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerStepwiseBridgeOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Arithmetic lower filler-side source on the actual canonical aperiodic
skeleton: every orbit point inside the filler interval has local Collatz
exponent at least `2`. Combined with oddness of the orbit, this is enough to
produce the stronger stepwise filler monotonicity theorem. -/
def canonical_aperiodic_phase_return_fill_step_type_two_bridge
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerStepTypeTwoBridgeOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Even more primitive arithmetic source on the actual canonical aperiodic
skeleton: every filler orbit point is already a complex step in the mod-4
sense. This is a residue-level precursor to the `step_type ≥ 2` bridge. -/
def canonical_aperiodic_phase_return_fill_complex_step_bridge
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerComplexStepBridgeOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Concrete next-left phase-compatibility promotion source on the actual
canonical aperiodic skeleton. This remains only a proxy layer beneath the
generic candidate-selection semantics. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_promotion_semantics
    (n t U : ℕ) : Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotionOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Concrete next-left phase-compatibility minimality source on the actual
canonical aperiodic skeleton: no index in the same selected phase class as the
chosen next left endpoint may occur strictly earlier inside the filler
interval. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_semantics
    (n t U : ℕ) : Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimalityOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- More explicit local theorem-source on the actual canonical aperiodic
skeleton for the current phase-compatible minimality proxy. This isolates the
local `noEarlier` content before repackaging it into the existing concrete
minimality wrapper. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_local_semantics
    (n t U : ℕ) : Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.CanonicalNextLeftPhaseCompatibleMinimalitySemanticsOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- The previous local theorem-source immediately fills the already exposed
concrete phase-compatible minimality wrapper on the actual aperiodic
skeleton. -/
theorem canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_semantics_of_local_semantics
    {n t U : ℕ}
    (hlocal :
      canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_local_semantics
        n t U) :
    canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_semantics
      n t U := by
  intro haper
  exact
    Epochs.gap_long_phase_returns_filler_canonical_next_left_phase_compatible_minimality_on_of_semantics
      (hlocal haper)

/-- Exclusion-style filler source on the actual canonical aperiodic skeleton:
inside the filler interval, no orbit point is a simple step in the mod-4
sense. This is a more faithful lower semantic target if the eventual proof is
phrased as an exclusion of new canonical simple-step events. -/
def canonical_aperiodic_phase_return_fill_candidate_promotion_semantics
    (n t U : ℕ) : Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.FillerSimpleStepPromotionOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Next-left minimality semantics on the actual canonical aperiodic skeleton:
once a filler-side admissibility notion is fixed by the promotion semantics, no
admissible selected event may occur strictly before the already chosen next
left endpoint. -/
def canonical_aperiodic_phase_return_fill_next_left_minimality_semantics
    (n t U : ℕ)
    (hprom : canonical_aperiodic_phase_return_fill_candidate_promotion_semantics n t U) :
    Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.FillerNextLeftMinimalityOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)
      ((hprom _ha).admissible)

/-- Exclusion-style filler source on the actual canonical aperiodic skeleton:
inside the filler interval, no orbit point is a simple step in the mod-4
sense. This is a more faithful lower semantic target if the eventual proof is
phrased as an exclusion of new canonical simple-step events. -/
def canonical_aperiodic_phase_return_fill_candidate_selection_semantics
    (n t U : ℕ) : Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.FillerCandidateSelectionSemanticsOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Honest actual-skeleton witness for the repaired concrete next-left layer:
the admissibility notion used for filler-side next-left reasoning is supplied
explicitly, rather than identified with a phase-only proxy. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics
    (n t U : ℕ) : Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.CanonicalNextLeftSelectionWitnessOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Actual-skeleton promotion source for the repaired concrete next-left layer,
relative to an explicit admissibility witness. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_semantics
    (n t U : ℕ)
    (hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U) :
    Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)
      (hnext _ha)

/-- Actual-skeleton explicit event-level source for the repaired promotion
slot: for each filler simple-step candidate one provides a promoted interior
event witness carrying both the chosen index and its realized orbit value. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_event_source_semantics
    (n t U : ℕ)
    (hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U) :
    Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionEventSourceOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)
      (hnext _ha)

/-- Actual-skeleton lower residual for the strict-interior case: if a filler
simple-step candidate already lies strictly after the current right endpoint,
its own index is admissible for the supplied next-left witness. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_interior_admissibility_semantics
    (n t U : ℕ)
    (hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U) :
    Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessInteriorAdmissibilityOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)
      (hnext _ha)

/-- Actual-skeleton lower residual for the remaining boundary case: if the
simple-step candidate occurs exactly at the current right endpoint, genuine
extra semantics must still produce a promoted interior event witness. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_right_boundary_event_source_semantics
    (n t U : ℕ)
    (hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U) :
    Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSourceOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)
      (hnext _ha)

/-- Concrete boundary-event theorem source on the actual canonical aperiodic
skeleton, independent of any chosen next-left admissibility language. This is
the new lower mathematical target for the boundary branch. -/
def canonical_aperiodic_phase_return_fill_boundary_promoted_selected_event_source_semantics
    (n t U : ℕ) : Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsBoundaryPromotedSelectedEventSourceOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Separate actual-skeleton bridge from the concrete boundary-event language
into one chosen witness-relative admissibility notion. -/
def canonical_aperiodic_phase_return_fill_boundary_promoted_selected_admissibility_bridge_semantics
    (n t U : ℕ)
    (hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U) :
    Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsBoundaryPromotedSelectedAdmissibilityBridgeOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)
      (hnext _ha)

/-- Sharpened actual-skeleton residual for the boundary case: if the orbit point
at `rightIdx j` is itself a simple step, produce a promoted interior event
witness for that canonical boundary candidate. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_right_boundary_simple_step_event_source_semantics
    (n t U : ℕ)
    (hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U) :
    Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSourceOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)
      (hnext _ha)

/-- The new concrete boundary-event theorem source, together with a chosen
admissibility bridge, immediately fills the sharpened witness-relative boundary
slot on the actual canonical aperiodic skeleton. -/
noncomputable def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_right_boundary_simple_step_event_source_of_boundary_event_source_and_admissibility
    {n t U : ℕ}
    {hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U}
    (hsrc :
      canonical_aperiodic_phase_return_fill_boundary_promoted_selected_event_source_semantics
        n t U)
    (hadm :
      canonical_aperiodic_phase_return_fill_boundary_promoted_selected_admissibility_bridge_semantics
        n t U hnext) :
    canonical_aperiodic_phase_return_fill_canonical_next_left_witness_right_boundary_simple_step_event_source_semantics
      n t U hnext := by
  intro haper
  exact
    Epochs.gap_long_phase_returns_filler_canonical_next_left_witness_right_boundary_simple_step_event_source_on_of_boundary_event_source_and_admissibility
      (hsrc haper) (hadm haper)

/-- Actual-skeleton next-left minimality source for the repaired concrete
next-left layer, relative to the same explicit admissibility witness. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_minimality_semantics
    (n t U : ℕ)
    (hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U) :
    Sort _ :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerCanonicalNextLeftWitnessMinimalityOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)
      (hnext _ha)

/-- The previous actual-skeleton event-level source immediately populates the
repaired witness-relative promotion slot. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_of_event_source
    {n t U : ℕ}
    {hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U}
    (hsrc :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_event_source_semantics
        n t U hnext) :
    canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_semantics
      n t U hnext := by
  intro haper
  exact
    Epochs.gap_long_phase_returns_filler_canonical_next_left_witness_promotion_on_of_event_source
      (hsrc haper)

/-- The explicit promoted-event source on the actual aperiodic skeleton also
decomposes into the same two local residuals: strict-interior admissibility and
the genuinely extra right-boundary event source. -/
noncomputable def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_event_source_of_interior_admissibility_and_right_boundary
    {n t U : ℕ}
    {hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U}
    (hinterior :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_interior_admissibility_semantics
        n t U hnext)
    (hboundary :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_right_boundary_event_source_semantics
        n t U hnext) :
    canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_event_source_semantics
      n t U hnext := by
  intro haper
  exact
    Epochs.gap_long_phase_returns_filler_canonical_next_left_witness_promotion_event_source_on_of_interior_admissibility_and_right_boundary
      (hinterior haper) (hboundary haper)

/-- The sharpened boundary simple-step source immediately fills the older
boundary slot on the actual aperiodic skeleton. -/
noncomputable def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_right_boundary_event_source_of_simple_step_event_source
    {n t U : ℕ}
    {hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U}
    (hsrc :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_right_boundary_simple_step_event_source_semantics
        n t U hnext) :
    canonical_aperiodic_phase_return_fill_canonical_next_left_witness_right_boundary_event_source_semantics
      n t U hnext := by
  intro haper
  exact
    Epochs.gap_long_phase_returns_filler_canonical_next_left_witness_right_boundary_event_source_on_of_simple_step_event_source
      (hsrc haper)

/-- The old phase-compatible admissibility language still provides one explicit
witness for the repaired next-left layer on the actual aperiodic skeleton. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_witness
    (n t U : ℕ) :
    canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics
      n t U := by
  intro haper
  exact
    Epochs.canonical_next_left_selection_witness_on_of_phase_compatibility
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)

/-- Any old phase-compatible promotion theorem can be viewed as a source for
the repaired witness-based layer once the witness is chosen to be the same
phase-compatible admissibility language. -/
def canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_of_phase_compatible_promotion
    {n t U : ℕ}
    (hprom :
      canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_promotion_semantics
        n t U) :
    canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_semantics
      n t U
      (canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_witness
        n t U) := by
  intro haper
  exact
    Epochs.filler_simple_step_promotion_on_of_phase_compatible_witness_and_promotion
      (hprom haper)

/-- The already proved phase-compatible minimality theorem also populates the
minimality half of the repaired witness-based layer when the witness is chosen
to be the old phase-compatible admissibility language. -/
theorem canonical_aperiodic_phase_return_fill_canonical_next_left_witness_minimality_of_phase_compatible_minimality
    {n t U : ℕ}
    (hmin :
      canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_semantics
        n t U) :
    canonical_aperiodic_phase_return_fill_canonical_next_left_witness_minimality_semantics
      n t U
      (canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_witness
        n t U) := by
  intro haper
  exact
    Epochs.filler_next_left_minimality_on_of_phase_compatible_witness_and_minimality
      (hmin haper)

/-- The repaired concrete next-left witness plus its witness-relative
promotion/minimality sources already assemble to the generic
candidate-selection semantics on the canonical filler interval. -/
noncomputable def canonical_aperiodic_phase_return_fill_candidate_selection_semantics_of_canonical_next_left_witness
    {n t U : ℕ}
    (hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U)
    (hprom :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_semantics
        n t U hnext)
    (hmin :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_minimality_semantics
        n t U hnext) :
    canonical_aperiodic_phase_return_fill_candidate_selection_semantics n t U := by
  intro haper
  exact Epochs.filler_candidate_selection_semantics_on_of_canonical_next_left_witness
    (hnext haper) (hprom haper) (hmin haper)

/-- The concrete next-left phase-compatibility promotion/minimality pair on the
actual canonical aperiodic skeleton already assembles to the more generic
candidate-selection semantics. -/
noncomputable def canonical_aperiodic_phase_return_fill_candidate_selection_semantics_of_canonical_next_left_phase_compatibility_and_minimality
    {n t U : ℕ}
    (hprom :
      canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_promotion_semantics n t U)
    (hmin :
      canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_semantics n t U) :
    canonical_aperiodic_phase_return_fill_candidate_selection_semantics n t U := by
  exact
    canonical_aperiodic_phase_return_fill_candidate_selection_semantics_of_canonical_next_left_witness
      (canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_witness n t U)
      (canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_of_phase_compatible_promotion
        hprom)
      (canonical_aperiodic_phase_return_fill_canonical_next_left_witness_minimality_of_phase_compatible_minimality
        hmin)

/-- Combining the actual-skeleton promotion semantics with actual-skeleton
next-left minimality produces the honest candidate-selection semantics on the
canonical filler interval. -/
noncomputable def canonical_aperiodic_phase_return_fill_candidate_selection_semantics_of_promotion_and_minimality
    {n t U : ℕ}
    (hprom : canonical_aperiodic_phase_return_fill_candidate_promotion_semantics n t U)
    (hmin :
      canonical_aperiodic_phase_return_fill_next_left_minimality_semantics n t U hprom) :
    canonical_aperiodic_phase_return_fill_candidate_selection_semantics n t U := by
  intro haper
  exact Epochs.filler_candidate_selection_semantics_on_of_promotion_and_minimality
    (hprom haper) (hmin haper)

/-- Exclusion-style filler source on the actual canonical aperiodic skeleton:
inside the filler interval, no orbit point is a simple step in the mod-4
sense. This is a more faithful lower semantic target if the eventual proof is
phrased as an exclusion of new canonical simple-step events. -/
def canonical_aperiodic_phase_return_fill_candidate_exclusion_bridge
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerCandidateExclusionBridgeOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Honest canonical-selection semantics on the filler interval immediately
produces the current lowest candidate-exclusion bridge on the actual canonical
aperiodic skeleton. -/
theorem canonical_aperiodic_phase_return_fill_candidate_exclusion_bridge_of_selection_semantics
    {n t U : ℕ}
    (hsel :
      canonical_aperiodic_phase_return_fill_candidate_selection_semantics n t U) :
    canonical_aperiodic_phase_return_fill_candidate_exclusion_bridge n t U := by
  intro haper
  exact Epochs.gap_long_phase_returns_filler_candidate_exclusion_of_selection_semantics_on
    (hsel haper)

/-- Exclusion-style filler source on the actual canonical aperiodic skeleton:
inside the filler interval, no orbit point is a simple step in the mod-4
sense. This is a more faithful lower semantic target if the eventual proof is
phrased as an exclusion of new canonical simple-step events. -/
def canonical_aperiodic_phase_return_fill_no_simple_step_bridge
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    Epochs.GapLongPhaseReturnsFillerNoSimpleStepBridgeOn
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- The candidate-exclusion filler bridge upgrades immediately to the
no-simple-step bridge on the actual canonical aperiodic skeleton. -/
theorem canonical_aperiodic_phase_return_fill_no_simple_step_bridge_of_candidate_exclusion_bridge
    {n t U : ℕ}
    (hexcl :
      canonical_aperiodic_phase_return_fill_candidate_exclusion_bridge n t U) :
    canonical_aperiodic_phase_return_fill_no_simple_step_bridge n t U := by
  intro haper
  exact Epochs.gap_long_phase_returns_filler_no_simple_step_of_candidate_exclusion_on
    (hexcl haper)

/-- The exclusion-style filler bridge upgrades immediately to the residue-level
complex-step bridge on the actual canonical aperiodic skeleton. -/
theorem canonical_aperiodic_phase_return_fill_complex_step_bridge_of_no_simple_step_bridge
    {n t U : ℕ}
    (hn : Odd n)
    (hnoSimple :
      canonical_aperiodic_phase_return_fill_no_simple_step_bridge n t U) :
    canonical_aperiodic_phase_return_fill_complex_step_bridge n t U := by
  intro haper
  exact Epochs.gap_long_phase_returns_filler_complex_step_of_no_simple_step_on hn
    (hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
    (hnoSimple haper)

/-- The residue-level complex-step bridge on the actual aperiodic filler
immediately upgrades to the arithmetic `step_type ≥ 2` bridge. -/
theorem canonical_aperiodic_phase_return_fill_step_type_two_bridge_of_complex_step_bridge
    {n t U : ℕ}
    (hn : Odd n)
    (hcomplex :
      canonical_aperiodic_phase_return_fill_complex_step_bridge n t U) :
    canonical_aperiodic_phase_return_fill_step_type_two_bridge n t U := by
  intro haper
  exact Epochs.gap_long_phase_returns_filler_step_type_two_of_complex_step_on hn
    (hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
    (hcomplex haper)

/-- The actual aperiodic lower step-type bridge upgrades to the filler-stepwise
bridge by the pure arithmetic lemma `collatz_step_le_self_of_step_type_ge_two`.
-/
theorem canonical_aperiodic_phase_return_fill_stepwise_bridge_of_step_type_two_bridge
    {n t U : ℕ}
    (hn : Odd n)
    (hstepTwo :
      canonical_aperiodic_phase_return_fill_step_type_two_bridge n t U) :
    canonical_aperiodic_phase_return_fill_stepwise_bridge n t U := by
  intro haper
  exact Epochs.gap_long_phase_returns_filler_stepwise_of_step_type_two_on hn
    (hphase :=
      aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
    (hstepTwo haper)

/-- The lower filler-stepwise bridge on the actual canonical aperiodic skeleton
is definitionally exactly the stronger filler target consumed downstream. -/
def canonical_aperiodic_phase_return_fill_stepwise_nonincrease_of_lower_bridge
    {n t U : ℕ}
    (hfill :
      canonical_aperiodic_phase_return_fill_stepwise_bridge n t U) :
    canonical_aperiodic_phase_return_fill_stepwise_nonincrease n t U :=
  hfill

/-- The arithmetic lower bridge `step_type ≥ 2` on the actual canonical
aperiodic filler also yields the downstream stronger stepwise filler target. -/
def canonical_aperiodic_phase_return_fill_stepwise_nonincrease_of_step_type_two_bridge
    {n t U : ℕ}
    (hn : Odd n)
    (hstepTwo :
      canonical_aperiodic_phase_return_fill_step_type_two_bridge n t U) :
    canonical_aperiodic_phase_return_fill_stepwise_nonincrease n t U :=
  canonical_aperiodic_phase_return_fill_stepwise_nonincrease_of_lower_bridge
    (canonical_aperiodic_phase_return_fill_stepwise_bridge_of_step_type_two_bridge
      hn hstepTwo)

/-- The arithmetic lower bridge `step_type ≥ 2` on every filler index also
immediately yields the weaker filler endpoint-order theorem consumed by the
existing downstream chain. -/
def canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_step_type_two_bridge
    {n t U : ℕ}
    (hn : Odd n)
    (hstepTwo :
      canonical_aperiodic_phase_return_fill_step_type_two_bridge n t U) :
    canonical_aperiodic_phase_return_fill_endpoint_nonincrease n t U := by
  intro haper
  exact phase_return_fill_endpoint_nonincrease_on_of_stepwise_nonincrease
    ((canonical_aperiodic_phase_return_fill_stepwise_nonincrease_of_step_type_two_bridge
      hn hstepTwo) haper)

/-- Constructor for the canonical filler endpoint-order contract from
witness-level theorems on the actual aperiodic phase-return witness. -/
def canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_witness
    (n t U : ℕ)
    (hcanon :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        phase_return_fill_endpoint_nonincrease_on n t U
          (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)) :
    canonical_aperiodic_phase_return_fill_endpoint_nonincrease n t U :=
  hcanon

/-- The stronger stepwise value-level monotonicity source on each filler segment
immediately yields the endpoint-order target consumed downstream. -/
def canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_stepwise_nonincrease
    (n t U : ℕ)
    (hstep :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        phase_return_fill_stepwise_nonincrease_on n t U
          (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)) :
    canonical_aperiodic_phase_return_fill_endpoint_nonincrease n t U := by
  intro haper
  exact phase_return_fill_endpoint_nonincrease_on_of_stepwise_nonincrease (hstep haper)

/-- Stream endpoint monotonicity decomposes honestly into the endpoint order on
the selected pair itself plus the missing endpoint order across the filler from
that pair end to the next canonical left index. -/
theorem canonical_aperiodic_orbit_epoch_endpoint_nonincrease_of_phase_return_endpoint_and_fill
    {n t U : ℕ}
    (hpair :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        phase_return_endpoint_nonincrease_on n t U
          (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha))
    (hfill : canonical_aperiodic_phase_return_fill_endpoint_nonincrease n t U) :
    canonical_aperiodic_orbit_epoch_endpoint_nonincrease n t U := by
  intro haper j
  have hmono :=
    phase_return_left_to_left_endpoint_nonincrease_on_of_pair_and_fill
      (hpair haper) (hfill haper)
  dsimp [canonical_aperiodic_orbit_long_epoch_stream, Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps,
    Epochs.orbit_long_epoch_supply_of_cofinal_long_epoch_gaps,
    Epochs.orbit_has_cofinal_long_epoch_gaps_of_gap_long_phase_returns,
    Epochs.canonical_gap_long_phase_returns_bridge]
  exact hmono j

/-- Build the `carryPaper` field on the actual aperiodic skeleton from the
minimal lower semantic input that still carries real D.1/E.1 content: a local
depth/carry theorem on each selected phase-return pair. The phase/touch side is
then supplied canonically from the skeleton's modulo-`Q_t` data. -/
noncomputable def canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry
    (n t U : ℕ) :
    canonical_aperiodic_selected_portrait_enumeration_semantics n t U := by
  intro haper j
  let hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper
  refine
    { touchWitness :=
        Collatz.Mixing.selected_touch_count_witness_of_qt_phase
          (Epochs.qt_phase_segment_witness_of_phase_returns hphase j)
      cappedBonus := Epochs.selected_multibit_gain_budget t U (hphase.leftIdx j) (hphase.rightIdx j)
      cappedBonusUpper := by exact le_rfl }

/-- Once the canonical actual-skeleton portrait semantics are fixed by the
phase geometry, the remaining depth-from-bonus target is exactly the already
exposed selected-pair carry-depth theorem source. -/
theorem canonical_aperiodic_selected_depth_from_bonus_semantics_of_depth_semantics
    {n t U : ℕ}
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U) :
    canonical_aperiodic_selected_depth_from_bonus_semantics n t U
      (canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry n t U) := by
  intro haper j
  dsimp [canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry,
    Epochs.selected_multibit_gain_budget]
  exact Epochs.selected_depth_from_bonus_bound_canonical_of_depth_semantics (hdepth haper j)

/-- Canonical carry-side residual after phase-geometry closure: the only
remaining lower selected-segment content is the depth-from-bonus inequality for
the canonical portrait semantics already forced by the actual skeleton's
modulo-`Q_t` phase data. -/
def canonical_aperiodic_selected_depth_from_bonus_semantics_canonical
    (n t U : ℕ) : Prop :=
  canonical_aperiodic_selected_depth_from_bonus_semantics n t U
    (canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry n t U)

/-- Minimal actual-skeleton carry theorem source after phase-geometry closure:
on each canonical selected pair, the depth drop is already bounded by the
canonical multibit budget minus the segment length. This states the remaining
carry-side content without reintroducing any portrait packaging. -/
def canonical_aperiodic_selected_depth_from_bonus_budget_source
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
    ∀ j : ℕ,
      let hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha
      ((Collatz.Foundations.depth_minus
            ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) n) : ℝ) -
          (Collatz.Foundations.depth_minus
            ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) n) : ℝ)) ≤
        Epochs.selected_multibit_gain_budget t U (hphase.leftIdx j) (hphase.rightIdx j) -
          ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ)

/-- The explicit budget-level source on canonical selected pairs is exactly the
canonical carry-side residual, since phase geometry has already fixed the
portrait semantics to use `selected_multibit_gain_budget`. -/
theorem canonical_aperiodic_selected_depth_from_bonus_semantics_canonical_of_budget_source
    {n t U : ℕ}
    (hsource : canonical_aperiodic_selected_depth_from_bonus_budget_source n t U) :
    canonical_aperiodic_selected_depth_from_bonus_semantics_canonical n t U := by
  intro haper j
  let hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper
  dsimp [canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry,
    Epochs.selected_multibit_gain_budget]
  simpa using hsource haper j

/-- In particular, the exact lower selected-segment actual-skeleton targets can
already be supplied from canonical phase geometry plus the current selected-pair
carry-depth theorem source. -/
noncomputable def canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_phase_geometry_and_depth_semantics
    {n t U : ℕ}
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U) :
    canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics n t U := by
  intro haper j
  refine
    { portrait :=
        (canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry n t U) haper j
      depthFromBonus :=
        (canonical_aperiodic_selected_depth_from_bonus_semantics_of_depth_semantics hdepth) haper j }

/-- The canonical carry-side residual target already determines the full
selected-segment depth-bookkeeping bridge semantics on the actual aperiodic
skeleton, since the portrait part is forced by phase geometry. -/
noncomputable def canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_canonical_depth_from_bonus
    {n t U : ℕ}
    (hbonus : canonical_aperiodic_selected_depth_from_bonus_semantics_canonical n t U) :
    canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics n t U := by
  intro haper j
  refine
    { portrait :=
        (canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry n t U) haper j
      depthFromBonus := hbonus haper j }

/-- Build the `carryPaper` field on the actual aperiodic skeleton from the
minimal lower semantic input that still carries real D.1/E.1 content: a local
depth/carry theorem on each selected phase-return pair. The phase/touch side is
then supplied canonically from the skeleton's modulo-`Q_t` data. -/
noncomputable def canonical_aperiodic_carry_paper_of_depth_semantics
    {n t U : ℕ}
    {haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n}
    (hdepth :
      ∀ j : ℕ,
        Epochs.SelectedCarryDepthSemantics n t U
          ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).leftIdx j)
          ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).rightIdx j)) :
    ∀ j : ℕ,
      Epochs.SelectedPaperCarryArguments n t U
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).leftIdx j)
        ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper).rightIdx j) := by
  let hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper
  intro j
  exact Epochs.selected_paper_carry_arguments_of_qt_phase_and_depth_semantics
    (Epochs.qt_phase_segment_witness_of_phase_returns hphase j) (hdepth j)

/-- Actual-skeleton carry-side constructor from a genuine selected long-epoch
bridge on the canonical aperiodic skeleton. This packages the selected witness
data back into the paper-faithful `carryPaper` arguments consumed by the
repaired canonical witness. -/
noncomputable def canonical_aperiodic_carry_paper_of_selected_long_epoch_bridge_on
    {n t U : ℕ}
    (hbridge : canonical_aperiodic_selected_long_epoch_bridge_on n t U) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      ∀ j : ℕ,
        Epochs.SelectedPaperCarryArguments n t U
          ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j)
          ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j) := by
  intro haper j
  let hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper
  let hw := hbridge haper j
  have hdepth :
      Epochs.SelectedCarryDepthSemantics n t U
        (hphase.leftIdx j) (hphase.rightIdx j) := by
    refine ⟨?_⟩
    dsimp [Epochs.selected_depth_bookkeeping_bound]
    rw [← hw.realizedStart, ← hw.realizedEnd]
    have hcombine :
        hw.multibitGain - ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ) ≤
          (Collatz.SEDT.α t U - 2) * ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ) +
            Collatz.SEDT.C t U := by
      linarith [hw.multibitGainUpper]
    exact le_trans hw.depthBookkeeping hcombine
  exact Epochs.selected_paper_carry_arguments_of_qt_phase_and_depth_semantics
    (Epochs.qt_phase_segment_witness_of_phase_returns hphase j)
    hdepth

/-- Actual-skeleton selected-long-epoch bridge from the honest selected-pair
paper semantics on the canonical aperiodic skeleton. This is the direct
theorem-producing constructor for the lower epoch/carry target. -/
noncomputable def canonical_aperiodic_selected_long_epoch_bridge_on_of_carry_paper
    {n t U : ℕ}
    (hn : Odd n)
    (hcarryPaper :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        ∀ j : ℕ,
          Epochs.SelectedPaperCarryArguments n t U
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j)
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j)) :
    canonical_aperiodic_selected_long_epoch_bridge_on n t U := by
  intro haper
  exact Epochs.selected_long_epoch_bridge_on_of_semantics hn
    (hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
    (hcarryPaper haper)

/-- Restrict any global selected-long-epoch bridge to the concrete canonical
aperiodic skeleton. This keeps the actual-skeleton target honest while allowing
reuse of a theorem already proved uniformly in `hphase`. -/
noncomputable def canonical_aperiodic_selected_long_epoch_bridge_on_of_selected_long_epoch_bridge
    {n t U : ℕ}
    (hbridge : Epochs.SelectedLongEpochBridge n t U) :
    canonical_aperiodic_selected_long_epoch_bridge_on n t U := by
  intro haper
  exact hbridge (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)

/-- Actual-skeleton selected-long-epoch bridge directly from the already exposed
selected-pair depth/carry theorem source. This is the clean theorem-producing
path from honest D.1/E.1 selected-segment semantics to the lower epoch bridge
on the canonical aperiodic skeleton. -/
noncomputable def canonical_aperiodic_selected_long_epoch_bridge_on_of_depth_semantics
    {n t U : ℕ}
    (hn : Odd n)
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U) :
    canonical_aperiodic_selected_long_epoch_bridge_on n t U := by
  exact canonical_aperiodic_selected_long_epoch_bridge_on_of_carry_paper hn
    (fun haper =>
      canonical_aperiodic_carry_paper_of_depth_semantics
        (haper := haper) (fun j => hdepth haper j))

/-- One selected long-epoch witness already contains exactly the local
depth/carry bookkeeping data needed for `SelectedCarryDepthSemantics`. -/
theorem selected_carry_depth_semantics_of_selected_long_epoch_witness
    {n t U : ℕ}
    {hphase : Epochs.OrbitHasCofinalGapLongPhaseReturns n t U}
    {j : ℕ}
    (hw : Epochs.SelectedLongEpochWitness hphase j) :
    Epochs.SelectedCarryDepthSemantics n t U
      (hphase.leftIdx j) (hphase.rightIdx j) := by
  refine ⟨?_⟩
  dsimp [Epochs.selected_depth_bookkeeping_bound]
  rw [← hw.realizedStart, ← hw.realizedEnd]
  have hcombine :
      hw.multibitGain - ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ) ≤
        (Collatz.SEDT.α t U - 2) * ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ) +
          Collatz.SEDT.C t U := by
    linarith [hw.multibitGainUpper]
  exact le_trans hw.depthBookkeeping hcombine

/-- Actual-skeleton depth-bridge semantics from still lower selected-segment
portrait/carry content on the canonical aperiodic skeleton. -/
noncomputable def canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_portrait_and_depth_from_bonus
    {n t U : ℕ}
    (hportrait : canonical_aperiodic_selected_portrait_enumeration_semantics n t U)
    (hbonus : canonical_aperiodic_selected_depth_from_bonus_semantics n t U hportrait) :
    canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics n t U := by
  intro haper j
  let hp := hportrait haper j
  refine
    { portrait := hp
      depthFromBonus := ?_ }
  exact hbonus haper j

/-- Forget the extra depth-side field of the actual selected-segment bridge
semantics and keep only the portrait enumeration data on the canonical
aperiodic skeleton. -/
noncomputable def canonical_aperiodic_selected_portrait_enumeration_semantics_of_depth_bookkeeping_bridge
    {n t U : ℕ}
    (hbridge : canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics n t U) :
    canonical_aperiodic_selected_portrait_enumeration_semantics n t U := by
  intro haper j
  exact (hbridge haper j).portrait

/-- Forget the portrait component of the actual selected-segment bridge
semantics and keep exactly the depth-from-bonus inequality on the canonical
aperiodic skeleton. -/
theorem canonical_aperiodic_selected_depth_from_bonus_semantics_of_depth_bookkeeping_bridge
    {n t U : ℕ}
    (hbridge : canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics n t U) :
    canonical_aperiodic_selected_depth_from_bonus_semantics n t U
      (canonical_aperiodic_selected_portrait_enumeration_semantics_of_depth_bookkeeping_bridge hbridge) := by
  intro haper j
  exact (hbridge haper j).depthFromBonus

/-- Actual-skeleton carry-depth source from the lower selected-segment bridge
semantics: once the portrait bonus and depth-from-bonus bridge are given on each
concrete selected pair of the canonical aperiodic skeleton, the D.1/E.1
carry-depth bound follows automatically. -/
theorem canonical_aperiodic_selected_carry_depth_semantics_of_depth_bookkeeping_bridge_semantics
    {n t U : ℕ}
    (hbridge :
      canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics n t U) :
    canonical_aperiodic_selected_carry_depth_semantics n t U := by
  intro haper j
  exact Epochs.selected_carry_depth_semantics_of_portrait_bridge (hbridge haper j)

/-- Hence the canonical carry-side residual target already determines the
selected-pair D.1/E.1 carry-depth theorem source on the actual aperiodic
skeleton. -/
theorem canonical_aperiodic_selected_carry_depth_semantics_of_canonical_depth_from_bonus
    {n t U : ℕ}
    (hbonus : canonical_aperiodic_selected_depth_from_bonus_semantics_canonical n t U) :
    canonical_aperiodic_selected_carry_depth_semantics n t U := by
  exact canonical_aperiodic_selected_carry_depth_semantics_of_depth_bookkeeping_bridge_semantics
    (canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_canonical_depth_from_bonus
      hbonus)

/-- The still lower selected-segment portrait/depth-from-bonus semantics on the
canonical aperiodic skeleton already determine the whole depth-bookkeeping
bridge layer. -/
noncomputable def canonical_aperiodic_selected_long_epoch_bridge_on_of_portrait_and_depth_from_bonus
    {n t U : ℕ}
    (hn : Odd n)
    (hportrait : canonical_aperiodic_selected_portrait_enumeration_semantics n t U)
    (hbonus : canonical_aperiodic_selected_depth_from_bonus_semantics n t U hportrait) :
    canonical_aperiodic_selected_long_epoch_bridge_on n t U := by
  exact canonical_aperiodic_selected_long_epoch_bridge_on_of_depth_semantics hn
    (canonical_aperiodic_selected_carry_depth_semantics_of_depth_bookkeeping_bridge_semantics
      (canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_portrait_and_depth_from_bonus
        hportrait hbonus))

/-- Direct carry-side closure from the canonical residual target: once the
canonical depth-from-bonus theorem is proved on the actual aperiodic skeleton,
the selected-long-epoch bridge follows automatically. -/
noncomputable def canonical_aperiodic_selected_long_epoch_bridge_on_of_canonical_depth_from_bonus
    {n t U : ℕ}
    (hn : Odd n)
    (hbonus : canonical_aperiodic_selected_depth_from_bonus_semantics_canonical n t U) :
    canonical_aperiodic_selected_long_epoch_bridge_on n t U := by
  exact canonical_aperiodic_selected_long_epoch_bridge_on_of_depth_semantics hn
    (canonical_aperiodic_selected_carry_depth_semantics_of_canonical_depth_from_bonus hbonus)

/-- Actual selected-pair paper arguments on the canonical aperiodic skeleton
already determine the lower portrait enumeration semantics. -/
noncomputable def canonical_aperiodic_selected_portrait_enumeration_semantics_of_carry_paper
    {n t U : ℕ}
    (hcarry :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        ∀ j : ℕ,
          Epochs.SelectedPaperCarryArguments n t U
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j)
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j)) :
    canonical_aperiodic_selected_portrait_enumeration_semantics n t U := by
  intro haper j
  refine
    { touchWitness := (hcarry haper j).touchWitness
      cappedBonus := (hcarry haper j).cappedBonus
      cappedBonusUpper := (hcarry haper j).cappedBonusUpper }

/-- Actual selected-pair paper arguments on the canonical aperiodic skeleton
already determine the lower depth-from-bonus inequality for the induced
portrait semantics. -/
theorem canonical_aperiodic_selected_depth_from_bonus_semantics_of_carry_paper
    {n t U : ℕ}
    (hcarry :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        ∀ j : ℕ,
          Epochs.SelectedPaperCarryArguments n t U
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j)
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j)) :
    canonical_aperiodic_selected_depth_from_bonus_semantics n t U
      (canonical_aperiodic_selected_portrait_enumeration_semantics_of_carry_paper hcarry) := by
  intro haper j
  exact (hcarry haper j).depthFromPortraitCarry

/-- Since phase geometry already fixes the portrait layer canonically on the
actual aperiodic skeleton, paper-faithful selected-pair carry arguments directly
imply the canonical depth-from-bonus residual by enlarging the local bonus to
the canonical budget. -/
theorem canonical_aperiodic_selected_depth_from_bonus_semantics_canonical_of_carry_paper
    {n t U : ℕ}
    (hcarry :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        ∀ j : ℕ,
          Epochs.SelectedPaperCarryArguments n t U
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j)
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j)) :
    canonical_aperiodic_selected_depth_from_bonus_semantics_canonical n t U := by
  intro haper j
  let hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper
  dsimp [canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry,
    Epochs.selected_multibit_gain_budget]
  simpa using
    (Epochs.selected_depth_from_bonus_bound_canonical_of_paper_arguments (hcarry haper j))

/-- Paper-faithful selected-pair carry arguments on the canonical aperiodic
skeleton already supply the minimal budget-level carry source after phase
geometry has fixed the portrait layer. -/
theorem canonical_aperiodic_selected_depth_from_bonus_budget_source_of_carry_paper
    {n t U : ℕ}
    (hcarry :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        ∀ j : ℕ,
          Epochs.SelectedPaperCarryArguments n t U
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j)
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j)) :
    canonical_aperiodic_selected_depth_from_bonus_budget_source n t U := by
  intro haper j
  simpa using
    (Epochs.selected_depth_from_bonus_bound_canonical_of_paper_arguments (hcarry haper j))

/-- Actual selected-pair paper arguments on the canonical aperiodic skeleton
therefore determine the whole lower portrait/depth bridge semantics. -/
noncomputable def canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_carry_paper
    {n t U : ℕ}
    (hcarry :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        ∀ j : ℕ,
          Epochs.SelectedPaperCarryArguments n t U
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j)
            ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j)) :
    canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics n t U := by
  exact canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_portrait_and_depth_from_bonus
    (canonical_aperiodic_selected_portrait_enumeration_semantics_of_carry_paper hcarry)
    (canonical_aperiodic_selected_depth_from_bonus_semantics_of_carry_paper hcarry)

/-- The repaired actual aperiodic semantic package already determines the lower
portrait enumeration semantics on the canonical aperiodic skeleton. -/
noncomputable def canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_return_semantics
    {n t U : ℕ} {β : ℝ}
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnSemantics n t U β _ha) :
    canonical_aperiodic_selected_portrait_enumeration_semantics n t U := by
  exact canonical_aperiodic_selected_portrait_enumeration_semantics_of_carry_paper
    (fun haper => (hsem haper).carryPaper)

/-- The repaired actual aperiodic semantic package already determines the lower
depth-from-bonus semantics on the canonical aperiodic skeleton. -/
theorem canonical_aperiodic_selected_depth_from_bonus_semantics_of_phase_return_semantics
    {n t U : ℕ} {β : ℝ}
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnSemantics n t U β _ha) :
    canonical_aperiodic_selected_depth_from_bonus_semantics n t U
      (canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_return_semantics hsem) := by
  exact canonical_aperiodic_selected_depth_from_bonus_semantics_of_carry_paper
    (fun haper => (hsem haper).carryPaper)

/-- Hence the repaired actual aperiodic semantic package already supplies the
minimal budget-level carry source on the concrete canonical selected pairs. -/
theorem canonical_aperiodic_selected_depth_from_bonus_budget_source_of_phase_return_semantics
    {n t U : ℕ} {β : ℝ}
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnSemantics n t U β _ha) :
    canonical_aperiodic_selected_depth_from_bonus_budget_source n t U := by
  exact canonical_aperiodic_selected_depth_from_bonus_budget_source_of_carry_paper
    (fun haper => (hsem haper).carryPaper)

/-- The repaired actual aperiodic semantic package therefore proves the
canonical carry-side residual directly, without passing through any stronger
selected-segment packaging than the concrete carry arguments it already carries. -/
theorem canonical_aperiodic_selected_depth_from_bonus_semantics_canonical_of_phase_return_semantics
    {n t U : ℕ} {β : ℝ}
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnSemantics n t U β _ha) :
    canonical_aperiodic_selected_depth_from_bonus_semantics_canonical n t U := by
  exact canonical_aperiodic_selected_depth_from_bonus_semantics_canonical_of_budget_source
    (canonical_aperiodic_selected_depth_from_bonus_budget_source_of_phase_return_semantics hsem)

/-- Hence the repaired actual aperiodic semantic package already determines the
entire lower selected-segment depth-bookkeeping bridge semantics. -/
noncomputable def canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_phase_return_semantics
    {n t U : ℕ} {β : ℝ}
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnSemantics n t U β _ha) :
    canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics n t U := by
  exact canonical_aperiodic_selected_depth_bookkeeping_bridge_semantics_of_portrait_and_depth_from_bonus
    (canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_return_semantics hsem)
    (canonical_aperiodic_selected_depth_from_bonus_semantics_of_phase_return_semantics hsem)

/-- Actual-skeleton carry-depth source from a genuine selected long-epoch bridge
on the canonical aperiodic skeleton. This moves the residual content below
`carryPaper` to the honest selected-epoch witness level. -/
theorem canonical_aperiodic_selected_carry_depth_semantics_of_selected_long_epoch_bridge_on
    {n t U : ℕ}
    (hbridge : canonical_aperiodic_selected_long_epoch_bridge_on n t U) :
    canonical_aperiodic_selected_carry_depth_semantics n t U := by
  intro haper j
  exact selected_carry_depth_semantics_of_selected_long_epoch_witness
    (hbridge haper j)

/-- Therefore the honest selected-long-epoch witness source on the actual
aperiodic skeleton already proves the canonical carry-side residual target: once
phase geometry fixes the portrait semantics, only the selected-pair depth
bookkeeping remains. -/
theorem canonical_aperiodic_selected_depth_from_bonus_semantics_canonical_of_selected_long_epoch_bridge_on
    {n t U : ℕ}
    (hbridge : canonical_aperiodic_selected_long_epoch_bridge_on n t U) :
    canonical_aperiodic_selected_depth_from_bonus_semantics_canonical n t U := by
  exact canonical_aperiodic_selected_depth_from_bonus_semantics_of_depth_semantics
    (canonical_aperiodic_selected_carry_depth_semantics_of_selected_long_epoch_bridge_on hbridge)

/-- Even before repackaging to the canonical dependent target, the honest
selected-long-epoch bridge on the actual aperiodic skeleton already supplies the
minimal budget-level carry source on each canonical selected pair. -/
theorem canonical_aperiodic_selected_depth_from_bonus_budget_source_of_selected_long_epoch_bridge_on
    {n t U : ℕ}
    (hbridge : canonical_aperiodic_selected_long_epoch_bridge_on n t U) :
    canonical_aperiodic_selected_depth_from_bonus_budget_source n t U := by
  intro haper j
  exact Epochs.selected_depth_from_bonus_bound_canonical_of_depth_semantics
    (selected_carry_depth_semantics_of_selected_long_epoch_witness (hbridge haper j))

/-- Actual-skeleton accounting theorem source: on the concrete canonical
aperiodic skeleton, each selected phase-return pair carries exactly the local
logarithmic and depth-side E.1/E.2 bounds used to assemble the native
`SEDT.potential_change` drift estimate. -/
def canonical_aperiodic_phase_return_epoch_accounting_witness
    (n t U : ℕ) (β : ℝ) : Prop :=
  t ≥ 3 →
    U ≥ 1 →
      β > Collatz.SEDT.β₀ t U →
        ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
          ∀ j : ℕ,
            Collatz.SEDT.local_log_drift_bound
              ((Collatz.Foundations.collatz_step^[
                (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j]) n)
              ((Collatz.Foundations.collatz_step^[
                (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j]) n)
              ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j -
                (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j) ∧
            Collatz.SEDT.local_depth_drift_bound t U β
              ((Collatz.Foundations.collatz_step^[
                (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j]) n)
              ((Collatz.Foundations.collatz_step^[
                (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j]) n)
              ((aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).rightIdx j -
                (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha).leftIdx j)

/-- The actual-skeleton selected-long-epoch bridge already contains exactly the
local accounting data needed on each canonical selected phase-return pair. -/
theorem canonical_aperiodic_phase_return_epoch_accounting_witness_of_selected_long_epoch_bridge_on
    {n t U : ℕ} {β : ℝ}
    (hbridge : canonical_aperiodic_selected_long_epoch_bridge_on n t U) :
    canonical_aperiodic_phase_return_epoch_accounting_witness n t U β := by
  intro ht hU hβ haper j
  let hw := hbridge haper j
  have hβpos : 0 < β := by
    have hβ0pos : 0 < Collatz.SEDT.β₀ t U := by
      exact Collatz.SEDT.beta_zero_pos t U
        (Collatz.SEDT.alpha_lt_two_of_ht_hU t U ht hU)
    linarith
  have hβnonneg : 0 ≤ β := le_of_lt hβpos
  refine ⟨?_, ?_⟩
  · exact Collatz.SEDT.local_log_drift_bound_of_selected_long_epoch hw
  · exact Collatz.SEDT.local_depth_drift_bound_of_selected_long_epoch hβnonneg hw

/-- Actual-skeleton pair-step theorem source from localized accounting and the
already separated correction theorem. This is the honest lower coercivity input
just above selected-segment semantics on the concrete aperiodic skeleton. -/
theorem canonical_aperiodic_phase_return_pair_step_sedt_on_of_accounting_witness_and_correction
    {n t U : ℕ} {β : ℝ}
    (hacc : canonical_aperiodic_phase_return_epoch_accounting_witness n t U β)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      phase_return_pair_step_sedt_on n t U β
        (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha) := by
  intro haper hparams j
  rcases hparams with ⟨ht, hU, hβ, _hdom⟩
  let hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper
  rcases hacc ht hU hβ haper j with ⟨hlog, hdepth⟩
  have hsegBound :
      Collatz.SEDT.potential_change
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) n)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) n)
        β ≤
          Collatz.SEDT.sedt_envelope t U β (hphase.rightIdx j - hphase.leftIdx j) := by
    exact Collatz.SEDT.potential_change_le_sedt_envelope_of_local_bounds hlog hdepth
  have hcorrBound :
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) n)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) n) ≤ 0 :=
    hcorr haper j
  have hbridge :
      potential β ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) n) -
        potential β ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) n) =
      Collatz.SEDT.potential_change
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) n)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) n)
        β +
      potential_change_correction
        ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) n)
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) n) := by
    exact potential_sub_eq_sedt_potential_change_plus_correction β
      ((Collatz.Foundations.collatz_step^[hphase.leftIdx j]) n)
      ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) n)
  rw [hbridge]
  linarith

/-- Actual-skeleton pair-step theorem source directly from the selected
long-epoch bridge and correction theorem. -/
theorem canonical_aperiodic_phase_return_pair_step_sedt_on_of_selected_long_epoch_bridge_on_and_correction
    {n t U : ℕ} {β : ℝ}
    (hbridge : canonical_aperiodic_selected_long_epoch_bridge_on n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      phase_return_pair_step_sedt_on n t U β
        (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha) := by
  exact
    canonical_aperiodic_phase_return_pair_step_sedt_on_of_accounting_witness_and_correction
      (canonical_aperiodic_phase_return_epoch_accounting_witness_of_selected_long_epoch_bridge_on
        hbridge)
      hcorr

/-- If one already has the repaired actual-skeleton semantic package, its
selected-pair paper data immediately refines to the actual-skeleton
`SelectedLongEpochBridgeOn`. This makes the residual carry/epoch target explicit
without passing through the higher witness layer. -/
noncomputable def canonical_aperiodic_selected_long_epoch_bridge_on_of_phase_return_semantics
    {n t U : ℕ} {β : ℝ}
    (hn : Odd n)
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnSemantics n t U β _ha) :
    canonical_aperiodic_selected_long_epoch_bridge_on n t U := by
  exact canonical_aperiodic_selected_long_epoch_bridge_on_of_carry_paper hn
    (fun haper => (hsem haper).carryPaper)

/-- The repaired actual-skeleton semantic package also carries the witness-level
filler endpoint-order theorem on the concrete canonical aperiodic skeleton. -/
def canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_phase_return_semantics
    {n t U : ℕ} {β : ℝ}
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnSemantics n t U β _ha) :
    canonical_aperiodic_phase_return_fill_endpoint_nonincrease n t U := by
  intro haper
  exact (hsem haper).fillEndpointNonincrease

/-- Once the repaired actual aperiodic semantic package supplies the witness-level
filler endpoint order, any separate proof of pair endpoint order upgrades
immediately to stream endpoint monotonicity on the induced canonical long-gap
stream. -/
theorem canonical_aperiodic_orbit_epoch_endpoint_nonincrease_of_phase_return_semantics_and_endpoint
    {n t U : ℕ} {β : ℝ}
    (hpair :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        phase_return_endpoint_nonincrease_on n t U
          (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha))
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnSemantics n t U β _ha) :
    canonical_aperiodic_orbit_epoch_endpoint_nonincrease n t U := by
  exact canonical_aperiodic_orbit_epoch_endpoint_nonincrease_of_phase_return_endpoint_and_fill
    hpair
    (canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_phase_return_semantics hsem)

/-- Actual-skeleton canonical-gap theorem from the orbitwise `E.2` envelope on
the induced canonical long-gap stream. This is the honest stream-level source
behind `canonical_aperiodic_phase_return_gap_step_sedt_on`. -/
theorem canonical_aperiodic_phase_return_gap_step_sedt_on_of_orbit_epoch_sedt_envelope
    {n t U : ℕ} {β : ℝ}
    (henv : canonical_aperiodic_orbit_epoch_sedt_envelope n t U β) :
    canonical_aperiodic_phase_return_gap_step_sedt_on n t U β := by
  intro haper
  exact canonical_phase_return_gap_step_sedt_on_of_orbit_epoch_sedt_envelope
    (henv haper)

/-- Actual-skeleton stream-level `E.2` envelope from the already exposed local
canonical-gap theorem on the same concrete canonical aperiodic skeleton. This
is the direct theorem-producing path from the repaired local target to the
induced long-gap stream semantics. -/
theorem canonical_aperiodic_orbit_epoch_sedt_envelope_of_canonical_gap_step
    {n t U : ℕ} {β : ℝ}
    (hgap : canonical_aperiodic_phase_return_gap_step_sedt_on n t U β)
    (hparams : sedt_dominant_parameters t U β) :
    canonical_aperiodic_orbit_epoch_sedt_envelope n t U β := by
  intro haper
  exact orbit_epoch_sedt_envelope_of_gap_step_sedt_on (hgap haper) hparams

/-- The actual stream-local accounting semantics immediately yield the native
`SEDT.potential_change` estimate on each epoch of the induced canonical long-gap
stream. -/
theorem canonical_aperiodic_orbit_epoch_native_sedt_semantics_of_local_accounting
    {n t U : ℕ} {β : ℝ}
    (hacc : canonical_aperiodic_orbit_epoch_local_accounting_semantics n t U β) :
    canonical_aperiodic_orbit_epoch_native_sedt_semantics n t U β := by
  intro haper
  let s := canonical_aperiodic_orbit_long_epoch_stream n t U haper
  intro j
  rcases hacc haper j with ⟨hlog, hdepth⟩
  exact Collatz.SEDT.potential_change_le_sedt_envelope_of_local_bounds hlog hdepth

/-- Stream endpoint monotonicity on the induced canonical long-gap stream forces
the stream normalization correction to be nonpositive on every actual stream
epoch. -/
theorem canonical_aperiodic_orbit_epoch_correction_nonpositive_of_endpoint_nonincrease
    {n t U : ℕ}
    (hn : Odd n)
    (hmono : canonical_aperiodic_orbit_epoch_endpoint_nonincrease n t U) :
    canonical_aperiodic_orbit_epoch_correction_nonpositive n t U := by
  intro haper j
  let s := canonical_aperiodic_orbit_long_epoch_stream n t U haper
  have hstartOdd : Odd (s.orbitVal j) := by
    simpa [canonical_aperiodic_orbit_long_epoch_stream, Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps,
      Epochs.orbit_long_epoch_stream_of_supply, Epochs.orbit_long_epoch_supply_of_cofinal_long_epoch_gaps]
      using Collatz.Foundations.odd_iterates_of_odd hn (s.idx j)
  have hendOdd : Odd (s.orbitVal (j + 1)) := by
    simpa [canonical_aperiodic_orbit_long_epoch_stream, Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps,
      Epochs.orbit_long_epoch_stream_of_supply, Epochs.orbit_long_epoch_supply_of_cofinal_long_epoch_gaps]
      using Collatz.Foundations.odd_iterates_of_odd hn (s.idx (j + 1))
  have hstartPos : 0 < s.orbitVal j := by
    obtain ⟨k, hk⟩ := hstartOdd
    omega
  have hendPos : 0 < s.orbitVal (j + 1) := by
    obtain ⟨k, hk⟩ := hendOdd
    omega
  exact potential_change_correction_nonpositive_of_end_le_start
    hstartPos hendPos (hmono haper j)

/-- Native stream-level `SEDT` semantics, together with nonpositive stream-step
normalization correction, immediately produce the actual-skeleton orbitwise
`E.2` envelope on the induced canonical long-gap stream. -/
theorem canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_semantics_and_correction
    {n t U : ℕ} {β : ℝ}
    (hnative : canonical_aperiodic_orbit_epoch_native_sedt_semantics n t U β)
    (hcorr : canonical_aperiodic_orbit_epoch_correction_nonpositive n t U) :
    canonical_aperiodic_orbit_epoch_sedt_envelope n t U β := by
  intro haper
  let s := canonical_aperiodic_orbit_long_epoch_stream n t U haper
  intro j
  have hnativej :
      Collatz.SEDT.potential_change (s.orbitVal j) (s.orbitVal (j + 1)) β ≤
        Collatz.SEDT.sedt_envelope t U β (s.epochLen j) := hnative haper j
  have hcorrj :
      potential_change_correction (s.orbitVal j) (s.orbitVal (j + 1)) ≤ 0 := hcorr haper j
  have hbridge :
      potential β (s.orbitVal (j + 1)) - potential β (s.orbitVal j) =
        Collatz.SEDT.potential_change (s.orbitVal j) (s.orbitVal (j + 1)) β +
          potential_change_correction (s.orbitVal j) (s.orbitVal (j + 1)) := by
    exact potential_sub_eq_sedt_potential_change_plus_correction β
      (s.orbitVal j) (s.orbitVal (j + 1))
  rw [hbridge]
  linarith

/-- The actual stream-local accounting semantics become a full stream-level
orbitwise `E.2` envelope as soon as the normalization correction is also
controlled on each canonical long-gap stream epoch. -/
theorem canonical_aperiodic_orbit_epoch_sedt_envelope_of_local_accounting_and_correction
    {n t U : ℕ} {β : ℝ}
    (hacc : canonical_aperiodic_orbit_epoch_local_accounting_semantics n t U β)
    (hcorr : canonical_aperiodic_orbit_epoch_correction_nonpositive n t U) :
    canonical_aperiodic_orbit_epoch_sedt_envelope n t U β := by
  exact canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_semantics_and_correction
    (canonical_aperiodic_orbit_epoch_native_sedt_semantics_of_local_accounting hacc)
    hcorr

/-- Even lower stream-level closure: local accounting plus endpoint nonincrease
already suffice for the full orbitwise `E.2` envelope on the induced canonical
long-gap stream. -/
theorem canonical_aperiodic_orbit_epoch_sedt_envelope_of_local_accounting_and_endpoint_nonincrease
    {n t U : ℕ} {β : ℝ}
    (hn : Odd n)
    (hacc : canonical_aperiodic_orbit_epoch_local_accounting_semantics n t U β)
    (hmono : canonical_aperiodic_orbit_epoch_endpoint_nonincrease n t U) :
    canonical_aperiodic_orbit_epoch_sedt_envelope n t U β := by
  exact canonical_aperiodic_orbit_epoch_sedt_envelope_of_local_accounting_and_correction
    hacc
    (canonical_aperiodic_orbit_epoch_correction_nonpositive_of_endpoint_nonincrease hn hmono)

/-- Alternative lowest stream-level closure: native `SEDT.potential_change`
semantics plus endpoint nonincrease already imply the full orbitwise `E.2`
envelope on the induced canonical long-gap stream. -/
theorem canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_semantics_and_endpoint_nonincrease
    {n t U : ℕ} {β : ℝ}
    (hn : Odd n)
    (hnative : canonical_aperiodic_orbit_epoch_native_sedt_semantics n t U β)
    (hmono : canonical_aperiodic_orbit_epoch_endpoint_nonincrease n t U) :
    canonical_aperiodic_orbit_epoch_sedt_envelope n t U β := by
  exact canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_semantics_and_correction
    hnative
    (canonical_aperiodic_orbit_epoch_correction_nonpositive_of_endpoint_nonincrease hn hmono)

/-- Minimal stream-side package after the witness-level endpoint repair: native
`SEDT.potential_change` semantics on canonical long-gap epochs together with
stream endpoint monotonicity. This is the weakest currently exposed stream
package that closes directly to the orbitwise `E.2` envelope. -/
def canonical_aperiodic_orbit_epoch_native_endpoint_package
    (n t U : ℕ) (β : ℝ) : Prop :=
  canonical_aperiodic_orbit_epoch_native_sedt_semantics n t U β ∧
    canonical_aperiodic_orbit_epoch_endpoint_nonincrease n t U

/-- The minimal native+endpoint stream package closes directly to the actual
orbitwise `E.2` envelope. -/
theorem canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_endpoint_package
    {n t U : ℕ} {β : ℝ}
    (hn : Odd n)
    (hpack : canonical_aperiodic_orbit_epoch_native_endpoint_package n t U β) :
    canonical_aperiodic_orbit_epoch_sedt_envelope n t U β := by
  exact canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_semantics_and_endpoint_nonincrease
    hn hpack.1 hpack.2

/-- Combining the repaired phase-return semantics with a separate pair-endpoint
theorem yields the stream endpoint half of the minimal native+endpoint package. -/
theorem canonical_aperiodic_orbit_epoch_native_endpoint_package_of_native_semantics_and_phase_return_semantics
    {n t U : ℕ} {β : ℝ}
    (hpair :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        phase_return_endpoint_nonincrease_on n t U
          (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha))
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnSemantics n t U β _ha)
    (hnative : canonical_aperiodic_orbit_epoch_native_sedt_semantics n t U β) :
    canonical_aperiodic_orbit_epoch_native_endpoint_package n t U β := by
  refine ⟨hnative, ?_⟩
  exact canonical_aperiodic_orbit_epoch_endpoint_nonincrease_of_phase_return_semantics_and_endpoint
    hpair hsem

/-- The minimal native+endpoint stream package can also be produced from a
pair-endpoint theorem together with the stronger value-level filler monotonicity
source on the canonical aperiodic skeleton. -/
theorem canonical_aperiodic_orbit_epoch_native_endpoint_package_of_native_semantics_and_fill_stepwise
    {n t U : ℕ} {β : ℝ}
    (hpair :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        phase_return_endpoint_nonincrease_on n t U
          (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha))
    (hfillStep :
      canonical_aperiodic_phase_return_fill_stepwise_nonincrease n t U)
    (hnative : canonical_aperiodic_orbit_epoch_native_sedt_semantics n t U β) :
    canonical_aperiodic_orbit_epoch_native_endpoint_package n t U β := by
  refine ⟨hnative, ?_⟩
  exact canonical_aperiodic_orbit_epoch_endpoint_nonincrease_of_phase_return_endpoint_and_fill
    hpair
    (canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_stepwise_nonincrease
      n t U hfillStep)

/-- The stepwise-aware actual-skeleton semantic package projects directly to the
global canonical filler-stepwise target. This isolates the remaining stream-side
closure problem as a theorem-producing source on the concrete canonical
aperiodic skeleton. -/
def canonical_aperiodic_phase_return_fill_stepwise_nonincrease_of_phase_return_stepwise_semantics
    {n t U : ℕ} {β : ℝ}
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnStepwiseSemantics n t U β _ha) :
    canonical_aperiodic_phase_return_fill_stepwise_nonincrease n t U := by
  intro haper
  exact (hsem haper).fillStepwiseNonincrease

/-- The stepwise-aware actual-skeleton semantic package also yields the weaker
endpoint-order filler theorem consumed by the existing downstream chain. -/
def canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_phase_return_stepwise_semantics
    {n t U : ℕ} {β : ℝ}
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnStepwiseSemantics n t U β _ha) :
    canonical_aperiodic_phase_return_fill_endpoint_nonincrease n t U :=
  canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_stepwise_nonincrease
    n t U
    (canonical_aperiodic_phase_return_fill_stepwise_nonincrease_of_phase_return_stepwise_semantics
      hsem)

/-- Forget the candidate-exclusion filler field and recover the exclusion-style
semantic package where filler content is expressed directly as `no simple
step`. -/
def CanonicalAperiodicPhaseReturnCandidateSelectionSemantics.toCandidateExclusionSemantics
    {n t U : ℕ} {β : ℝ}
    {haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n}
    (hsem : CanonicalAperiodicPhaseReturnCandidateSelectionSemantics n t U β haper) :
    CanonicalAperiodicPhaseReturnCandidateExclusionSemantics n t U β haper :=
  { carryPaper := hsem.carryPaper
    correctionNonpositive := hsem.correctionNonpositive
    fillCandidateExclusion :=
      Epochs.gap_long_phase_returns_filler_candidate_exclusion_of_selection_semantics_on
        hsem.fillCandidateSelection
    canonicalGapStep := hsem.canonicalGapStep }

/-- Forget the candidate-exclusion filler field and recover the exclusion-style
semantic package where filler content is expressed directly as `no simple
step`. -/
def CanonicalAperiodicPhaseReturnCandidateExclusionSemantics.toNoSimpleStepSemantics
    {n t U : ℕ} {β : ℝ}
    {haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n}
    (hsem : CanonicalAperiodicPhaseReturnCandidateExclusionSemantics n t U β haper) :
    CanonicalAperiodicPhaseReturnNoSimpleStepSemantics n t U β haper :=
  { carryPaper := hsem.carryPaper
    correctionNonpositive := hsem.correctionNonpositive
    fillNoSimpleStep :=
      Epochs.gap_long_phase_returns_filler_no_simple_step_of_candidate_exclusion_on
        hsem.fillCandidateExclusion
    canonicalGapStep := hsem.canonicalGapStep }

/-- Forget the exclusion-style filler field and recover the narrower arithmetic
package where filler content is expressed as `step_type ≥ 2` on each actual
canonical filler index. -/
def CanonicalAperiodicPhaseReturnNoSimpleStepSemantics.toStepTypeTwoSemantics
    {n t U : ℕ} {β : ℝ}
    {haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n}
    (hsem : CanonicalAperiodicPhaseReturnNoSimpleStepSemantics n t U β haper)
    (hn : Odd n) :
    CanonicalAperiodicPhaseReturnStepTypeTwoSemantics n t U β haper :=
  { carryPaper := hsem.carryPaper
    correctionNonpositive := hsem.correctionNonpositive
    fillStepTypeTwo :=
      Epochs.gap_long_phase_returns_filler_step_type_two_of_complex_step_on hn
        (hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
        (Epochs.gap_long_phase_returns_filler_complex_step_of_no_simple_step_on hn
          (hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
          hsem.fillNoSimpleStep)
    canonicalGapStep := hsem.canonicalGapStep }

/-- Forget the more atomic `step_type ≥ 2` filler field and recover the
stepwise-aware semantic package on the same actual canonical aperiodic
skeleton. -/
def CanonicalAperiodicPhaseReturnStepTypeTwoSemantics.toStepwiseSemantics
    {n t U : ℕ} {β : ℝ}
    {haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n}
    (hsem : CanonicalAperiodicPhaseReturnStepTypeTwoSemantics n t U β haper)
    (hn : Odd n) :
    CanonicalAperiodicPhaseReturnStepwiseSemantics n t U β haper :=
  { carryPaper := hsem.carryPaper
    correctionNonpositive := hsem.correctionNonpositive
    fillStepwiseNonincrease :=
      Epochs.gap_long_phase_returns_filler_stepwise_of_step_type_two_on hn
        (hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
        hsem.fillStepTypeTwo
    canonicalGapStep := hsem.canonicalGapStep }

/-- Forget the stronger per-step filler monotonicity field and recover the
endpoint-order semantic package already consumed by the downstream coercivity
chain. -/
def CanonicalAperiodicPhaseReturnStepwiseSemantics.toPhaseReturnSemantics
    {n t U : ℕ} {β : ℝ}
    {haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n}
    (hsem : CanonicalAperiodicPhaseReturnStepwiseSemantics n t U β haper) :
    CanonicalAperiodicPhaseReturnSemantics n t U β haper :=
  { carryPaper := hsem.carryPaper
    correctionNonpositive := hsem.correctionNonpositive
    fillEndpointNonincrease :=
      phase_return_fill_endpoint_nonincrease_on_of_stepwise_nonincrease
        hsem.fillStepwiseNonincrease
    canonicalGapStep := hsem.canonicalGapStep }

/-- Forget the more atomic `step_type ≥ 2` filler field all the way down to the
ordinary repaired phase-return semantic package. -/
def CanonicalAperiodicPhaseReturnStepTypeTwoSemantics.toPhaseReturnSemantics
    {n t U : ℕ} {β : ℝ}
    {haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n}
    (hsem : CanonicalAperiodicPhaseReturnStepTypeTwoSemantics n t U β haper)
    (hn : Odd n) :
    CanonicalAperiodicPhaseReturnSemantics n t U β haper :=
  (hsem.toStepwiseSemantics hn).toPhaseReturnSemantics

/-- Forget the exclusion-style filler field all the way down to the ordinary
repaired phase-return semantic package. -/
def CanonicalAperiodicPhaseReturnNoSimpleStepSemantics.toPhaseReturnSemantics
    {n t U : ℕ} {β : ℝ}
    {haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n}
    (hsem : CanonicalAperiodicPhaseReturnNoSimpleStepSemantics n t U β haper)
    (hn : Odd n) :
    CanonicalAperiodicPhaseReturnSemantics n t U β haper :=
  (hsem.toStepTypeTwoSemantics hn).toPhaseReturnSemantics hn

def CanonicalAperiodicPhaseReturnCandidateExclusionSemantics.toPhaseReturnSemantics
    {n t U : ℕ} {β : ℝ}
    {haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n}
    (hsem : CanonicalAperiodicPhaseReturnCandidateExclusionSemantics n t U β haper)
    (hn : Odd n) :
    CanonicalAperiodicPhaseReturnSemantics n t U β haper :=
  (hsem.toNoSimpleStepSemantics).toPhaseReturnSemantics hn

/-- Forget the candidate-selection filler field all the way down to the
ordinary repaired phase-return semantic package. -/
def CanonicalAperiodicPhaseReturnCandidateSelectionSemantics.toPhaseReturnSemantics
    {n t U : ℕ} {β : ℝ}
    {haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n}
    (hsem : CanonicalAperiodicPhaseReturnCandidateSelectionSemantics n t U β haper)
    (hn : Odd n) :
    CanonicalAperiodicPhaseReturnSemantics n t U β haper :=
  (hsem.toCandidateExclusionSemantics).toPhaseReturnSemantics hn

/-- Specialize the older `phase_return_sedt_envelope_bridge` interface to the
actual canonical aperiodic skeleton. This produces the honest stream-level
actual-skeleton `E.2` target directly. -/
theorem canonical_aperiodic_orbit_epoch_sedt_envelope_of_phase_return_bridge
    {n t U : ℕ} {β : ℝ}
    (hbridge : phase_return_sedt_envelope_bridge n t U β)
    (hparams : sedt_dominant_parameters t U β) :
    canonical_aperiodic_orbit_epoch_sedt_envelope n t U β := by
  intro haper
  exact orbit_epoch_sedt_envelope_of_phase_returns hbridge hparams
    (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)

/-- Build the full repaired semantic package on the actual aperiodic skeleton
from the exact theorem sources that remain scientifically meaningful after the
endpoint/filler repair. -/
noncomputable def canonical_aperiodic_phase_return_semantics_of_theorem_sources
    {n t U : ℕ} {β : ℝ}
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hfillEndpoint : canonical_aperiodic_phase_return_fill_endpoint_nonincrease n t U)
    (hgap : canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      CanonicalAperiodicPhaseReturnSemantics n t U β _ha := by
  intro haper
  refine
    { carryPaper :=
        canonical_aperiodic_carry_paper_of_depth_semantics
          (haper := haper) (fun j => hdepth haper j)
      correctionNonpositive := hcorr haper
      fillEndpointNonincrease := hfillEndpoint haper
      canonicalGapStep := hgap haper }

/-- Build the stronger stepwise-aware semantic package on the actual aperiodic
skeleton from theorem sources. This is the direct entrypoint for the remaining
stream-side residual when the filler theorem is supplied at the raw per-step
value level. -/
noncomputable def canonical_aperiodic_phase_return_stepwise_semantics_of_theorem_sources
    {n t U : ℕ} {β : ℝ}
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hfillStep : canonical_aperiodic_phase_return_fill_stepwise_nonincrease n t U)
    (hgap : canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      CanonicalAperiodicPhaseReturnStepwiseSemantics n t U β _ha := by
  intro haper
  refine
    { carryPaper :=
        canonical_aperiodic_carry_paper_of_depth_semantics
          (haper := haper) (fun j => hdepth haper j)
      correctionNonpositive := hcorr haper
      fillStepwiseNonincrease := hfillStep haper
      canonicalGapStep := hgap haper }

/-- Build the stronger stepwise-aware semantic package on the actual aperiodic
skeleton from the more atomic arithmetic filler theorem source `step_type ≥ 2`
on every filler index. This is the narrowest currently exposed stream-side
entrypoint below the stepwise wrapper. -/
noncomputable def canonical_aperiodic_phase_return_stepwise_semantics_of_step_type_two_theorem_sources
    {n t U : ℕ} {β : ℝ}
    (hn : Odd n)
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hfillStepTwo : canonical_aperiodic_phase_return_fill_step_type_two_bridge n t U)
    (hgap : canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      CanonicalAperiodicPhaseReturnStepwiseSemantics n t U β _ha := by
  exact canonical_aperiodic_phase_return_stepwise_semantics_of_theorem_sources
    hdepth hcorr
    (canonical_aperiodic_phase_return_fill_stepwise_nonincrease_of_step_type_two_bridge
      hn hfillStepTwo)
    hgap

/-- Build the narrowest currently exposed actual-skeleton semantic package from
theorem sources: the filler input is only the arithmetic bridge `step_type ≥ 2`
on canonical filler indices. -/
noncomputable def canonical_aperiodic_phase_return_step_type_two_semantics_of_theorem_sources
    {n t U : ℕ} {β : ℝ}
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hfillStepTwo : canonical_aperiodic_phase_return_fill_step_type_two_bridge n t U)
    (hgap : canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      CanonicalAperiodicPhaseReturnStepTypeTwoSemantics n t U β _ha := by
  intro haper
  refine
    { carryPaper :=
        canonical_aperiodic_carry_paper_of_depth_semantics
          (haper := haper) (fun j => hdepth haper j)
      correctionNonpositive := hcorr haper
      fillStepTypeTwo := hfillStepTwo haper
      canonicalGapStep := hgap haper }

/-- Build the exclusion-style actual-skeleton semantic package from theorem
sources: the filler input only says that no simple step appears on the canonical
filler interval. -/
noncomputable def canonical_aperiodic_phase_return_candidate_selection_semantics_of_theorem_sources
    {n t U : ℕ} {β : ℝ}
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hfillSelection :
      canonical_aperiodic_phase_return_fill_candidate_selection_semantics n t U)
    (hgap : canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      CanonicalAperiodicPhaseReturnCandidateSelectionSemantics n t U β _ha := by
  intro haper
  refine
    { carryPaper :=
        canonical_aperiodic_carry_paper_of_depth_semantics
          (haper := haper) (fun j => hdepth haper j)
      correctionNonpositive := hcorr haper
      fillCandidateSelection := hfillSelection haper
      canonicalGapStep := hgap haper }

/-- Build the exclusion-style actual-skeleton semantic package from theorem
sources: the filler input is split into the two even lower concrete theorem
sources `phase-compatibility promotion` and `phase-compatibility minimality` on
the canonical filler interval. -/
noncomputable def canonical_aperiodic_phase_return_candidate_selection_semantics_of_canonical_next_left_phase_compatibility_and_minimality_theorem_sources
    {n t U : ℕ} {β : ℝ}
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hfillProm :
      canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_promotion_semantics n t U)
    (hfillMin :
      canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_semantics n t U)
    (hgap : canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      CanonicalAperiodicPhaseReturnCandidateSelectionSemantics n t U β _ha := by
  exact canonical_aperiodic_phase_return_candidate_selection_semantics_of_theorem_sources
    hdepth hcorr
    (canonical_aperiodic_phase_return_fill_candidate_selection_semantics_of_canonical_next_left_witness
      (canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_witness n t U)
      (canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_of_phase_compatible_promotion
        hfillProm)
      (canonical_aperiodic_phase_return_fill_canonical_next_left_witness_minimality_of_phase_compatible_minimality
        hfillMin))
    hgap

/-- Build the exclusion-style actual-skeleton semantic package from theorem
sources: the filler input is given by an explicit next-left admissibility
witness plus witness-relative promotion/minimality on the canonical filler
interval. This is the repaired concrete path after retiring the phase-only
promotion proxy. -/
noncomputable def canonical_aperiodic_phase_return_candidate_selection_semantics_of_canonical_next_left_witness_theorem_sources
    {n t U : ℕ} {β : ℝ}
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hnext :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_semantics n t U)
    (hfillProm :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_promotion_semantics
        n t U hnext)
    (hfillMin :
      canonical_aperiodic_phase_return_fill_canonical_next_left_witness_minimality_semantics
        n t U hnext)
    (hgap : canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      CanonicalAperiodicPhaseReturnCandidateSelectionSemantics n t U β _ha := by
  exact canonical_aperiodic_phase_return_candidate_selection_semantics_of_theorem_sources
    hdepth hcorr
    (canonical_aperiodic_phase_return_fill_candidate_selection_semantics_of_canonical_next_left_witness
      hnext hfillProm hfillMin)
    hgap

/-- Build the exclusion-style actual-skeleton semantic package from theorem
sources: the filler input is split into the two even lower theorem sources
`promotion` and `next-left minimality` on the canonical filler interval. -/
noncomputable def canonical_aperiodic_phase_return_candidate_selection_semantics_of_promotion_and_minimality_theorem_sources
    {n t U : ℕ} {β : ℝ}
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hfillProm :
      canonical_aperiodic_phase_return_fill_candidate_promotion_semantics n t U)
    (hfillMin :
      canonical_aperiodic_phase_return_fill_next_left_minimality_semantics n t U hfillProm)
    (hgap : canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      CanonicalAperiodicPhaseReturnCandidateSelectionSemantics n t U β _ha := by
  exact canonical_aperiodic_phase_return_candidate_selection_semantics_of_theorem_sources
    hdepth hcorr
    (canonical_aperiodic_phase_return_fill_candidate_selection_semantics_of_promotion_and_minimality
      hfillProm hfillMin)
    hgap

/-- Build the exclusion-style actual-skeleton semantic package from theorem
sources: the filler input only says that no simple step appears on the canonical
filler interval. -/
noncomputable def canonical_aperiodic_phase_return_no_simple_step_semantics_of_theorem_sources
    {n t U : ℕ} {β : ℝ}
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hfillNoSimple : canonical_aperiodic_phase_return_fill_no_simple_step_bridge n t U)
    (hgap : canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      CanonicalAperiodicPhaseReturnNoSimpleStepSemantics n t U β _ha := by
  intro haper
  refine
    { carryPaper :=
        canonical_aperiodic_carry_paper_of_depth_semantics
          (haper := haper) (fun j => hdepth haper j)
      correctionNonpositive := hcorr haper
      fillNoSimpleStep := hfillNoSimple haper
      canonicalGapStep := hgap haper }

/-- Build the lowest currently exposed actual-skeleton semantic package from
theorem sources: the filler input only excludes simple-step candidates on the
canonical filler interval. -/
noncomputable def canonical_aperiodic_phase_return_candidate_exclusion_semantics_of_theorem_sources
    {n t U : ℕ} {β : ℝ}
    (hdepth : canonical_aperiodic_selected_carry_depth_semantics n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hfillCandidate :
      canonical_aperiodic_phase_return_fill_candidate_exclusion_bridge n t U)
    (hgap : canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
      CanonicalAperiodicPhaseReturnCandidateExclusionSemantics n t U β _ha := by
  intro haper
  refine
    { carryPaper :=
        canonical_aperiodic_carry_paper_of_depth_semantics
          (haper := haper) (fun j => hdepth haper j)
      correctionNonpositive := hcorr haper
      fillCandidateExclusion := hfillCandidate haper
      canonicalGapStep := hgap haper }

/-- Build the repaired canonical aperiodic witness from honest semantics on the
actual aperiodic phase-return skeleton. This is the point where the weak
`choose`-based skeleton is upgraded to a semantic object carrying the content
needed by the local E.2 closure. -/
noncomputable def canonical_aperiodic_phase_return_witness_of_semantics
    {n t U : ℕ} {β : ℝ}
    {haper : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n}
    (hsem : CanonicalAperiodicPhaseReturnSemantics n t U β haper) :
    CanonicalAperiodicPhaseReturnWitness n t U β := by
  let hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper
  refine
    { leftIdx := hphase.leftIdx
      rightIdx := hphase.rightIdx
      leftStep := hphase.leftStep
      rightStep := hphase.rightStep
      longSep := hphase.longSep
      selectedPhaseAligned := hphase.selectedPhaseAligned
      cofinalLeft := hphase.cofinalLeft
      carryPaper := hsem.carryPaper
      correctionNonpositive := hsem.correctionNonpositive
      fillEndpointNonincrease := hsem.fillEndpointNonincrease
      canonicalGapStep := hsem.canonicalGapStep }

/-- The honest canonical witness already contains the exact selected-segment
paper arguments needed to refine its concrete phase-return skeleton to local
selected long epochs. -/
noncomputable def CanonicalAperiodicPhaseReturnWitness.selectedLongEpochBridgeOn
    {n t U : ℕ} {β : ℝ}
    (hw : CanonicalAperiodicPhaseReturnWitness n t U β)
    (hn : Odd n) :
    Epochs.SelectedLongEpochBridgeOn hw.toPhaseReturns := by
  exact Epochs.selected_long_epoch_bridge_on_of_semantics hn
    (hphase := hw.toPhaseReturns) hw.carryPaper

/-- Witness-indexed correction theorem extracted from the honest canonical
aperiodic witness. -/
theorem CanonicalAperiodicPhaseReturnWitness.correction_nonpositive_on
    {n t U : ℕ} {β : ℝ}
    (hw : CanonicalAperiodicPhaseReturnWitness n t U β) :
    phase_return_potential_correction_nonpositive_on n t U hw.toPhaseReturns :=
  hw.correctionNonpositive

/-- Witness-indexed filler endpoint-order theorem extracted from the honest
canonical aperiodic witness. -/
theorem CanonicalAperiodicPhaseReturnWitness.fill_endpoint_nonincrease_on
    {n t U : ℕ} {β : ℝ}
    (hw : CanonicalAperiodicPhaseReturnWitness n t U β) :
    phase_return_fill_endpoint_nonincrease_on n t U hw.toPhaseReturns :=
  hw.fillEndpointNonincrease

/-- A family of honest canonical aperiodic witnesses already supplies the
canonical filler endpoint-order wrapper by simple field projection. This makes
the remaining stream-side residual explicit at the witness level, without
requiring the stronger semantic package. -/
def canonical_aperiodic_phase_return_fill_endpoint_nonincrease_of_witness_family
    {n t U : ℕ} {β : ℝ}
    (hwit :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnWitness n t U β) :
    (hcanon :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        (hwit _ha).toPhaseReturns =
          aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha) →
    canonical_aperiodic_phase_return_fill_endpoint_nonincrease n t U := by
  intro hcanon haper
  rw [← hcanon haper]
  exact (hwit haper).fill_endpoint_nonincrease_on

/-- Local canonical-gap theorem extracted from the honest canonical aperiodic
witness. This is the repaired filler-side target after pushing the content to
the level actually consumed downstream. -/
theorem CanonicalAperiodicPhaseReturnWitness.canonical_gap_step_sedt_on
    {n t U : ℕ} {β : ℝ}
    (hw : CanonicalAperiodicPhaseReturnWitness n t U β)
    : canonical_phase_return_gap_step_sedt_on n t U β hw.toPhaseReturns := by
  exact hw.canonicalGapStep

/-- Stream-level `E.2` envelope extracted from the honest canonical witness. -/
theorem CanonicalAperiodicPhaseReturnWitness.orbit_epoch_sedt_envelope
    {n t U : ℕ} {β : ℝ}
    (hw : CanonicalAperiodicPhaseReturnWitness n t U β)
    (hparams : sedt_dominant_parameters t U β) :
    orbit_epoch_sedt_envelope t U β
      (Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps n t U
        ((Epochs.canonical_gap_long_phase_returns_bridge n t U) hw.toPhaseReturns)) := by
  exact orbit_epoch_sedt_envelope_of_gap_step_sedt_on
    hw.canonical_gap_step_sedt_on hparams

/-- The repaired actual-skeleton semantic package also produces the honest
stream-level `E.2` target directly, after building the canonical witness
internally. -/
theorem canonical_aperiodic_orbit_epoch_sedt_envelope_of_phase_return_semantics
    {n t U : ℕ} {β : ℝ}
    (hsem :
      ∀ _ha : ¬ Collatz.CycleExclusion.orbit_eventually_periodic n,
        CanonicalAperiodicPhaseReturnSemantics n t U β _ha)
    (hparams : sedt_dominant_parameters t U β) :
    canonical_aperiodic_orbit_epoch_sedt_envelope n t U β := by
  intro haper
  simpa using
    (canonical_aperiodic_phase_return_witness_of_semantics (hsem haper)).orbit_epoch_sedt_envelope hparams

/-- Aperiodic tail contradiction from orbitwise/cofinal coercive decay. -/
theorem aperiodic_tail_contradiction_from_coercivity
    (n t U : ℕ) (β : ℝ)
    (_haper : ¬Collatz.CycleExclusion.orbit_eventually_periodic n)
    (hw : OrbitLongEpochE2Witness n t U β)
    (hparams : sedt_dominant_parameters t U β)
    (hn : Odd n)
    : False := by
  let hstream : Collatz.Epochs.OrbitLongEpochStream n t U :=
    hw.toStream
  have ht : t ≥ 3 := hparams.1
  have hU : U ≥ 1 := hparams.2.1
  have hβgt : β > Collatz.SEDT.β₀ t U := hparams.2.2.1
  have hdom : sedt_dominance_condition t U β := hparams.2.2.2
  have hα : Collatz.SEDT.α t U < 2 := Collatz.SEDT.alpha_lt_two_of_ht_hU t U ht hU
  have hε : Collatz.SEDT.ε t U β > 0 := Collatz.SEDT.epsilon_pos t U β ht hU hα hβgt
  have hβ0pos : 0 < Collatz.SEDT.β₀ t U := Collatz.SEDT.beta_zero_pos t U hα
  have hβpos : 0 < β := by linarith
  have hβnonneg : 0 ≤ β := le_of_lt hβpos
  have hoddIter : ∀ k : ℕ, Odd ((Collatz.Foundations.collatz_step^[k]) n) := odd_iterates_of_odd n hn
  have hstep : orbit_epoch_step_drift t U β hstream :=
    orbit_epoch_step_drift_of_sedt_envelope t U β hstream (by simpa [OrbitLongEpochE2Witness.toStream] using hw.envelope)
  have hpack := strong_i2_orbitwise_packaged_of_dominance t U β hstream hε hβnonneg hstep hdom
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
  have hle : potential β ((Collatz.Foundations.collatz_step^[hstream.idx J]) n) <
      0 := lt_of_le_of_lt hupper' hneg
  exact not_lt_of_ge hnonneg hle

/-- Strict I.1 closure through the periodic/aperiodic dichotomy and W6 bridges. -/
theorem collatz_convergence
    (n t U : ℕ) (β : ℝ) (hn : Odd n)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicWitness :
      ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
        OrbitLongEpochE2Witness n t U β)
    (hparams : sedt_dominant_parameters t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  have hperiodicBridge : Collatz.CycleExclusion.periodic_tail_cycle_bridge n :=
    hperiodicContracts.1
  have hperiodOneCanon :
      ∀ x : ℕ, (Collatz.Foundations.collatz_step x = x) → 3 * x + 1 = 4 * x :=
    hperiodicContracts.2
  by_cases hentry : enters_trivial_cycle n
  · exact collatz_convergence_from_entry n hn hentry
  · by_cases hper : Collatz.CycleExclusion.orbit_eventually_periodic n
    · let hw := Collatz.CycleExclusion.orbit_periodic_tail_witness_of_eventual n hper
      rcases Collatz.CycleExclusion.orbit_periodic_tail_period_one_or_gt_one hw with hperiod1 | hperiodGt
      · rcases period_one_tail_reaches_one n hw hperiod1 hperiodOneCanon with ⟨k, hk⟩
        have hentry' : enters_trivial_cycle n := by
          refine ⟨k, ?_⟩
          simp [trivialCycleSet, hk]
        exact False.elim (hentry hentry')
      · have hfalse : False := by
          exact Collatz.CycleExclusion.periodic_tail_contradiction_from_bridge n hw hperiodGt
            hperiodicBridge
        exact False.elim hfalse
    · have hfalse : False := by
        exact aperiodic_tail_contradiction_from_coercivity n t U β hper (haperiodicWitness hper)
          hparams hn
      exact False.elim hfalse

/-- Compatibility alias: strict I.1 closure under the orbitwise bridge assumptions. -/
theorem strict_i1 (n t U : ℕ) (β : ℝ) (hn : Odd n)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicWitness :
      ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
        OrbitLongEpochE2Witness n t U β)
    (hparams : sedt_dominant_parameters t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence n t U β hn hperiodicContracts haperiodicWitness hparams

/-- Once the orbitwise `E.2 + G.5` witness can be produced uniformly in the
paper-admissible parameter choice, the residual `sedt_dominant_parameters`
package is no longer an external bridge: it is instantiated canonically from
`t ≥ 3`, `U ≥ 1`. -/
theorem collatz_convergence_with_parameter_choice
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicWitness :
      ∀ β : ℝ, sedt_dominant_parameters t U β →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          OrbitLongEpochE2Witness n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  rcases exists_sedt_dominant_parameters t U ht hU with ⟨β, hparams⟩
  exact collatz_convergence n t U β hn hperiodicContracts (haperiodicWitness β hparams) hparams

/-- Strict I.1 alias with the parameter package discharged internally from
the canonical SEDT choice. The only remaining residual bridge is the uniform
production of the `OrbitLongEpochE2Witness`. -/
theorem strict_i1_with_parameter_choice
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicWitness :
      ∀ β : ℝ, sedt_dominant_parameters t U β →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          OrbitLongEpochE2Witness n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_with_parameter_choice n t U hn ht hU
    hperiodicContracts haperiodicWitness

/-- Upstream-shaped strict-I.1 wrapper: the remaining aperiodic input is split
into the actual `G.5/G.Super-SEDT` long-epoch supply and the `E.2` envelope on
the canonical stream it induces, rather than a prepackaged witness object. -/
theorem collatz_convergence_from_upstream_contracts
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSupply :
      ∀ β : ℝ, sedt_dominant_parameters t U β →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          Collatz.Epochs.OrbitLongEpochSupply n t U)
    (haperiodicEnvelope :
      ∀ β : ℝ, (hparams : sedt_dominant_parameters t U β) →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          let hsupply := haperiodicSupply β hparams _ha
          orbit_epoch_sedt_envelope t U β
            (Collatz.Epochs.orbit_long_epoch_stream_of_supply n t U hsupply))
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_with_parameter_choice n t U hn ht hU hperiodicContracts ?_
  intro β hparams haper
  let hsupply := haperiodicSupply β hparams haper
  have henv :
      orbit_epoch_sedt_envelope t U β
        (Collatz.Epochs.orbit_long_epoch_stream_of_supply n t U hsupply) := by
    simpa [hsupply] using haperiodicEnvelope β hparams haper
  exact orbit_long_epoch_e2_witness_of_supply hsupply henv

/-- Same as `collatz_convergence_from_upstream_contracts`, but exposed under the
strict-I.1 naming used in the roadmap. This leaves a single honest gap: proving
those two upstream contracts from orbit semantics. -/
theorem strict_i1_from_upstream_contracts
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSupply :
      ∀ β : ℝ, sedt_dominant_parameters t U β →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          Collatz.Epochs.OrbitLongEpochSupply n t U)
    (haperiodicEnvelope :
      ∀ β : ℝ, (hparams : sedt_dominant_parameters t U β) →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          let hsupply := haperiodicSupply β hparams _ha
          orbit_epoch_sedt_envelope t U β
            (Collatz.Epochs.orbit_long_epoch_stream_of_supply n t U hsupply))
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_upstream_contracts n t U hn ht hU
    hperiodicContracts haperiodicSupply haperiodicEnvelope

/-- More orbit-semantic strict-I.1 wrapper: the aperiodic branch now asks only
for a cofinal sequence of SEDT-long orbit gaps, and derives the formal
`OrbitLongEpochSupply` object internally. This is the smallest honest
intermediate target on the road from orbit semantics to W6. -/
theorem collatz_convergence_from_gap_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicGaps :
      ∀ β : ℝ, sedt_dominant_parameters t U β →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          Epochs.OrbitHasCofinalLongEpochGaps n t U)
    (haperiodicEnvelope :
      ∀ β : ℝ, (hparams : sedt_dominant_parameters t U β) →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          orbit_epoch_sedt_envelope t U β
            (Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps n t U
              (haperiodicGaps β hparams _ha)))
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_upstream_contracts n t U hn ht hU hperiodicContracts ?_ ?_
  · intro β hparams haper
    exact Epochs.orbit_long_epoch_supply_of_cofinal_long_epoch_gaps
      (haperiodicGaps β hparams haper)
  · intro β hparams haper
    simpa [Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps]
      using haperiodicEnvelope β hparams haper

/-- Strict-I.1 alias for the gap-semantic orbit interface. The remaining honest
research task is now exactly to prove `OrbitHasCofinalLongEpochGaps` from
aperiodicity. -/
theorem strict_i1_from_gap_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicGaps :
      ∀ β : ℝ, sedt_dominant_parameters t U β →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          Epochs.OrbitHasCofinalLongEpochGaps n t U)
    (haperiodicEnvelope :
      ∀ β : ℝ, (hparams : sedt_dominant_parameters t U β) →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          orbit_epoch_sedt_envelope t U β
            (Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps n t U
              (haperiodicGaps β hparams _ha)))
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_gap_semantics n t U hn ht hU
    hperiodicContracts haperiodicGaps haperiodicEnvelope

/-- Further-localized strict-I.1 wrapper: after the orbit-semantic reductions
already proved in `Convergence/MainTheorem`, the remaining aperiodic bridge can
be stated as a single epoch-side theorem converting cofinal `gap_long` phase
returns into actual cofinal SEDT-long gaps. -/
theorem collatz_convergence_from_phase_return_bridge
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (hphaseBridge : Epochs.GapLongPhaseReturnsBridge n t U)
    (haperiodicEnvelope :
      ∀ β : ℝ, (hparams : sedt_dominant_parameters t U β) →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          orbit_epoch_sedt_envelope t U β
            (Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps n t U
              (hphaseBridge (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha))))
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_gap_semantics n t U hn ht hU hperiodicContracts ?_ ?_
  · intro β hparams haper
    exact Epochs.orbit_has_cofinal_long_epoch_gaps_of_gap_long_phase_returns
      hphaseBridge (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  · intro β hparams haper
    simpa using haperiodicEnvelope β hparams haper

/-- Strict-I.1 alias for the phase-return-localized bridge. At this point the
remaining honest gap is a single epoch theorem:
`GapLongPhaseReturnsBridge n t U`. -/
theorem strict_i1_from_phase_return_bridge
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (hphaseBridge : Epochs.GapLongPhaseReturnsBridge n t U)
    (haperiodicEnvelope :
      ∀ β : ℝ, (hparams : sedt_dominant_parameters t U β) →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          orbit_epoch_sedt_envelope t U β
            (Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps n t U
              (hphaseBridge (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha))))
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_phase_return_bridge n t U hn ht hU
    hperiodicContracts hphaseBridge haperiodicEnvelope

/-- Once the epoch-side phase-return bridge is supplied canonically by
`Epochs.LongEpochs`, the remaining aperiodic input reduces again: only the
`E.2` envelope on the induced long-gap stream remains external. -/
theorem collatz_convergence_from_canonical_phase_return_bridge
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicEnvelope :
      ∀ β : ℝ, (hparams : sedt_dominant_parameters t U β) →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          orbit_epoch_sedt_envelope t U β
            (Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps n t U
              ((Epochs.canonical_gap_long_phase_returns_bridge n t U)
                (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha))))
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_phase_return_bridge n t U hn ht hU
    hperiodicContracts (Epochs.canonical_gap_long_phase_returns_bridge n t U)
    haperiodicEnvelope

/-- Strict-I.1 alias with the phase-return bridge discharged canonically inside
`Epochs.LongEpochs`. The remaining residual bridge is now only the orbitwise
`E.2` envelope on the selected cofinal long-gap stream. -/
theorem strict_i1_from_canonical_phase_return_bridge
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicEnvelope :
      ∀ β : ℝ, (hparams : sedt_dominant_parameters t U β) →
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          orbit_epoch_sedt_envelope t U β
            (Epochs.orbit_long_epoch_stream_of_cofinal_long_epoch_gaps n t U
              ((Epochs.canonical_gap_long_phase_returns_bridge n t U)
                (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha))))
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_canonical_phase_return_bridge n t U hn ht hU
    hperiodicContracts haperiodicEnvelope

/-- After canonical closure of the epoch-side phase-return bridge, the remaining
aperiodic input can be stated as a single `E.2`-bridge from the structured
phase-return witness to the orbitwise envelope on the induced canonical stream. -/
theorem collatz_convergence_from_canonical_aperiodic_bridges
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicE2Bridge :
      ∀ β : ℝ, phase_return_sedt_envelope_bridge n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_canonical_phase_return_bridge n t U hn ht hU
    hperiodicContracts ?_
  intro β hparams haper
  exact orbit_epoch_sedt_envelope_of_phase_returns
    (haperiodicE2Bridge β) hparams
    (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)

/-- Localized strict-I.1 wrapper for the remaining aperiodic `E.2` task:
instead of a whole-stream bridge, it suffices to prove the canonical per-gap
SEDT inequality on the long gaps extracted from the structured phase-return
witness. -/
theorem collatz_convergence_from_local_gap_step_bridge
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicLocalE2 :
      ∀ β : ℝ, canonical_phase_return_gap_step_sedt n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_canonical_aperiodic_bridges n t U hn ht hU
    hperiodicContracts ?_
  intro β
  exact phase_return_sedt_envelope_bridge_of_gap_step_sedt (haperiodicLocalE2 β)

/-- Strict-I.1 alias exposing the residual aperiodic gap in the localized
per-gap `E.2` form. -/
theorem strict_i1_from_local_gap_step_bridge
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicLocalE2 :
      ∀ β : ℝ, canonical_phase_return_gap_step_sedt n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_local_gap_step_bridge n t U hn ht hU
    hperiodicContracts haperiodicLocalE2

/-- More semantic localization of the remaining aperiodic input: enough to prove
`E.2` on each actual phase-return pair and a drift bound on the filler segment
up to the next canonical left index. These two local contracts reassemble into
the canonical-gap bridge used by the coercivity layer. -/
theorem collatz_convergence_from_phase_return_pair_and_fill_bridges
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicPairE2 :
      ∀ β : ℝ, phase_return_pair_step_sedt n t U β)
    (haperiodicFillDrift :
      ∀ β : ℝ, phase_return_gap_fill_bridge n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_local_gap_step_bridge n t U hn ht hU
    hperiodicContracts ?_
  intro β
  exact canonical_phase_return_gap_step_sedt_of_pair_and_fill
    (haperiodicPairE2 β) (haperiodicFillDrift β)

/-- Same as `collatz_convergence_from_phase_return_pair_and_fill_bridges`, but
the phase-return pair bound is given in the smallest single-gap form: an
arbitrary aligned return pair with SEDT-long separation satisfies `E.2`. -/
theorem collatz_convergence_from_single_gap_and_fill_bridges
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSingleGap :
      ∀ β : ℝ, sedt_single_gap_of_phase_return n t U β)
    (haperiodicFillDrift :
      ∀ β : ℝ, phase_return_gap_fill_bridge n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_phase_return_pair_and_fill_bridges n t U hn ht hU
    hperiodicContracts ?_ haperiodicFillDrift
  intro β
  exact phase_return_pair_step_sedt_of_single_gap (haperiodicSingleGap β)

/-- Strict-I.1 alias for the pair+fill localized aperiodic bridge. -/
theorem strict_i1_from_phase_return_pair_and_fill_bridges
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicPairE2 :
      ∀ β : ℝ, phase_return_pair_step_sedt n t U β)
    (haperiodicFillDrift :
      ∀ β : ℝ, phase_return_gap_fill_bridge n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_phase_return_pair_and_fill_bridges n t U hn ht hU
    hperiodicContracts haperiodicPairE2 haperiodicFillDrift

/-- Strict-I.1 alias for the smallest single-gap + filler formulation of the
remaining aperiodic `E.2` input. -/
theorem strict_i1_from_single_gap_and_fill_bridges
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSingleGap :
      ∀ β : ℝ, sedt_single_gap_of_phase_return n t U β)
    (haperiodicFillDrift :
      ∀ β : ℝ, phase_return_gap_fill_bridge n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_single_gap_and_fill_bridges n t U hn ht hU
    hperiodicContracts haperiodicSingleGap haperiodicFillDrift

/-- Canonical aperiodic endpoint-order contract: only the phase-return witness
actually produced from a non-periodic orbit must satisfy endpoint nonincrease. -/
def canonical_aperiodic_phase_return_endpoint_nonincrease
    (n t U : ℕ) : Prop :=
  ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
    phase_return_endpoint_nonincrease_on n t U
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Canonical aperiodic filler-drift contract: the witness-indexed filler bound is
required only for the concrete selected phase-return witness produced by the
aperiodic orbit. -/
def canonical_aperiodic_phase_return_gap_fill_bridge
    (n t U : ℕ) (β : ℝ) : Prop :=
  ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
    phase_return_gap_fill_step_drift n t U β
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)

/-- Constructor for the canonical endpoint-order contract from witness-level
theorems on the actual aperiodic phase-return witness. -/
def canonical_aperiodic_phase_return_endpoint_nonincrease_of_witness
    (n t U : ℕ)
    (hcanon :
      ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
        phase_return_endpoint_nonincrease_on n t U
          (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)) :
    canonical_aperiodic_phase_return_endpoint_nonincrease n t U :=
  hcanon

/-- Constructor for the canonical filler-drift bridge from witness-level theorems
on the actual aperiodic phase-return witness. -/
def canonical_aperiodic_phase_return_gap_fill_bridge_of_witness
    (n t U : ℕ) (β : ℝ)
    (hcanon :
      ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
        phase_return_gap_fill_step_drift n t U β
          (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)) :
    canonical_aperiodic_phase_return_gap_fill_bridge n t U β :=
  hcanon

/-- Actual-skeleton canonical-gap theorem source directly from the selected
long-epoch bridge, correction theorem, and filler theorem on the concrete
canonical aperiodic skeleton. -/
theorem canonical_aperiodic_phase_return_gap_step_sedt_on_of_selected_long_epoch_bridge_on_correction_and_fill
    {n t U : ℕ} {β : ℝ}
    (hbridge : canonical_aperiodic_selected_long_epoch_bridge_on n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hfill : canonical_aperiodic_phase_return_gap_fill_bridge n t U β) :
    canonical_aperiodic_phase_return_gap_step_sedt_on n t U β := by
  intro haper
  exact canonical_phase_return_gap_step_sedt_on_of_pair_and_fill
    (canonical_aperiodic_phase_return_pair_step_sedt_on_of_selected_long_epoch_bridge_on_and_correction
      hbridge hcorr haper)
    (hfill haper)

/-- Actual-skeleton stream-level `E.2` envelope directly from the selected
long-epoch bridge, correction theorem, and filler theorem on the concrete
canonical aperiodic skeleton. -/
theorem canonical_aperiodic_orbit_epoch_sedt_envelope_of_selected_long_epoch_bridge_on_correction_and_fill
    {n t U : ℕ} {β : ℝ}
    (hbridge : canonical_aperiodic_selected_long_epoch_bridge_on n t U)
    (hcorr : canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (hfill : canonical_aperiodic_phase_return_gap_fill_bridge n t U β)
    (hparams : sedt_dominant_parameters t U β) :
    canonical_aperiodic_orbit_epoch_sedt_envelope n t U β := by
  exact canonical_aperiodic_orbit_epoch_sedt_envelope_of_canonical_gap_step
    (canonical_aperiodic_phase_return_gap_step_sedt_on_of_selected_long_epoch_bridge_on_correction_and_fill
      hbridge hcorr hfill)
    hparams

/-- Lowest currently exposed aperiodic interface: enough to prove a native
`SEDT.potential_change` bound on one aligned phase-return segment, control the
normalization correction back to `Coercivity.potential`, and bound the filler
segment up to the next canonical left index. -/
theorem collatz_convergence_from_segment_correction_and_fill_bridges
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSegmentE2 :
      ∀ β : ℝ, Collatz.SEDT.sedt_potential_change_of_phase_return_segment n t U β)
    (haperiodicEndpointOrder :
      canonical_aperiodic_phase_return_endpoint_nonincrease n t U)
    (haperiodicFillDrift :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_fill_bridge n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_canonical_phase_return_bridge n t U hn ht hU
    hperiodicContracts ?_
  intro β hparams haper
  let hphase := aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper
  have hpair :
      phase_return_pair_step_sedt_on n t U β hphase :=
    phase_return_pair_step_sedt_on_of_segment_bound_and_endpoint_nonincrease
      hn (haperiodicSegmentE2 β) (haperiodicEndpointOrder haper)
  have hgap :
      canonical_phase_return_gap_step_sedt_on n t U β hphase :=
    canonical_phase_return_gap_step_sedt_on_of_pair_and_fill
      hpair (haperiodicFillDrift β haper)
  exact orbit_epoch_sedt_envelope_of_gap_step_sedt_on hgap hparams

/-- Strict-I.1 alias for the most localized currently exposed aperiodic bridge. -/
theorem strict_i1_from_segment_correction_and_fill_bridges
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSegmentE2 :
      ∀ β : ℝ, Collatz.SEDT.sedt_potential_change_of_phase_return_segment n t U β)
    (haperiodicEndpointOrder :
      canonical_aperiodic_phase_return_endpoint_nonincrease n t U)
    (haperiodicFillDrift :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_fill_bridge n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_segment_correction_and_fill_bridges n t U hn ht hU
    hperiodicContracts haperiodicSegmentE2 haperiodicEndpointOrder haperiodicFillDrift

/-- Most atomic currently exposed aperiodic interface on the `SEDT` side: it is
enough to control `SEDT.potential_change` on any orbit segment whose length is
both SEDT-long and divisible by `gap_long t`, together with the normalization
correction and the filler drift. -/
theorem collatz_convergence_from_gap_multiple_correction_and_fill_bridges
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicGapMultipleE2 :
      ∀ β : ℝ, Collatz.SEDT.sedt_potential_change_of_gap_long_multiple_segment n t U β)
    (haperiodicEndpointOrder :
      canonical_aperiodic_phase_return_endpoint_nonincrease n t U)
    (haperiodicFillDrift :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_fill_bridge n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_segment_correction_and_fill_bridges n t U hn ht hU
    hperiodicContracts ?_ haperiodicEndpointOrder haperiodicFillDrift
  intro β
  exact Collatz.SEDT.sedt_potential_change_of_phase_return_segment_of_gap_long_multiple
    (haperiodicGapMultipleE2 β)

/-- Strict-I.1 alias for the gap-multiple + correction + filler formulation of
the remaining aperiodic bridge. -/
theorem strict_i1_from_gap_multiple_correction_and_fill_bridges
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicGapMultipleE2 :
      ∀ β : ℝ, Collatz.SEDT.sedt_potential_change_of_gap_long_multiple_segment n t U β)
    (haperiodicEndpointOrder :
      canonical_aperiodic_phase_return_endpoint_nonincrease n t U)
    (haperiodicFillDrift :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_fill_bridge n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_gap_multiple_correction_and_fill_bridges n t U hn ht hU
    hperiodicContracts haperiodicGapMultipleE2 haperiodicEndpointOrder haperiodicFillDrift

/-- Direct canonical-witness formulation of the lowest aperiodic interface: the
local `SEDT` segment theorem, endpoint order, and filler drift are supplied only
for the actual witness `aperiodic_orbit_has_cofinal_gap_long_phase_returns`. -/
theorem collatz_convergence_from_canonical_witness_segment_correction_and_fill_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSegmentE2 :
      ∀ β : ℝ, Collatz.SEDT.sedt_potential_change_of_phase_return_segment n t U β)
    (haperiodicEndpointOn :
      ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
        phase_return_endpoint_nonincrease_on n t U
          (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha))
    (haperiodicFillOn :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          phase_return_gap_fill_step_drift n t U β
            (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_segment_correction_and_fill_bridges n t U hn ht hU
    hperiodicContracts haperiodicSegmentE2 ?_ ?_
  · exact canonical_aperiodic_phase_return_endpoint_nonincrease_of_witness n t U
      haperiodicEndpointOn
  · intro β
    exact canonical_aperiodic_phase_return_gap_fill_bridge_of_witness n t U β
      (haperiodicFillOn β)

/-- Same canonical-witness localization, but starting from the gap-multiple
`SEDT` contract. -/
theorem collatz_convergence_from_canonical_witness_gap_multiple_correction_and_fill_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicGapMultipleE2 :
      ∀ β : ℝ, Collatz.SEDT.sedt_potential_change_of_gap_long_multiple_segment n t U β)
    (haperiodicEndpointOn :
      ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
        phase_return_endpoint_nonincrease_on n t U
          (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha))
    (haperiodicFillOn :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          phase_return_gap_fill_step_drift n t U β
            (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U _ha)) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_gap_multiple_correction_and_fill_bridges n t U hn ht hU
    hperiodicContracts haperiodicGapMultipleE2 ?_ ?_
  · exact canonical_aperiodic_phase_return_endpoint_nonincrease_of_witness n t U
      haperiodicEndpointOn
  · intro β
    exact canonical_aperiodic_phase_return_gap_fill_bridge_of_witness n t U β
      (haperiodicFillOn β)

/-- Honest repaired aperiodic entrypoint: instead of asking separately for
segment, correction, and filler facts on the weak `choose`-based witness,
supply one canonical witness object already built from real selected-segment
semantics. Its repaired canonical-gap theorem is used directly. -/
theorem collatz_convergence_from_semantic_canonical_witness_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicWitness :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          CanonicalAperiodicPhaseReturnWitness n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_gap_semantics n t U hn ht hU
    hperiodicContracts ?_ ?_
  · intro β hparams haper
    let hw := haperiodicWitness β haper
    exact (Epochs.canonical_gap_long_phase_returns_bridge n t U) hw.toPhaseReturns
  · intro β hparams haper
    let hw := haperiodicWitness β haper
    simpa using hw.orbit_epoch_sedt_envelope hparams

/-- Compatibility wrapper under the older name where the pair-side `SEDT`
segment theorem was still an explicit external hypothesis. The repaired
canonical witness now already contains the honest canonical-gap theorem, so the
extra assumption is no longer used. -/
theorem collatz_convergence_from_semantic_canonical_witness_segment_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (_haperiodicSegmentE2 :
      ∀ β : ℝ, Collatz.SEDT.sedt_potential_change_of_phase_return_segment n t U β)
    (haperiodicWitness :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          CanonicalAperiodicPhaseReturnWitness n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_semantic_canonical_witness_semantics
    n t U hn ht hU hperiodicContracts haperiodicWitness

/-- Compatibility wrapper under the older gap-multiple name. The repaired
canonical witness already packages the honest canonical-gap theorem directly. -/
theorem collatz_convergence_from_semantic_canonical_witness_gap_multiple_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (_haperiodicGapMultipleE2 :
      ∀ β : ℝ, Collatz.SEDT.sedt_potential_change_of_gap_long_multiple_segment n t U β)
    (haperiodicWitness :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          CanonicalAperiodicPhaseReturnWitness n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_semantic_canonical_witness_semantics
    n t U hn ht hU hperiodicContracts haperiodicWitness

/-- Same honest repaired aperiodic entrypoint, but now the external content is
stated directly as theorem-producing semantics on the actual aperiodic
phase-return skeleton. The repaired canonical witness is built internally from
that semantic package. -/
theorem collatz_convergence_from_aperiodic_phase_return_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSemantics :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          CanonicalAperiodicPhaseReturnSemantics n t U β _ha) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_semantic_canonical_witness_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact canonical_aperiodic_phase_return_witness_of_semantics
    (haperiodicSemantics β haper)

/-- Same repaired aperiodic entrypoint, but now the external content is stated
as the narrower actual-skeleton semantic package whose filler field is only the
arithmetic source `step_type ≥ 2` on canonical filler indices. -/
theorem collatz_convergence_from_aperiodic_step_type_two_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSemantics :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          CanonicalAperiodicPhaseReturnStepTypeTwoSemantics n t U β _ha) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_phase_return_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact (haperiodicSemantics β haper).toPhaseReturnSemantics hn

/-- Same repaired aperiodic entrypoint, but now the external content is stated
as the exclusion-style actual-skeleton semantic package whose filler field only
rules out simple steps on canonical filler indices. -/
theorem collatz_convergence_from_aperiodic_no_simple_step_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSemantics :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          CanonicalAperiodicPhaseReturnNoSimpleStepSemantics n t U β _ha) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_phase_return_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact (haperiodicSemantics β haper).toPhaseReturnSemantics hn

/-- Same repaired aperiodic entrypoint, but now the external content is stated
as the lowest currently exposed candidate-exclusion semantic package on the
actual canonical phase-return skeleton. -/
theorem collatz_convergence_from_aperiodic_candidate_selection_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSemantics :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          CanonicalAperiodicPhaseReturnCandidateSelectionSemantics n t U β _ha) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_phase_return_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact (haperiodicSemantics β haper).toPhaseReturnSemantics hn

/-- Same repaired aperiodic entrypoint, but now the external content is stated
as the lowest currently exposed candidate-exclusion semantic package on the
actual canonical phase-return skeleton. -/
theorem collatz_convergence_from_aperiodic_candidate_exclusion_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicSemantics :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          CanonicalAperiodicPhaseReturnCandidateExclusionSemantics n t U β _ha) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_phase_return_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact (haperiodicSemantics β haper).toPhaseReturnSemantics hn

/-- Direct theorem-source entrypoint for the repaired aperiodic branch: the
remaining scientific content is stated exactly as localized carry-depth,
correction, and canonical-gap theorems on the actual aperiodic skeleton. -/
theorem collatz_convergence_from_aperiodic_theorem_sources
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicDepth :
      canonical_aperiodic_selected_carry_depth_semantics n t U)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicFillEndpoint :
      canonical_aperiodic_phase_return_fill_endpoint_nonincrease n t U)
    (haperiodicGap :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_phase_return_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact (canonical_aperiodic_phase_return_semantics_of_theorem_sources
    haperiodicDepth haperiodicCorrection haperiodicFillEndpoint (haperiodicGap β)) haper

/-- Variant of the direct theorem-source entrypoint where the filler-side
residual is supplied at the stronger raw stepwise level on the concrete
canonical aperiodic skeleton. This matches the current lowest stream-side
scientific target more faithfully than the endpoint-only interface. -/
theorem collatz_convergence_from_aperiodic_stepwise_theorem_sources
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicDepth :
      canonical_aperiodic_selected_carry_depth_semantics n t U)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicFillStepwise :
      canonical_aperiodic_phase_return_fill_stepwise_nonincrease n t U)
    (haperiodicGap :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_phase_return_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact (canonical_aperiodic_phase_return_stepwise_semantics_of_theorem_sources
    haperiodicDepth haperiodicCorrection haperiodicFillStepwise (haperiodicGap β)
  haper).toPhaseReturnSemantics

/-- Narrowest currently exposed theorem-source entrypoint for the repaired
aperiodic branch on the stream side: instead of assuming filler stepwise
monotonicity directly, one only assumes the more atomic arithmetic source that
every filler orbit point has local Collatz exponent at least `2`. -/
theorem collatz_convergence_from_aperiodic_step_type_two_theorem_sources
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicDepth :
      canonical_aperiodic_selected_carry_depth_semantics n t U)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicFillStepTwo :
      canonical_aperiodic_phase_return_fill_step_type_two_bridge n t U)
    (haperiodicGap :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_step_type_two_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact (canonical_aperiodic_phase_return_step_type_two_semantics_of_theorem_sources
    haperiodicDepth haperiodicCorrection haperiodicFillStepTwo (haperiodicGap β)
  haper)

/-- Current narrowest arithmetic theorem-source entrypoint on the stream side:
instead of assuming `step_type ≥ 2` directly, one only assumes that every
filler orbit point is a complex step modulo `4`. -/
theorem collatz_convergence_from_aperiodic_complex_step_theorem_sources
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicDepth :
      canonical_aperiodic_selected_carry_depth_semantics n t U)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicFillComplex :
      canonical_aperiodic_phase_return_fill_complex_step_bridge n t U)
    (haperiodicGap :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_aperiodic_step_type_two_theorem_sources
    n t U hn ht hU hperiodicContracts
    haperiodicDepth haperiodicCorrection
    (canonical_aperiodic_phase_return_fill_step_type_two_bridge_of_complex_step_bridge
      hn haperiodicFillComplex)
    haperiodicGap

/-- Current narrowest exclusion-style theorem-source entrypoint on the stream
side: instead of assuming complex steps directly, one only assumes that no
simple step appears on the canonical filler interval. -/
theorem collatz_convergence_from_aperiodic_no_simple_step_theorem_sources
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicDepth :
      canonical_aperiodic_selected_carry_depth_semantics n t U)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicFillNoSimple :
      canonical_aperiodic_phase_return_fill_no_simple_step_bridge n t U)
    (haperiodicGap :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_no_simple_step_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact (canonical_aperiodic_phase_return_no_simple_step_semantics_of_theorem_sources
    haperiodicDepth haperiodicCorrection haperiodicFillNoSimple
    (haperiodicGap β)
  haper)

/-- Lowest currently exposed theorem-source entrypoint on the stream side:
instead of assuming the no-simple-step statement directly, one only assumes the
more primitive concrete next-left phase-compatibility promotion/minimality pair
on the canonical filler interval. -/
theorem collatz_convergence_from_aperiodic_canonical_next_left_phase_compatibility_and_minimality_theorem_sources
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicDepth :
      canonical_aperiodic_selected_carry_depth_semantics n t U)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicFillProm :
      canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_promotion_semantics n t U)
    (haperiodicFillMin :
      canonical_aperiodic_phase_return_fill_canonical_next_left_phase_compatible_minimality_semantics n t U)
    (haperiodicGap :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_candidate_selection_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact
    (canonical_aperiodic_phase_return_candidate_selection_semantics_of_canonical_next_left_phase_compatibility_and_minimality_theorem_sources
      haperiodicDepth haperiodicCorrection haperiodicFillProm haperiodicFillMin
      (haperiodicGap β) haper)

/-- Lowest currently exposed theorem-source entrypoint on the stream side:
instead of assuming the no-simple-step statement directly, one only assumes the
more primitive candidate-exclusion bridge on the canonical filler interval. -/
theorem collatz_convergence_from_aperiodic_candidate_promotion_and_minimality_theorem_sources
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicDepth :
      canonical_aperiodic_selected_carry_depth_semantics n t U)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicFillProm :
      canonical_aperiodic_phase_return_fill_candidate_promotion_semantics n t U)
    (haperiodicFillMin :
      canonical_aperiodic_phase_return_fill_next_left_minimality_semantics n t U
        haperiodicFillProm)
    (haperiodicGap :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_candidate_selection_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact (canonical_aperiodic_phase_return_candidate_selection_semantics_of_promotion_and_minimality_theorem_sources
    haperiodicDepth haperiodicCorrection haperiodicFillProm haperiodicFillMin
    (haperiodicGap β) haper)

/-- Lowest currently exposed theorem-source entrypoint on the stream side:
instead of assuming the no-simple-step statement directly, one only assumes the
more primitive candidate-exclusion bridge on the canonical filler interval. -/
theorem collatz_convergence_from_aperiodic_candidate_selection_theorem_sources
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicDepth :
      canonical_aperiodic_selected_carry_depth_semantics n t U)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicFillSelection :
      canonical_aperiodic_phase_return_fill_candidate_selection_semantics n t U)
    (haperiodicGap :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_candidate_selection_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact (canonical_aperiodic_phase_return_candidate_selection_semantics_of_theorem_sources
    haperiodicDepth haperiodicCorrection haperiodicFillSelection (haperiodicGap β)
  haper)

/-- Lowest currently exposed theorem-source entrypoint on the stream side:
instead of assuming the no-simple-step statement directly, one only assumes the
more primitive candidate-exclusion bridge on the canonical filler interval. -/
theorem collatz_convergence_from_aperiodic_candidate_exclusion_theorem_sources
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicDepth :
      canonical_aperiodic_selected_carry_depth_semantics n t U)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicFillCandidate :
      canonical_aperiodic_phase_return_fill_candidate_exclusion_bridge n t U)
    (haperiodicGap :
      ∀ β : ℝ, canonical_aperiodic_phase_return_gap_step_sedt_on n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_candidate_exclusion_semantics
    n t U hn ht hU hperiodicContracts ?_
  intro β haper
  exact (canonical_aperiodic_phase_return_candidate_exclusion_semantics_of_theorem_sources
    haperiodicDepth haperiodicCorrection haperiodicFillCandidate (haperiodicGap β)
  haper)

/-- More orbit/epoch-semantic convergence entrypoint: the residual aperiodic
content is stated as an actual selected-long-epoch bridge on the concrete
aperiodic skeleton together with correction control and the orbitwise `E.2`
envelope on the induced canonical long-gap stream. -/
theorem collatz_convergence_from_aperiodic_selected_long_epoch_and_orbit_epoch_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (_haperiodicBridgeOn :
      canonical_aperiodic_selected_long_epoch_bridge_on n t U)
    (_haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicEnvelope :
      ∀ β : ℝ, canonical_aperiodic_orbit_epoch_sedt_envelope n t U β) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_gap_semantics n t U hn ht hU hperiodicContracts ?_ ?_
  · intro β hparams haper
    exact Epochs.orbit_has_cofinal_long_epoch_gaps_of_gap_long_phase_returns
      (Epochs.canonical_gap_long_phase_returns_bridge n t U)
      (aperiodic_orbit_has_cofinal_gap_long_phase_returns n t U haper)
  · intro β hparams haper
    simpa [canonical_aperiodic_orbit_long_epoch_stream] using haperiodicEnvelope β haper

/-- Lowest selected-segment + stream-local convergence entrypoint now exposed by
Lean: the carry side is supplied only as actual selected-segment portrait and
depth-from-bonus semantics on the canonical aperiodic skeleton, while the `E.2`
side is supplied only as local accounting and endpoint monotonicity on the
induced canonical long-gap stream. -/
theorem collatz_convergence_from_aperiodic_lower_selected_segment_and_stream_local_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicPortrait :
      canonical_aperiodic_selected_portrait_enumeration_semantics n t U)
    (haperiodicDepthFromBonus :
      canonical_aperiodic_selected_depth_from_bonus_semantics n t U haperiodicPortrait)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicStreamLocal :
      ∀ β : ℝ, canonical_aperiodic_orbit_epoch_local_accounting_semantics n t U β)
    (haperiodicStreamEndpoint :
      canonical_aperiodic_orbit_epoch_endpoint_nonincrease n t U) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_selected_long_epoch_and_orbit_epoch_semantics
    n t U hn ht hU hperiodicContracts
    (canonical_aperiodic_selected_long_epoch_bridge_on_of_portrait_and_depth_from_bonus
      hn haperiodicPortrait haperiodicDepthFromBonus)
    haperiodicCorrection ?_
  intro β
  exact canonical_aperiodic_orbit_epoch_sedt_envelope_of_local_accounting_and_endpoint_nonincrease
    hn (haperiodicStreamLocal β) haperiodicStreamEndpoint

/-- Parallel lowest entrypoint using the native stream-level `SEDT.potential_change`
semantics instead of local log/depth accounting, while keeping the same
selected-segment portrait/depth-from-bonus carry layer and the same stream
endpoint target. -/
theorem collatz_convergence_from_aperiodic_lower_selected_segment_and_stream_native_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicPortrait :
      canonical_aperiodic_selected_portrait_enumeration_semantics n t U)
    (haperiodicDepthFromBonus :
      canonical_aperiodic_selected_depth_from_bonus_semantics n t U haperiodicPortrait)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicStreamNative :
      ∀ β : ℝ, canonical_aperiodic_orbit_epoch_native_sedt_semantics n t U β)
    (haperiodicStreamEndpoint :
      canonical_aperiodic_orbit_epoch_endpoint_nonincrease n t U) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  refine collatz_convergence_from_aperiodic_selected_long_epoch_and_orbit_epoch_semantics
    n t U hn ht hU hperiodicContracts
    (canonical_aperiodic_selected_long_epoch_bridge_on_of_portrait_and_depth_from_bonus
      hn haperiodicPortrait haperiodicDepthFromBonus)
    haperiodicCorrection ?_
  intro β
  exact canonical_aperiodic_orbit_epoch_sedt_envelope_of_native_semantics_and_endpoint_nonincrease
    hn (haperiodicStreamNative β) haperiodicStreamEndpoint

/-- Even narrower honest convergence entrypoint: after canonical closure of the
selected-segment portrait semantics from phase geometry, the carry side asks
only for the dependent actual-skeleton depth-from-bonus theorem, while the
stream side asks for local accounting plus endpoint monotonicity on the induced
canonical long-gap stream. -/
theorem collatz_convergence_from_aperiodic_canonical_depth_from_bonus_and_stream_local_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicDepthFromBonus :
      canonical_aperiodic_selected_depth_from_bonus_semantics_canonical n t U)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicStreamLocal :
      ∀ β : ℝ, canonical_aperiodic_orbit_epoch_local_accounting_semantics n t U β)
    (haperiodicStreamEndpoint :
      canonical_aperiodic_orbit_epoch_endpoint_nonincrease n t U) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_aperiodic_lower_selected_segment_and_stream_local_semantics
    n t U hn ht hU hperiodicContracts
    (canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry n t U)
    haperiodicDepthFromBonus
    haperiodicCorrection haperiodicStreamLocal haperiodicStreamEndpoint

/-- Parallel narrow entrypoint using native stream-level `SEDT.potential_change`
semantics instead of local accounting, while the carry side is reduced to the
single canonical depth-from-bonus residual target. -/
theorem collatz_convergence_from_aperiodic_canonical_depth_from_bonus_and_stream_native_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicDepthFromBonus :
      canonical_aperiodic_selected_depth_from_bonus_semantics_canonical n t U)
    (haperiodicCorrection :
      canonical_aperiodic_phase_return_correction_nonpositive_on n t U)
    (haperiodicStreamNative :
      ∀ β : ℝ, canonical_aperiodic_orbit_epoch_native_sedt_semantics n t U β)
    (haperiodicStreamEndpoint :
      canonical_aperiodic_orbit_epoch_endpoint_nonincrease n t U) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_aperiodic_lower_selected_segment_and_stream_native_semantics
    n t U hn ht hU hperiodicContracts
    (canonical_aperiodic_selected_portrait_enumeration_semantics_of_phase_geometry n t U)
    haperiodicDepthFromBonus
    haperiodicCorrection haperiodicStreamNative haperiodicStreamEndpoint

/-- Compatibility wrapper under the older segment-semantics name. -/
theorem collatz_convergence_from_aperiodic_phase_return_semantics_segment_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (_haperiodicSegmentE2 :
      ∀ β : ℝ, Collatz.SEDT.sedt_potential_change_of_phase_return_segment n t U β)
    (haperiodicSemantics :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          CanonicalAperiodicPhaseReturnSemantics n t U β _ha) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_aperiodic_phase_return_semantics
    n t U hn ht hU hperiodicContracts haperiodicSemantics

/-- Compatibility wrapper under the older gap-multiple-semantics name. -/
theorem collatz_convergence_from_aperiodic_phase_return_semantics_gap_multiple_semantics
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (_haperiodicGapMultipleE2 :
      ∀ β : ℝ, Collatz.SEDT.sedt_potential_change_of_gap_long_multiple_segment n t U β)
    (haperiodicSemantics :
      ∀ β : ℝ,
        ∀ _ha : ¬Collatz.CycleExclusion.orbit_eventually_periodic n,
          CanonicalAperiodicPhaseReturnSemantics n t U β _ha) :
    ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_aperiodic_phase_return_semantics
    n t U hn ht hU hperiodicContracts haperiodicSemantics

/-- Strict-I.1 alias with both the phase-return-to-gap closure and the final
aperiodic witness packaging internalized. The only remaining external bridges
are now the periodic extractor and the canonicalized `E.2` bridge. -/
theorem strict_i1_from_canonical_aperiodic_bridges
    (n t U : ℕ) (hn : Odd n)
    (ht : t ≥ 3) (hU : U ≥ 1)
    (hperiodicContracts : periodic_orbit_bridge_contract n)
    (haperiodicE2Bridge :
      ∀ β : ℝ, phase_return_sedt_envelope_bridge n t U β)
    : ∃ k : ℕ, (Collatz.Foundations.collatz_step^[k]) n = 1 := by
  exact collatz_convergence_from_canonical_aperiodic_bridges n t U hn ht hU
    hperiodicContracts haperiodicE2Bridge

end Collatz.Convergence
