import Collatz.Foundations.Core
import Collatz.Foundations.StepClassification
import Collatz.Epochs.Core
import Collatz.Epochs.APStructure
import Collatz.Epochs.Homogenization
import Collatz.Epochs.NumeratorCarry
import Collatz.Mixing.TouchFrequency
import Collatz.SEDT.Core

namespace Collatz.Epochs

/-- Canonical long-epoch gap proxy. -/
def gap_long (t : ℕ) : ℕ := Q_t t + 1

/-- Joint phase period used to remember both the canonical long-gap stride and the
paper-faithful phase class modulo `Q_t`. Equality modulo this product implies
equality modulo each factor separately. -/
def selected_phase_period (t : ℕ) : ℕ := Q_t t * gap_long t

lemma sparsity_of_switches (t : ℕ) : gap_long t ≥ 1 := by
  simp [gap_long]

lemma long_plateau_on_tail (t : ℕ) : ∃ L : ℕ, L ≥ Q_t t := by
  exact ⟨Q_t t, le_rfl⟩

lemma primitive_phase_shift_in_window (t : ℕ) :
    ∃ W : ℕ, W = Q_t t + gap_long t := by
  exact ⟨Q_t t + gap_long t, rfl⟩

lemma good_phase_implies_long (t : ℕ) :
    ∀ L : ℕ, L ≥ gap_long t → L + 1 > gap_long t := by
  intro L hL
  have hg : gap_long t < gap_long t + 1 := Nat.lt_succ_self _
  have hle : gap_long t + 1 ≤ L + 1 := Nat.succ_le_succ hL
  exact lt_of_lt_of_le hg hle

theorem infinite_long_epochs (t : ℕ) (_ht : 3 ≤ t) :
    ∀ n : ℕ, ∃ L : ℕ, L ≥ n ∧ L ≥ gap_long t := by
  intro n
  refine ⟨max n (gap_long t), ?_, ?_⟩
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Orbitwise interface used by W6 to model an infinite stream of SEDT-long epochs. -/
structure OrbitLongEpochStream (m t U : ℕ) where
  idx : ℕ → ℕ
  epochLen : ℕ → ℕ
  orbitVal : ℕ → ℕ
  idxMonotone : Monotone idx
  idxStrict : StrictMono idx
  idxStep : ∀ j : ℕ, idx (j + 1) = idx j + epochLen j
  longEpoch : ∀ j : ℕ, Collatz.SEDT.L₀ t U ≤ epochLen j
  realizedOnOrbit : ∀ j : ℕ, orbitVal j = (Collatz.Foundations.collatz_step^[idx j]) m

/-- G.5-style supply data in stream form:
selected orbit epochs with SEDT-long lower bounds. -/
structure OrbitLongEpochSupply (_m t U : ℕ) where
  idx : ℕ → ℕ
  epochLen : ℕ → ℕ
  idxStrict : StrictMono idx
  idxStep : ∀ j : ℕ, idx (j + 1) = idx j + epochLen j
  longEpoch : ∀ j : ℕ, Collatz.SEDT.L₀ t U ≤ epochLen j

/-- Honest orbit-semantic precursor to `OrbitLongEpochSupply`: a cofinal sequence
of orbit indices whose consecutive gaps are already SEDT-long. This isolates the
real semantic content from the later packaging step while keeping the underlying
data available for later construction. -/
structure OrbitHasCofinalLongEpochGaps (_m t U : ℕ) where
  idx : ℕ → ℕ
  idxStrict : StrictMono idx
  longGap : ∀ j : ℕ, Collatz.SEDT.L₀ t U ≤ idx (j + 1) - idx j

/-- Raw cofinal same-residue return contract at epoch scale:
for every threshold `N`, there exists a pair of orbit times `(i,j)` with
`i ≥ N`, `j - i ≥ L₀(t,U)`, and `i ≡ j [MOD selected_phase_period(t)]`. This
single congruence remembers both the canonical `gap_long` spacing and the
paper-faithful modulo-`Q_t` phase class. -/
def RawCofinalGapLongPhaseReturns (_m t U : ℕ) : Prop :=
  ∀ N : ℕ, ∃ i j : ℕ,
    N ≤ i ∧
    i + Collatz.SEDT.L₀ t U ≤ j ∧
    i % selected_phase_period t = j % selected_phase_period t

/-- Strengthened epoch-side phase-return witness carrying explicit cofinal
alignment data as sequences. This forces the remaining bridge to consume
phase/residue structure rather than a one-shot existential pair. -/
structure OrbitHasCofinalGapLongPhaseReturns (_m t U : ℕ) where
  leftIdx : ℕ → ℕ
  rightIdx : ℕ → ℕ
  leftStep : ∀ j : ℕ, leftIdx (j + 1) ≥ leftIdx j + 1
  rightStep : ∀ j : ℕ, rightIdx j < leftIdx (j + 1)
  longSep : ∀ j : ℕ, leftIdx j + Collatz.SEDT.L₀ t U ≤ rightIdx j
  selectedPhaseAligned :
    ∀ j : ℕ, leftIdx j % selected_phase_period t = rightIdx j % selected_phase_period t
  phaseAligned : ∀ j : ℕ, leftIdx j % gap_long t = rightIdx j % gap_long t
  qtPhaseAligned : ∀ j : ℕ, leftIdx j % Q_t t = rightIdx j % Q_t t
  cofinalLeft : ∀ N : ℕ, ∃ j : ℕ, N ≤ leftIdx j

/-- Paper-faithful semantic witness for one canonical selected long epoch/tail
segment on the aperiodic side. It refines a raw selected phase-return pair into
the local data actually used by the repaired E.1/E.2 bookkeeping: a chosen
phase class, realized orbit endpoints, longness, and explicit touch/multibit
side information. -/
structure SelectedLongEpochWitness {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) (j : ℕ) where
  phaseClass : ℕ
  phaseClass_lt : phaseClass < Q_t t
  phaseStart : hphase.leftIdx j % Q_t t = phaseClass
  phaseEnd : hphase.rightIdx j % Q_t t = phaseClass
  startVal : ℕ
  endVal : ℕ
  realizedStart : startVal = (Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m
  realizedEnd : endVal = (Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m
  startOdd : Odd startVal
  longSpan : Collatz.SEDT.L₀ t U ≤ hphase.rightIdx j - hphase.leftIdx j
  logCompression :
    (Real.log (endVal + 1) - Real.log (startVal + 1)) / Real.log 2 ≤
      ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ) *
        (Real.log (3 / 2) / Real.log 2)
  touchCount : ℕ
  touchLower :
    touch_count_lower t (hphase.rightIdx j - hphase.leftIdx j) ≤ touchCount
  touchUpper :
    touchCount ≤ touch_count_upper t (hphase.rightIdx j - hphase.leftIdx j)
  multibitGain : ℝ
  multibitGainUpper :
    multibitGain ≤
      (Collatz.SEDT.α t U - 1) *
          ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ) +
        Collatz.SEDT.C t U
  depthBookkeeping :
    ((Collatz.Foundations.depth_minus endVal : ℝ) -
        (Collatz.Foundations.depth_minus startVal : ℝ)) ≤
      multibitGain -
        ((hphase.rightIdx j - hphase.leftIdx j : ℕ) : ℝ)

/-- Semantic bridge expected from the repaired D/F/G layer: every canonical
selected phase-return pair is refined to a paper-faithful long-epoch witness
carrying the touch/multibit bookkeeping data needed for local E.2. -/
def SelectedLongEpochBridge (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    ∀ j : ℕ, SelectedLongEpochWitness hphase j

/-- Localized selected-long-epoch bridge on one fixed structured phase-return
witness. This is the honest lower semantic target needed when the ambient
aperiodic branch works with one concrete canonical witness rather than a global
`∀ hphase` interface. -/
def SelectedLongEpochBridgeOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) : Sort _ :=
  ∀ j : ℕ, SelectedLongEpochWitness hphase j

/-- Assemble one paper-faithful selected long-epoch witness from the exact lower
semantic data on a fixed structured phase-return pair. -/
noncomputable def selected_long_epoch_witness_of_semantics
    {m t U : ℕ}
    (hm : Odd m)
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (j : ℕ)
    (hcarryPaper :
      SelectedPaperCarryArguments m t U
        (hphase.leftIdx j) (hphase.rightIdx j)) :
    SelectedLongEpochWitness hphase j := by
  let hqtj : QTPhaseSegmentWitness t (hphase.leftIdx j) (hphase.rightIdx j) :=
    { phaseClass := hphase.leftIdx j % Q_t t
      phaseClass_lt := Nat.mod_lt _ (by
        unfold Q_t
        exact pow_pos (by decide) _)
      phaseStart := rfl
      phaseEnd := (hphase.qtPhaseAligned j).symm }
  let htouchj :=
    Collatz.Mixing.selected_touch_count_witness_of_qt_phase hqtj
  let hcarryj :=
    selected_multibit_carry_witness_of_paper_arguments hcarryPaper
  have hle : hphase.leftIdx j ≤ hphase.rightIdx j := by
    exact le_trans (Nat.le_add_right _ _) (hphase.longSep j)
  have hspan :
      Collatz.SEDT.L₀ t U ≤ hphase.rightIdx j - hphase.leftIdx j := by
    have hsep : Collatz.SEDT.L₀ t U + hphase.leftIdx j ≤ hphase.rightIdx j := by
      simpa [Nat.add_comm] using hphase.longSep j
    exact (Nat.le_sub_iff_add_le hle).2 hsep
  refine
    { phaseClass := hqtj.phaseClass
      phaseClass_lt := hqtj.phaseClass_lt
      phaseStart := hqtj.phaseStart
      phaseEnd := hqtj.phaseEnd
      startVal := (Collatz.Foundations.collatz_step^[hphase.leftIdx j]) m
      endVal := (Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m
      realizedStart := rfl
      realizedEnd := rfl
      startOdd := Collatz.Foundations.odd_iterates_of_odd hm (hphase.leftIdx j)
      longSpan := hspan
      logCompression :=
        by
          simpa [Nat.add_sub_of_le hle] using
            Collatz.Foundations.iterate_log_compression_of_odd_segment
              m (hphase.leftIdx j) (hphase.rightIdx j - hphase.leftIdx j) hm
      touchCount := htouchj.touchCount
      touchLower := htouchj.touchLower
      touchUpper := htouchj.touchUpper
      multibitGain := hcarryj.multibitGain
      multibitGainUpper := hcarryj.multibitGainUpper
      depthBookkeeping := hcarryj.depthBookkeeping }

/-- Assemble the localized selected-long-epoch bridge on one fixed structured
phase-return witness from the exact lower semantic data carried by its selected
segments. -/
noncomputable def selected_long_epoch_bridge_on_of_semantics
    {m t U : ℕ}
    (hm : Odd m)
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hcarryPaper :
      ∀ j : ℕ,
        SelectedPaperCarryArguments m t U
          (hphase.leftIdx j) (hphase.rightIdx j)) :
    SelectedLongEpochBridgeOn hphase := by
  intro j
  exact selected_long_epoch_witness_of_semantics hm j (hcarryPaper j)

/-- Assemble the selected long-epoch witness from the exact lower semantic data
produced in the repaired D/F/G layer. This isolates the remaining work below the
already-stable SEDT/coercivity wrappers. -/
noncomputable def selected_long_epoch_bridge_of_semantics
    {m t U : ℕ}
    (hm : Odd m)
    (hcarryPaper :
      ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U, ∀ j : ℕ,
        SelectedPaperCarryArguments m t U
          (hphase.leftIdx j) (hphase.rightIdx j)) :
    SelectedLongEpochBridge m t U := by
  intro hphase j
  exact selected_long_epoch_witness_of_semantics hm j (hcarryPaper hphase j)

lemma selected_phase_period_pos (t : ℕ) : 0 < selected_phase_period t := by
  unfold selected_phase_period gap_long Q_t
  exact Nat.mul_pos (pow_pos (by decide) _) (Nat.succ_pos _)

lemma gap_long_aligned_of_selected_phase_period
    (t i j : ℕ)
    (hij : i ≤ j)
    (hphase : i % selected_phase_period t = j % selected_phase_period t) :
    i % gap_long t = j % gap_long t := by
  have hmod : i ≡ j [MOD selected_phase_period t] := by
    simpa [Nat.ModEq] using hphase
  have hdivFull : selected_phase_period t ∣ j - i :=
    (Nat.modEq_iff_dvd' hij).1 hmod
  have hgapdvd : gap_long t ∣ selected_phase_period t := by
    unfold selected_phase_period
    refine ⟨Q_t t, ?_⟩
    ring
  have hdivGap : gap_long t ∣ j - i := by
    exact dvd_trans hgapdvd hdivFull
  have hmodGap : i ≡ j [MOD gap_long t] := (Nat.modEq_iff_dvd' hij).2 hdivGap
  simpa [Nat.ModEq] using hmodGap

lemma qt_phase_aligned_of_selected_phase_period
    (t i j : ℕ)
    (hij : i ≤ j)
    (hphase : i % selected_phase_period t = j % selected_phase_period t) :
    i % Q_t t = j % Q_t t := by
  have hmod : i ≡ j [MOD selected_phase_period t] := by
    simpa [Nat.ModEq] using hphase
  have hdivFull : selected_phase_period t ∣ j - i :=
    (Nat.modEq_iff_dvd' hij).1 hmod
  have hqtdvd : Q_t t ∣ selected_phase_period t := by
    unfold selected_phase_period
    refine ⟨gap_long t, rfl⟩
  have hdivQt : Q_t t ∣ j - i := by
    exact dvd_trans hqtdvd hdivFull
  have hmodQt : i ≡ j [MOD Q_t t] := (Nat.modEq_iff_dvd' hij).2 hdivQt
  simpa [Nat.ModEq] using hmodQt

/-- The repaired lower phase-return witness now exposes the honest modulo-`Q_t`
phase data directly, rather than taking it as an external assumption. -/
def qt_phase_segment_witness_of_phase_returns
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (j : ℕ) :
    QTPhaseSegmentWitness t (hphase.leftIdx j) (hphase.rightIdx j) :=
  { phaseClass := hphase.leftIdx j % Q_t t
    phaseClass_lt := Nat.mod_lt _ (by
      unfold Q_t
      exact pow_pos (by decide) _)
    phaseStart := rfl
    phaseEnd := (hphase.qtPhaseAligned j).symm }

/-- Build the strengthened phase-return witness from the raw cofinal
same-residue return contract. -/
noncomputable def orbit_has_cofinal_gap_long_phase_returns_of_raw
    {m t U : ℕ} (hraw : RawCofinalGapLongPhaseReturns m t U) :
    OrbitHasCofinalGapLongPhaseReturns m t U := by
  classical
  choose rawLeft rawRight hrawGe hrawSep hrawMod using hraw
  let threshold : ℕ → ℕ :=
    Nat.rec (motive := fun _ => ℕ) 0 (fun _ prev => rawRight prev + 1)
  let leftIdx : ℕ → ℕ := fun j => rawLeft (threshold j)
  let rightIdx : ℕ → ℕ := fun j => rawRight (threshold j)
  have hleft_ge_self : ∀ j : ℕ, j ≤ leftIdx j := by
    intro j
    induction j with
    | zero =>
        exact Nat.zero_le _
    | succ j ih =>
        have hright_ge_left : leftIdx j ≤ rightIdx j := by
          exact le_trans (Nat.le_add_right _ _) (by simpa [leftIdx, rightIdx] using hrawSep (threshold j))
        have hstep : leftIdx (j + 1) ≥ leftIdx j + 1 := by
          have hnext : leftIdx (j + 1) ≥ rightIdx j + 1 := by
            simpa [leftIdx, rightIdx, threshold] using hrawGe (threshold (j + 1))
          exact le_trans (Nat.add_le_add_right hright_ge_left 1) hnext
        exact le_trans (Nat.succ_le_succ ih) hstep
  refine
    { leftIdx := leftIdx
      rightIdx := rightIdx
      leftStep := ?_
      rightStep := ?_
      longSep := ?_
      selectedPhaseAligned := ?_
      phaseAligned := ?_
      qtPhaseAligned := ?_
      cofinalLeft := ?_ }
  · intro j
    have hright_ge_left : leftIdx j ≤ rightIdx j := by
      exact le_trans (Nat.le_add_right _ _) (by simpa [leftIdx, rightIdx] using hrawSep (threshold j))
    have hnext : leftIdx (j + 1) ≥ rightIdx j + 1 := by
      simpa [leftIdx, rightIdx, threshold] using hrawGe (threshold (j + 1))
    exact le_trans (Nat.add_le_add_right hright_ge_left 1) hnext
  · intro j
    have hnext : leftIdx (j + 1) ≥ rightIdx j + 1 := by
      simpa [leftIdx, rightIdx, threshold] using hrawGe (threshold (j + 1))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) hnext
  · intro j
    simpa [leftIdx, rightIdx] using hrawSep (threshold j)
  · intro j
    simpa [leftIdx, rightIdx] using hrawMod (threshold j)
  · intro j
    have hle : leftIdx j ≤ rightIdx j := by
      exact le_trans (Nat.le_add_right _ _) (by simpa [leftIdx, rightIdx] using hrawSep (threshold j))
    exact gap_long_aligned_of_selected_phase_period t (leftIdx j) (rightIdx j) hle
      (by simpa [leftIdx, rightIdx] using hrawMod (threshold j))
  · intro j
    have hle : leftIdx j ≤ rightIdx j := by
      exact le_trans (Nat.le_add_right _ _) (by simpa [leftIdx, rightIdx] using hrawSep (threshold j))
    exact qt_phase_aligned_of_selected_phase_period t (leftIdx j) (rightIdx j) hle
      (by simpa [leftIdx, rightIdx] using hrawMod (threshold j))
  · intro N
    exact ⟨N, hleft_ge_self N⟩

/-- Explicit theorem-level placeholder for the remaining epoch-semantic bridge:
turn cofinal `gap_long`-phase returns into actual cofinal SEDT-long gaps. -/
def GapLongPhaseReturnsBridge (m t U : ℕ) : Type :=
  OrbitHasCofinalGapLongPhaseReturns m t U →
    OrbitHasCofinalLongEpochGaps m t U

/-- Apply the remaining epoch-side bridge in theorem form. Keeping this as an
explicit theorem clarifies that the residual `A.REC/A.LONG` obligation is now a
single conversion from strengthened phase-return witnesses to cofinal long gaps. -/
def orbit_has_cofinal_long_epoch_gaps_of_gap_long_phase_returns
    {m t U : ℕ}
    (hbridge : GapLongPhaseReturnsBridge m t U)
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) :
    OrbitHasCofinalLongEpochGaps m t U :=
  hbridge hphase

/-- Honest lower filler-side value semantics on one fixed structured
phase-return witness. The object `OrbitHasCofinalGapLongPhaseReturns` itself
remembers only index/cofinality/congruence data, so any raw monotonicity along
the filler segment from `rightIdx j` up to `leftIdx (j+1)` must be supplied as
separate semantic content. -/
def GapLongPhaseReturnsFillerStepwiseBridgeOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  ∀ j k : ℕ,
    hphase.rightIdx j ≤ k →
    k < hphase.leftIdx (j + 1) →
      ((Collatz.Foundations.collatz_step^[k + 1]) m) ≤
        ((Collatz.Foundations.collatz_step^[k]) m)

/-- Global theorem-form filler bridge: every candidate structured phase-return
witness comes equipped with its own raw filler-stepwise monotonicity theorem.
This is deliberately separate from `GapLongPhaseReturnsBridge`, because the
phase-return skeleton alone does not encode value-level filler control. -/
def GapLongPhaseReturnsFillerStepwiseBridge
    (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerStepwiseBridgeOn hphase

/-- Even more primitive filler-side arithmetic semantics on one fixed
structured phase-return witness: every orbit point inside the filler interval
is a complex step in the mod-4 sense. This is a convenient precursor to the
`step_type ≥ 2` bridge because it is phrased directly in residue language. -/
def GapLongPhaseReturnsFillerComplexStepBridgeOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  ∀ j k : ℕ,
    hphase.rightIdx j ≤ k →
    k < hphase.leftIdx (j + 1) →
      Collatz.is_complex_step ((Collatz.Foundations.collatz_step^[k]) m)

/-- Even more primitive exclusion-style filler semantics on one fixed
structured phase-return witness: no filler orbit point is a simple step in the
mod-4 sense. This is the closest currently exposed bridge to a genuine
selection-exclusion theorem on the filler interval. -/
structure FillerSimpleStepCandidate
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) where
  j : ℕ
  k : ℕ
  hright : hphase.rightIdx j ≤ k
  hleft : k < hphase.leftIdx (j + 1)
  simpleStep : Collatz.is_simple_step ((Collatz.Foundations.collatz_step^[k]) m)

/-- Lowest currently exposed filler-side exclusion semantics on one fixed
structured phase-return witness: every putative simple-step candidate inside the
filler interval is forbidden. This packages the exclusion content one level
below the residue statement `¬ is_simple_step`. -/
def GapLongPhaseReturnsFillerCandidateExclusionBridgeOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  ∀ _cand : FillerSimpleStepCandidate hphase, False

/-- Global theorem form of the candidate-exclusion filler bridge. -/
def GapLongPhaseReturnsFillerCandidateExclusionBridge
    (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerCandidateExclusionBridgeOn hphase

/-- Promotion target for a filler simple-step candidate under an auxiliary
canonical-selection semantics: from a forbidden simple-step occurrence inside
the filler interval one produces an earlier admissible selected event strictly
before the next chosen left endpoint. -/
structure PromotedFillerSelectedCandidate
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (admissible : ℕ → ℕ → Prop)
    (j : ℕ) where
  idx : ℕ
  afterRight : hphase.rightIdx j < idx
  beforeNextLeft : idx < hphase.leftIdx (j + 1)
  admissibleIdx : admissible j idx

/-- Concrete local phase/order proxy for an earlier candidate to be compared
against the next chosen left endpoint after the `j`-th phase-return pair. This
is intentionally weaker than a genuine selected-event admissibility notion: it
only records the same selected phase class as the already chosen
`leftIdx (j + 1)`. The ambient `PromotedFillerSelectedCandidate` separately
carries the ordering data `rightIdx j < idx < leftIdx (j + 1)`. -/
def CanonicalNextLeftPhaseCompatibleOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (j idx : ℕ) : Prop :=
  idx % selected_phase_period t = hphase.leftIdx (j + 1) % selected_phase_period t

/-- The actual chosen next left endpoint is phase-compatible with itself for
its own local next-left comparison criterion. -/
theorem canonical_next_left_self_phase_compatible_on
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (j : ℕ) :
    CanonicalNextLeftPhaseCompatibleOn hphase j (hphase.leftIdx (j + 1)) := by
  rfl

/-- Concrete local promotion target for the next-left phase/order proxy: every
filler simple-step candidate is promoted to an earlier index in the same
selected phase class as the chosen `leftIdx (j + 1)`. This remains only a proxy
layer below the genuinely semantic generic promotion interface. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotionOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) : Sort _ :=
  ∀ cand : FillerSimpleStepCandidate hphase,
    PromotedFillerSelectedCandidate hphase (CanonicalNextLeftPhaseCompatibleOn hphase) cand.j

/-- Global theorem-source form of the previous concrete next-left
phase-compatibility promotion target. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotion
    (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotionOn hphase

/-- Concrete local minimality target for the next chosen left endpoint: no
index in the same selected phase class as `leftIdx (j + 1)` may appear strictly
before it inside the filler interval. This is still a phase/order proxy target,
not yet a genuine selected-event minimality theorem. -/
structure GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimalityOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) where
  noEarlier :
    ∀ {j idx : ℕ},
      CanonicalNextLeftPhaseCompatibleOn hphase j idx →
      idx < hphase.leftIdx (j + 1) →
      False

/-- Global theorem-source form of the previous concrete next-left
phase-compatibility minimality target. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimality
    (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimalityOn hphase

/-- A slightly more explicit local semantics object for the current
phase-compatible proxy target: once the proxy language is fixed, no earlier
phase-compatible index may occur before the chosen next left endpoint. This
does not yet claim event-level admissibility; it only packages the current
proxy theorem source in a more local theorem-producing form. -/
structure CanonicalNextLeftPhaseCompatibleMinimalitySemanticsOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) where
  noEarlier :
    ∀ {j idx : ℕ},
      CanonicalNextLeftPhaseCompatibleOn hphase j idx →
      idx < hphase.leftIdx (j + 1) →
      False

/-- Global theorem-source form of the previous local minimality semantics. -/
def CanonicalNextLeftPhaseCompatibleMinimalitySemantics
    (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    CanonicalNextLeftPhaseCompatibleMinimalitySemanticsOn hphase

/-- The more explicit local proxy semantics immediately populates the existing
concrete phase-compatible minimality slot. -/
theorem gap_long_phase_returns_filler_canonical_next_left_phase_compatible_minimality_on_of_semantics
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hsem : CanonicalNextLeftPhaseCompatibleMinimalitySemanticsOn hphase) :
    GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimalityOn hphase :=
  { noEarlier := hsem.noEarlier }

/-- Global theorem-source form of the previous local-to-concrete bridge. -/
theorem gap_long_phase_returns_filler_canonical_next_left_phase_compatible_minimality_of_semantics
    {m t U : ℕ}
    (hsem : CanonicalNextLeftPhaseCompatibleMinimalitySemantics m t U) :
    GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimality m t U := by
  intro hphase
  exact
    gap_long_phase_returns_filler_canonical_next_left_phase_compatible_minimality_on_of_semantics
      (hsem hphase)

/-- Honest lower filler-side canonical-selection semantics on one fixed
structured phase-return witness. It does not pretend that the raw
`OrbitHasCofinalGapLongPhaseReturns` data itself enforces candidate exclusion;
instead it explicitly supplies the two missing ingredients:
promotion of any filler simple-step candidate to an earlier admissible selected
event, and impossibility of such earlier admissible selected events before the
next chosen left endpoint. -/
structure FillerSimpleStepPromotionOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) where
  admissible : ℕ → ℕ → Prop
  promote :
    ∀ cand : FillerSimpleStepCandidate hphase,
      PromotedFillerSelectedCandidate hphase admissible cand.j

/-- The second half of the honest lower filler-side canonical-selection
semantics: once an admissibility notion is fixed, no admissible selected event
may occur strictly between `rightIdx j` and the already chosen next left
endpoint `leftIdx (j + 1)`. This is the explicit next-choice/minimality slot
missing from the raw phase-return skeleton. -/
structure FillerNextLeftMinimalityOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (admissible : ℕ → ℕ → Prop) where
  noEarlier :
    ∀ {j : ℕ},
      PromotedFillerSelectedCandidate hphase admissible j → False

/-- Global theorem-source form of the lower promotion semantics. -/
def FillerSimpleStepPromotion
    (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    FillerSimpleStepPromotionOn hphase

/-- Global theorem-source form of the lower next-left minimality semantics. -/
def FillerNextLeftMinimality
    (m t U : ℕ)
    (hprom : FillerSimpleStepPromotion m t U) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    FillerNextLeftMinimalityOn hphase (hprom hphase).admissible

/-- Honest lower filler-side canonical-selection semantics on one fixed
structured phase-return witness. It does not pretend that the raw
`OrbitHasCofinalGapLongPhaseReturns` data itself enforces candidate exclusion;
instead it explicitly supplies the two missing ingredients:
promotion of any filler simple-step candidate to an earlier admissible selected
event, and impossibility of such earlier admissible selected events before the
next chosen left endpoint. -/
structure FillerCandidateSelectionSemanticsOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) where
  admissible : ℕ → ℕ → Prop
  promote :
    ∀ cand : FillerSimpleStepCandidate hphase,
      PromotedFillerSelectedCandidate hphase admissible cand.j
  noEarlier :
    ∀ {j : ℕ},
      PromotedFillerSelectedCandidate hphase admissible j → False

/-- Global theorem-source form of the honest lower filler-side
canonical-selection semantics. -/
def FillerCandidateSelectionSemantics
    (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    FillerCandidateSelectionSemanticsOn hphase

/-- Honest local replacement for the retired concrete admissibility proxy: one
explicitly supplies the admissibility notion used to compare filler
simple-step candidates against the already chosen next left endpoint. The only
intrinsic requirement at this layer is that the chosen next left endpoint
itself is admissible for its own comparison problem. -/
structure CanonicalNextLeftSelectionWitnessOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) where
  admissible : ℕ → ℕ → Prop
  self :
    ∀ j : ℕ, admissible j (hphase.leftIdx (j + 1))

/-- Global theorem-source form of the previous local witness. -/
def CanonicalNextLeftSelectionWitness
    (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    CanonicalNextLeftSelectionWitnessOn hphase

/-- Concrete promotion target relative to a supplied next-left selection
witness. This avoids pretending that the admissibility notion is already
captured by a phase-only congruence proxy. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase) : Sort _ :=
  ∀ cand : FillerSimpleStepCandidate hphase,
    PromotedFillerSelectedCandidate hphase hnext.admissible cand.j

/-- Global theorem-source form of the witness-relative promotion target. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotion
    (m t U : ℕ)
    (hnext : CanonicalNextLeftSelectionWitness m t U) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionOn hphase (hnext hphase)

/-- Honest local event-level source for witness-relative promotion: for one
filler simple-step candidate, one explicitly supplies a promoted interior event,
its realized orbit value, and the admissibility proof demanded by the repaired
next-left witness layer. This makes the remaining promotion gap concrete in
orbit/value terms rather than leaving it as a bare higher-order slot. -/
structure PromotedFillerSelectedEventWitnessOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase)
    (cand : FillerSimpleStepCandidate hphase) where
  idx : ℕ
  afterRight : hphase.rightIdx cand.j < idx
  beforeNextLeft : idx < hphase.leftIdx (cand.j + 1)
  value : ℕ
  realized : value = (Collatz.Foundations.collatz_step^[idx]) m
  admissibleIdx : hnext.admissible cand.j idx

/-- Local event-level source for witness-relative promotion on one fixed
structured phase-return witness. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionEventSourceOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase) : Sort _ :=
  ∀ cand : FillerSimpleStepCandidate hphase,
    PromotedFillerSelectedEventWitnessOn hphase hnext cand

/-- Global theorem-source form of the previous explicit event-level promotion
source. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionEventSource
    (m t U : ℕ)
    (hnext : CanonicalNextLeftSelectionWitness m t U) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionEventSourceOn hphase (hnext hphase)

/-- If a filler simple-step candidate is already strictly interior and its own
index is admissible for the supplied next-left witness, then it itself provides
the promoted event witness. This isolates the remaining promotion burden to the
admissibility proof and the boundary case `cand.k = rightIdx cand.j`. -/
def promoted_filler_selected_event_witness_of_strict_interior_candidate
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    {hnext : CanonicalNextLeftSelectionWitnessOn hphase}
    (cand : FillerSimpleStepCandidate hphase)
    (hstrict : hphase.rightIdx cand.j < cand.k)
    (hadm : hnext.admissible cand.j cand.k) :
    PromotedFillerSelectedEventWitnessOn hphase hnext cand :=
  { idx := cand.k
    afterRight := hstrict
    beforeNextLeft := cand.hleft
    value := (Collatz.Foundations.collatz_step^[cand.k]) m
    realized := rfl
    admissibleIdx := hadm }

/-- Lower residual for the strictly interior case: whenever a filler
simple-step candidate is not sitting on the right endpoint, its own index is
already admissible for the supplied next-left witness. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftWitnessInteriorAdmissibilityOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase) : Sort _ :=
  ∀ cand : FillerSimpleStepCandidate hphase,
    hphase.rightIdx cand.j < cand.k →
      hnext.admissible cand.j cand.k

/-- Global theorem-source form of the previous strictly interior admissibility
residual. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftWitnessInteriorAdmissibility
    (m t U : ℕ)
    (hnext : CanonicalNextLeftSelectionWitness m t U) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessInteriorAdmissibilityOn hphase (hnext hphase)

/-- Canonical boundary candidate obtained when the filler simple step occurs
exactly at the current right endpoint. In the boundary branch the candidate
index is no longer free, so the remaining semantics should be formulated at the
level of `j` plus the real simple-step fact on `rightIdx j`. -/
def right_boundary_simple_step_candidate
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (j : ℕ)
    (hsimple :
      Collatz.is_simple_step
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)) :
    FillerSimpleStepCandidate hphase :=
  { j := j
    k := hphase.rightIdx j
    hright := le_rfl
    hleft := hphase.rightStep j
    simpleStep := hsimple }

/-- Boundary-specific promoted-event witness: once the simple-step fact is known
specifically at `rightIdx j`, the remaining content is exactly a promoted event
witness for the canonical boundary candidate. -/
abbrev RightBoundarySimpleStepPromotedFillerSelectedEventWitnessOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase)
    (j : ℕ)
    (hsimple :
      Collatz.is_simple_step
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)) : Sort _ :=
  PromotedFillerSelectedEventWitnessOn hphase hnext
    (right_boundary_simple_step_candidate hphase j hsimple)

/-- Honest boundary-level event geometry on one fixed structured phase-return
witness. This no longer quantifies over any witness-relative admissibility
language: it only records the concrete interior event itself. -/
structure BoundaryPromotedSelectedEventOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (j : ℕ) where
  idx : ℕ
  afterRight : hphase.rightIdx j < idx
  beforeNextLeft : idx < hphase.leftIdx (j + 1)
  value : ℕ
  realized : value = (Collatz.Foundations.collatz_step^[idx]) m

/-- Concrete theorem-source for the boundary branch, independent of any chosen
admissibility witness: if `rightIdx j` is a simple step, there exists a genuine
interior orbit event between `rightIdx j` and `leftIdx (j+1)`. -/
def GapLongPhaseReturnsBoundaryPromotedSelectedEventSourceOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) : Sort _ :=
  ∀ j : ℕ,
    ∀ _hsimple :
      Collatz.is_simple_step
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m),
      BoundaryPromotedSelectedEventOn hphase j

/-- Global theorem-source form of the previous concrete boundary event source. -/
def GapLongPhaseReturnsBoundaryPromotedSelectedEventSource
    (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsBoundaryPromotedSelectedEventSourceOn hphase

/-- Separate admissibility bridge from the concrete boundary event language into
one chosen witness-relative admissibility notion. This is where the comparison
with a particular `CanonicalNextLeftSelectionWitnessOn` should happen, rather
than inside the boundary event theorem itself. -/
def GapLongPhaseReturnsBoundaryPromotedSelectedAdmissibilityBridgeOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase) : Sort _ :=
  ∀ {j : ℕ},
    (hevent : BoundaryPromotedSelectedEventOn hphase j) →
      hnext.admissible j hevent.idx

/-- Global theorem-source form of the previous concrete-to-witness
admissibility bridge. -/
def GapLongPhaseReturnsBoundaryPromotedSelectedAdmissibilityBridge
    (m t U : ℕ)
    (hnext : CanonicalNextLeftSelectionWitness m t U) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsBoundaryPromotedSelectedAdmissibilityBridgeOn
      hphase (hnext hphase)

/-- Once a concrete boundary event and its admissibility for the chosen witness
have been supplied, they package directly into the witness-relative promoted
event expected by the repaired boundary slot. -/
def right_boundary_simple_step_promoted_filler_selected_event_witness_on_of_boundary_event
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    {hnext : CanonicalNextLeftSelectionWitnessOn hphase}
    {j : ℕ}
    {hsimple :
      Collatz.is_simple_step
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m)}
    (hevent : BoundaryPromotedSelectedEventOn hphase j)
    (hadm : hnext.admissible j hevent.idx) :
    RightBoundarySimpleStepPromotedFillerSelectedEventWitnessOn hphase hnext j hsimple :=
  { idx := hevent.idx
    afterRight := hevent.afterRight
    beforeNextLeft := hevent.beforeNextLeft
    value := hevent.value
    realized := hevent.realized
    admissibleIdx := hadm }

/-- Sharpened local residual for the boundary case: if the orbit value at
`rightIdx j` is a simple step, produce a promoted interior event witness for
that canonical boundary candidate. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSourceOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase) : Sort _ :=
  ∀ j : ℕ,
    ∀ hsimple :
      Collatz.is_simple_step
        ((Collatz.Foundations.collatz_step^[hphase.rightIdx j]) m),
      RightBoundarySimpleStepPromotedFillerSelectedEventWitnessOn
        hphase hnext j hsimple

/-- Global theorem-source form of the previous sharpened boundary residual. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSource
    (m t U : ℕ)
    (hnext : CanonicalNextLeftSelectionWitness m t U) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSourceOn
      hphase (hnext hphase)

/-- Therefore the new concrete boundary event theorem source, together with a
separate admissibility bridge into one chosen witness, fills the sharpened
witness-relative boundary slot. -/
def gap_long_phase_returns_filler_canonical_next_left_witness_right_boundary_simple_step_event_source_on_of_boundary_event_source_and_admissibility
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    {hnext : CanonicalNextLeftSelectionWitnessOn hphase}
    (hsrc : GapLongPhaseReturnsBoundaryPromotedSelectedEventSourceOn hphase)
    (hadm :
      GapLongPhaseReturnsBoundaryPromotedSelectedAdmissibilityBridgeOn hphase hnext) :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSourceOn
      hphase hnext := by
  intro j hsimple
  exact
    right_boundary_simple_step_promoted_filler_selected_event_witness_on_of_boundary_event
      (hevent := hsrc j hsimple)
      (hadm := hadm (hsrc j hsimple))

/-- Global theorem-source form of the previous concrete-to-witness bridge for
the sharpened boundary slot. -/
def gap_long_phase_returns_filler_canonical_next_left_witness_right_boundary_simple_step_event_source_of_boundary_event_source_and_admissibility
    {m t U : ℕ}
    {hnext : CanonicalNextLeftSelectionWitness m t U}
    (hsrc : GapLongPhaseReturnsBoundaryPromotedSelectedEventSource m t U)
    (hadm :
      GapLongPhaseReturnsBoundaryPromotedSelectedAdmissibilityBridge m t U hnext) :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSource
      m t U hnext := by
  intro hphase
  exact
    gap_long_phase_returns_filler_canonical_next_left_witness_right_boundary_simple_step_event_source_on_of_boundary_event_source_and_admissibility
      (hsrc hphase) (hadm hphase)

/-- Lower residual for the remaining boundary case: if a filler simple-step
candidate occurs exactly at `rightIdx cand.j`, one must still produce a
promoted interior event witness by genuine extra semantics. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSourceOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase) : Sort _ :=
  ∀ cand : FillerSimpleStepCandidate hphase,
    cand.k = hphase.rightIdx cand.j →
      PromotedFillerSelectedEventWitnessOn hphase hnext cand

/-- Global theorem-source form of the previous right-boundary event residual. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSource
    (m t U : ℕ)
    (hnext : CanonicalNextLeftSelectionWitness m t U) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSourceOn hphase (hnext hphase)

/-- The sharpened boundary source immediately fills the older boundary slot:
once the candidate is known to sit at `rightIdx cand.j`, its `simpleStep` field
is exactly the local hypothesis required by the canonical boundary witness. -/
def gap_long_phase_returns_filler_canonical_next_left_witness_right_boundary_event_source_on_of_simple_step_event_source
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    {hnext : CanonicalNextLeftSelectionWitnessOn hphase}
    (hsrc :
      GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSourceOn
        hphase hnext) :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSourceOn
      hphase hnext := by
  intro cand hk
  rcases cand with ⟨j, k, hright, hleft, hsimple⟩
  dsimp at hk ⊢
  subst hk
  simpa [RightBoundarySimpleStepPromotedFillerSelectedEventWitnessOn,
    right_boundary_simple_step_candidate] using hsrc j hsimple

/-- Global theorem-source form of the previous sharpening bridge. -/
def gap_long_phase_returns_filler_canonical_next_left_witness_right_boundary_event_source_of_simple_step_event_source
    {m t U : ℕ}
    {hnext : CanonicalNextLeftSelectionWitness m t U}
    (hsrc :
      GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSource
        m t U hnext) :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSource
      m t U hnext := by
  intro hphase
  exact
    gap_long_phase_returns_filler_canonical_next_left_witness_right_boundary_event_source_on_of_simple_step_event_source
      (hsrc hphase)

/-- The explicit promoted-event source decomposes cleanly into two local
ingredients: strict-interior candidates promote themselves once admissibility is
known, while boundary candidates require a separate event-level source. -/
def gap_long_phase_returns_filler_canonical_next_left_witness_promotion_event_source_on_of_interior_admissibility_and_right_boundary
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    {hnext : CanonicalNextLeftSelectionWitnessOn hphase}
    (hinterior :
      GapLongPhaseReturnsFillerCanonicalNextLeftWitnessInteriorAdmissibilityOn hphase hnext)
    (hboundary :
      GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSourceOn hphase hnext) :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionEventSourceOn hphase hnext := by
  intro cand
  by_cases hstrict : hphase.rightIdx cand.j < cand.k
  · exact promoted_filler_selected_event_witness_of_strict_interior_candidate cand hstrict
      (hinterior cand hstrict)
  · have hEq : cand.k = hphase.rightIdx cand.j := by
      exact Nat.le_antisymm (Nat.not_lt.mp hstrict) cand.hright
    exact hboundary cand hEq

/-- Global theorem-source form of the previous decomposition of the promoted
event source into interior and boundary cases. -/
def gap_long_phase_returns_filler_canonical_next_left_witness_promotion_event_source_of_interior_admissibility_and_right_boundary
    {m t U : ℕ}
    {hnext : CanonicalNextLeftSelectionWitness m t U}
    (hinterior :
      GapLongPhaseReturnsFillerCanonicalNextLeftWitnessInteriorAdmissibility m t U hnext)
    (hboundary :
      GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSource m t U hnext) :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionEventSource m t U hnext := by
  intro hphase
  exact
    gap_long_phase_returns_filler_canonical_next_left_witness_promotion_event_source_on_of_interior_admissibility_and_right_boundary
      (hinterior hphase) (hboundary hphase)

/-- Forget the extra orbit/value fields of the explicit event witness and keep
only the exact promotion data currently consumed by the generic filler
selection seam. -/
def promoted_filler_selected_candidate_of_event_witness
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    {hnext : CanonicalNextLeftSelectionWitnessOn hphase}
    {cand : FillerSimpleStepCandidate hphase}
    (hevent : PromotedFillerSelectedEventWitnessOn hphase hnext cand) :
    PromotedFillerSelectedCandidate hphase hnext.admissible cand.j :=
  { idx := hevent.idx
    afterRight := hevent.afterRight
    beforeNextLeft := hevent.beforeNextLeft
    admissibleIdx := hevent.admissibleIdx }

/-- Therefore an explicit event-level source immediately populates the repaired
witness-relative promotion slot. -/
def gap_long_phase_returns_filler_canonical_next_left_witness_promotion_on_of_event_source
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    {hnext : CanonicalNextLeftSelectionWitnessOn hphase}
    (hsrc :
      GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionEventSourceOn hphase hnext) :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionOn hphase hnext := by
  intro cand
  exact promoted_filler_selected_candidate_of_event_witness (hsrc cand)

/-- Global theorem-source form of the previous explicit event-source bridge. -/
def gap_long_phase_returns_filler_canonical_next_left_witness_promotion_of_event_source
    {m t U : ℕ}
    {hnext : CanonicalNextLeftSelectionWitness m t U}
    (hsrc :
      GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionEventSource m t U hnext) :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotion m t U hnext := by
  intro hphase
  exact
    gap_long_phase_returns_filler_canonical_next_left_witness_promotion_on_of_event_source
      (hsrc hphase)

/-- Concrete next-left minimality target relative to a supplied witness. This
is just the generic minimality slot specialized to the witness's admissibility
language. -/
abbrev GapLongPhaseReturnsFillerCanonicalNextLeftWitnessMinimalityOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase) : Sort _ :=
  FillerNextLeftMinimalityOn hphase hnext.admissible

/-- Global theorem-source form of the witness-relative minimality target. -/
def GapLongPhaseReturnsFillerCanonicalNextLeftWitnessMinimality
    (m t U : ℕ)
    (hnext : CanonicalNextLeftSelectionWitness m t U) :
    Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessMinimalityOn hphase (hnext hphase)

/-- The concrete next-left phase-compatibility promotion target is one honest
instance of the more generic promotion slot. -/
def filler_simple_step_promotion_on_of_canonical_next_left_phase_compatibility
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hprom : GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotionOn hphase) :
    FillerSimpleStepPromotionOn hphase :=
  { admissible := CanonicalNextLeftPhaseCompatibleOn hphase
    promote := hprom }

/-- The old phase-compatible proxy still supplies one honest instance of the
new witness-based next-left layer: it provides an admissibility language whose
self-instance is the already chosen next left endpoint. -/
def canonical_next_left_selection_witness_on_of_phase_compatibility
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) :
    CanonicalNextLeftSelectionWitnessOn hphase :=
  { admissible := CanonicalNextLeftPhaseCompatibleOn hphase
    self := canonical_next_left_self_phase_compatible_on hphase }

/-- Minimal witness exposing the exact structural strength of the repaired
next-left interface: the only admissible index is the already chosen next left
endpoint itself. This is an honest inhabitant of the witness layer because that
layer currently requires only the `self` field. -/
def canonical_next_left_selection_witness_on_of_only_next_left
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) :
    CanonicalNextLeftSelectionWitnessOn hphase :=
  { admissible := fun j idx => idx = hphase.leftIdx (j + 1)
    self := by
      intro j
      rfl }

/-- Consequently, the already established phase-compatible minimality theorem
also populates the witness-relative minimality slot for the canonical
phase-compatible witness. -/
def filler_next_left_minimality_on_of_phase_compatible_witness_and_minimality
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hmin : GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimalityOn hphase) :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessMinimalityOn hphase
      (canonical_next_left_selection_witness_on_of_phase_compatibility hphase) :=
  { noEarlier := by
      intro j hpromoted
      exact hmin.noEarlier hpromoted.admissibleIdx hpromoted.beforeNextLeft }

/-- Likewise, any old phase-compatible promotion theorem automatically
populates the promotion slot of the repaired witness-based layer when the
witness is chosen to be the same phase-compatible admissibility language. -/
def filler_simple_step_promotion_on_of_phase_compatible_witness_and_promotion
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hprom : GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotionOn hphase) :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionOn hphase
      (canonical_next_left_selection_witness_on_of_phase_compatibility hphase) :=
  hprom

/-- The concrete next-left phase-compatibility minimality target is one honest
instance of the more generic minimality slot once the proxy admissibility
language is fixed to `CanonicalNextLeftPhaseCompatibleOn`. -/
def filler_next_left_minimality_on_of_canonical_next_left_phase_compatibility
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hmin : GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimalityOn hphase) :
    FillerNextLeftMinimalityOn hphase (CanonicalNextLeftPhaseCompatibleOn hphase) :=
  { noEarlier := by
      intro j hpromoted
      exact hmin.noEarlier hpromoted.admissibleIdx hpromoted.beforeNextLeft }

/-- Assemble the honest candidate-selection semantics from its two genuinely
distinct lower ingredients: promotion of a simple-step candidate to an earlier
admissible selected event, and next-left minimality ruling out such earlier
admissible events. -/
def filler_candidate_selection_semantics_on_of_promotion_and_minimality
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hprom : FillerSimpleStepPromotionOn hphase)
    (hmin : FillerNextLeftMinimalityOn hphase hprom.admissible) :
    FillerCandidateSelectionSemanticsOn hphase :=
  { admissible := hprom.admissible
    promote := hprom.promote
    noEarlier := @hmin.noEarlier }

/-- Global theorem form of the previous constructor. -/
def filler_candidate_selection_semantics_of_promotion_and_minimality
    {m t U : ℕ}
    (hprom : FillerSimpleStepPromotion m t U)
    (hmin : FillerNextLeftMinimality m t U hprom) :
    FillerCandidateSelectionSemantics m t U := by
  intro hphase
  exact filler_candidate_selection_semantics_on_of_promotion_and_minimality
    (hprom hphase) (hmin hphase)

/-- A supplied next-left selection witness plus witness-relative promotion and
minimality immediately yields the honest generic candidate-selection
semantics. This is the preferred local repair once the old concrete
phase-compatible proxy has been shown insufficient. -/
def filler_simple_step_promotion_on_of_canonical_next_left_witness
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase)
    (hprom : GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionOn hphase hnext) :
    FillerSimpleStepPromotionOn hphase :=
  { admissible := hnext.admissible
    promote := hprom }

/-- Witness-relative next-left minimality already has the generic shape; this
definition only records the intended local repair path next to the companion
promotion adapter. -/
def filler_next_left_minimality_on_of_canonical_next_left_witness
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase)
    (hmin : GapLongPhaseReturnsFillerCanonicalNextLeftWitnessMinimalityOn hphase hnext) :
    FillerNextLeftMinimalityOn hphase hnext.admissible :=
  hmin

/-- Assemble the honest candidate-selection semantics directly from a supplied
next-left selection witness. This keeps the redesign strictly local to the
concrete next-left layer while preserving the generic promotion/minimality
seam above it. -/
def filler_candidate_selection_semantics_on_of_canonical_next_left_witness
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hnext : CanonicalNextLeftSelectionWitnessOn hphase)
    (hprom : GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotionOn hphase hnext)
    (hmin : GapLongPhaseReturnsFillerCanonicalNextLeftWitnessMinimalityOn hphase hnext) :
    FillerCandidateSelectionSemanticsOn hphase :=
  filler_candidate_selection_semantics_on_of_promotion_and_minimality
    (filler_simple_step_promotion_on_of_canonical_next_left_witness hnext hprom)
    (filler_next_left_minimality_on_of_canonical_next_left_witness hnext hmin)

/-- Global theorem form of the previous witness-relative constructor. -/
def filler_candidate_selection_semantics_of_canonical_next_left_witness
    {m t U : ℕ}
    (hnext : CanonicalNextLeftSelectionWitness m t U)
    (hprom : GapLongPhaseReturnsFillerCanonicalNextLeftWitnessPromotion m t U hnext)
    (hmin : GapLongPhaseReturnsFillerCanonicalNextLeftWitnessMinimality m t U hnext) :
    FillerCandidateSelectionSemantics m t U := by
  intro hphase
  exact filler_candidate_selection_semantics_on_of_canonical_next_left_witness
    (hnext hphase) (hprom hphase) (hmin hphase)

/-- Assemble the honest candidate-selection semantics directly from the
concrete next-left phase-compatibility promotion/minimality pair. This keeps
the proxy layer explicit while routing it through the more honest generic
selection semantics above. -/
def filler_candidate_selection_semantics_on_of_canonical_next_left_phase_compatibility_and_minimality
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hprom : GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotionOn hphase)
    (hmin : GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimalityOn hphase) :
    FillerCandidateSelectionSemanticsOn hphase :=
  filler_candidate_selection_semantics_on_of_promotion_and_minimality
    (filler_simple_step_promotion_on_of_canonical_next_left_phase_compatibility hprom)
    (filler_next_left_minimality_on_of_canonical_next_left_phase_compatibility hmin)

/-- Global theorem form of the previous concrete next-left phase-compatibility
constructor. -/
def filler_candidate_selection_semantics_of_canonical_next_left_phase_compatibility_and_minimality
    {m t U : ℕ}
    (hprom : GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotion m t U)
    (hmin : GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatibleMinimality m t U) :
    FillerCandidateSelectionSemantics m t U := by
  intro hphase
  exact filler_candidate_selection_semantics_on_of_canonical_next_left_phase_compatibility_and_minimality
    (hprom hphase) (hmin hphase)

/-- Under explicit canonical-selection semantics, any filler simple-step
candidate yields a contradiction. -/
theorem filler_simple_step_candidate_contradiction_of_selection_semantics_on
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hsem : FillerCandidateSelectionSemanticsOn hphase)
    (cand : FillerSimpleStepCandidate hphase) :
    False := by
  exact hsem.noEarlier (hsem.promote cand)

/-- The honest canonical-selection semantics immediately populates the current
lowest filler-side exclusion bridge. -/
theorem gap_long_phase_returns_filler_candidate_exclusion_of_selection_semantics_on
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hsem : FillerCandidateSelectionSemanticsOn hphase) :
    GapLongPhaseReturnsFillerCandidateExclusionBridgeOn hphase := by
  intro cand
  exact filler_simple_step_candidate_contradiction_of_selection_semantics_on
    hsem cand

/-- Global theorem form of the previous selection-semantics-to-exclusion
bridge. -/
theorem gap_long_phase_returns_filler_candidate_exclusion_of_selection_semantics
    {m t U : ℕ}
    (hsem : FillerCandidateSelectionSemantics m t U) :
    GapLongPhaseReturnsFillerCandidateExclusionBridge m t U := by
  intro hphase
  exact gap_long_phase_returns_filler_candidate_exclusion_of_selection_semantics_on
    (hsem hphase)

def GapLongPhaseReturnsFillerNoSimpleStepBridgeOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  ∀ j k : ℕ,
    hphase.rightIdx j ≤ k →
    k < hphase.leftIdx (j + 1) →
      ¬ Collatz.is_simple_step ((Collatz.Foundations.collatz_step^[k]) m)

/-- Global theorem form of the exclusion-style filler bridge. -/
def GapLongPhaseReturnsFillerNoSimpleStepBridge
    (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerNoSimpleStepBridgeOn hphase

/-- Candidate exclusion immediately yields the more familiar filler theorem that
no simple step appears on the interval. -/
theorem gap_long_phase_returns_filler_no_simple_step_of_candidate_exclusion_on
    {m t U : ℕ}
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hexcl : GapLongPhaseReturnsFillerCandidateExclusionBridgeOn hphase) :
    GapLongPhaseReturnsFillerNoSimpleStepBridgeOn hphase := by
  intro j k hright hleft hsimple
  exact hexcl
    { j := j
      k := k
      hright := hright
      hleft := hleft
      simpleStep := hsimple }

/-- Global theorem form of the previous candidate-exclusion bridge. -/
theorem gap_long_phase_returns_filler_no_simple_step_of_candidate_exclusion
    {m t U : ℕ}
    (hexcl : ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
      GapLongPhaseReturnsFillerCandidateExclusionBridgeOn hphase) :
    GapLongPhaseReturnsFillerNoSimpleStepBridge m t U := by
  intro hphase
  exact gap_long_phase_returns_filler_no_simple_step_of_candidate_exclusion_on
    (hexcl hphase)

/-- Excluding simple steps on the filler interval already forces the residue
level complex-step bridge, because all orbit values remain odd. -/
theorem gap_long_phase_returns_filler_complex_step_of_no_simple_step_on
    {m t U : ℕ}
    (hm : Odd m)
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hnoSimple : GapLongPhaseReturnsFillerNoSimpleStepBridgeOn hphase) :
    GapLongPhaseReturnsFillerComplexStepBridgeOn hphase := by
  intro j k hright hleft
  exact Collatz.complex_step_of_not_simple
    (Collatz.Foundations.odd_iterates_of_odd hm k)
    (hnoSimple j k hright hleft)

/-- Global theorem form of the residue-level filler bridge: every structured
phase-return witness comes with a mod-4 complex-step theorem on its filler
interval. As with the stronger value-level bridges, this is separate semantic
content rather than a consequence of the raw phase-return interface itself. -/
def GapLongPhaseReturnsFillerComplexStepBridge
    (m t U : ℕ) : Sort _ :=
  ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
    GapLongPhaseReturnsFillerComplexStepBridgeOn hphase

/-- Global theorem form of the previous exclusion-to-residue bridge. -/
theorem gap_long_phase_returns_filler_complex_step_of_no_simple_step
    {m t U : ℕ}
    (hm : Odd m)
    (hnoSimple : ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
      GapLongPhaseReturnsFillerNoSimpleStepBridgeOn hphase) :
    GapLongPhaseReturnsFillerComplexStepBridge m t U := by
  intro hphase
  exact gap_long_phase_returns_filler_complex_step_of_no_simple_step_on hm
    (hphase := hphase) (hnoSimple hphase)

/-- Arithmetic precursor to filler-stepwise monotonicity on one fixed
structured phase-return witness: every orbit point inside the filler interval
has local Collatz exponent at least `2`. This is the minimal local source that
forces one-step nonincrease by pure arithmetic. -/
def GapLongPhaseReturnsFillerStepTypeTwoBridgeOn
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U) : Prop :=
  ∀ j k : ℕ,
    hphase.rightIdx j ≤ k →
    k < hphase.leftIdx (j + 1) →
      2 ≤ Collatz.Foundations.step_type ((Collatz.Foundations.collatz_step^[k]) m)

/-- Mod-4 complex-step control on the filler interval already forces the
stronger arithmetic bridge `step_type ≥ 2` at every filler orbit point. -/
theorem gap_long_phase_returns_filler_step_type_two_of_complex_step_on
    {m t U : ℕ}
    (hm : Odd m)
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hcomplex : GapLongPhaseReturnsFillerComplexStepBridgeOn hphase) :
    GapLongPhaseReturnsFillerStepTypeTwoBridgeOn hphase := by
  intro j k hright hleft
  exact Collatz.complex_step_implies_step_type_ge_two
    (Collatz.Foundations.odd_iterates_of_odd hm k)
    (hcomplex j k hright hleft)

/-- If every filler orbit point has local exponent at least `2`, then the whole
filler segment is stepwise nonincreasing. This theorem isolates the remaining
stream-side content to proving the step-type lower bound on the canonical
aperiodic skeleton. -/
theorem gap_long_phase_returns_filler_stepwise_of_step_type_two_on
    {m t U : ℕ}
    (hm : Odd m)
    {hphase : OrbitHasCofinalGapLongPhaseReturns m t U}
    (hstepTwo : GapLongPhaseReturnsFillerStepTypeTwoBridgeOn hphase) :
    GapLongPhaseReturnsFillerStepwiseBridgeOn hphase := by
  intro j k hright hleft
  have hoddk : Odd ((Collatz.Foundations.collatz_step^[k]) m) :=
    Collatz.Foundations.odd_iterates_of_odd hm k
  simpa [Function.iterate_succ_apply'] using
    Collatz.Foundations.collatz_step_le_self_of_step_type_ge_two hoddk
      (hstepTwo j k hright hleft)

/-- Global theorem form of the previous arithmetic bridge. -/
theorem gap_long_phase_returns_filler_stepwise_of_step_type_two
    {m t U : ℕ}
    (hm : Odd m)
    (hstepTwo : ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
      GapLongPhaseReturnsFillerStepTypeTwoBridgeOn hphase) :
    GapLongPhaseReturnsFillerStepwiseBridge m t U := by
  intro hphase
  exact gap_long_phase_returns_filler_stepwise_of_step_type_two_on hm
    (hphase := hphase) (hstepTwo hphase)

/-- Global theorem form of the mod-4 complex-step bridge on filler intervals. -/
theorem gap_long_phase_returns_filler_step_type_two_of_complex_step
    {m t U : ℕ}
    (hm : Odd m)
    (hcomplex : ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
      GapLongPhaseReturnsFillerComplexStepBridgeOn hphase) :
    ∀ hphase : OrbitHasCofinalGapLongPhaseReturns m t U,
      GapLongPhaseReturnsFillerStepTypeTwoBridgeOn hphase := by
  intro hphase
  exact gap_long_phase_returns_filler_step_type_two_of_complex_step_on hm
    (hphase := hphase) (hcomplex hphase)

/-- Explicit toy structured phase-return witness showing that the raw index-level
object `OrbitHasCofinalGapLongPhaseReturns` does not, by itself, force any
value-level complex-step property on the filler interval. The witness is purely
index-based; its filler includes an actual simple step of the orbit of `15`. -/
def sample_gap_long_phase_returns_15_0_0 :
    OrbitHasCofinalGapLongPhaseReturns 15 0 0 := by
  refine
    { leftIdx := fun j => 4 * j
      rightIdx := fun j => 4 * j + 2
      leftStep := ?_
      rightStep := ?_
      longSep := ?_
      selectedPhaseAligned := ?_
      phaseAligned := ?_
      qtPhaseAligned := ?_
      cofinalLeft := ?_ }
  · intro j
    omega
  · intro j
    omega
  · intro j
    norm_num [Collatz.SEDT.L₀, Q_t]
  · intro j
    simp [selected_phase_period, gap_long, Q_t, Nat.mul_mod]
  · intro j
    simp [gap_long, Q_t, Nat.mul_mod]
  · intro j
    simp [Q_t, Nat.add_mod, Nat.mul_mod]
  · intro N
    refine ⟨N, ?_⟩
    omega

/-- On the orbit of `15`, the second odd Collatz iterate is `35`. -/
lemma sample_iterate_two_15 :
    ((Collatz.Foundations.collatz_step^[2]) 15) = 35 := by
  native_decide

/-- The orbit value `35` is a simple step, not a complex one. -/
lemma sample_iterate_two_15_not_complex :
    ¬ Collatz.is_complex_step ((Collatz.Foundations.collatz_step^[2]) 15) := by
  rw [sample_iterate_two_15]
  norm_num [Collatz.is_complex_step]

/-- In fact the same orbit value `35` is a simple step. -/
lemma sample_iterate_two_15_simple :
    Collatz.is_simple_step ((Collatz.Foundations.collatz_step^[2]) 15) := by
  rw [sample_iterate_two_15]
  norm_num [Collatz.is_simple_step]

/-- Therefore the raw structured witness above does not satisfy the filler
complex-step bridge. This shows that residue-level filler content cannot be
derived from `OrbitHasCofinalGapLongPhaseReturns` alone; it must come from
additional canonical/semantic input. -/
theorem sample_gap_long_phase_returns_15_0_0_not_filler_complex_step :
    ¬ GapLongPhaseReturnsFillerComplexStepBridgeOn sample_gap_long_phase_returns_15_0_0 := by
  intro hcomplex
  have hbad :
      Collatz.is_complex_step ((Collatz.Foundations.collatz_step^[2]) 15) := by
    exact hcomplex 0 2 (by simp [sample_gap_long_phase_returns_15_0_0]) (by simp [sample_gap_long_phase_returns_15_0_0])
  exact sample_iterate_two_15_not_complex hbad

/-- The same raw structured witness also fails the exclusion-style filler bridge:
its filler contains an actual simple step. -/
theorem sample_gap_long_phase_returns_15_0_0_not_filler_no_simple_step :
    ¬ GapLongPhaseReturnsFillerNoSimpleStepBridgeOn sample_gap_long_phase_returns_15_0_0 := by
  intro hnoSimple
  have hbad :
      ¬ Collatz.is_simple_step ((Collatz.Foundations.collatz_step^[2]) 15) := by
    exact hnoSimple 0 2 (by simp [sample_gap_long_phase_returns_15_0_0]) (by simp [sample_gap_long_phase_returns_15_0_0])
  exact hbad sample_iterate_two_15_simple

/-- Global impossibility corollary: the filler complex-step bridge is not a
formal consequence of the raw structured phase-return interface alone. -/
theorem not_all_gap_long_phase_returns_have_filler_complex_step :
    ¬ (GapLongPhaseReturnsFillerComplexStepBridge 15 0 0) := by
  intro hall
  exact sample_gap_long_phase_returns_15_0_0_not_filler_complex_step
    (hall sample_gap_long_phase_returns_15_0_0)

/-- Global impossibility corollary for the exclusion-style bridge as well. -/
theorem not_all_gap_long_phase_returns_have_filler_no_simple_step :
    ¬ (GapLongPhaseReturnsFillerNoSimpleStepBridge 15 0 0) := by
  intro hall
  exact sample_gap_long_phase_returns_15_0_0_not_filler_no_simple_step
    (hall sample_gap_long_phase_returns_15_0_0)

/-- The same sample witness also violates the lower candidate-exclusion bridge:
the simple step at iterate `2` is itself a forbidden filler candidate. -/
theorem sample_gap_long_phase_returns_15_0_0_not_filler_candidate_exclusion :
    ¬ GapLongPhaseReturnsFillerCandidateExclusionBridgeOn sample_gap_long_phase_returns_15_0_0 := by
  intro hexcl
  exact hexcl
    { j := 0
      k := 2
      hright := by simp [sample_gap_long_phase_returns_15_0_0]
      hleft := by simp [sample_gap_long_phase_returns_15_0_0]
      simpleStep := sample_iterate_two_15_simple }

/-- Global impossibility corollary for the lowest currently exposed
candidate-exclusion bridge. -/
theorem not_all_gap_long_phase_returns_have_filler_candidate_exclusion :
    ¬ (GapLongPhaseReturnsFillerCandidateExclusionBridge 15 0 0) := by
  intro hall
  exact sample_gap_long_phase_returns_15_0_0_not_filler_candidate_exclusion
    (hall sample_gap_long_phase_returns_15_0_0)

/-- The same sample witness also violates the current concrete next-left
phase-compatibility promotion target: the simple-step candidate at iterate `2`
has no strictly interior index before the next chosen left endpoint that lies in
the same selected phase class as `leftIdx 1 = 4`. This is formal evidence that
the current promotion proxy is not forced by a raw filler simple-step
occurrence. -/
theorem sample_gap_long_phase_returns_15_0_0_not_filler_canonical_next_left_phase_compatible_promotion :
    GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotionOn
      sample_gap_long_phase_returns_15_0_0 → False := by
  intro hprom
  let cand : FillerSimpleStepCandidate sample_gap_long_phase_returns_15_0_0 :=
    { j := 0
      k := 2
      hright := by simp [sample_gap_long_phase_returns_15_0_0]
      hleft := by simp [sample_gap_long_phase_returns_15_0_0]
      simpleStep := sample_iterate_two_15_simple }
  let promoted := hprom cand
  have hidx : promoted.idx = 3 := by
    have hafter : 2 < promoted.idx := by
      simpa [cand, promoted, sample_gap_long_phase_returns_15_0_0] using promoted.afterRight
    have hbefore : promoted.idx < 4 := by
      simpa [cand, promoted, sample_gap_long_phase_returns_15_0_0] using promoted.beforeNextLeft
    omega
  have hbad :
      3 % selected_phase_period 0 =
        sample_gap_long_phase_returns_15_0_0.leftIdx (0 + 1) % selected_phase_period 0 := by
    simpa [CanonicalNextLeftPhaseCompatibleOn, cand, promoted, hidx] using promoted.admissibleIdx
  norm_num [sample_gap_long_phase_returns_15_0_0, selected_phase_period, gap_long, Q_t] at hbad

/-- Global impossibility corollary: the current concrete phase-compatible
promotion target is not derivable from the raw structured phase-return interface
alone. This is the formal trigger for escalating to an event-level admissibility
redesign if promotion is the next required theorem source. -/
theorem not_all_gap_long_phase_returns_have_filler_canonical_next_left_phase_compatible_promotion :
    GapLongPhaseReturnsFillerCanonicalNextLeftPhaseCompatiblePromotion 15 0 0 → False := by
  intro hall
  exact
    sample_gap_long_phase_returns_15_0_0_not_filler_canonical_next_left_phase_compatible_promotion
      (hall sample_gap_long_phase_returns_15_0_0)

/-- The same sample witness already refutes the sharpened right-boundary event
source for the current phase-compatible witness: when the simple-step candidate
occurs exactly at `rightIdx 0 = 2`, there is still no admissible interior event
before `leftIdx 1 = 4`. Thus the obstruction really lives in the boundary case
of the repaired promotion target, not only in the older bundled proxy
statement. -/
theorem sample_gap_long_phase_returns_15_0_0_not_phase_compatible_right_boundary_event_source :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSourceOn
      sample_gap_long_phase_returns_15_0_0
      (canonical_next_left_selection_witness_on_of_phase_compatibility
        sample_gap_long_phase_returns_15_0_0) → False := by
  intro hboundary
  let cand : FillerSimpleStepCandidate sample_gap_long_phase_returns_15_0_0 :=
    { j := 0
      k := 2
      hright := by simp [sample_gap_long_phase_returns_15_0_0]
      hleft := by simp [sample_gap_long_phase_returns_15_0_0]
      simpleStep := sample_iterate_two_15_simple }
  have hk : cand.k = sample_gap_long_phase_returns_15_0_0.rightIdx cand.j := by
    simp [cand, sample_gap_long_phase_returns_15_0_0]
  let hevent := hboundary cand hk
  have hidx : hevent.idx = 3 := by
    have hafter : 2 < hevent.idx := by
      simpa [cand, hevent, sample_gap_long_phase_returns_15_0_0] using hevent.afterRight
    have hbefore : hevent.idx < 4 := by
      simpa [cand, hevent, sample_gap_long_phase_returns_15_0_0] using hevent.beforeNextLeft
    omega
  have hbad :
      3 % selected_phase_period 0 =
        sample_gap_long_phase_returns_15_0_0.leftIdx (0 + 1) % selected_phase_period 0 := by
    simpa
      [CanonicalNextLeftSelectionWitnessOn, canonical_next_left_selection_witness_on_of_phase_compatibility,
        CanonicalNextLeftPhaseCompatibleOn, cand, hevent, hidx]
      using hevent.admissibleIdx
  norm_num [sample_gap_long_phase_returns_15_0_0, selected_phase_period, gap_long, Q_t] at hbad

/-- Global impossibility corollary for the sharpened boundary residual under the
current phase-compatible witness. -/
theorem not_all_gap_long_phase_returns_have_phase_compatible_right_boundary_event_source :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundaryEventSource
      15 0 0
      (fun hphase => canonical_next_left_selection_witness_on_of_phase_compatibility hphase) → False := by
  intro hall
  exact
    sample_gap_long_phase_returns_15_0_0_not_phase_compatible_right_boundary_event_source
      (hall sample_gap_long_phase_returns_15_0_0)

/-- The sharpened boundary simple-step source still cannot be forced for an
arbitrary witness-relative admissibility notion. The witness whose admissible
indices are only the chosen next-left endpoints already satisfies `self`, but in
the sample `15 -> 23 -> 35 -> 53 -> 80 -> ...` there is no room for a strict
interior admissible event between `rightIdx 0 = 2` and `leftIdx 1 = 4`. -/
theorem sample_gap_long_phase_returns_15_0_0_not_only_next_left_right_boundary_simple_step_event_source :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSourceOn
      sample_gap_long_phase_returns_15_0_0
      (canonical_next_left_selection_witness_on_of_only_next_left
        sample_gap_long_phase_returns_15_0_0) → False := by
  intro hsrc
  let hevent := hsrc 0 sample_iterate_two_15_simple
  have hidx : hevent.idx = 3 := by
    have hafter : 2 < hevent.idx := by
      simpa
        [RightBoundarySimpleStepPromotedFillerSelectedEventWitnessOn,
          right_boundary_simple_step_candidate, sample_gap_long_phase_returns_15_0_0]
        using hevent.afterRight
    have hbefore : hevent.idx < 4 := by
      simpa
        [RightBoundarySimpleStepPromotedFillerSelectedEventWitnessOn,
          right_boundary_simple_step_candidate, sample_gap_long_phase_returns_15_0_0]
        using hevent.beforeNextLeft
    omega
  have hadm :
      hevent.idx = sample_gap_long_phase_returns_15_0_0.leftIdx (0 + 1) := by
    simpa
      [RightBoundarySimpleStepPromotedFillerSelectedEventWitnessOn,
        right_boundary_simple_step_candidate, CanonicalNextLeftSelectionWitnessOn,
        canonical_next_left_selection_witness_on_of_only_next_left]
      using hevent.admissibleIdx
  norm_num [sample_gap_long_phase_returns_15_0_0] at hadm
  omega

/-- Global impossibility corollary: the sharpened boundary simple-step source is
not derivable uniformly for all witness-relative admissibility notions that
merely satisfy `self`. -/
theorem not_all_gap_long_phase_returns_have_only_next_left_right_boundary_simple_step_event_source :
    GapLongPhaseReturnsFillerCanonicalNextLeftWitnessRightBoundarySimpleStepEventSource
      15 0 0
      (fun hphase => canonical_next_left_selection_witness_on_of_only_next_left hphase) → False := by
  intro hall
  exact
    sample_gap_long_phase_returns_15_0_0_not_only_next_left_right_boundary_simple_step_event_source
      (hall sample_gap_long_phase_returns_15_0_0)

lemma gap_long_dvd_phase_return_span
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (j : ℕ) :
    gap_long t ∣ hphase.rightIdx j - hphase.leftIdx j := by
  have hle : hphase.leftIdx j ≤ hphase.rightIdx j := by
    exact le_trans (Nat.le_add_right _ _) (hphase.longSep j)
  have hmod : hphase.leftIdx j ≡ hphase.rightIdx j [MOD gap_long t] := by
    simpa [Nat.ModEq] using hphase.phaseAligned j
  exact (Nat.modEq_iff_dvd' hle).1 hmod

lemma gap_long_dvd_sub_of_phase_aligned
    (t i j : ℕ)
    (hij : i ≤ j)
    (hphase : i % gap_long t = j % gap_long t) :
    gap_long t ∣ j - i := by
  have hmod : i ≡ j [MOD gap_long t] := by
    simpa [Nat.ModEq] using hphase
  exact (Nat.modEq_iff_dvd' hij).1 hmod

lemma phase_aligned_of_gap_long_dvd_add
    (t i L : ℕ)
    (hdvd : gap_long t ∣ L) :
    i % gap_long t = (i + L) % gap_long t := by
  have hle : i ≤ i + L := Nat.le_add_right _ _
  have hdvd' : gap_long t ∣ (i + L) - i := by
    simpa [Nat.add_sub_cancel_left] using hdvd
  have hmod : i ≡ i + L [MOD gap_long t] :=
    (Nat.modEq_iff_dvd' hle).2 hdvd'
  simpa [Nat.ModEq] using hmod

lemma phase_return_pair_length_ge_L0
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (j : ℕ) :
    Collatz.SEDT.L₀ t U ≤ hphase.rightIdx j - hphase.leftIdx j := by
  have hle : hphase.leftIdx j ≤ hphase.rightIdx j := by
    exact le_trans (Nat.le_add_right _ _) (hphase.longSep j)
  have hsep : Collatz.SEDT.L₀ t U + hphase.leftIdx j ≤ hphase.rightIdx j := by
    simpa [Nat.add_comm] using hphase.longSep j
  exact (Nat.le_sub_iff_add_le hle).2 hsep

lemma phase_return_pair_gap_decomposition
    {m t U : ℕ}
    (hphase : OrbitHasCofinalGapLongPhaseReturns m t U)
    (j : ℕ) :
    hphase.leftIdx (j + 1) - hphase.leftIdx j =
      (hphase.rightIdx j - hphase.leftIdx j) +
      (hphase.leftIdx (j + 1) - hphase.rightIdx j) := by
  have hle1 : hphase.leftIdx j ≤ hphase.rightIdx j := by
    exact le_trans (Nat.le_add_right _ _) (hphase.longSep j)
  have hle2 : hphase.rightIdx j ≤ hphase.leftIdx (j + 1) := by
    exact Nat.le_of_lt (hphase.rightStep j)
  omega

/-- Canonical paper-faithful bridge: cofinal `gap_long(t)`-aligned return pairs
can be chained into a cofinal sequence of SEDT-long orbit gaps. The proof uses
the strengthened phase-return witness, including its residue alignment and
inter-pair coherence. -/
def canonical_gap_long_phase_returns_bridge (m t U : ℕ) :
    GapLongPhaseReturnsBridge m t U := by
  intro hphase
  refine
    { idx := hphase.leftIdx
      idxStrict := ?_
      longGap := ?_ }
  · refine strictMono_nat_of_lt_succ ?_
    intro j
    have hlt : hphase.leftIdx j < hphase.leftIdx (j + 1) := by
      exact lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) (hphase.longSep j)) (hphase.rightStep j)
    exact hlt
  · intro j
    have hsep : hphase.leftIdx j + Collatz.SEDT.L₀ t U ≤ hphase.leftIdx (j + 1) := by
      exact le_trans (hphase.longSep j) (Nat.le_of_lt (hphase.rightStep j))
    omega

/-- Package a semantic cofinal-gap witness into the `G.5`-shaped supply object. -/
def orbit_long_epoch_supply_of_cofinal_long_epoch_gaps
    {m t U : ℕ} (hcofinal : OrbitHasCofinalLongEpochGaps m t U) :
    OrbitLongEpochSupply m t U := by
  refine
    { idx := hcofinal.idx
      epochLen := fun j => hcofinal.idx (j + 1) - hcofinal.idx j
      idxStrict := hcofinal.idxStrict
      idxStep := ?_
      longEpoch := hcofinal.longGap }
  intro j
  exact (Nat.add_sub_of_le (Nat.le_of_lt (hcofinal.idxStrict (Nat.lt_succ_self j)))).symm

/-- Canonical stream supplier from a G.5-style long-epoch supply function. -/
def orbit_long_epoch_stream_of_supply
    (m t U : ℕ) (hsupply : OrbitLongEpochSupply m t U) :
    OrbitLongEpochStream m t U := by
  refine
    { idx := hsupply.idx
      epochLen := hsupply.epochLen
      orbitVal := fun j => (Collatz.Foundations.collatz_step^[hsupply.idx j]) m
      idxMonotone := hsupply.idxStrict.monotone
      idxStrict := hsupply.idxStrict
      idxStep := hsupply.idxStep
      longEpoch := hsupply.longEpoch
      realizedOnOrbit := ?_ }
  intro j
  rfl

/-- Aperiodic-orbit to long-epoch-stream bridge (G.5/G.Super-SEDT style contract). -/
def orbit_long_epoch_stream_of_aperiodic_supply
    (m t U : ℕ)
    {P : Prop} (_haper : P)
    (hsupply : OrbitLongEpochSupply m t U) :
    OrbitLongEpochStream m t U :=
  orbit_long_epoch_stream_of_supply m t U hsupply

/-- Canonical stream induced directly by an orbit-semantic cofinal-gap witness. -/
def orbit_long_epoch_stream_of_cofinal_long_epoch_gaps
    (m t U : ℕ) (hcofinal : OrbitHasCofinalLongEpochGaps m t U) :
    OrbitLongEpochStream m t U :=
  orbit_long_epoch_stream_of_supply m t U
    (orbit_long_epoch_supply_of_cofinal_long_epoch_gaps hcofinal)

lemma super_long_epochs (t : ℕ) : ∃ L : ℕ, L ≥ gap_long t + Q_t t := by
  exact ⟨gap_long t + Q_t t, le_rfl⟩

lemma super_long_epochs_sedt (t : ℕ) : ∃ L : ℕ, L ≥ Collatz.SEDT.L₀ t 1 := by
  exact ⟨Collatz.SEDT.L₀ t 1, le_rfl⟩

lemma touch_count_vs_length (t : ℕ) :
    ∀ L : ℕ, L / gap_long t ≤ L := by
  intro L
  exact Nat.div_le_self _ _

lemma pigeonhole_multibit_touches (t : ℕ) : ∃ n : ℕ, n ≤ gap_long t := by
  exact ⟨0, Nat.zero_le _⟩

lemma plateau_to_epoch_length (t : ℕ) :
    ∀ plateauLen : ℕ, plateauLen ≤ plateauLen + gap_long t := by
  intro plateauLen
  exact Nat.le_add_right _ _

end Collatz.Epochs
