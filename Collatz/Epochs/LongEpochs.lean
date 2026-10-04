import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

/-!
# Long-epoch index bookkeeping

Index-level structures used to state the SEDT-envelope hypothesis of
`Collatz/Convergence/MainTheorem.lean` on an orbit: sequences of orbit times
whose consecutive gaps are at least `L₀(t, U)`, and the construction of such a
sequence from cofinal "phase returns" (pairs of times `i < j`, `j - i ≥ L₀`,
`i ≡ j (mod selected_phase_period t)`).

Nothing here is a statement about the dynamics: these structures exist for
every orbit (they only constrain indices), and no drift, touch-frequency or
"long epoch" property of the Collatz orbit is proved. The paper's long-epoch
results G.1–G.5 are not formalized (they are withdrawn in the corrected paper).

The former ~3300 lines of filler / boundary / promotion plumbing and the toy
sample block were deleted in the 2026-10 clean-up; none of it was used by a
convergence theorem.
-/

namespace Collatz.Epochs

/-- Stride `Q_t + 1` used to align phase-return pairs (an index convention). -/
def gap_long (t : ℕ) : ℕ := Q_t t + 1

/-- Joint period `Q_t · gap_long`. Equality of indices modulo this product implies
equality modulo each factor separately. -/
def selected_phase_period (t : ℕ) : ℕ := Q_t t * gap_long t

/-- A strictly increasing sequence of orbit times `idx j` with consecutive gaps
`epochLen j ≥ L₀(t, U)`, together with the orbit values at those times. Only the
field `realizedOnOrbit` mentions the orbit; such a stream exists for every `m`
(see `Tests/VacuityRegression.lean`, `cofinal_long_epoch_gaps_trivial`). -/
structure OrbitLongEpochStream (m t U : ℕ) where
  idx : ℕ → ℕ
  epochLen : ℕ → ℕ
  orbitVal : ℕ → ℕ
  idxMonotone : Monotone idx
  idxStrict : StrictMono idx
  idxStep : ∀ j : ℕ, idx (j + 1) = idx j + epochLen j
  longEpoch : ∀ j : ℕ, Collatz.SEDT.L₀ t U ≤ epochLen j
  realizedOnOrbit : ∀ j : ℕ, orbitVal j = (Collatz.Foundations.collatz_step^[idx j]) m

/-- Index data for SEDT-long epochs (stream form). Like
`OrbitHasCofinalLongEpochGaps`, it does not mention the orbit and is inhabited
for every `_m`. -/
structure OrbitLongEpochSupply (_m t U : ℕ) where
  idx : ℕ → ℕ
  epochLen : ℕ → ℕ
  idxStrict : StrictMono idx
  idxStep : ∀ j : ℕ, idx (j + 1) = idx j + epochLen j
  longEpoch : ∀ j : ℕ, Collatz.SEDT.L₀ t U ≤ epochLen j

/-- A strictly increasing index sequence with consecutive gaps at least
`L₀(t, U)`. Note: this structure does **not** mention the orbit of `_m`; it is
inhabited for every `_m` (e.g. `idx j = j * (L₀ t U + 1)`), so it carries no
orbit information by itself. Orbit content enters only through hypotheses
stated on the values `T^[idx j] m`. -/
structure OrbitHasCofinalLongEpochGaps (_m t U : ℕ) where
  idx : ℕ → ℕ
  idxStrict : StrictMono idx
  longGap : ∀ j : ℕ, Collatz.SEDT.L₀ t U ≤ idx (j + 1) - idx j

/-- Cofinal same-residue return pairs: for every threshold `N` there are times
`N < i`, `i + L₀(t, U) ≤ j` with `i ≡ j (mod selected_phase_period t)`. This
only constrains indices and holds for every `_m` (take `i = N + 1`,
`j = i + L₀ · selected_phase_period t`); the orbit is not mentioned. -/
def RawStrictCofinalGapLongPhaseReturns (_m t U : ℕ) : Prop :=
  ∀ N : ℕ, ∃ i j : ℕ,
    N < i ∧
    i + Collatz.SEDT.L₀ t U ≤ j ∧
    i % selected_phase_period t = j % selected_phase_period t

/-- Sequences of phase-return pairs `(leftIdx j, rightIdx j)` with separation
`≥ L₀(t, U)`, residue alignment and `rightIdx j < leftIdx (j + 1)`. Index data
only: the orbit `_m` is not mentioned. -/
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

/-- Chain cofinal return pairs into a sequence of phase-return pairs. -/
noncomputable def orbit_has_cofinal_gap_long_phase_returns_of_raw_strict
    {m t U : ℕ} (hraw : RawStrictCofinalGapLongPhaseReturns m t U) :
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
          exact le_trans (Nat.le_add_right _ _)
            (by simpa [leftIdx, rightIdx] using hrawSep (threshold j))
        have hstep : leftIdx (j + 1) ≥ leftIdx j + 1 := by
          have hnext : rightIdx j + 1 < leftIdx (j + 1) := by
            simpa [leftIdx, rightIdx, threshold] using hrawGe (threshold (j + 1))
          have hnext' : rightIdx j + 1 ≤ leftIdx (j + 1) := Nat.le_of_lt hnext
          exact le_trans (Nat.add_le_add_right hright_ge_left 1) hnext'
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
      exact le_trans (Nat.le_add_right _ _)
        (by simpa [leftIdx, rightIdx] using hrawSep (threshold j))
    have hnext : rightIdx j + 1 < leftIdx (j + 1) := by
      simpa [leftIdx, rightIdx, threshold] using hrawGe (threshold (j + 1))
    exact le_trans (Nat.add_le_add_right hright_ge_left 1) (Nat.le_of_lt hnext)
  · intro j
    have hnext : rightIdx j + 1 < leftIdx (j + 1) := by
      simpa [leftIdx, rightIdx, threshold] using hrawGe (threshold (j + 1))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_lt hnext)
  · intro j
    simpa [leftIdx, rightIdx] using hrawSep (threshold j)
  · intro j
    simpa [leftIdx, rightIdx] using hrawMod (threshold j)
  · intro j
    have hle : leftIdx j ≤ rightIdx j := by
      exact le_trans (Nat.le_add_right _ _)
        (by simpa [leftIdx, rightIdx] using hrawSep (threshold j))
    exact gap_long_aligned_of_selected_phase_period t (leftIdx j) (rightIdx j) hle
      (by simpa [leftIdx, rightIdx] using hrawMod (threshold j))
  · intro j
    have hle : leftIdx j ≤ rightIdx j := by
      exact le_trans (Nat.le_add_right _ _)
        (by simpa [leftIdx, rightIdx] using hrawSep (threshold j))
    exact qt_phase_aligned_of_selected_phase_period t (leftIdx j) (rightIdx j) hle
      (by simpa [leftIdx, rightIdx] using hrawMod (threshold j))
  · intro N
    exact ⟨N, hleft_ge_self N⟩

/-- Map from phase-return pair sequences to index sequences with gaps `≥ L₀`. -/
def GapLongPhaseReturnsBridge (m t U : ℕ) : Type :=
  OrbitHasCofinalGapLongPhaseReturns m t U →
    OrbitHasCofinalLongEpochGaps m t U

/-- The left endpoints of a phase-return pair sequence have consecutive gaps
`≥ L₀(t, U)`. Index bookkeeping only. -/
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

/-- Repackage an index sequence with large gaps as an `OrbitLongEpochSupply`. -/
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

/-- Attach the orbit values `T^[idx j] m` to an index supply. -/
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

/-- The stream induced by an index sequence with large gaps. -/
def orbit_long_epoch_stream_of_cofinal_long_epoch_gaps
    (m t U : ℕ) (hcofinal : OrbitHasCofinalLongEpochGaps m t U) :
    OrbitLongEpochStream m t U :=
  orbit_long_epoch_stream_of_supply m t U
    (orbit_long_epoch_supply_of_cofinal_long_epoch_gaps hcofinal)

end Collatz.Epochs
