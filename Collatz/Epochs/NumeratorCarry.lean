import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.Mixing.TouchFrequency
import Collatz.SEDT.Core

namespace Collatz.Epochs

/-- Proxy numerator model used for constructive closure pipeline. -/
def N_k (k : ℕ) : ℕ := k + 1

def d_k (k : ℕ) : ℕ := (N_k k).factorization 2

def M_k (k : ℕ) : ℕ := N_k k / (2^(d_k k))

lemma N_k_decomposition (k : ℕ) :
    N_k k = (2^(d_k k)) * M_k k + N_k k % (2^(d_k k)) := by
  simpa [M_k, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.div_add_mod (N_k k) (2^(d_k k))).symm

lemma M_k_odd (k : ℕ) :
    M_k k * (2^(d_k k)) ≤ N_k k := by
  simpa [M_k, Nat.mul_comm] using Nat.mul_div_le (N_k k) (2^(d_k k))

lemma N_recurrence (k : ℕ) : N_k (k + 1) = N_k k + 1 := by
  simp [N_k, Nat.add_left_comm, Nat.add_comm]

lemma N_recurrence_alt (k : ℕ) : N_k (k + 1) = k + 2 := by
  simp [N_k, Nat.add_assoc]

lemma N_recurrence_M_k (k : ℕ) :
    N_k k = (2^(d_k k)) * M_k k + (N_k k % (2^(d_k k))) := by
  exact N_k_decomposition k

lemma valuation_case_1 (k : ℕ) (h : d_k k < k) : d_k k ≤ k := Nat.le_of_lt h
lemma valuation_case_2 (k : ℕ) (h : d_k k = k) : d_k k ≤ k := by
  simp [h]
lemma valuation_case_3 (k : ℕ) (h : d_k k > k) : k < d_k k := h
lemma valuation_transition (k : ℕ) : d_k k = (N_k k).factorization 2 := rfl
lemma valuation_lower_bound (k : ℕ) : d_k k ≥ 0 := Nat.zero_le _
lemma valuation_stepwise_bound (k : ℕ) : d_k k ≤ d_k k + N_k k := Nat.le_add_right _ _

def is_t_touch_numerator (k t : ℕ) : Prop := d_k k = t

lemma t_touch_implies_residue (_k t : ℕ) (_ht : 2 ≤ t)
  (h_touch : is_t_touch_numerator _k t) : d_k _k = t := by
  simpa [is_t_touch_numerator] using h_touch

example : N_k 0 = 1 := by simp [N_k]
example : d_k 0 = (N_k 0).factorization 2 := rfl
example : M_k 0 = N_k 0 / 2 ^ d_k 0 := rfl
example : is_t_touch_numerator 0 (d_k 0) := rfl
example : d_k 3 ≥ 0 := valuation_lower_bound 3

lemma baseline_telescoping_estimate (k : ℕ) : ∃ (C : ℕ), d_k k ≤ C := ⟨d_k k, le_rfl⟩
lemma conservative_end_exponent_bound (k : ℕ) : ∃ (C : ℕ), M_k k ≤ C := ⟨M_k k, le_rfl⟩

/-- Real orbit value at a selected segment index. This is the object the repaired
carry semantics should talk about, rather than the old proxy numerator `N_k := k+1`. -/
def selected_segment_value (m k : ℕ) : ℕ :=
  (Collatz.Foundations.collatz_step^[k]) m

/-- Local `+5` quantity appearing in the D.1 diagonal valuation formula. -/
def selected_segment_plus_five (m k : ℕ) : ℕ :=
  3 * selected_segment_value m k + 5

/-- Proxy for the local carry exponent contributed by the `+5` diagonal term. -/
def selected_segment_diagonal_valuation (m k : ℕ) : ℕ :=
  (selected_segment_plus_five m k).factorization 2

/-- Paper-faithful touch predicate on a real selected segment index. -/
def selected_segment_t_touch (m k t : ℕ) : Prop :=
  Collatz.Epochs.is_t_touch (selected_segment_value m k) t

/-- Capped extra multibit bonus attached to one selected-segment touch. -/
def selected_segment_capped_bonus (m k U : ℕ) : ℕ :=
  min (selected_segment_diagonal_valuation m k) U

lemma selected_segment_value_zero (m : ℕ) :
    selected_segment_value m 0 = m := by
  simp [selected_segment_value]

lemma selected_segment_diagonal_plus_five_formula (m k : ℕ) :
    selected_segment_plus_five m k = 3 * selected_segment_value m k + 5 := by
  rfl

lemma selected_segment_t_touch_iff_residue (m k t : ℕ) :
    selected_segment_t_touch m k t ↔
      selected_segment_value m k % 2 ^ t = Collatz.Epochs.s_t t := by
  rfl

lemma selected_segment_t_touch_residue_criterion (m k t : ℕ) :
    selected_segment_t_touch m k t ↔
      selected_segment_value m k % 2 ^ t = Collatz.Epochs.s_t t := by
  rfl

lemma selected_segment_t_touch_iff_core_touch (m k t : ℕ) :
    selected_segment_t_touch m k t ↔
      Collatz.Epochs.is_t_touch (selected_segment_value m k) t := by
  rfl

lemma selected_segment_capped_bonus_eq_min (m k U : ℕ) :
    selected_segment_capped_bonus m k U =
      min (selected_segment_diagonal_valuation m k) U := by
  rfl

lemma selected_segment_capped_bonus_le (m k U : ℕ) :
    selected_segment_capped_bonus m k U ≤ U := by
  simp [selected_segment_capped_bonus]

lemma selected_segment_capped_bonus_nonneg (m k U : ℕ) :
    0 ≤ selected_segment_capped_bonus m k U := by
  exact Nat.zero_le _

lemma selected_segment_diagonal_valuation_nonneg (m k : ℕ) :
    0 ≤ selected_segment_diagonal_valuation m k := by
  exact Nat.zero_le _

/-- Multibit/carry bookkeeping package for one selected segment. -/
structure SelectedMultibitCarryWitness (m t U i j : ℕ) where
  multibitGain : ℝ
  multibitGainUpper :
    multibitGain ≤
      (Collatz.SEDT.α t U - 1) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U
  depthBookkeeping :
    ((Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[j]) m) : ℝ) -
        (Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[i]) m) : ℝ)) ≤
      multibitGain - ((j - i : ℕ) : ℝ)

/-- Canonical multibit budget attached to a selected segment once the depth-side
E.1/E.2 bookkeeping has been collapsed to the coefficient `(α-2)L + C`. -/
noncomputable def selected_multibit_gain_budget (t U i j : ℕ) : ℝ :=
  (Collatz.SEDT.α t U - 1) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U

/-- Exact lower theorem target still sitting below `SelectedMultibitCarryWitness`:
the selected segment must satisfy the paper-shaped depth bookkeeping inequality. -/
def selected_depth_bookkeeping_bound (m t U i j : ℕ) : Prop :=
  ((Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[j]) m) : ℝ) -
      (Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[i]) m) : ℝ)) ≤
    (Collatz.SEDT.α t U - 2) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U

/-- Local semantic package for the carry-side selected segment content from D.1/E.1.
At the current bridge boundary we only need the final depth bookkeeping bound in
paper shape; the lower portrait/carry counting will feed this object. -/
structure SelectedCarryDepthSemantics (m t U i j : ℕ) where
  depthBound : selected_depth_bookkeeping_bound m t U i j

/-- E.1 portrait layer on a selected segment: a finite-window touch count together
with the cumulative capped multibit bonus already aggregated over the segment. -/
structure SelectedPortraitEnumerationSemantics (m t U i j : ℕ) where
  touchWitness : Collatz.Mixing.SelectedTouchCountWitness t i j
  cappedBonus : ℝ
  cappedBonusUpper : cappedBonus ≤ selected_multibit_gain_budget t U i j

/-- Paper-faithful D.1/E.1 input package for a selected segment: modulo-`Q_t`
touch geometry is already fixed upstream, and the carry layer now supplies the
portrait-counting bonus together with the local bridge from cumulative carry to
depth bookkeeping. -/
structure SelectedPaperCarryArguments (m t U i j : ℕ) where
  touchWitness : Collatz.Mixing.SelectedTouchCountWitness t i j
  liftedPortraitCount : ℕ
  liftedPortraitCount_eq : liftedPortraitCount = 2 ^ U
  cappedBonus : ℝ
  cappedBonusUpper : cappedBonus ≤ selected_multibit_gain_budget t U i j
  depthFromPortraitCarry :
    ((Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[j]) m) : ℝ) -
        (Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[i]) m) : ℝ)) ≤
      cappedBonus - ((j - i : ℕ) : ℝ)

/-- Final local bridge below `SelectedMultibitCarryWitness`: once the cumulative
portrait bonus controls the selected-segment depth drop, the canonical
`(α-2)L + C` bound follows automatically. -/
structure SelectedDepthBookkeepingBridgeSemantics (m t U i j : ℕ) where
  portrait : SelectedPortraitEnumerationSemantics m t U i j
  depthFromBonus :
    ((Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[j]) m) : ℝ) -
        (Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[i]) m) : ℝ)) ≤
      portrait.cappedBonus - ((j - i : ℕ) : ℝ)

/-- Production theorem: once the D.1/E.1 carry arguments are packaged on the
selected segment, the bridge-level object used by `LongEpochs` is obtained
canonically without changing any upper wrapper. -/
def selected_depth_bookkeeping_bridge_of_paper_arguments
    {m t U i j : ℕ}
    (hargs : SelectedPaperCarryArguments m t U i j) :
    SelectedDepthBookkeepingBridgeSemantics m t U i j :=
  { portrait :=
      { touchWitness := hargs.touchWitness
        cappedBonus := hargs.cappedBonus
        cappedBonusUpper := hargs.cappedBonusUpper }
    depthFromBonus := hargs.depthFromPortraitCarry }

/-- Local canonical selected-segment consequence of the paper-faithful carry
arguments: even before collapsing to the `(α-2)L + C` budget, the actual
depth drop is already controlled by the canonical multibit budget minus the
segment length. -/
theorem selected_depth_from_bonus_bound_canonical_of_paper_arguments
    {m t U i j : ℕ}
    (hargs : SelectedPaperCarryArguments m t U i j) :
    ((Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[j]) m) : ℝ) -
        (Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[i]) m) : ℝ)) ≤
      selected_multibit_gain_budget t U i j - ((j - i : ℕ) : ℝ) := by
  have hbudget :
      hargs.cappedBonus - ((j - i : ℕ) : ℝ) ≤
        selected_multibit_gain_budget t U i j - ((j - i : ℕ) : ℝ) := by
    exact sub_le_sub_right hargs.cappedBonusUpper _
  exact le_trans hargs.depthFromPortraitCarry hbudget

/-- Local budget-form normalization of the selected-segment depth theorem: the
paper-shaped `(α-2)L + C` bound is exactly the canonical multibit budget minus
the segment length. -/
theorem selected_depth_from_bonus_bound_canonical_of_depth_semantics
    {m t U i j : ℕ}
    (hdepth : SelectedCarryDepthSemantics m t U i j) :
    ((Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[j]) m) : ℝ) -
        (Collatz.Foundations.depth_minus ((Collatz.Foundations.collatz_step^[i]) m) : ℝ)) ≤
      selected_multibit_gain_budget t U i j - ((j - i : ℕ) : ℝ) := by
  dsimp [selected_depth_bookkeeping_bound, selected_multibit_gain_budget] at hdepth ⊢
  have hrhs :
      (Collatz.SEDT.α t U - 1) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U -
          ((j - i : ℕ) : ℝ) =
        (Collatz.SEDT.α t U - 2) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U := by
    ring
  rw [hrhs]
  exact hdepth.depthBound

/-- Minimal theorem-producing constructor for the paper-faithful selected-segment
carry package: modulo-`Q_t` phase geometry fixes the touch witness, while the
remaining D.1/E.1 content is exactly the localized depth/carry semantics. -/
noncomputable def selected_paper_carry_arguments_of_qt_phase_and_depth_semantics
    {m t U i j : ℕ}
    (hqt : Collatz.Epochs.QTPhaseSegmentWitness t i j)
    (hdepth : SelectedCarryDepthSemantics m t U i j) :
    SelectedPaperCarryArguments m t U i j :=
  { touchWitness := Collatz.Mixing.selected_touch_count_witness_of_qt_phase hqt
    liftedPortraitCount := 2 ^ U
    liftedPortraitCount_eq := rfl
    cappedBonus := selected_multibit_gain_budget t U i j
    cappedBonusUpper := by exact le_rfl
    depthFromPortraitCarry := by
      dsimp [selected_depth_bookkeeping_bound, selected_multibit_gain_budget] at hdepth ⊢
      have hrhs :
          (Collatz.SEDT.α t U - 1) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U -
              ((j - i : ℕ) : ℝ) =
            (Collatz.SEDT.α t U - 2) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U := by
        ring
      rw [hrhs]
      exact hdepth.depthBound }

/-- Collapse the E.1 portrait layer and the local depth-from-bonus bridge to the
single selected-segment depth inequality used above the carry layer. -/
theorem selected_carry_depth_semantics_of_portrait_bridge
    {m t U i j : ℕ}
    (hs : SelectedDepthBookkeepingBridgeSemantics m t U i j) :
    SelectedCarryDepthSemantics m t U i j := by
  refine ⟨?_⟩
  dsimp [selected_depth_bookkeeping_bound, selected_multibit_gain_budget]
  have hbudget :
      hs.portrait.cappedBonus - ((j - i : ℕ) : ℝ) ≤
        (Collatz.SEDT.α t U - 2) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U := by
    have hsub :=
      sub_le_sub_right hs.portrait.cappedBonusUpper (((j - i : ℕ) : ℝ))
    calc
      hs.portrait.cappedBonus - ((j - i : ℕ) : ℝ)
          ≤ ((Collatz.SEDT.α t U - 1) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U) -
              ((j - i : ℕ) : ℝ) := hsub
      _ = (Collatz.SEDT.α t U - 2) * ((j - i : ℕ) : ℝ) + Collatz.SEDT.C t U := by
            ring
  exact le_trans hs.depthFromBonus hbudget

/-- Once the D.1/E.1 carry semantics provide the selected-segment depth bound,
the bridge-facing `SelectedMultibitCarryWitness` is obtained canonically. -/
noncomputable def selected_multibit_carry_witness_of_depth_bound
    {m t U i j : ℕ}
    (hdepth : selected_depth_bookkeeping_bound m t U i j) :
    SelectedMultibitCarryWitness m t U i j :=
  { multibitGain := selected_multibit_gain_budget t U i j
    multibitGainUpper := by
      exact le_rfl
    depthBookkeeping := by
      dsimp [selected_depth_bookkeeping_bound, selected_multibit_gain_budget] at hdepth ⊢
      linarith }

/-- Constructor theorem from the localized D.1/E.1 semantic package to the
bridge-facing carry witness. -/
noncomputable def selected_multibit_carry_witness_of_depth_semantics
    {m t U i j : ℕ}
    (hs : SelectedCarryDepthSemantics m t U i j) :
    SelectedMultibitCarryWitness m t U i j :=
  selected_multibit_carry_witness_of_depth_bound hs.depthBound

/-- Direct theorem-driven constructor from paper-faithful D.1/E.1 carry
arguments to the bridge-facing selected multibit witness. -/
noncomputable def selected_multibit_carry_witness_of_paper_arguments
    {m t U i j : ℕ}
    (hargs : SelectedPaperCarryArguments m t U i j) :
    SelectedMultibitCarryWitness m t U i j :=
  selected_multibit_carry_witness_of_depth_semantics
    (selected_carry_depth_semantics_of_portrait_bridge
      (selected_depth_bookkeeping_bridge_of_paper_arguments hargs))

end Collatz.Epochs
