import Mathlib.Tactic
import Collatz.Mixing.PhaseMixing

namespace Collatz.Mixing

open Collatz.Epochs

/-- Explicit `tails -> raw prefix` transfer interface for paper Bridge Lemma
F.6.1 / Corollary F.7. The tail-level F.6 discrepancy witness is kept separate
from the additional mapping-overhead semantics needed to pass from admissible
tails to raw odd-step prefixes. No unsupported policy constants are baked in. -/
structure RawPrefixTailTransferSemantics (n t : ℕ) where
  tailWitness : AdmissibleTailTouchFrequencyWitness n t
  rawTouchCount : ℕ → ℕ
  transferConst : ℕ
  prefixToTailLength :
    ∀ L : ℕ,
      L / Q_t t ≤
        (tailWitness.tailStop L - tailWitness.tailStart L) / Q_t t + transferConst
  tailToPrefixLength :
    ∀ L : ℕ,
      (tailWitness.tailStop L - tailWitness.tailStart L) / Q_t t ≤
        L / Q_t t + transferConst
  tailToRawTouches :
    ∀ L : ℕ,
      tailWitness.touchCount L ≤ rawTouchCount L + transferConst
  rawToTailTouches :
    ∀ L : ℕ,
      rawTouchCount L ≤ tailWitness.touchCount L + transferConst

/-- Integer-coded raw-prefix discrepancy witness corresponding to paper F.7 after
the bridge step from admissible tails has been supplied. -/
structure RawPrefixTouchFrequencyWitness (n t : ℕ) where
  discrepancyConst : ℕ
  rawTouchCount : ℕ → ℕ
  lower :
    ∀ L : ℕ,
      L / Q_t t ≤ rawTouchCount L + discrepancyConst
  upper :
    ∀ L : ℕ,
      rawTouchCount L ≤ L / Q_t t + discrepancyConst

/-- Public bridge residual: the explicit `tails -> raw prefix` transfer
semantics needed by paper Lemma F.6.1 / Corollary F.7.

**Wave 2H deprecation note.** Superseded by the direct one-sided orbit-side
residual `Collatz.Mixing.OrbitSideAggregateTouchRateResidual`
(`Collatz/Mixing/AggregateTouchRate.lean`), which speaks about the actual
Collatz orbit prefix `[0, L)` natively (no `tails -> raw prefix` transfer
overhead). Retained as a deprecated back-compat alias for the old two-sided
F.7 consumer path. -/
def RawPrefixTouchFrequencyBridgeResidual (n t : ℕ) : Prop :=
  Nonempty (RawPrefixTailTransferSemantics n t)

/-- Public raw-prefix frequency residual after the bridge has been discharged.

**Wave 2H deprecation note.** Same as above: superseded by
`OrbitSideAggregateTouchRateResidual`. -/
def RawPrefixTouchFrequencyResidual (n t : ℕ) : Prop :=
  Nonempty (RawPrefixTouchFrequencyWitness n t)

/-- Compose the tail-level Appendix-F.6 witness with explicit raw-prefix transfer
semantics to obtain the raw-prefix Appendix-F.7 discrepancy witness. The new
constant is the honest arithmetic accumulation of the tail discrepancy constant
and the transfer overhead. -/
noncomputable def raw_prefix_touch_frequency_witness_of_transfer
    {n t : ℕ}
    (hbridge : RawPrefixTailTransferSemantics n t) :
    RawPrefixTouchFrequencyWitness n t := by
  refine
    { discrepancyConst :=
        hbridge.tailWitness.discrepancyConst + 2 * hbridge.transferConst
      rawTouchCount := hbridge.rawTouchCount
      lower := ?_
      upper := ?_ }
  · intro L
    have hlen := hbridge.prefixToTailLength L
    have htail := hbridge.tailWitness.lower L
    have htouch := hbridge.tailToRawTouches L
    omega
  · intro L
    have htouch := hbridge.rawToTailTouches L
    have htail := hbridge.tailWitness.upper L
    have hlen := hbridge.tailToPrefixLength L
    omega

/-- Extract the explicit raw-prefix discrepancy witness from the bridge residual
wrapper. -/
noncomputable def raw_prefix_touch_frequency_witness_of_residual
    {n t : ℕ}
    (hbridge : RawPrefixTouchFrequencyBridgeResidual n t) :
    RawPrefixTouchFrequencyWitness n t :=
  raw_prefix_touch_frequency_witness_of_transfer (Classical.choice hbridge)

/-- Public residual wrapper after composing the tail-level F.6 witness with the
explicit F.6.1 / F.7 bridge semantics. -/
theorem raw_prefix_touch_frequency_residual_of_bridge
    {n t : ℕ}
    (hbridge : RawPrefixTouchFrequencyBridgeResidual n t) :
    RawPrefixTouchFrequencyResidual n t := by
  exact ⟨raw_prefix_touch_frequency_witness_of_residual hbridge⟩

end Collatz.Mixing
