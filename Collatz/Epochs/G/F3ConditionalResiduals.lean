/-
Collatz Conjecture: typed shape attached to paper Appendix F, Theorem F.3/F.4.

Status after the 2026-10 review:

* The former residuals `PrimitiveJunctionRecurrenceResidual` and
  `UniformPhaseDistributionResidual` were defined as `True` and were removed.
* The former `PrimitiveJunctionRecurrenceTypedResidual n t :=
  Nonempty (PrimitiveJunctionRecurrenceWitness n t)` was also removed: the
  witness structure below never mentions the orbit of `n` (nor `t`), so it is
  inhabited for every `n, t` (`PrimitiveJunctionRecurrenceWitness.trivial`).
  It therefore cannot express F.3.

The structure itself is kept only as the subject of the regression fact
`primitive_junction_witness_trivial` in `Collatz/Tests/VacuityRegression.lean`
(its former user `Mixing/OrbitAdmissibleSupplyFromF3.lean` was deleted). No
theorem of the library depends on it.
-/

import Collatz.Epochs.Core

namespace Collatz.Epochs.G

/-- An increasing-with-bounded-gaps index sequence. Despite the name, this
structure does **not** mention the Collatz orbit, primitive junctions, `n`, or
`t`: it is inhabited for all parameters (`PrimitiveJunctionRecurrenceWitness.trivial`)
and carries no information about F.3. -/
structure PrimitiveJunctionRecurrenceWitness (_n _t : ℕ) where
  /-- Gap bound on consecutive indices. -/
  G : ℕ
  G_pos : 0 < G
  /-- Index sequence (not tied to the orbit). -/
  occursAt : ℕ → ℕ
  /-- Consecutive indices are within distance `G`. -/
  gap_bound : ∀ m : ℕ, occursAt (m + 1) ≤ occursAt m + G
  /-- The indices are unbounded. -/
  cofinal : ∀ k : ℕ, ∃ m : ℕ, k ≤ occursAt m

/-- The witness structure is trivially inhabited for every `n, t`
(take `G = 1`, `occursAt = id`). -/
def PrimitiveJunctionRecurrenceWitness.trivial (n t : ℕ) :
    PrimitiveJunctionRecurrenceWitness n t where
  G := 1
  G_pos := Nat.one_pos
  occursAt := id
  gap_bound := fun _ => le_refl _
  cofinal := fun k => ⟨k, le_refl _⟩

end Collatz.Epochs.G
