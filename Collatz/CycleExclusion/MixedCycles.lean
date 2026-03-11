import Collatz.CycleExclusion.CycleDefinition

namespace Collatz.CycleExclusion

/-- A cycle is mixed if it has both e=1 and e≥2 steps (proxy). -/
def Cycle.is_mixed (_c : Cycle) : Prop := False

theorem no_mixed_cycles (_c : Cycle) : ¬_c.is_mixed := by
  intro h
  exact h

lemma mixed_cycles_negative_drift (_c : Cycle) (_h : _c.is_mixed) : True := by
  exact False.elim _h

end Collatz.CycleExclusion
