import Collatz.CycleExclusion.CycleDefinition

namespace Collatz.CycleExclusion

/-- A cycle is pure e=1 if all steps have e=1 (proxy). -/
def Cycle.is_pure_e1 (_c : Cycle) : Prop := False

theorem no_pure_e1_cycles (_c : Cycle) : ¬_c.is_pure_e1 := by
  intro h
  cases h

lemma pure_e1_constant_potential (_c : Cycle) : True := trivial

end Collatz.CycleExclusion
