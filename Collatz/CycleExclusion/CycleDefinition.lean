/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Cycle Definition

This file contains the core cycle definition that is used by all other cycle exclusion modules.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Collatz.Foundations

namespace Collatz.CycleExclusion

/-- A cycle is a sequence of distinct integers that map to each other -/
structure Cycle where
  len : ℕ
  atIdx : Fin len → ℕ
  succIdx : Fin len → Fin len
  is_nontrivial : Prop
  IsCycle : Prop

end Collatz.CycleExclusion
