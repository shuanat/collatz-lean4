/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Unified Notation Conventions

This file provides unified notation conventions for the Collatz formalization:
- Mathematical notation
- Function notation
- Set notation
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Iterate
import Collatz.Utilities.Constants

namespace Collatz.Utilities

-- Mathematical Notation

-- Set membership notation: x ∈ S
notation:50 x "∈" S => Set.Mem x S

-- Set subset notation: S ⊆ T
notation:50 S "⊆" T => Set.Subset S T

-- Function notation: f : A → B
notation:max f ":" A "→" B => f ∈ A → B

-- Constants notation

-- SEDT constants
notation:max "α" => Collatz.Utilities.α
notation:max "β₀" => Collatz.Utilities.β₀
notation:max "ε" => Collatz.Utilities.ε
notation:max "C" => Collatz.Utilities.C
notation:max "L₀" => Collatz.Utilities.L₀
notation:max "K_glue" => Collatz.Utilities.K_glue

-- Epoch constants
notation:max "ord_3_mod_2t(" t ")" => Collatz.Utilities.ord_3_mod_2t t
notation:max "p_touch" => Collatz.Utilities.p_touch

-- Convergence constants
notation:max "β_coercivity" => Collatz.Utilities.β_coercivity
notation:max "K_convergence" => Collatz.Utilities.K_convergence

end Collatz.Utilities
