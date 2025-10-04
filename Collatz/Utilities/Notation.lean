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

-- Core epoch constants
notation:max "Q_t(" t ")" => Collatz.Utilities.Q_t t

-- SEDT constants (parameterized)
notation:max "α(" t "," U ")" => Collatz.Utilities.α t U
notation:max "β₀(" t "," U ")" => Collatz.Utilities.β₀ t U
notation:max "ε(" t "," U "," β ")" => Collatz.Utilities.ε t U β
notation:max "C(" t "," U ")" => Collatz.Utilities.C t U
notation:max "L₀(" t "," U ")" => Collatz.Utilities.L₀ t U
notation:max "K_glue(" t ")" => Collatz.Utilities.K_glue t
notation:max "C_short(" t "," U ")" => Collatz.Utilities.C_short t U

-- Touch analysis constants
notation:max "s_t(" t ")" => Collatz.Utilities.s_t t
notation:max "p_touch(" t "," L ")" => Collatz.Utilities.p_touch t L

-- Head/plateau/tail bounds
notation:max "c_h" => Collatz.Utilities.c_h
notation:max "c_p" => Collatz.Utilities.c_p
notation:max "c_b" => Collatz.Utilities.c_b

-- Potential function
notation:max "V(" n "," β ")" => Collatz.Utilities.V n β

-- Additional epoch constants
notation:max "P_t(" t ")" => Collatz.Utilities.P_t t
notation:max "C_t(" t ")" => Collatz.Utilities.C_t t
notation:max "G_t(" t ")" => Collatz.Utilities.G_t t

end Collatz.Utilities
