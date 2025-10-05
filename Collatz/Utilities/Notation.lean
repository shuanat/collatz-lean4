/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Unified Notation Conventions

This file provides unified notation conventions for the Collatz formalization
using the centralized Core.lean architecture.
-/

import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.Utilities

-- Use centralized definitions from Core.lean
open Collatz.Foundations (depth_minus step_type collatz_step)
open Collatz.Epochs (Q_t is_t_touch M_tilde)
open Collatz.SEDT (α β₀ C L₀ K_glue ε)

/-!
## Mathematical Notation

Basic notation conventions for the Collatz formalization.
-/

-- Set membership notation: x ∈ S
notation:50 x "∈" S => Set.Mem x S

-- Set subset notation: S ⊆ T
notation:50 S "⊆" T => Set.Subset S T

-- Function notation: f : A → B
notation:max f ":" A "→" B => f ∈ A → B

-- Core epoch constants
notation:max "Q_t(" t ")" => Q_t t

-- SEDT constants (simplified)
notation:max "α(" t "," U ")" => α t U
notation:max "β₀(" t "," U ")" => β₀ t U
notation:max "ε(" t "," U "," β ")" => ε t U β
notation:max "C(" t "," U ")" => C t U
notation:max "L₀(" t "," U ")" => L₀ t U
notation:max "K_glue(" t ")" => K_glue t

end Collatz.Utilities
