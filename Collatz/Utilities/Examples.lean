/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Worked Examples for Collatz Formalization

This file contains simple concrete examples demonstrating key computations
using the centralized Core.lean architecture.
-/

import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.Examples

-- Use centralized definitions from Core.lean
open Collatz.Foundations (depth_minus step_type collatz_step)
open Collatz.Epochs (Q_t is_t_touch M_tilde)
open Collatz.SEDT (α β₀ C L₀ K_glue ε)

/-!
## Basic Examples

Simple examples using centralized definitions.
-/

/-- Basic arithmetic example -/
example : (2 : ℕ) ^ 3 = 8 := by norm_num

/-- Q_t for small values -/
example : Q_t 3 = 2 := by simp [Q_t]

example : Q_t 4 = 4 := by simp [Q_t]

example : Q_t 5 = 8 := by simp [Q_t]

/-- Depth examples -/
example : depth_minus 7 = 3 := sorry

example : depth_minus 15 = 4 := sorry

/-- Touch examples -/
example : is_t_touch 3 7 := sorry

example : ¬is_t_touch 3 5 := sorry

end Collatz.Examples
