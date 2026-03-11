/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Two-adic depth utilities

This module exposes the `depth_minus` helper used across the Collatz
formalization using the centralized Core.lean architecture.
-/

import Collatz.Foundations.Core

namespace Collatz

-- Use centralized definitions from Core.lean
open Collatz.Foundations (depth_minus step_type collatz_step)

/-!
## Two-adic Depth Utilities

This module provides utilities for working with 2-adic depth.
All definitions are now centralized in Foundations.Core.
-/

/-- Simple helper: two-adic depth is always nonnegative. -/
lemma depth_minus_add_one (r : ℕ) : 0 ≤ depth_minus (r + 1) := by
  exact Nat.zero_le _

end Collatz
