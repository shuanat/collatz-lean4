/-!
## Two-adic depth utilities

This module exposes the `depth_minus` helper used across the Collatz
formalization.  The definition lives in the shared utilities namespace so
that both the SEDT machinery and other components (e.g. constants,
foundational lemmas) can import a single canonical version.
-/
import Mathlib.Data.Nat.Factorization.Basic

namespace Collatz

/-- Two-adic depth towards `-1`: `depth_minus r = ν₂(r + 1)`.

This measures the multiplicity of the prime `2` in the number `r + 1`, and
is the key valuation used when tracking parity transitions in the reduced
Collatz dynamics.
-/
def depth_minus (r : ℕ) : ℕ := (r + 1).factorization 2

@[simp] lemma depth_minus_add_one (r : ℕ) : depth_minus r = (r + 1).factorization 2 := rfl

end Collatz
