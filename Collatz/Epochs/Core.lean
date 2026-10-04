/-
Core definitions for the epoch / touch layer: the period `Q_t`, the touch
residue `s_t`, and the touch predicate on orbit values.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Collatz.Foundations.Core

namespace Collatz.Epochs

/-- `Q_t = 2^{t-2}`. For `t ≥ 3` this is the multiplicative order of `3`
modulo `2^t` (proved in `Collatz/Epochs/OrdFact.lean`,
`Collatz.OrdFact.orderOf_three_eq_pow_two`). -/
def Q_t (t : ℕ) : ℕ := 2^(t - 2)

/-- The `t`-touch residue `s_t ≡ -5 · 3⁻¹ (mod 2^t)` (for `t ≥ 2`; `0` otherwise),
i.e. the unique residue with `3 s_t + 5 ≡ 0 (mod 2^t)`. Values: `s_3 = 1`,
`s_4 = s_5 = 9`, `s_6 = 41`; for `t ≥ 4` one has `s_t ≡ 9 (mod 16)`, in
particular `s_t ≠ 1`. -/
def s_t (t : ℕ) : ℕ :=
  if t ≥ 2 then
    let inv_three := (3 : ZMod (2^t))⁻¹
    let s_t_zmod := (-5 : ZMod (2^t)) * inv_three
    s_t_zmod.val
  else 0

/-- Touch condition on a value: `M ≡ s_t (mod 2^t)`, equivalently
`2^t ∣ 3M + 5`. Applied to an odd orbit value `n` with `t ≥ 3` it forces
`e(n) = ν₂(3n + 1) = 2`. -/
def is_t_touch (M_k : ℕ) (t : ℕ) : Prop :=
  M_k % (2^t) = s_t t

/-- Orbit value `T^[k] m` of the odd-step map. -/
def selected_segment_value (m k : ℕ) : ℕ :=
  (Collatz.Foundations.collatz_step^[k]) m

/-- `t`-touch at time `k` on the orbit of `m`: `T^[k] m ≡ s_t (mod 2^t)`. -/
def selected_segment_t_touch (m k t : ℕ) : Prop :=
  is_t_touch (selected_segment_value m k) t

end Collatz.Epochs
