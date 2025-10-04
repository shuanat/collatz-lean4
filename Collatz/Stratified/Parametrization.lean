import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Collatz.Foundations

noncomputable section
open Classical

namespace Collatz.Stratified

open Collatz
open Collatz.Stratified

open scoped Nat

-- "минимальная" ступень для попадания в класс 1 mod 3
def k_0 (n : ℕ) : ℕ := if n ≡ 1 [MOD 3] then 2 else 1

lemma k_0_minimal
    (n : ℕ) (hn_odd : Odd n) (hn_not_div3 : ¬ (3 ∣ n)) :
    2^(k_0 n) * n ≡ 1 [MOD 3] := by
  -- Простое доказательство через свойства модульной арифметики
  sorry

-- явная параметризация прообразов
def m (n : ℕ) (t : ℕ) : ℕ :=
  (2^(k_0 n + 2 * t) * n - 1) / 3

-- биективность t ↦ m(n,t) на соответствующем слое
theorem parametric_bijection
    (n : ℕ) (hn_odd : Odd n) (hn_not_div3 : ¬ (3 ∣ n)) :
    Function.Bijective (m n) := by
  -- инъективность: арифметика показателей 2
  -- сюръективность: сводится к вашему описанию S_n/S_n_star
  sorry

end Collatz.Stratified
