/-
Collatz Conjecture: 2-adic Cylinders
Characterization of depth runs and cylinder intersections
-/

import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Parity
import Collatz.Basic
import Collatz.Arithmetic
import Collatz.Coordinates

noncomputable section
open Classical

namespace Collatz.Cylinders

open Collatz
open Collatz.Arithmetic
open Collatz.Coordinates

/-- 2-adic cylinder C_ℓ: all odd integers m with ν₂(3m+1) = ℓ -/
def C_ell (ℓ : ℕ) : Set ℕ :=
  { m : ℕ | Odd m ∧ (3 * m + 1).factorization 2 = ℓ }

/-- Alternative characterization: C_ℓ = {m : 3m+1 ≡ 2^ℓ (mod 2^{ℓ+1})} -/
lemma C_ell_modular (ℓ m : ℕ) (hm_odd : Odd m) :
  m ∈ C_ell ℓ ↔ 3 * m + 1 ≡ 2^ℓ [MOD 2^(ℓ+1)] := by
  sorry

/-- Depth run starts: m starts a depth run of length ℓ iff m ∈ C_ℓ -/
lemma depth_run_starts (m ℓ : ℕ) (hm_odd : Odd m) :
  m ∈ C_ell ℓ ↔
  (∀ i : ℕ, i < ℓ → (T_odd^[i] m).factorization 2 = ℓ - i) ∧
  (ℓ = 0 ∨ (T_odd^[ℓ] m).factorization 2 < ℓ) := by
  sorry

/-- Cylinder intersection: C_ℓ₁ ∩ C_ℓ₂ = ∅ for ℓ₁ ≠ ℓ₂ -/
theorem cylinder_disjoint (ℓ₁ ℓ₂ : ℕ) :
  ℓ₁ ≠ ℓ₂ → C_ell ℓ₁ ∩ C_ell ℓ₂ = ∅ := by
  intro h_ne
  ext m
  constructor
  · intro ⟨hm1, hm2⟩
    have h_fac1 := hm1.2
    have h_fac2 := hm2.2
    exact h_ne (h_fac1 ▸ h_fac2)
  · intro h_empty
    exfalso
    exact h_empty

/-- Complete coverage: union of all C_ℓ gives all odd integers -/
theorem cylinder_coverage :
  { m : ℕ | Odd m } = ⋃ ℓ, C_ell ℓ := by
  ext m
  constructor
  · intro hm_odd
    classical
    -- извлекаем Odd m из членства
    have hm_odd' : Odd m := hm_odd
    set ℓ := (3 * m + 1).factorization 2 with hℓ
    -- m ∈ ⋃ ℓ, C_ell ℓ  ⇔  ∃ ℓ, m ∈ C_ell ℓ
    refine Set.mem_iUnion.mpr ?_
    refine ⟨ℓ, ?_⟩
    -- собрать правильный конъюнкт и отдать через simpa
    have : Odd m ∧ (3 * m + 1).factorization 2 = ℓ := ⟨hm_odd', hℓ⟩
    simpa [C_ell] using this
  · intro hm_union
    classical
    -- m ∈ ⋃ ℓ, C_ell ℓ  →  ∃ ℓ, m ∈ C_ell ℓ
    rcases Set.mem_iUnion.mp hm_union with ⟨ℓ, hm_in⟩
    -- из определения C_ell: hm_in : Odd m ∧ …, берём первую проекцию
    exact (show Odd m from (show Odd m ∧ _ from hm_in).1)

/-- Cylinder-coordinate relationship: m(n,t) ∈ C_{k_0(n)+2t} -/
lemma cylinder_coordinate_relation (n t : ℕ) (hn_odd : Odd n) (hn_not_div3 : ¬(3 ∣ n)) :
  m n t ∈ C_ell (k_0 n + 2 * t) := by
  sorry

end Collatz.Cylinders
end  -- закрывает noncomputable section
