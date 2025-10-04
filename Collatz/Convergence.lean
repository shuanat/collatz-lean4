/-
  Collatz/Convergence.lean
  Lean 4.24.0-rc1 + mathlib (latest)
-/

import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Collatz.Basic

noncomputable section
open Classical

namespace Collatz.Convergence

open Collatz

/-- Сокращение: итератор T_odd -/
abbrev TIt (k : ℕ) : ℕ → ℕ := T_odd^[k]

/-- Базовая «главная» теорема сходимости к 1 (скелет). -/
theorem main_convergence (n : ℕ) (hn_pos : n > 0) :
  ∃ k : ℕ, TIt k n = 1 := by
  -- здесь будет твоя основная техника (SEDT/энергетики/коэрцитивность)
  sorry

/-- Теорема о попадании в тривиальный цикл {1,2,4}. -/
theorem convergence_to_trivial_cycle (n : ℕ) (hn_pos : n > 0) :
  ∃ k : ℕ, TIt k n ∈ ({1, 2, 4} : Finset ℕ) := by
  -- обычно выводится из `main_convergence`, плюс несколько шагов симпа
  -- замечание: при желании можно вернуть `Set ℕ`, но Finset проще
  sorry

/-- Лемма коэрцитивности/сжатия масштаба (скелет). -/
lemma coercivity
    (n : ℕ) (hn_pos : n > 0)
    (β : ℝ) (hβ : β ≥ 1)
    (ε : ℝ) (hε : ε > 0) :
    -- пример неравенства; следи, чтобы все `ℕ` кастились в `ℝ`
    β * (Real.log (n : ℝ) / Real.log 2) - ε * (1 : ℝ) ≤
    β * (Real.log ((T_odd n : ℕ) : ℝ) / Real.log 2) := by
  -- NB: это просто типовой шаблон: у тебя будет своя формулировка
  --     главное: `Real.log` требует импорта и не работает на `ℕ` без кастов
  sorry

/-- Уникальность неподвижной точки (скелет). -/
theorem fixed_point_uniqueness :
    ∀ {x : ℕ}, T_odd x = x → x = 1 := by
  -- порядок: это определено до того, как мы будем на него ссылаться ниже
  sorry

/-- Глобальная сходимость (гипотеза Коллатца, скелет). -/
theorem global_convergence :
  ∀ n : ℕ, n > 0 → ∃ k : ℕ, TIt k n = 1 := by
  intro n hn
  -- обычно: ссылку на `main_convergence` + оформление
  exact main_convergence n hn

-- Полезные леммы про итерации (можно оставить здесь для удобства):
-- section IterateLemmas
-- variable {f : ℕ → ℕ} {k ℓ : ℕ} {x : ℕ}
-- примеры стандартных фактов (есть в mathlib, привожу для ориентира):
-- f^[0] = id, f^[k+1] = f ∘ f^[k], f^[k+ℓ] = f^[k] ∘ f^[ℓ], …
-- В реальном коде обычно используем их из mathlib через `simp`/`rewrite`.
-- см. документацию к `Function.iterate`.
-- end IterateLemmas

/-- Техничная лемма: удобная запись множества {1,2,4} как `Set ℕ` при необходимости. -/
def trivialCycleSet : Set ℕ := {x | x = 1 ∨ x = 2 ∨ x = 4}

@[simp] lemma mem_trivialCycleSet :
  ∀ {x}, x ∈ trivialCycleSet ↔ (x = 1 ∨ x = 2 ∨ x = 4) := by
  intro x; rfl

end Collatz.Convergence
