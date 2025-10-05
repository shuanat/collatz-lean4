-- Практические примеры: Базовые определения
-- Демонстрирует правильное использование централизованной архитектуры

import Collatz.Foundations.Core
import Collatz.Epochs.Aliases

-- Использование алиасов для удобства
open Collatz.Epochs.Aliases (Depth StepType CollatzStep Orbit)

namespace Collatz.Examples.BasicDefinitions

-- Пример 1.1: Работа с глубиной числа
example (n : ℕ) : Depth n ≥ 0 := by
  sorry

-- Пример 1.2: Анализ типа шага Коллатца
example (n : ℕ) : StepType n ≥ 1 := by
  sorry

-- Пример 1.3: Свойства шага Коллатца
example (n : ℕ) (h : n > 0) :
  CollatzStep n < n ∨ CollatzStep n = 3 * n + 1 := by
  sorry

-- Пример 1.4: Орбита Коллатца
example (n : ℕ) : n ∈ Orbit n := by
  sorry

-- Пример 1.5: Сходимость орбиты
example (n : ℕ) : ∃ k : ℕ, (Orbit n)[k]! = 1 := by
  sorry

-- Пример 1.6: Свойства глубины
example (n : ℕ) : n = 0 ∨ Depth n > 0 := by
  sorry

-- Пример 1.7: Связь типа шага и четности
example (n : ℕ) : StepType n = 0 ↔ Even n := by
  sorry

-- Пример 1.8: Монотонность шага
example (n : ℕ) (h : n > 0) :
  CollatzStep n ≠ n := by
  sorry

end Collatz.Examples.BasicDefinitions
