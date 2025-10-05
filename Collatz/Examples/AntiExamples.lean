-- Анти-примеры: Что НЕ следует делать
-- Демонстрирует неправильные подходы и их исправления

import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core
import Collatz.Epochs.Aliases

namespace Collatz.Examples.AntiExamples

-- ❌ АНТИ-ПРИМЕР 1: Неправильные импорты

-- ❌ НЕПРАВИЛЬНО: Прямой импорт специализированного модуля в Core
-- import Collatz.Epochs.Structure  -- НЕ ДЕЛАЙТЕ ТАК!

-- ❌ НЕПРАВИЛЬНО: Импорт между модулями одного уровня
-- import Collatz.Epochs.Structure
-- import Collatz.Epochs.TouchAnalysis  -- НЕ ДЕЛАЙТЕ ТАК!

-- ✅ ПРАВИЛЬНО: Импорт Core модулей
-- import Collatz.Foundations.Core
-- import Collatz.Epochs.Core
-- import Collatz.SEDT.Core
-- import Collatz.Epochs.Aliases

-- ❌ АНТИ-ПРИМЕР 2: Дублирование определений

-- ❌ НЕПРАВИЛЬНО: Дублирование определений
-- def depth_minus (n : ℕ) : ℕ := sorry  -- УЖЕ ЕСТЬ В Foundations.Core!

-- ❌ НЕПРАВИЛЬНО: Переопределение алиасов
-- abbrev Depth := sorry  -- УЖЕ ЕСТЬ В Epochs.Aliases!

-- ✅ ПРАВИЛЬНО: Использование существующих определений
open Collatz.Epochs.Aliases (Depth)
-- Используйте Depth вместо переопределения

-- ❌ АНТИ-ПРИМЕР 3: Неправильное использование алиасов

-- ❌ НЕПРАВИЛЬНО: Смешивание длинных и коротких имен
-- example (n : ℕ) : Collatz.Foundations.depth_minus n ≥ 0 := by sorry
-- example (m : ℕ) : Depth m ≥ 0 := by sorry  -- Непоследовательность!

-- ✅ ПРАВИЛЬНО: Последовательное использование алиасов
open Collatz.Epochs.Aliases (Depth)
example (n : ℕ) : Depth n ≥ 0 := by sorry
example (m : ℕ) : Depth m ≥ 0 := by sorry

-- ❌ АНТИ-ПРИМЕР 4: Неправильная структура модуля

-- ❌ НЕПРАВИЛЬНО: Определения без импортов
-- def bad_function (n : ℕ) : ℕ := sorry  -- Нет импортов!

-- ✅ ПРАВИЛЬНО: Правильная структура модуля
-- import Collatz.Foundations.Core
-- import Collatz.Epochs.Aliases
-- open Collatz.Epochs.Aliases (Depth)
-- def good_function (n : ℕ) : ℕ := sorry

-- ❌ АНТИ-ПРИМЕР 5: Неправильные зависимости

-- ❌ НЕПРАВИЛЬНО: Циклические зависимости
-- Модуль A импортирует модуль B, который импортирует модуль A

-- ✅ ПРАВИЛЬНО: Иерархические зависимости
-- Core модули → Специализированные модули

-- ❌ АНТИ-ПРИМЕР 6: Неправильное именование

-- ❌ НЕПРАВИЛЬНО: Непоследовательное именование
-- def depthMinus (n : ℕ) : ℕ := sorry  -- camelCase
-- def step_type (n : ℕ) : ℕ := sorry   -- snake_case

-- ✅ ПРАВИЛЬНО: Последовательное именование
-- def depth_minus (n : ℕ) : ℕ := sorry  -- snake_case
-- def step_type (n : ℕ) : ℕ := sorry    -- snake_case

-- ❌ АНТИ-ПРИМЕР 7: Неправильное использование типов

-- ❌ НЕПРАВИЛЬНО: Неправильные типы
-- def bad_function (n : ℕ) : ℕ := sorry  -- Возвращает ℕ вместо ℝ

-- ✅ ПРАВИЛЬНО: Правильные типы
-- def good_function (n : ℕ) : ℝ := sorry  -- Возвращает ℝ

-- ❌ АНТИ-ПРИМЕР 8: Неправильная документация

-- ❌ НЕПРАВИЛЬНО: Отсутствие документации
-- def undocumented_function (n : ℕ) : ℕ := sorry

-- ✅ ПРАВИЛЬНО: Хорошая документация
-- /-- Функция вычисляет глубину числа -/
-- def documented_function (n : ℕ) : ℕ := sorry

-- ❌ АНТИ-ПРИМЕР 9: Неправильное использование sorry

-- ❌ НЕПРАВИЛЬНО: Использование sorry в финальном коде
-- theorem bad_theorem (n : ℕ) : n ≥ 0 := by sorry  -- НЕ ДЕЛАЙТЕ ТАК!

-- ✅ ПРАВИЛЬНО: Использование sorry только в разработке
-- theorem good_theorem (n : ℕ) : n ≥ 0 := by
--   exact Nat.zero_le n

-- ❌ АНТИ-ПРИМЕР 10: Неправильная организация кода

-- ❌ НЕПРАВИЛЬНО: Все в одном файле
-- Множество несвязанных определений в одном модуле

-- ✅ ПРАВИЛЬНО: Логическая организация
-- Связанные определения в отдельных модулях

end Collatz.Examples.AntiExamples
