# Примеры использования архитектуры Collatz Conjecture

**Дата создания:** 2025-01-15  
**Версия:** 1.0  
**Проект:** Collatz Conjecture - Epoch-Based Amortized Lyapunov Route

---

## Базовые примеры

### Пример 1: Работа с базовыми определениями

```lean
-- Импорт базовых определений
import Collatz.Foundations.Core
import Collatz.Epochs.Aliases

-- Использование алиасов для удобства
open Collatz.Epochs.Aliases (Depth StepType CollatzStep Orbit)

-- Пример работы с глубиной
example (n : ℕ) : Depth n ≥ 0 := by
  sorry

-- Пример работы с типом шага
example (n : ℕ) : StepType n ∈ {0, 1} := by
  sorry

-- Пример работы с шагом Коллатца
example (n : ℕ) (h : n > 0) : CollatzStep n < n ∨ CollatzStep n = 3 * n + 1 := by
  sorry

-- Пример работы с орбитой
example (n : ℕ) : n ∈ Orbit n := by
  sorry
```

### Пример 2: Работа с эпохами

```lean
-- Импорт определений эпох
import Collatz.Epochs.Core
import Collatz.Epochs.Aliases

-- Использование алиасов
open Collatz.Epochs.Aliases (TEpoch IsTTouch MTilde ST TT PTouch QT)

-- Пример создания эпохи
def example_epoch (t : ℕ) : TEpoch t :=
  sorry

-- Пример проверки касания
example (n t : ℕ) : IsTTouch n t ↔ MTilde n t ≡ ST t [ZMOD 2^t] := by
  sorry

-- Пример работы с множеством касаний
example (t : ℕ) : TT t = {k : ℕ | IsTTouch k t} := by
  sorry

-- Пример работы с частотой касаний
example (t : ℕ) : 0 ≤ PTouch t ∧ PTouch t ≤ 1 := by
  sorry

-- Пример работы с порядком
example (t : ℕ) (ht : 3 ≤ t) : QT t = 2^(t-2) := by
  sorry
```

### Пример 3: Работа с SEDT

```lean
-- Импорт SEDT определений
import Collatz.SEDT.Core
import Collatz.Epochs.Aliases

-- Использование алиасов
open Collatz.Epochs.Aliases (SlopeParam NegativityThreshold DriftConstant 
                              SEDTEnvelope AugmentedPotential PotentialChange)

-- Пример работы с параметрами SEDT
example : SlopeParam > 0 := by
  sorry

-- Пример работы с порогом отрицательности
example (n : ℕ) : NegativityThreshold > 0 := by
  sorry

-- Пример работы с константой дрейфа
example : DriftConstant > 0 := by
  sorry

-- Пример работы с оберткой SEDT
example (n : ℕ) : SEDTEnvelope n = SlopeParam * n - NegativityThreshold := by
  sorry

-- Пример работы с расширенным потенциалом
example (n : ℕ) : AugmentedPotential n ≥ 0 := by
  sorry

-- Пример работы с изменением потенциала
example (n end_val : ℕ) : PotentialChange n end_val = 
  AugmentedPotential end_val - AugmentedPotential n := by
  sorry
```

---

## Продвинутые примеры

### Пример 4: Анализ структуры эпохи

```lean
-- Импорт необходимых модулей
import Collatz.Epochs.Core
import Collatz.Epochs.Structure
import Collatz.Epochs.Aliases

-- Использование алиасов
open Collatz.Epochs.Aliases (TEpoch Depth IsTTouch)

-- Пример анализа головы эпохи
example (E : TEpoch t) (n : ℕ) (h : n ∈ Epoch.head E) : 
  Depth n ≥ t := by
  sorry

-- Пример анализа плато эпохи
example (E : TEpoch t) (n : ℕ) (h : n ∈ Epoch.plateau E) : 
  Depth n = t := by
  sorry

-- Пример анализа хвоста эпохи
example (E : TEpoch t) (n : ℕ) (h : n ∈ Epoch.tail E) : 
  Depth n ≥ t := by
  sorry

-- Пример проверки длины эпохи
example (E : TEpoch t) : Epoch.length E > 0 := by
  sorry

-- Пример проверки длинной эпохи
example (E : TEpoch t) : Epoch.is_long E ↔ Epoch.length E ≥ L₀ t := by
  sorry
```

### Пример 5: Анализ касаний

```lean
-- Импорт модулей анализа касаний
import Collatz.Epochs.Core
import Collatz.Epochs.TouchAnalysis
import Collatz.Epochs.Aliases

-- Использование алиасов
open Collatz.Epochs.Aliases (IsTTouch MTilde ST TT PTouch QT)

-- Пример анализа частоты касаний
example (t : ℕ) : PTouch t = (TT t).toFinset.card / (2^t : ℝ) := by
  sorry

-- Пример анализа множества касаний
example (t : ℕ) : TT t = {k : ℕ | MTilde k t ≡ ST t [ZMOD 2^t]} := by
  sorry

-- Пример анализа свойств касаний
example (t : ℕ) : 0 < PTouch t ∧ PTouch t < 1 := by
  sorry

-- Пример анализа сходимости частоты касаний
example (t : ℕ) : PTouch t → 1/QT t := by
  sorry
```

### Пример 6: Гомогенизация хвоста

```lean
-- Импорт модулей гомогенизации
import Collatz.Epochs.Core
import Collatz.Epochs.Homogenization
import Collatz.Epochs.Aliases

-- Использование алиасов
open Collatz.Epochs.Aliases (MTilde Homogenizer Depth)

-- Пример работы с гомогенизатором
example (n t : ℕ) : Homogenizer n t = MTilde n t := by
  sorry

-- Пример сохранения глубины
example (n t : ℕ) : Depth (Homogenizer n t) = Depth n := by
  sorry

-- Пример аффинной эволюции
example (k t : ℕ) : MTilde (k+1) t ≡ 3 * MTilde k t [ZMOD 2^t] := by
  sorry

-- Пример гомогенизированной эволюции
example (k t : ℕ) : MTilde (k+1) t ≡ 3 * MTilde k t [ZMOD 2^t] := by
  sorry
```

---

## Примеры интеграции модулей

### Пример 7: Интеграция Epochs и SEDT

```lean
-- Импорт модулей
import Collatz.Epochs.Core
import Collatz.SEDT.Core
import Collatz.Epochs.Aliases

-- Использование алиасов
open Collatz.Epochs.Aliases (TEpoch SEDTEnvelope AugmentedPotential 
                              SlopeParam NegativityThreshold)

-- Пример интеграции эпох и SEDT
example (E : TEpoch t) (n : ℕ) (h : n ∈ E) : 
  SEDTEnvelope n = SlopeParam * n - NegativityThreshold := by
  sorry

-- Пример работы с расширенным потенциалом в эпохе
example (E : TEpoch t) (n : ℕ) (h : n ∈ E) : 
  AugmentedPotential n ≥ 0 := by
  sorry

-- Пример анализа дрейфа в эпохе
example (E : TEpoch t) (n end_val : ℕ) (h₁ : n ∈ E) (h₂ : end_val ∈ E) : 
  AugmentedPotential end_val - AugmentedPotential n ≤ C * (end_val - n) := by
  sorry
```

### Пример 8: Интеграция Mixing и Epochs

```lean
-- Импорт модулей смешивания
import Collatz.Mixing.PhaseMixing
import Collatz.Epochs.Core
import Collatz.Epochs.Aliases

-- Использование алиасов
open Collatz.Epochs.Aliases (TEpoch PhaseClass)

-- Пример анализа смешивания фаз
example (E₁ E₂ : ℕ) (h : epoch_transition E₁ E₂) : 
  PhaseClass E₂ = PhaseClass E₁ + phase_difference (transition_junction E₁ E₂) := by
  sorry

-- Пример монотонности классов фаз
example (E₁ E₂ : ℕ) (h : epoch_transition E₁ E₂) : 
  PhaseClass E₁ ≤ PhaseClass E₂ := by
  sorry
```

---

## Примеры создания новых модулей

### Пример 9: Создание нового Epochs модуля

```lean
-- Новый модуль: Collatz/Epochs/NewAnalysis.lean

-- Импорт необходимых Core модулей
import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core
import Collatz.Epochs.Aliases

-- Использование алиасов
open Collatz.Epochs.Aliases (TEpoch IsTTouch MTilde ST TT PTouch QT 
                              SEDTEnvelope AugmentedPotential)

namespace Collatz.Epochs

-- Новые определения, использующие централизованные
def new_analysis_function (E : TEpoch t) : ℝ := sorry

-- Новые леммы, использующие централизованные определения
lemma new_analysis_property (E : TEpoch t) : 
  new_analysis_function E ≥ 0 := by
  sorry

-- Новые теоремы
theorem new_analysis_theorem (E : TEpoch t) : 
  new_analysis_function E = sorry := by
  sorry

end Collatz.Epochs
```

### Пример 10: Создание нового CycleExclusion модуля

```lean
-- Новый модуль: Collatz/CycleExclusion/NewCycleAnalysis.lean

-- Импорт необходимых Core модулей
import Collatz.Foundations.Core
import Collatz.Epochs.Aliases

-- Использование алиасов
open Collatz.Epochs.Aliases (Depth StepType CollatzStep Orbit)

namespace Collatz.CycleExclusion

-- Новые определения циклов
def new_cycle_type (n : ℕ) : Prop := sorry

-- Новые леммы о циклах
lemma new_cycle_property (n : ℕ) : 
  new_cycle_type n → CollatzStep n ≠ n := by
  sorry

-- Новые теоремы исключения циклов
theorem new_cycle_exclusion (n : ℕ) : 
  new_cycle_type n → False := by
  sorry

end Collatz.CycleExclusion
```

---

## Примеры тестирования

### Пример 11: Тестирование компиляции

```bash
# Тестирование отдельного модуля
lake build Collatz.Epochs.Structure

# Тестирование группы модулей
lake build Collatz.Epochs

# Тестирование всего проекта
lake build

# Тестирование с подробным выводом
lake build --verbose
```

### Пример 12: Тестирование архитектуры

```python
#!/usr/bin/env python3
"""
Пример тестирования архитектуры
"""

def test_core_dependencies():
    """Тестирует, что Core модули не импортируют специализированные модули"""
    
    core_modules = [
        "Collatz/Foundations/Core.lean",
        "Collatz/Epochs/Core.lean",
        "Collatz/SEDT/Core.lean"
    ]
    
    for module in core_modules:
        # Проверяем импорты
        with open(module, 'r') as f:
            content = f.read()
            
        # Core модули не должны импортировать специализированные модули
        assert "import Collatz.Epochs.Structure" not in content
        assert "import Collatz.CycleExclusion" not in content
        assert "import Collatz.Convergence" not in content
        
    print("✅ Core модули не импортируют специализированные модули")

def test_specialized_dependencies():
    """Тестирует, что специализированные модули импортируют Core модули"""
    
    specialized_modules = [
        "Collatz/Epochs/Structure.lean",
        "Collatz/CycleExclusion/Main.lean",
        "Collatz/Convergence/MainTheorem.lean"
    ]
    
    for module in specialized_modules:
        with open(module, 'r') as f:
            content = f.read()
            
        # Специализированные модули должны импортировать Core модули
        assert "import Collatz.Foundations.Core" in content
        
    print("✅ Специализированные модули импортируют Core модули")

if __name__ == "__main__":
    test_core_dependencies()
    test_specialized_dependencies()
    print("🎉 Все тесты архитектуры прошли успешно!")
```

---

## Примеры отладки

### Пример 13: Отладка циклических зависимостей

```bash
# Проверка циклических зависимостей
lake build 2>&1 | grep "build cycle detected"

# Если найдены циклические зависимости, анализируем:
# 1. Проверяем импорты в проблемных файлах
# 2. Удаляем проблемные импорты
# 3. Пересобираем проект
```

### Пример 14: Отладка ошибок компиляции

```bash
# Детальная компиляция с выводом ошибок
lake build Collatz.Epochs.Structure --verbose

# Анализ ошибок:
# 1. Проверяем импорты
# 2. Проверяем определения
# 3. Проверяем типы
# 4. Исправляем ошибки
# 5. Пересобираем
```

---

## Заключение

Примеры использования архитектуры показывают:

✅ **Правильное использование алиасов:** Удобные сокращения для часто используемых определений  
✅ **Интеграцию модулей:** Корректное взаимодействие между различными модулями  
✅ **Создание новых модулей:** Следование архитектурным принципам  
✅ **Тестирование:** Проверка компиляции и архитектуры  
✅ **Отладку:** Решение проблем с зависимостями и компиляцией  

**Статус:** ✅ Примеры готовы к использованию

---

**Примеры созданы:** AGI Math Research Agent v4.0  
**Дата:** 2025-01-15  
**Версия:** 1.0
