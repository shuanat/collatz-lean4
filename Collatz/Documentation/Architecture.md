# Архитектура проекта Collatz Conjecture

**Дата создания:** 2025-01-15  
**Версия:** 1.0  
**Проект:** Collatz Conjecture - Epoch-Based Amortized Lyapunov Route  
**Статус:** ✅ Полностью интегрирован и компилируется

---

## Обзор архитектуры

Проект Collatz Conjecture использует **централизованную архитектуру** с тремя основными Core модулями, которые содержат все общие определения и предотвращают дублирование кода.

### Ключевые принципы

1. **Централизация:** Все общие определения в Core модулях
2. **Иерархия зависимостей:** Четкая структура импортов
3. **Соответствие статье:** Структура кода отражает структуру доказательств
4. **Устранение дублирования:** Единые точки определения
5. **Система алиасов:** Удобные сокращения для часто используемых определений

---

## Диаграмма архитектуры

```
┌─────────────────────────────────────────────────────────────┐
│                    Collatz.lean                            │
│                   (Main Module)                            │
└─────────────────────┬───────────────────────────────────────┘
                      │
        ┌─────────────┼─────────────┐
        │             │             │
        ▼             ▼             ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐
│Foundations  │ │   Epochs    │ │    SEDT     │
│   Core      │ │    Core     │ │    Core     │
│             │ │             │ │             │
│• depth_minus│ │• TEpoch     │ │• α, β₀, C   │
│• step_type  │ │• is_t_touch │ │• L₀, K_glue │
│• collatz_step│ │• M_tilde    │ │• ε          │
│• identities │ │• s_t, T_t   │ │• envelope   │
│             │ │• p_touch    │ │• potential  │
│             │ │• Q_t        │ │             │
└─────────────┘ └─────────────┘ └─────────────┘
        │             │             │
        └─────────────┼─────────────┘
                      │
                      ▼
              ┌─────────────┐
              │   Aliases   │
              │   System    │
              │             │
              │• Shortcuts  │
              │• Abbreviations│
              │• Convenience│
              └─────────────┘
                      │
        ┌─────────────┼─────────────┐
        │             │             │
        ▼             ▼             ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐
│   Epochs    │ │CycleExclusion│ │Convergence  │
│  Modules    │ │   Modules    │ │  Modules    │
│             │ │             │ │             │
│• Structure  │ │• Main       │ │• MainTheorem│
│• TouchAnalysis│ │• MixedCycles│ │• FixedPoints│
│• Homogenization│ │• PeriodSum │ │• Coercivity │
│• MultibitBonus│ │• PureE1Cycles│ │• NoAttractors│
│• LongEpochs  │ │• RepeatTrick│ │             │
│• APStructure │ │• CycleDefinition│             │
│• PhaseClasses│ │             │             │
│• CosetAdmissibility│         │             │
│• NumeratorCarry│             │             │
│• OrdFact     │             │             │
└─────────────┘ └─────────────┘ └─────────────┘
        │             │             │
        └─────────────┼─────────────┘
                      │
        ┌─────────────┼─────────────┐
        │             │             │
        ▼             ▼             ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐
│   Mixing    │ │ Stratified  │ │  Utilities  │
│  Modules    │ │  Modules    │ │  Modules    │
│             │ │             │ │             │
│• PhaseMixing│ │• BranchingDensity│ │• Constants │
│• Semigroup  │ │• CompleteStratification│ │• Examples │
│• TouchFrequency│ │• Cylinders │ │• Notation  │
│             │ │• Parametrization│ │• TwoAdicDepth│
│             │ │• PreimageLayers│ │             │
└─────────────┘ └─────────────┘ └─────────────┘
```

---

## Core модули

### 1. Foundations.Core.lean

**Назначение:** Базовые математические определения и леммы

**Содержание:**
- `depth_minus` - 2-adic глубина числа
- `step_type` - тип шага Коллатца
- `collatz_step` - функция шага Коллатца
- `collatz_step_odd` - шаг для нечетных чисел
- `collatz_orbit` - орбита Коллатца
- Базовые леммы и свойства

**Импорты:** Только Mathlib
**Экспорты:** Все базовые определения

### 2. Epochs.Core.lean

**Назначение:** Централизованные определения эпох и связанных структур

**Содержание:**
- `TEpoch` - структура эпохи
- `is_t_touch` - условие t-касания
- `M_tilde` - гомогенизированная последовательность
- `s_t`, `T_t` - параметры касаний
- `p_touch` - частота касаний
- `Q_t` - порядок 3 по модулю 2^t
- `phase_class` - классификация фаз
- `homogenizer` - функция гомогенизации
- `is_long_epoch` - условие длинной эпохи
- `long_epoch_gap`, `long_epoch_density` - свойства длинных эпох
- `sedt_envelope` - обертка SEDT
- `sedt_negativity_condition` - условие отрицательности SEDT
- `sedt_parameter_valid` - валидность параметров SEDT

**Импорты:** `Foundations.Core`
**Экспорты:** Все определения эпох

### 3. SEDT.Core.lean

**Назначение:** Константы и теоремы SEDT (Shumak Epoch Drift Theorem)

**Содержание:**
- `α` (alpha_SEDT) - параметр наклона
- `β₀` (beta0_SEDT) - порог отрицательности
- `C` (C_SEDT) - константа дрейфа
- `L₀` (L0_SEDT) - порог длинных эпох
- `K_glue` (K_glue_SEDT) - константа склеивания
- `ε` (epsilon_SEDT) - скорость дрейфа
- `sedt_envelope` - обертка SEDT
- `augmented_potential` - расширенный потенциал
- `potential_change` - изменение потенциала
- Основные теоремы SEDT

**Импорты:** `Foundations.Core`, `Epochs.Core`
**Экспорты:** Все SEDT константы и теоремы

---

## Система алиасов

### Epochs.Aliases.lean

**Назначение:** Удобные сокращения для часто используемых определений

**Содержание:**
- **Foundations алиасы:** `Depth`, `StepType`, `CollatzStep`, `Orbit`
- **Epochs алиасы:** `TEpoch`, `IsTTouch`, `PhaseClass`, `Homogenizer`
- **SEDT алиасы:** `SlopeParam`, `NegativityThreshold`, `DriftConstant`

**Импорты:** Все Core модули
**Экспорты:** Все алиасы

---

## Модули по категориям

### Epochs модули

| Модуль | Назначение | Основные определения |
|--------|------------|---------------------|
| `Structure.lean` | Структура эпох | `Epoch.head`, `Epoch.plateau`, `Epoch.tail` |
| `TouchAnalysis.lean` | Анализ касаний | Леммы о частоте касаний |
| `Homogenization.lean` | Гомогенизация хвоста | Свойства гомогенизации |
| `MultibitBonus.lean` | Многобитный бонус | Анализ бонусов |
| `LongEpochs.lean` | Длинные эпохи | Свойства длинных эпох |
| `APStructure.lean` | AP-структура касаний | Арифметические прогрессии |
| `PhaseClasses.lean` | Классы фаз | Классификация фаз |
| `CosetAdmissibility.lean` | Косет-допустимость | Критерий допустимости |
| `NumeratorCarry.lean` | Перенос числителя | Рекуррентность N_k/M_k/d_k |
| `OrdFact.lean` | Порядковые факты | Порядок 3 по модулю 2^t |

### CycleExclusion модули

| Модуль | Назначение | Основные определения |
|--------|------------|---------------------|
| `CycleDefinition.lean` | Определения циклов | `Cycle`, `is_cycle` |
| `Main.lean` | Основная теорема | `no_nontrivial_odd_cycles` |
| `MixedCycles.lean` | Смешанные циклы | Анализ смешанных циклов |
| `PeriodSum.lean` | Периодические суммы | Телескопический аргумент |
| `PureE1Cycles.lean` | Чистые e=1 циклы | Анализ чистых циклов |
| `RepeatTrick.lean` | Трюк повторения | Техника повторения |

### Convergence модули

| Модуль | Назначение | Основные определения |
|--------|------------|---------------------|
| `MainTheorem.lean` | Основная теорема | `collatz_convergence` |
| `FixedPoints.lean` | Неподвижные точки | Единственность неподвижной точки |
| `Coercivity.lean` | Принудительность | Свойства принудительности |
| `NoAttractors.lean` | Отсутствие аттракторов | Отсутствие аттракторов |

### Mixing модули

| Модуль | Назначение | Основные определения |
|--------|------------|---------------------|
| `PhaseMixing.lean` | Смешивание фаз | Свойства смешивания |
| `Semigroup.lean` | Полугруппы | Генерация полугрупп |
| `TouchFrequency.lean` | Частота касаний | Анализ частоты касаний |

### Stratified модули

| Модуль | Назначение | Основные определения |
|--------|------------|---------------------|
| `BranchingDensity.lean` | Плотность ветвления | Анализ плотности |
| `CompleteStratification.lean` | Полная стратификация | Стратифицированная декомпозиция |
| `Cylinders.lean` | Цилиндры | Цилиндрические множества |
| `Parametrization.lean` | Параметризация | Параметризация траекторий |
| `PreimageLayers.lean` | Слои прообразов | Слоистая структура |

### Utilities модули

| Модуль | Назначение | Основные определения |
|--------|------------|---------------------|
| `Constants.lean` | Константы | Реестр всех констант |
| `Examples.lean` | Примеры | Примеры использования |
| `Notation.lean` | Нотация | Соглашения о нотации |
| `TwoAdicDepth.lean` | 2-adic глубина | Специализированные леммы |

---

## Правила импортов и зависимостей

### Иерархия зависимостей

1. **Уровень 0 (Базовый):** `Foundations.Core`
   - Не зависит ни от чего, кроме Mathlib
   - Содержит базовые математические определения

2. **Уровень 1 (Эпохи):** `Epochs.Core`
   - Зависит от: `Foundations.Core`
   - Содержит определения эпох

3. **Уровень 2 (SEDT):** `SEDT.Core`
   - Зависит от: `Foundations.Core`, `Epochs.Core`
   - Содержит SEDT константы и теоремы

4. **Уровень 3 (Алиасы):** `Epochs.Aliases`
   - Зависит от: Все Core модули
   - Предоставляет удобные алиасы

5. **Уровень 4 (Специализированные модули):** Все остальные модули
   - Зависят от соответствующих Core модулей
   - Используют алиасы для удобства

### Правила импортов

#### ✅ Правильно:
```lean
-- В специализированном модуле
import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core
import Collatz.Epochs.Aliases

-- Использование алиасов
open Collatz.Epochs.Aliases (Depth StepType TEpoch)
```

#### ❌ Неправильно:
```lean
-- Прямой импорт специализированного модуля в Core
import Collatz.Epochs.Structure  -- НЕ ДЕЛАЙТЕ ТАК!

-- Импорт между модулями одного уровня
import Collatz.Epochs.Structure
import Collatz.Epochs.TouchAnalysis  -- НЕ ДЕЛАЙТЕ ТАК!
```

### Запрещенные зависимости

1. **Core модули НЕ должны импортировать специализированные модули**
2. **Модули одного уровня НЕ должны импортировать друг друга**
3. **НЕ создавайте циклические зависимости**

---

## Guidelines для разработки

### Создание нового модуля

1. **Определите уровень модуля:**
   - Epochs → импортируйте `Epochs.Core`
   - CycleExclusion → импортируйте `Foundations.Core`
   - Convergence → импортируйте `Foundations.Core`
   - И т.д.

2. **Импортируйте необходимые Core модули:**
   ```lean
   import Collatz.Foundations.Core
   import Collatz.Epochs.Core
   import Collatz.SEDT.Core
   import Collatz.Epochs.Aliases
   ```

3. **Используйте алиасы:**
   ```lean
   open Collatz.Epochs.Aliases (Depth StepType TEpoch)
   ```

4. **Следуйте соглашениям именования:**
   - Определения: `snake_case`
   - Теоремы: `theorem_name`
   - Леммы: `lemma_name`

### Добавление новых определений

1. **Определите, где должно быть определение:**
   - Базовые математические → `Foundations.Core`
   - Связанные с эпохами → `Epochs.Core`
   - SEDT константы → `SEDT.Core`

2. **Добавьте определение в соответствующий Core модуль**

3. **Добавьте алиас в `Epochs.Aliases` (если нужно)**

4. **Обновите документацию**

### Рефакторинг существующего модуля

1. **Удалите дублированные определения**
2. **Замените на импорты из Core модулей**
3. **Используйте алиасы для удобства**
4. **Проверьте компиляцию**

---

## Соответствие структуре статьи

### Маппинг разделов статьи

| Раздел статьи | Lean4 модули |
|---------------|--------------|
| **Основные результаты** | `Collatz.lean` |
| SEDT | `SEDT.Core.lean` |
| A.LONG.5 | `Epochs.LongEpochs.lean` |
| Cycle Exclusion | `CycleExclusion.Main.lean` |
| Final Convergence | `Convergence.MainTheorem.lean` |
| **Приложение A** | `Foundations.Core.lean`, `Epochs.Core.lean` |
| A.1-A.3 (Точные тождества) | `Foundations.Core.lean` |
| A.E0-A.E1 (Структура эпох) | `Epochs.Structure.lean` |
| A.E3.f-i (Гомогенизация хвоста) | `Epochs.Homogenization.lean` |
| A.E4 (SEDT обертка) | `SEDT.Core.lean` |
| A.MIX (Смешивание фаз) | `Mixing.PhaseMixing.lean` |
| A.LONG (Длинные эпохи) | `Epochs.LongEpochs.lean` |
| **Приложение B** | `CycleExclusion.*.lean` |
| **Приложение C** | `Convergence.*.lean` |
| **Приложение D** | `Utilities.Constants.lean` |

### Критические пути зависимостей

#### A.REC.2 → A.CYC.1 → A.LONG.4 → A.LONG.5
- `Epochs.APStructure.lean` → `Epochs.Homogenization.lean` → `Epochs.LongEpochs.lean`

#### SEDT зависимости
- `Epochs.MultibitBonus.lean` → `Mixing.TouchFrequency.lean` → `SEDT.Core.lean`

---

## Качество и тестирование

### Автоматические проверки

1. **Проверка компиляции:** `lake build`
2. **Проверка архитектуры:** `scripts/architecture_check.py`
3. **Проверка дублирований:** `scripts/duplication_check.py`
4. **Проверка соответствия статье:** `scripts/article_compliance_check.py`

### Метрики качества

- **Компиляция:** 100% модулей компилируются без ошибок
- **Дублирование:** 0 дублированных определений
- **Архитектура:** Соблюдение иерархии зависимостей
- **Соответствие:** Полное соответствие структуре статьи

---

## Заключение

Архитектура проекта Collatz Conjecture обеспечивает:

✅ **Централизованное управление:** Все общие определения в Core модулях  
✅ **Устранение дублирования:** Единые точки определения  
✅ **Четкую иерархию:** Правильные зависимости между модулями  
✅ **Соответствие статье:** Структура кода отражает структуру доказательств  
✅ **Удобство использования:** Система алиасов для часто используемых определений  
✅ **Масштабируемость:** Легкое добавление новых модулей  
✅ **Качество:** Автоматические проверки и метрики  

**Статус:** ✅ Полностью интегрирован и готов к использованию

---

**Документация создана:** AGI Math Research Agent v4.0  
**Дата:** 2025-01-15  
**Версия:** 1.0
