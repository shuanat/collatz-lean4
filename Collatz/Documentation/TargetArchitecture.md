# Target Architecture for Collatz Lean4 Project

**Дата:** 2025-01-15  
**Проект:** Collatz Conjecture - Epoch-Based Amortized Lyapunov Route  
**Цель:** Спроектировать целевую архитектуру, точно соответствующую структуре статьи

## Executive Summary

Целевая архитектура обеспечивает:
- **Точное соответствие статье** - структура кода отражает структуру доказательств
- **Централизованная архитектура** - Core.lean как основа всех модулей
- **Устранение дублирований** - единые определения для всех модулей
- **Правильная иерархия зависимостей** - четкая структура импортов

## Architecture Overview

```
Collatz.lean (Main Module)
├── Foundations/
│   ├── Core.lean (Central definitions)
│   ├── Arithmetic.lean (Basic arithmetic)
│   ├── StepClassification.lean (Step types)
│   └── TwoAdicDepth.lean (2-adic depth)
├── Epochs/
│   ├── Core.lean (Central epoch definitions)
│   ├── Structure.lean (Epoch structure)
│   ├── TouchAnalysis.lean (Touch analysis)
│   ├── Homogenization.lean (Tail homogenization)
│   ├── MultibitBonus.lean (Multibit bonus)
│   ├── LongEpochs.lean (Long epochs)
│   ├── APStructure.lean (AP structure)
│   ├── PhaseClasses.lean (Phase classes)
│   ├── CosetAdmissibility.lean (Coset admissibility)
│   ├── NumeratorCarry.lean (Numerator carry)
│   └── OrdFact.lean (Order factorization)
├── SEDT/
│   ├── Core.lean (SEDT theorem)
│   ├── Axioms.lean (SEDT axioms)
│   └── Theorems.lean (SEDT theorems)
├── Mixing/
│   ├── PhaseMixing.lean (Phase mixing)
│   ├── TouchFrequency.lean (Touch frequency)
│   └── Semigroup.lean (Semigroup structure)
├── CycleExclusion/
│   ├── Main.lean (Main theorem)
│   ├── CycleDefinition.lean (Cycle definitions)
│   ├── MixedCycles.lean (Mixed cycles)
│   ├── PureE1Cycles.lean (Pure e=1 cycles)
│   ├── PeriodSum.lean (Period sum)
│   └── RepeatTrick.lean (Repeat trick)
├── Convergence/
│   ├── MainTheorem.lean (Final convergence)
│   ├── FixedPoints.lean (Fixed points)
│   ├── Coercivity.lean (Coercivity)
│   └── NoAttractors.lean (No attractors)
├── Stratified/
│   ├── CompleteStratification.lean (Complete stratification)
│   ├── BranchingDensity.lean (Branching density)
│   ├── Cylinders.lean (Cylinders)
│   ├── Parametrization.lean (Parametrization)
│   └── PreimageLayers.lean (Preimage layers)
├── Utilities/
│   ├── Constants.lean (All constants)
│   ├── Notation.lean (Notation)
│   ├── Examples.lean (Examples)
│   └── TwoAdicDepth.lean (2-adic depth utilities)
└── Documentation/
    ├── PaperMapping.lean (Paper-code mapping)
    ├── ProofStructure.lean (Proof structure)
    └── Architecture.lean (Architecture documentation)
```

## Module Hierarchy

### Level 0: Foundations
**Purpose:** Базовые математические определения
**Modules:**
- `Collatz/Foundations/Core.lean` - Центральные определения
- `Collatz/Foundations/Arithmetic.lean` - Арифметические леммы
- `Collatz/Foundations/StepClassification.lean` - Классификация шагов
- `Collatz/Foundations/TwoAdicDepth.lean` - 2-adic глубина

**Dependencies:** Mathlib only
**Exports:** Все базовые определения для остальных модулей

### Level 1: Epochs
**Purpose:** Структура эпох и анализ касаний
**Modules:**
- `Collatz/Epochs/Core.lean` - Центральные определения эпох
- `Collatz/Epochs/Structure.lean` - Структура эпох
- `Collatz/Epochs/TouchAnalysis.lean` - Анализ касаний
- `Collatz/Epochs/Homogenization.lean` - Гомогенизация хвоста
- `Collatz/Epochs/MultibitBonus.lean` - Многобитный бонус
- `Collatz/Epochs/LongEpochs.lean` - Длинные эпохи
- `Collatz/Epochs/APStructure.lean` - AP-структура
- `Collatz/Epochs/PhaseClasses.lean` - Классы фаз
- `Collatz/Epochs/CosetAdmissibility.lean` - Косет-допустимость
- `Collatz/Epochs/NumeratorCarry.lean` - Числитель и перенос
- `Collatz/Epochs/OrdFact.lean` - Порядковая факторизация

**Dependencies:** Foundations
**Exports:** Все определения эпох для SEDT и Mixing

### Level 2: SEDT
**Purpose:** Теорема SEDT и связанные результаты
**Modules:**
- `Collatz/SEDT/Core.lean` - Основная теорема SEDT
- `Collatz/SEDT/Axioms.lean` - Аксиомы SEDT
- `Collatz/SEDT/Theorems.lean` - Теоремы SEDT

**Dependencies:** Epochs, Mixing
**Exports:** SEDT теорема для CycleExclusion и Convergence

### Level 3: Mixing
**Purpose:** Теория смешивания фаз
**Modules:**
- `Collatz/Mixing/PhaseMixing.lean` - Смешивание фаз
- `Collatz/Mixing/TouchFrequency.lean` - Частота касаний
- `Collatz/Mixing/Semigroup.lean` - Полугрупповая структура

**Dependencies:** Epochs
**Exports:** Частота касаний для SEDT

### Level 4: CycleExclusion
**Purpose:** Исключение циклов
**Modules:**
- `Collatz/CycleExclusion/Main.lean` - Основная теорема
- `Collatz/CycleExclusion/CycleDefinition.lean` - Определения циклов
- `Collatz/CycleExclusion/MixedCycles.lean` - Смешанные циклы
- `Collatz/CycleExclusion/PureE1Cycles.lean` - Чистые e=1 циклы
- `Collatz/CycleExclusion/PeriodSum.lean` - Периодические суммы
- `Collatz/CycleExclusion/RepeatTrick.lean` - Трюк повторения

**Dependencies:** SEDT, Epochs
**Exports:** Исключение циклов для Convergence

### Level 5: Convergence
**Purpose:** Финальная сходимость
**Modules:**
- `Collatz/Convergence/MainTheorem.lean` - Основная теорема сходимости
- `Collatz/Convergence/FixedPoints.lean` - Неподвижные точки
- `Collatz/Convergence/Coercivity.lean` - Принудительность
- `Collatz/Convergence/NoAttractors.lean` - Отсутствие аттракторов

**Dependencies:** SEDT, CycleExclusion
**Exports:** Финальная теорема сходимости

### Level 6: Stratified
**Purpose:** Стратифицированная декомпозиция
**Modules:**
- `Collatz/Stratified/CompleteStratification.lean` - Полная стратификация
- `Collatz/Stratified/BranchingDensity.lean` - Плотность ветвления
- `Collatz/Stratified/Cylinders.lean` - Цилиндры
- `Collatz/Stratified/Parametrization.lean` - Параметризация
- `Collatz/Stratified/PreimageLayers.lean` - Слои прообразов

**Dependencies:** Foundations
**Exports:** Стратифицированная структура для Epochs

### Level 7: Utilities
**Purpose:** Утилиты и константы
**Modules:**
- `Collatz/Utilities/Constants.lean` - Все константы
- `Collatz/Utilities/Notation.lean` - Нотация
- `Collatz/Utilities/Examples.lean` - Примеры
- `Collatz/Utilities/TwoAdicDepth.lean` - Утилиты 2-adic глубины

**Dependencies:** Foundations
**Exports:** Константы и утилиты для всех модулей

### Level 8: Documentation
**Purpose:** Документация архитектуры
**Modules:**
- `Collatz/Documentation/PaperMapping.lean` - Соответствие с бумагой
- `Collatz/Documentation/ProofStructure.lean` - Структура доказательств
- `Collatz/Documentation/Architecture.lean` - Документация архитектуры

**Dependencies:** All modules
**Exports:** Документация для разработчиков

## Core.lean Architecture

### Collatz/Foundations/Core.lean
**Purpose:** Центральные математические определения
**Contents:**
```lean
-- Basic definitions
def depth_minus (r : ℕ) : ℕ := (r + 1).factorization 2
def step_type (r : ℕ) : ℕ := (3 * r + 1).factorization 2
def collatz_step (r : ℕ) : ℕ := (3 * r + 1) / 2^step_type r

-- Basic lemmas
lemma depth_minus_nonneg (r : ℕ) : depth_minus r ≥ 0
lemma step_type_pos (r : ℕ) : step_type r ≥ 1
lemma collatz_step_odd (r : ℕ) : Odd (collatz_step r)
```

### Collatz/Epochs/Core.lean
**Purpose:** Центральные определения эпох
**Contents:**
```lean
-- Epoch structure
structure TEpoch (t : ℕ) where
  start : ℕ
  length : ℕ
  head : List ℕ
  plateau : List ℕ
  tail : List ℕ

-- Touch definitions
def is_t_touch (M_k : ℕ) (t : ℕ) : Prop :=
  M_k ≡ s_t (mod 2^t)

-- Touch set
def T_t (t : ℕ) : Set ℕ :=
  {k : ℕ | is_t_touch M_k t}

-- Basic properties
lemma t_touch_residue_unique (t : ℕ) :
  ∃! s : ℕ, s ≡ -5 * 3^(-1) (mod 2^t)
```

## Naming Conventions

### Paper Notation Mapping
| Paper Symbol | Lean4 Name | Location |
|--------------|------------|----------|
| `depth₋(n)` | `depth_minus` | `Foundations/Core.lean` |
| `e(m)` | `step_type` | `Foundations/Core.lean` |
| `T_t` | `T_t` | `Epochs/Core.lean` |
| `s_t` | `s_t` | `Epochs/Core.lean` |
| `Q_t` | `Q_t` | `Utilities/Constants.lean` |
| `α(t,U)` | `α` | `Utilities/Constants.lean` |
| `β₀(t,U)` | `β₀` | `Utilities/Constants.lean` |
| `p_t` | `p_touch` | `Mixing/TouchFrequency.lean` |

### Function Naming
- **Definitions:** `def function_name`
- **Lemmas:** `lemma property_name`
- **Theorems:** `theorem theorem_name`
- **Constants:** `def CONSTANT_NAME`

### Module Naming
- **Core modules:** `Core.lean`
- **Main modules:** `Main.lean`
- **Utility modules:** `Utilities/ModuleName.lean`
- **Documentation:** `Documentation/ModuleName.lean`

## Import Rules

### Dependency Rules
1. **Level 0 (Foundations):** Only Mathlib
2. **Level 1 (Epochs):** Foundations only
3. **Level 2 (SEDT):** Epochs + Mixing
4. **Level 3 (Mixing):** Epochs only
5. **Level 4 (CycleExclusion):** SEDT + Epochs
6. **Level 5 (Convergence):** SEDT + CycleExclusion
7. **Level 6 (Stratified):** Foundations only
8. **Level 7 (Utilities):** Foundations only
9. **Level 8 (Documentation):** All modules

### Import Patterns
```lean
-- Level 0: Foundations
import Mathlib.Data.Nat.Factorization.Basic

-- Level 1: Epochs
import Collatz.Foundations.Core
import Collatz.Foundations.Arithmetic

-- Level 2: SEDT
import Collatz.Epochs.Core
import Collatz.Mixing.TouchFrequency

-- Level 3: Mixing
import Collatz.Epochs.Core

-- Level 4: CycleExclusion
import Collatz.SEDT.Core
import Collatz.Epochs.Core

-- Level 5: Convergence
import Collatz.SEDT.Core
import Collatz.CycleExclusion.Main

-- Level 6: Stratified
import Collatz.Foundations.Core

-- Level 7: Utilities
import Collatz.Foundations.Core

-- Level 8: Documentation
import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core
import Collatz.Mixing.TouchFrequency
import Collatz.CycleExclusion.Main
import Collatz.Convergence.MainTheorem
import Collatz.Stratified.CompleteStratification
import Collatz.Utilities.Constants
```

## Quality Standards

### Code Quality
- **Consistency:** Единый стиль кодирования
- **Documentation:** Полная документация всех определений
- **Testing:** Тесты для всех критических функций
- **Performance:** Оптимизированные алгоритмы

### Architecture Quality
- **Modularity:** Четкое разделение ответственности
- **Cohesion:** Высокая связанность внутри модулей
- **Coupling:** Низкая связанность между модулями
- **Extensibility:** Легкое расширение функциональности

### Documentation Quality
- **Completeness:** Полная документация архитектуры
- **Accuracy:** Точное соответствие коду
- **Clarity:** Понятные объяснения
- **Examples:** Примеры использования

## Migration Strategy

### Phase 1: Foundation
1. Создать `Collatz/Foundations/Core.lean`
2. Перенести все базовые определения
3. Устранить дублирования

### Phase 2: Epochs
1. Создать `Collatz/Epochs/Core.lean`
2. Рефакторить все Epochs модули
3. Унифицировать определения

### Phase 3: SEDT
1. Создать `Collatz/SEDT/Core.lean`
2. Интегрировать с Epochs и Mixing
3. Доказать основную теорему

### Phase 4: Integration
1. Рефакторить все остальные модули
2. Исправить зависимости
3. Создать документацию

## Success Criteria

- [ ] Все модули используют централизованную архитектуру
- [ ] Нет дублирований между модулями
- [ ] Правильная иерархия зависимостей
- [ ] Именование соответствует бумаге
- [ ] Все модули компилируются
- [ ] Документация архитектуры создана
- [ ] Автоматические проверки работают

## Conclusion

Целевая архитектура обеспечивает точное соответствие структуре статьи, устраняет дублирования и создает централизованную систему модулей. Архитектура готова к реализации.

**Следующий шаг:** Начать Фазу 2 - создание централизованной архитектуры
