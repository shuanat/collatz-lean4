# План реструктуризации проекта Collatz Lean4

**Дата:** 2025-10-04  
**Цель:** Привести структуру формализации в Lean в соответствие со структурой статьи

## Анализ текущего состояния

### Текущая структура Lean проекта
```
Collatz/
├── Arithmetic.lean          # Базовые арифметические леммы
├── Basic.lean               # T_odd, e(m), depth_minus, основные определения
├── OrdFact.lean             # Теорема ord_{2^t}(3) = 2^{t-2}
├── Epoch.lean               # Структуры эпох, фазы, джанкшены
├── Stratified.lean          # S_n, S_n_star (частично)
├── Coordinates.lean         # k_0(n), m(n,t) параметризация
├── Cylinders.lean           # 2-адические цилиндры C_ℓ
├── SEDT/
│   ├── Core.lean            # V(n), α, β₀, ε, константы
│   ├── Axioms.lean          # 3 моделирующих аксиомы
│   └── Theorems.lean        # Основные теоремы SEDT
├── SEDT.lean                # Агрегирующий модуль
├── Semigroup.lean           # Генерация ⟨Δ⟩
├── Convergence.lean         # Теоремы сходимости
├── Cycles.lean              # Исключение циклов
└── Examples.lean            # Примеры вычислений
```

### Структура статьи (paper-sn/md/)
```
sn-00-*.md                   # Титул, аннотация, ключевые слова
sn-01-introduction.md        # Введение
sn-02-setup-and-defs.md      # §2: Основные определения
sn-03-stratified-decomposition.md  # §3: Стратифицированная декомпозиция
sn-04-main-results.md        # §4: Главные результаты
sn-05-discussion.md          # §5: Обсуждение
sn-06-references.md          # Литература
appendices/
├── A-core.md                # Приложение A: Ядро (эпохи, SEDT)
├── B-cycle-exclusion.md     # Приложение B: Исключение циклов
├── C-final-theorem.md       # Приложение C: Финальная теорема
└── D-symbols-constants.md   # Приложение D: Символы и константы
```

## Проблемы текущей структуры

### 1. **Несоответствие иерархии статье**
- **Статья**: §2 Setup → §3 Stratified → §4 Main Results → Appendices
- **Lean**: Плоская структура с произвольным порядком модулей

### 2. **Отсутствие ключевых разделов из статьи**
- ❌ Нет модуля для Section 2 (Setup): смешано в Basic.lean
- ❌ Нет явного модуля для Preimage Layers (§3)
- ❌ Нет структуры для Main Results (§4)
- ❌ Appendix B (Cycle Exclusion) частично в Cycles.lean
- ❌ Appendix C (Final Theorem) отсутствует

### 3. **Избыточное дублирование**
- `Convergence.lean` и `Cycles.lean` частично пересекаются
- Константы разбросаны по разным файлам
- Нет единого источника для Appendix D (Constants)

### 4. **Непоследовательная модульность SEDT**
- ✅ SEDT хорошо модулизирован (Core, Axioms, Theorems)
- ❌ Остальные разделы не следуют этой практике

## Предлагаемая новая структура

### Уровень 1: Foundations (соответствует §2 Setup)
```
Collatz/Foundations/
├── Basic.lean               # T_odd, e(m), основные определения
├── Arithmetic.lean          # Арифметические леммы (nu_2, модульная арифметика)
├── TwoAdicDepth.lean        # depth_minus, 2-adic valuation properties
└── StepClassification.lean  # Классификация шагов (e=1, e≥2)
```

**Обоснование:** Группирует базовые определения из §2.

### Уровень 2: Stratified Decomposition (соответствует §3)
```
Collatz/Stratified/
├── PreimageLayers.lean      # S_n, S_n_star, основные определения
├── CompleteStratification.lean  # Theorem 4.1 (полная стратификация)
├── BranchingDensity.lean    # Theorem 4.3 (2/3 плотность)
├── Parametrization.lean     # k_0(n), m(n,t), bivariate coordinates
└── Cylinders.lean           # C_ℓ, 2-adic cylinders
```

**Обоснование:** Прямое соответствие §3 статьи.

### Уровень 3: Epoch Theory (соответствует Appendix A.E0-A.E2)
```
Collatz/Epochs/
├── Structure.lean           # Epoch, TEpoch, Head/Plateau/Tail
├── OrdFact.lean             # Q_t = ord_{2^t}(3) = 2^{t-2}
├── PhaseClasses.lean        # φ(E), junction shifts Δ(J)
├── Homogenization.lean      # Homogenizer, affine tail evolution
├── TouchAnalysis.lean       # t-touches, touch frequency
└── LongEpochs.lean          # Theorem A.LONG.5 (infinitely many long epochs)
```

**Обоснование:** Структурирует теорию эпох из Appendix A.

### Уровень 4: SEDT Framework (соответствует Appendix A.E3-A.E4)
```
Collatz/SEDT/
├── Constants.lean           # α, β₀, ε, C, L₀, K_glue (из Appendix D)
├── PotentialFunction.lean   # V(n) = log₂(n) + β·depth_minus(n)
├── Core.lean                # Drift analysis, single-step bounds
├── Axioms.lean              # Touch frequency, overhead bounds
├── EnvelopeTheorem.lean     # Main SEDT: ΔV ≤ -ε·L + β·C
└── Theorems.lean            # Corollaries, negativity lemmas
```

**Обоснование:** Усиливает существующую модульность SEDT.

### Уровень 5: Mixing Theory (соответствует Appendix A.MIX)
```
Collatz/Mixing/
├── Semigroup.lean           # ⟨Δ⟩ generates ℤ/Q_t ℤ
├── PhaseMixing.lean         # Theorem A.HMix(t)
└── TouchFrequency.lean      # p_t = Q_t^{-1} (deterministic)
```

**Обоснование:** Выделяет теорию смешивания фаз в отдельный модуль.

### Уровень 6: Cycle Exclusion (соответствует Appendix B)
```
Collatz/CycleExclusion/
├── PeriodSum.lean           # Lemma 4.1 (telescoping)
├── PureE1Cycles.lean        # Theorem C.B (e=1 cycles impossible)
├── MixedCycles.lean         # SEDT-based exclusion
├── RepeatTrick.lean         # R_0 threshold calculation
└── Main.lean                # Theorem: No nontrivial cycles
```

**Обоснование:** Структурирует Appendix B (Cycle Exclusion).

### Уровень 7: Convergence (соответствует §4 + Appendix C)
```
Collatz/Convergence/
├── Coercivity.lean          # Coercivity lemma (Appendix C)
├── NoAttractors.lean        # No other attractors besides 1
├── MainTheorem.lean         # Global convergence to 1
└── FixedPoints.lean         # Uniqueness of fixed point
```

**Обоснование:** Финальная теорема сходимости.

### Уровень 8: Utilities and Examples
```
Collatz/Utilities/
├── Constants.lean           # Centralized constants (Appendix D)
├── Notation.lean            # Unified notation conventions
└── Examples.lean            # Concrete computations

Collatz/Documentation/
├── ProofRoadmap.lean        # High-level proof structure
└── PaperMapping.lean        # Mapping to paper sections/theorems
```

**Обоснование:** Вспомогательные модули для навигации и документации.

## Полная новая структура (дерево)
```
Collatz/
├── Foundations/             # §2 Setup and Definitions
│   ├── Basic.lean
│   ├── Arithmetic.lean
│   ├── TwoAdicDepth.lean
│   └── StepClassification.lean
├── Stratified/              # §3 Stratified Decomposition
│   ├── PreimageLayers.lean
│   ├── CompleteStratification.lean
│   ├── BranchingDensity.lean
│   ├── Parametrization.lean
│   └── Cylinders.lean
├── Epochs/                  # Appendix A.E0-A.E2
│   ├── Structure.lean
│   ├── OrdFact.lean
│   ├── PhaseClasses.lean
│   ├── Homogenization.lean
│   ├── TouchAnalysis.lean
│   └── LongEpochs.lean
├── SEDT/                    # Appendix A.E3-A.E4
│   ├── Constants.lean
│   ├── PotentialFunction.lean
│   ├── Core.lean
│   ├── Axioms.lean
│   ├── EnvelopeTheorem.lean
│   └── Theorems.lean
├── Mixing/                  # Appendix A.MIX
│   ├── Semigroup.lean
│   ├── PhaseMixing.lean
│   └── TouchFrequency.lean
├── CycleExclusion/          # Appendix B
│   ├── PeriodSum.lean
│   ├── PureE1Cycles.lean
│   ├── MixedCycles.lean
│   ├── RepeatTrick.lean
│   └── Main.lean
├── Convergence/             # §4 + Appendix C
│   ├── Coercivity.lean
│   ├── NoAttractors.lean
│   ├── MainTheorem.lean
│   └── FixedPoints.lean
├── Utilities/
│   ├── Constants.lean       # Appendix D
│   ├── Notation.lean
│   └── Examples.lean
├── Documentation/
│   ├── ProofRoadmap.lean
│   └── PaperMapping.lean
└── Collatz.lean             # Root aggregating module
```

## План миграции

### Фаза 1: Создание структуры папок
```bash
mkdir -p Collatz/{Foundations,Stratified,Epochs,Mixing,CycleExclusion,Convergence,Utilities,Documentation}
```

### Фаза 2: Перенос существующих файлов

#### Foundations
- `Basic.lean` → `Foundations/Basic.lean`
- `Arithmetic.lean` → `Foundations/Arithmetic.lean`
- Выделить `TwoAdicDepth.lean` из `Basic.lean`
- Выделить `StepClassification.lean` из `Basic.lean`

#### Stratified
- `Stratified.lean` → `Stratified/PreimageLayers.lean`
- Создать `Stratified/CompleteStratification.lean` (Theorem 4.1)
- Создать `Stratified/BranchingDensity.lean` (Theorem 4.3)
- `Coordinates.lean` → `Stratified/Parametrization.lean`
- `Cylinders.lean` → `Stratified/Cylinders.lean`

#### Epochs
- `Epoch.lean` → `Epochs/Structure.lean`
- `OrdFact.lean` → `Epochs/OrdFact.lean`
- Выделить phase classes из `Epoch.lean` → `Epochs/PhaseClasses.lean`
- Создать `Epochs/Homogenization.lean`
- Создать `Epochs/TouchAnalysis.lean`
- Создать `Epochs/LongEpochs.lean` (A.LONG.5)

#### SEDT (рефакторинг)
- Создать `SEDT/Constants.lean` из `SEDT/Core.lean`
- Создать `SEDT/PotentialFunction.lean` из `SEDT/Core.lean`
- Разбить `SEDT/Theorems.lean` на `EnvelopeTheorem.lean` + `Theorems.lean`

#### Mixing
- `Semigroup.lean` → `Mixing/Semigroup.lean`
- Создать `Mixing/PhaseMixing.lean` (A.HMix)
- Создать `Mixing/TouchFrequency.lean`

#### CycleExclusion
- Выделить из `Cycles.lean`:
  - `CycleExclusion/PeriodSum.lean` (period_sum lemmas)
  - `CycleExclusion/PureE1Cycles.lean` (e=1 cycle exclusion)
  - `CycleExclusion/MixedCycles.lean` (SEDT-based exclusion)
  - `CycleExclusion/RepeatTrick.lean` (R_0 calculation)
  - `CycleExclusion/Main.lean` (main theorem)

#### Convergence
- Выделить из `Convergence.lean`:
  - `Convergence/Coercivity.lean`
  - `Convergence/MainTheorem.lean`
  - `Convergence/FixedPoints.lean`
  - `Convergence/NoAttractors.lean`

#### Utilities
- Создать `Utilities/Constants.lean` (централизованные константы)
- Создать `Utilities/Notation.lean` (unified notation)
- `Examples.lean` → `Utilities/Examples.lean`

### Фаза 3: Создание новых модулей

#### Documentation
```lean
-- Documentation/ProofRoadmap.lean
/-!
# Proof Structure Roadmap

Maps the proof chain to paper sections:

1. Setup (§2) → Foundations/
2. Stratification (§3) → Stratified/
3. Epoch Theory (App A.E0-E2) → Epochs/
4. SEDT (App A.E3-E4) → SEDT/
5. Mixing (App A.MIX) → Mixing/
6. Cycle Exclusion (App B) → CycleExclusion/
7. Convergence (§4 + App C) → Convergence/
-/
```

```lean
-- Documentation/PaperMapping.lean
/-!
# Paper-to-Lean Mapping

## Section 2: Setup and Definitions
- Definition 2.1 (T_odd) → Foundations.Basic.T_odd
- Definition 2.2 (depth_minus) → Foundations.TwoAdicDepth.depth_minus
- Lemma 2.3 (e≥1 for odd m) → Foundations.Basic.e_pos_of_odd

## Section 3: Stratified Decomposition
- Theorem 4.1 → Stratified.CompleteStratification.complete_stratification
- Theorem 4.3 → Stratified.BranchingDensity.branching_decomposition
- Theorem 4.5 → Stratified.Parametrization.parametric_bijection

## Appendix A: Core
- Theorem A.E4 (SEDT) → SEDT.EnvelopeTheorem.sedt_envelope_bound
- Theorem A.HMix(t) → Mixing.PhaseMixing.phase_mixing_theorem
- Theorem A.LONG.5 → Epochs.LongEpochs.infinitely_many_long_epochs

## Appendix B: Cycle Exclusion
- Lemma B.1 (Period sum) → CycleExclusion.PeriodSum.period_sum_zero
- Theorem C.B (e=1 cycles) → CycleExclusion.PureE1Cycles.no_e1_cycles
- Theorem B.Main → CycleExclusion.Main.no_nontrivial_cycles

## Appendix C: Final Theorem
- Lemma C.1 (Coercivity) → Convergence.Coercivity.coercivity
- Theorem C.Main → Convergence.MainTheorem.global_convergence
-/
```

### Фаза 4: Обновление импортов

Создать агрегирующие модули для каждой подпапки:

```lean
-- Foundations.lean
import Collatz.Foundations.Basic
import Collatz.Foundations.Arithmetic
import Collatz.Foundations.TwoAdicDepth
import Collatz.Foundations.StepClassification

-- Stratified.lean
import Collatz.Stratified.PreimageLayers
import Collatz.Stratified.CompleteStratification
import Collatz.Stratified.BranchingDensity
import Collatz.Stratified.Parametrization
import Collatz.Stratified.Cylinders

-- Epochs.lean (аналогично)
-- SEDT.lean (уже существует, обновить)
-- Mixing.lean (новый)
-- CycleExclusion.lean (новый)
-- Convergence.lean (рефакторить)
```

Обновить корневой `Collatz.lean`:
```lean
-- Collatz.lean (root module)
import Collatz.Foundations
import Collatz.Stratified
import Collatz.Epochs
import Collatz.SEDT
import Collatz.Mixing
import Collatz.CycleExclusion
import Collatz.Convergence
import Collatz.Utilities
```

### Фаза 5: Тестирование и верификация
1. ✅ Все модули компилируются без ошибок
2. ✅ Все тесты проходят (`lake build`)
3. ✅ Документация актуальна
4. ✅ Соответствие структуре статьи проверено

## Преимущества новой структуры

### 1. **Прямое соответствие статье**
- Каждая папка соответствует разделу статьи
- Легко найти формализацию любого утверждения
- Упрощает review и сопровождение

### 2. **Модульность и масштабируемость**
- Чёткие границы между модулями
- Независимые подпроекты (Foundations, SEDT, Mixing)
- Легко добавлять новые результаты

### 3. **Образовательная ценность**
- Структура сама по себе объясняет логику доказательства
- Roadmap и Mapping помогают навигации
- Четкая прогрессия: Setup → Stratified → Epochs → SEDT → Cycles → Convergence

### 4. **Соответствие best practices**
- Аналогично структуре mathlib4 (по модулям)
- Следует рекомендациям Lean community
- Готовность к публикации/формальному review

## Таблица соответствия: Статья → Lean

| Статья | Текущий Lean | Новый Lean |
|--------|--------------|------------|
| §2 Setup | `Basic.lean` (частично) | `Foundations/` (4 модуля) |
| §3 Stratified | `Stratified.lean` (частично) | `Stratified/` (5 модулей) |
| §4 Main Results | Разбросано | `Convergence/` (4 модуля) |
| App A.E0-E2 (Epochs) | `Epoch.lean`, `OrdFact.lean` | `Epochs/` (6 модулей) |
| App A.E3-E4 (SEDT) | `SEDT/` (хорошо) | `SEDT/` (рефакторинг: 6 модулей) |
| App A.MIX (Mixing) | `Semigroup.lean` | `Mixing/` (3 модуля) |
| App B (Cycles) | `Cycles.lean` | `CycleExclusion/` (5 модулей) |
| App C (Final) | `Convergence.lean` (частично) | `Convergence/` (завершить) |
| App D (Constants) | Разбросано | `Utilities/Constants.lean` |

## Метрики успеха

### До реструктуризации
- 📁 Папки: 2 (корень + SEDT)
- 📄 Файлов в корне: 13
- 🔗 Связь со статьёй: Неявная
- 📖 Документация: Разрозненная
- ⚖️ Модульность: Частичная (только SEDT)

### После реструктуризации (цель)
- 📁 Папки: 9 (Foundations, Stratified, Epochs, SEDT, Mixing, CycleExclusion, Convergence, Utilities, Documentation)
- 📄 Файлов в корне: 1 (Collatz.lean)
- 🔗 Связь со статьёй: **Прямое соответствие 1:1**
- 📖 Документация: **Централизованная (ProofRoadmap, PaperMapping)**
- ⚖️ Модульность: **Полная (все разделы)**

## Приоритизация задач

### Priority 1: Критические разделы (соответствие статье)
1. ✅ **Foundations/** - основа всего
2. ✅ **Stratified/** - §3 статьи (ключевой раздел)
3. ✅ **CycleExclusion/** - Appendix B (центральный результат)

### Priority 2: Завершение теории
4. ✅ **Epochs/** - структура для всего остального
5. ✅ **Mixing/** - выделить из SEDT
6. ✅ **Convergence/** - финальная теорема

### Priority 3: Документация и навигация
7. ✅ **Utilities/Constants.lean** - Appendix D
8. ✅ **Documentation/** - roadmap и mapping

### Priority 4: Полировка
9. ✅ Обновить README.md с новой структурой
10. ✅ Создать CONTRIBUTING.md с guidelines
11. ✅ Добавить CI/CD для проверки структуры

## Следующие шаги (немедленные действия)

1. **Создать issue/branch** для реструктуризации
2. **Получить feedback** от коллег/reviewers
3. **Начать миграцию** с Priority 1 задач
4. **Проверить компиляцию** после каждого шага
5. **Обновить документацию** параллельно с кодом

---

**Примечание:** Эта реструктуризация не меняет математическое содержание, только организацию кода для лучшей читаемости и соответствия статье.

