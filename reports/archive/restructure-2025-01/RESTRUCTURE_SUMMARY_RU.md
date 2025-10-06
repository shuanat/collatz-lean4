# Сводка реструктуризации проекта Collatz Lean4

**Дата:** 2025-10-04  
**Статус:** 📋 План подготовлен

## 🎯 Цель

Привести структуру формализации в Lean в **прямое соответствие** со структурой научной статьи.

## 📊 Текущее состояние vs Целевое

### ❌ Текущая структура (плоская)
```
Collatz/
├── 13 файлов в корне (неорганизовано)
├── SEDT/ (единственная подпапка)
└── Нет явной связи со статьёй
```

**Проблемы:**
- Нет соответствия разделам статьи
- Трудно найти формализацию конкретного утверждения
- Отсутствуют ключевые разделы (Appendix B, C)
- Константы разбросаны по файлам

### ✅ Целевая структура (модульная, соответствует статье)
```
Collatz/
├── Foundations/          # §2 Setup and Definitions
├── Stratified/           # §3 Stratified Decomposition
├── Epochs/               # Appendix A.E0-A.E2
├── SEDT/                 # Appendix A.E3-A.E4 (рефакторинг)
├── Mixing/               # Appendix A.MIX
├── CycleExclusion/       # Appendix B ⭐
├── Convergence/          # §4 + Appendix C ⭐
├── Utilities/            # Appendix D (Constants)
└── Documentation/        # Roadmap + Paper Mapping
```

**Преимущества:**
- ✅ Прямое соответствие структуре статьи (1:1)
- ✅ Каждая теорема легко найти
- ✅ Модульность и масштабируемость
- ✅ Готовность к публикации

## 🗺️ Карта соответствия: Статья → Lean

| Раздел статьи | Текущий Lean | → | Новый Lean |
|---------------|--------------|---|------------|
| **§2 Setup** | `Basic.lean` | → | `Foundations/` (4 модуля) |
| **§3 Stratified** | `Stratified.lean` | → | `Stratified/` (5 модулей) |
| **§4 Main Results** | Разбросано | → | `Convergence/` (4 модуля) |
| **App A: Epochs** | `Epoch.lean`, `OrdFact.lean` | → | `Epochs/` (6 модулей) |
| **App A: SEDT** | `SEDT/` | → | `SEDT/` (**рефакторинг**: 6 модулей) |
| **App A: Mixing** | `Semigroup.lean` | → | `Mixing/` (3 модуля) |
| **App B: Cycles** ⭐ | `Cycles.lean` | → | `CycleExclusion/` (**5 модулей**) |
| **App C: Final** ⭐ | Частично | → | `Convergence/` (**завершить**) |
| **App D: Constants** | Разбросано | → | `Utilities/Constants.lean` |

## 📦 Новые модули (детали)

### 1. Foundations/ (§2 Setup)
```
├── Basic.lean               # T_odd, e(m), collatz_seq
├── Arithmetic.lean          # ν_2, модульная арифметика
├── TwoAdicDepth.lean        # depth_minus, свойства
└── StepClassification.lean  # e=1, e≥2 классификация
```

### 2. Stratified/ (§3 Stratified Decomposition)
```
├── PreimageLayers.lean           # S_n, S_n_star
├── CompleteStratification.lean   # Theorem 4.1
├── BranchingDensity.lean         # Theorem 4.3 (2/3 плотность)
├── Parametrization.lean          # k_0(n), m(n,t)
└── Cylinders.lean                # C_ℓ, 2-adic cylinders
```

### 3. Epochs/ (Appendix A.E0-A.E2)
```
├── Structure.lean          # Epoch, TEpoch, Head/Plateau/Tail
├── OrdFact.lean            # Q_t = 2^{t-2} (уже есть)
├── PhaseClasses.lean       # φ(E), junction shifts Δ(J)
├── Homogenization.lean     # Homogenizer, affine evolution
├── TouchAnalysis.lean      # t-touches, frequency
└── LongEpochs.lean         # A.LONG.5 (infinitely many)
```

### 4. SEDT/ (Appendix A.E3-A.E4) — рефакторинг
```
├── Constants.lean          # α, β₀, ε, C, L₀, K_glue
├── PotentialFunction.lean  # V(n) = log₂(n) + β·depth_minus(n)
├── Core.lean               # Drift analysis, bounds
├── Axioms.lean             # 3 моделирующих аксиомы (уже есть)
├── EnvelopeTheorem.lean    # Main SEDT: ΔV ≤ -ε·L + β·C
└── Theorems.lean           # Corollaries, negativity
```

### 5. Mixing/ (Appendix A.MIX)
```
├── Semigroup.lean          # ⟨Δ⟩ generates ℤ/Q_t ℤ
├── PhaseMixing.lean        # Theorem A.HMix(t)
└── TouchFrequency.lean     # p_t = Q_t^{-1} (deterministic)
```

### 6. CycleExclusion/ (Appendix B) ⭐ НОВЫЙ
```
├── PeriodSum.lean          # Lemma: telescoping sum = 0
├── PureE1Cycles.lean       # Theorem C.B (e=1 impossible)
├── MixedCycles.lean        # SEDT-based exclusion
├── RepeatTrick.lean        # R_0 threshold calculation
└── Main.lean               # Main theorem: no nontrivial cycles
```

### 7. Convergence/ (§4 + Appendix C) ⭐ ЗАВЕРШИТЬ
```
├── Coercivity.lean         # Coercivity lemma (App C)
├── NoAttractors.lean       # No other attractors besides 1
├── MainTheorem.lean        # Global convergence to 1
└── FixedPoints.lean        # Uniqueness of fixed point
```

### 8. Utilities/ & Documentation/
```
Utilities/
├── Constants.lean          # Appendix D (централизованно)
├── Notation.lean           # Унифицированная нотация
└── Examples.lean           # Конкретные вычисления

Documentation/
├── ProofRoadmap.lean       # High-level структура доказательства
└── PaperMapping.lean       # Таблица: Paper theorem → Lean definition
```

## 🚀 План миграции (5 фаз)

### Фаза 1: Создание структуры папок
```bash
mkdir -p Collatz/{Foundations,Stratified,Epochs,Mixing,CycleExclusion,Convergence,Utilities,Documentation}
```

### Фаза 2: Перенос существующих файлов
- `Basic.lean` → `Foundations/Basic.lean`
- `Stratified.lean` → `Stratified/PreimageLayers.lean`
- `Epoch.lean` → `Epochs/Structure.lean`
- `Cycles.lean` → разбить на `CycleExclusion/*` (5 модулей)
- `Convergence.lean` → разбить на `Convergence/*` (4 модуля)

### Фаза 3: Создание новых модулей
- **CycleExclusion/** (5 новых модулей)
- **Mixing/** (2 новых модуля)
- **Documentation/** (2 новых модуля)
- **Utilities/Constants.lean**

### Фаза 4: Обновление импортов
Создать агрегирующие модули для каждой подпапки:
```lean
-- Foundations.lean
import Collatz.Foundations.Basic
import Collatz.Foundations.Arithmetic
...

-- Корневой Collatz.lean
import Collatz.Foundations
import Collatz.Stratified
import Collatz.Epochs
import Collatz.SEDT
import Collatz.Mixing
import Collatz.CycleExclusion
import Collatz.Convergence
```

### Фаза 5: Тестирование и верификация
- ✅ `lake build` проходит без ошибок
- ✅ Все тесты проходят
- ✅ Документация актуальна
- ✅ Соответствие статье проверено

## 🎯 Приоритизация

### Priority 1: Критические разделы (соответствие статье) 🔥
1. **Foundations/** — основа всего
2. **Stratified/** — §3 статьи (ключевой раздел)
3. **CycleExclusion/** — Appendix B (центральный результат)

### Priority 2: Завершение теории
4. **Epochs/** — структура для всего остального
5. **Mixing/** — выделить из SEDT
6. **Convergence/** — финальная теорема

### Priority 3: Документация и навигация
7. **Utilities/Constants.lean** — Appendix D
8. **Documentation/** — roadmap и mapping

### Priority 4: Полировка
9. Обновить README.md с новой структурой
10. Создать CONTRIBUTING.md с guidelines
11. Добавить CI/CD для проверки структуры

## 📈 Метрики успеха

| Метрика | До | После | Улучшение |
|---------|----|----|-----------|
| **Папки** | 2 | 9 | **+350%** |
| **Файлов в корне** | 13 | 1 | **-92%** |
| **Связь со статьёй** | Неявная | Прямая 1:1 | ✅ **100%** |
| **Документация** | Разрозненная | Централизованная | ✅ |
| **Модульность** | Частичная | Полная | ✅ |

## 📝 Следующие шаги (immediate)

1. ✅ **Создан план** (`RESTRUCTURE_PLAN.md`)
2. 🔄 **Получить feedback** от коллег/reviewers
3. 🚧 **Начать миграцию** с Priority 1 (Foundations, Stratified, CycleExclusion)
4. ✅ **Проверить компиляцию** после каждого шага
5. 📚 **Обновить документацию** параллельно с кодом

## 🔗 Связанные файлы

- **Детальный план:** `RESTRUCTURE_PLAN.md` (English, 15+ страниц)
- **Текущий README:** `README.md`
- **Статья:** `../collatz-paper/paper-sn/md/`

## ✨ Ключевые преимущества

1. **Прямое соответствие статье** — каждая теорема легко найти
2. **Модульность** — независимые подпроекты, легко расширять
3. **Образовательная ценность** — структура объясняет логику доказательства
4. **Best practices** — готовность к публикации и formal review
5. **Навигация** — ProofRoadmap и PaperMapping упрощают работу

---

**Автор:** AI Assistant  
**Дата:** 2025-10-04  
**Статус:** ✅ План готов к реализации

**Примечание:** Реструктуризация не меняет математическое содержание, только организацию для лучшей читаемости и соответствия статье.

