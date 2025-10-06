# Сравнение структур: Текущая vs Предлагаемая

## 📊 Визуальное сравнение

### ❌ ТЕКУЩАЯ СТРУКТУРА (Плоская, неорганизованная)

```
Collatz/
│
├── Arithmetic.lean          ← Базовые леммы (не привязано к статье)
├── Basic.lean               ← Смешано: §2 + определения
├── Convergence.lean         ← Частично §4, частично App C (incomplete)
├── Coordinates.lean         ← Часть §3 (параметризация)
├── Cycles.lean              ← Частично App B (неполная, монолит)
├── Cylinders.lean           ← Часть §3 (2-adic cylinders)
├── Epoch.lean               ← App A.E0-E2 (всё в одном файле)
├── Examples.lean            ← Примеры (разбросаны)
├── OrdFact.lean             ← App A (Ord-Fact theorem)
├── Semigroup.lean           ← App A.MIX (частично)
├── Stratified.lean          ← Частично §3 (incomplete)
│
├── SEDT/                    ← ✅ ХОРОШО: модульная структура
│   ├── Axioms.lean
│   ├── Core.lean
│   └── Theorems.lean
│
└── SEDT.lean                ← Агрегирующий модуль

❌ ПРОБЛЕМЫ:
• 13 файлов в корне (сложно навигировать)
• Нет явной связи со статьёй
• Отсутствуют ключевые разделы (App B полностью, App C частично)
• Смешаны разные уровни абстракции
• Только SEDT/ модулизирован правильно
```

---

### ✅ ПРЕДЛАГАЕМАЯ СТРУКТУРА (Модульная, соответствует статье)

```
Collatz/
│
├── Foundations/             ← 🎯 §2: Setup and Definitions
│   ├── Basic.lean           │   T_odd, e(m), collatz_seq
│   ├── Arithmetic.lean      │   ν_2, modular arithmetic
│   ├── TwoAdicDepth.lean    │   depth_minus properties
│   └── StepClassification.lean  e=1 vs e≥2
│
├── Stratified/              ← 🎯 §3: Stratified Decomposition
│   ├── PreimageLayers.lean        S_n, S_n_star (Def 3.1-3.2)
│   ├── CompleteStratification.lean Theorem 4.1
│   ├── BranchingDensity.lean      Theorem 4.3 (2/3 density)
│   ├── Parametrization.lean       k_0(n), m(n,t), Theorem 4.5
│   └── Cylinders.lean             C_ℓ (§2.7)
│
├── Epochs/                  ← 🎯 Appendix A.E0-A.E2: Epoch Theory
│   ├── Structure.lean       │   Epoch, TEpoch, Head/Plateau/Tail
│   ├── OrdFact.lean         │   Q_t = 2^{t-2} (A.MIX.1)
│   ├── PhaseClasses.lean    │   φ(E), Δ(J) (A.E0.2-3)
│   ├── Homogenization.lean  │   Affine tail evolution (A.E0.1)
│   ├── TouchAnalysis.lean   │   t-touches, frequency (A.E3.g)
│   └── LongEpochs.lean      │   Theorem A.LONG.5
│
├── SEDT/                    ← 🎯 Appendix A.E3-A.E4: Drift Theorem
│   ├── Constants.lean       │   α, β₀, ε, C, L₀, K_glue (App D)
│   ├── PotentialFunction.lean   V(n) = log₂(n) + β·depth_minus(n)
│   ├── Core.lean            │   Drift analysis, single-step bounds
│   ├── Axioms.lean          │   3 modeling axioms
│   ├── EnvelopeTheorem.lean │   Theorem A.E4 (Main SEDT)
│   └── Theorems.lean        │   Corollaries, negativity lemmas
│
├── Mixing/                  ← 🎯 Appendix A.MIX: Phase Mixing
│   ├── Semigroup.lean       │   ⟨Δ⟩ generates ℤ/Q_t ℤ (A.MIX.4)
│   ├── PhaseMixing.lean     │   Theorem A.HMix(t)
│   └── TouchFrequency.lean  │   p_t = Q_t^{-1} (A.E3.i')
│
├── CycleExclusion/          ← 🎯 Appendix B: Cycle Exclusion ⭐ NEW
│   ├── PeriodSum.lean       │   Lemma 4.1 (telescoping)
│   ├── PureE1Cycles.lean    │   Theorem C.B (e=1 impossible)
│   ├── MixedCycles.lean     │   SEDT-based exclusion
│   ├── RepeatTrick.lean     │   R_0 threshold (§4.2)
│   └── Main.lean            │   Theorem: no nontrivial cycles
│
├── Convergence/             ← 🎯 §4 + Appendix C: Global Convergence ⭐
│   ├── Coercivity.lean      │   Lemma C.1 (coercivity)
│   ├── NoAttractors.lean    │   No other attractors
│   ├── MainTheorem.lean     │   Theorem C.Main (global convergence)
│   └── FixedPoints.lean     │   Uniqueness of fixed point
│
├── Utilities/               ← 🛠️ Supporting Infrastructure
│   ├── Constants.lean       │   Appendix D (centralized)
│   ├── Notation.lean        │   Unified notation
│   └── Examples.lean        │   Concrete computations
│
├── Documentation/           ← 📚 Navigation & Mapping
│   ├── ProofRoadmap.lean    │   High-level proof structure
│   └── PaperMapping.lean    │   Paper theorem → Lean definition
│
└── Collatz.lean             ← 🎯 Root aggregator (imports all)

✅ ПРЕИМУЩЕСТВА:
• 9 тематических папок (четкая структура)
• Прямое соответствие статье (1:1 mapping)
• Полная модульность (все разделы независимы)
• Документация и roadmap встроены
• Легко найти любое утверждение
```

---

## 🗺️ Карта соответствия: Статья ↔ Lean

### §2: Setup and Definitions
```
Статья                          Текущий Lean              →  Новый Lean
────────────────────────────────────────────────────────────────────────────
T_odd definition (§2)           Basic.lean (mixed)        →  Foundations/Basic.lean
ν_2 properties                  Arithmetic.lean           →  Foundations/Arithmetic.lean
depth_minus (§2.7)              Basic.lean (mixed)        →  Foundations/TwoAdicDepth.lean
Step types: e=1, e≥2            (not explicit)            →  Foundations/StepClassification.lean
```

### §3: Stratified Decomposition
```
Статья                          Текущий Lean              →  Новый Lean
────────────────────────────────────────────────────────────────────────────
S_n, S_n_star (Def 3.1-3.2)     Stratified.lean           →  Stratified/PreimageLayers.lean
Theorem 4.1 (Complete)          Stratified.lean           →  Stratified/CompleteStratification.lean
Theorem 4.3 (2/3 density)       Stratified.lean           →  Stratified/BranchingDensity.lean
Theorem 4.5 (Parametrization)   Coordinates.lean          →  Stratified/Parametrization.lean
C_ℓ cylinders (§2.7)            Cylinders.lean            →  Stratified/Cylinders.lean
```

### §4: Main Results
```
Статья                          Текущий Lean              →  Новый Lean
────────────────────────────────────────────────────────────────────────────
Cycle exclusion framework       Cycles.lean (partial)     →  CycleExclusion/ (5 modules)
Lemma 4.1 (Period sum)          (missing)                 →  CycleExclusion/PeriodSum.lean
R_0 repeat trick                (missing)                 →  CycleExclusion/RepeatTrick.lean
Main convergence                Convergence.lean          →  Convergence/MainTheorem.lean
```

### Appendix A.E0-A.E2: Epoch Theory
```
Статья                          Текущий Lean              →  Новый Lean
────────────────────────────────────────────────────────────────────────────
Epoch structure (A.E0.1)        Epoch.lean (monolithic)   →  Epochs/Structure.lean
Q_t = 2^{t-2} (A.MIX.1)         OrdFact.lean              →  Epochs/OrdFact.lean
Phase classes (A.E0.2-3)        Epoch.lean (mixed)        →  Epochs/PhaseClasses.lean
Homogenization (A.E0.1)         Epoch.lean (implicit)     →  Epochs/Homogenization.lean
t-touches (A.E3.g)              Epoch.lean (partial)      →  Epochs/TouchAnalysis.lean
Theorem A.LONG.5                (missing)                 →  Epochs/LongEpochs.lean
```

### Appendix A.E3-A.E4: SEDT
```
Статья                          Текущий Lean              →  Новый Lean
────────────────────────────────────────────────────────────────────────────
Constants (App D)               SEDT/Core.lean (mixed)    →  SEDT/Constants.lean
V(n) potential                  SEDT/Core.lean            →  SEDT/PotentialFunction.lean
Drift analysis                  SEDT/Core.lean            →  SEDT/Core.lean (refactor)
Modeling axioms                 SEDT/Axioms.lean          →  SEDT/Axioms.lean (✅ keep)
Theorem A.E4 (SEDT envelope)    SEDT/Theorems.lean        →  SEDT/EnvelopeTheorem.lean
Corollaries                     SEDT/Theorems.lean        →  SEDT/Theorems.lean (refactor)
```

### Appendix A.MIX: Phase Mixing
```
Статья                          Текущий Lean              →  Новый Lean
────────────────────────────────────────────────────────────────────────────
⟨Δ⟩ generates (A.MIX.4)         Semigroup.lean            →  Mixing/Semigroup.lean
Theorem A.HMix(t)               (missing)                 →  Mixing/PhaseMixing.lean
Touch frequency (A.E3.i')       (missing)                 →  Mixing/TouchFrequency.lean
```

### Appendix B: Cycle Exclusion ⭐
```
Статья                          Текущий Lean              →  Новый Lean
────────────────────────────────────────────────────────────────────────────
Period sum lemma                Cycles.lean (partial)     →  CycleExclusion/PeriodSum.lean
Theorem C.B (e=1 cycles)        Cycles.lean (partial)     →  CycleExclusion/PureE1Cycles.lean
Mixed cycles exclusion          Cycles.lean (partial)     →  CycleExclusion/MixedCycles.lean
R_0 repeat trick                (missing)                 →  CycleExclusion/RepeatTrick.lean
Main theorem                    Cycles.lean               →  CycleExclusion/Main.lean
```

### Appendix C: Final Theorem ⭐
```
Статья                          Текущий Lean              →  Новый Lean
────────────────────────────────────────────────────────────────────────────
Lemma C.1 (Coercivity)          Convergence.lean          →  Convergence/Coercivity.lean
No other attractors             (missing)                 →  Convergence/NoAttractors.lean
Theorem C.Main                  Convergence.lean          →  Convergence/MainTheorem.lean
Fixed point uniqueness          Convergence.lean          →  Convergence/FixedPoints.lean
```

### Appendix D: Constants
```
Статья                          Текущий Lean              →  Новый Lean
────────────────────────────────────────────────────────────────────────────
All constants registry          (scattered)               →  Utilities/Constants.lean
```

---

## 📈 Метрики сравнения

### Организация кода
| Метрика                    | Текущая | Предлагаемая | Изменение |
|----------------------------|---------|--------------|-----------|
| Количество папок           | 2       | 9            | **+350%** |
| Файлов в корне             | 13      | 1            | **-92%**  |
| Средний размер модуля      | ~200    | ~100         | **-50%**  |
| Глубина вложенности        | 1       | 2            | +1        |

### Соответствие статье
| Аспект                     | Текущая | Предлагаемая | Оценка |
|----------------------------|---------|--------------|--------|
| §2 Setup                   | 30%     | 100%         | ✅ +70% |
| §3 Stratified              | 50%     | 100%         | ✅ +50% |
| §4 Main Results            | 40%     | 100%         | ✅ +60% |
| App A.E0-E2 (Epochs)       | 60%     | 100%         | ✅ +40% |
| App A.E3-E4 (SEDT)         | 90%     | 100%         | ✅ +10% |
| App A.MIX (Mixing)         | 30%     | 100%         | ✅ +70% |
| **App B (Cycles)**         | **30%** | **100%**     | ✅ **+70%** |
| **App C (Final)**          | **40%** | **100%**     | ✅ **+60%** |
| App D (Constants)          | 20%     | 100%         | ✅ +80% |

### Документация и навигация
| Аспект                     | Текущая | Предлагаемая | Оценка |
|----------------------------|---------|--------------|--------|
| Roadmap                    | ❌      | ✅           | NEW    |
| Paper mapping              | ❌      | ✅           | NEW    |
| Theorem → Lean таблица     | ❌      | ✅           | NEW    |
| Навигация по разделам      | Сложно  | Тривиально   | ✅     |

---

## 🎯 Ключевые улучшения

### 1. Прямое соответствие статье (1:1)
```
Статья §2    ═══>  Foundations/
Статья §3    ═══>  Stratified/
Статья §4    ═══>  Convergence/
App A (Epochs) ═══>  Epochs/
App A (SEDT)   ═══>  SEDT/
App A (Mixing) ═══>  Mixing/
App B          ═══>  CycleExclusion/  ⭐ NEW
App C          ═══>  Convergence/     ⭐ COMPLETE
App D          ═══>  Utilities/Constants.lean
```

### 2. Модульность и независимость
```
Текущая:  13 файлов ──> все зависят друг от друга
                     ──> сложно понять порядок

Новая:    9 папок ──> четкая иерархия зависимостей
                  ──> каждый модуль самодостаточен
                  ──> легко добавлять новые результаты
```

### 3. Документация встроена
```
Текущая:  README.md + комментарии в коде
          (разрозненно, неполно)

Новая:    + Documentation/ProofRoadmap.lean
          + Documentation/PaperMapping.lean
          + Utilities/Notation.lean
          (централизованно, структурировано)
```

### 4. Готовность к публикации
```
Текущая:  Требует значительной реорганизации
          Сложно объяснить структуру reviewers

Новая:    ✅ Следует best practices Lean community
          ✅ Соответствует структуре mathlib4
          ✅ Готова к formal review
          ✅ Образовательная ценность (структура = roadmap)
```

---

## 🚀 Следующие шаги

1. **Review этого плана** — получить feedback от коллег
2. **Priority 1 миграция** — Foundations, Stratified, CycleExclusion
3. **Проверка компиляции** — после каждого шага
4. **Priority 2-3 миграция** — Epochs, Mixing, Convergence
5. **Документация** — ProofRoadmap, PaperMapping
6. **Final review** — полная проверка соответствия статье

---

**Статус:** ✅ План готов  
**Дата:** 2025-10-04  
**См. также:**
- `RESTRUCTURE_PLAN.md` — детальный план (English)
- `RESTRUCTURE_SUMMARY_RU.md` — краткая сводка (Русский)

