# Чеклист миграции: Реструктуризация Collatz Lean4

**Дата начала:** 2025-10-04  
**Цель:** Привести структуру в соответствие со статьей

## 📋 Pre-Migration Checklist

- [ ] ✅ Создан детальный план (`RESTRUCTURE_PLAN.md`)
- [ ] ✅ Создана сводка на русском (`RESTRUCTURE_SUMMARY_RU.md`)
- [ ] ✅ Создано сравнение структур (`STRUCTURE_COMPARISON.md`)
- [ ] 🔄 Получен feedback от коллег/reviewers
- [ ] 🔄 Создан feature branch: `git checkout -b restructure/paper-alignment`
- [ ] 🔄 Сохранен backup текущей структуры

---

## 🎯 PRIORITY 1: Критические модули (2-3 дня)

### Step 1.1: Foundations/ (§2 Setup)
**Цель:** Группировка базовых определений из §2

- [ ] Создать `Collatz/Foundations/` директорию
- [ ] Переместить `Basic.lean` → `Foundations/Basic.lean`
- [ ] Переместить `Arithmetic.lean` → `Foundations/Arithmetic.lean`
- [ ] Выделить из `Basic.lean`:
  - [ ] `TwoAdicDepth.lean` (depth_minus, properties)
  - [ ] `StepClassification.lean` (e=1, e≥2)
- [ ] Создать `Foundations.lean` (агрегатор)
- [ ] Обновить импорты в зависимых файлах
- [ ] ✅ Проверить: `lake build` проходит без ошибок

**Команды:**
```bash
mkdir -p Collatz/Foundations
git mv Collatz/Basic.lean Collatz/Foundations/Basic.lean
git mv Collatz/Arithmetic.lean Collatz/Foundations/Arithmetic.lean
# TODO: создать TwoAdicDepth.lean, StepClassification.lean
```

---

### Step 1.2: Stratified/ (§3 Stratified Decomposition)
**Цель:** Полная формализация §3

- [ ] Создать `Collatz/Stratified/` директорию
- [ ] Переименовать:
  - [ ] `Stratified.lean` → `PreimageLayers.lean`
  - [ ] `Coordinates.lean` → `Parametrization.lean`
  - [ ] `Cylinders.lean` → `Cylinders.lean` (переместить)
- [ ] Создать новые модули:
  - [ ] `CompleteStratification.lean` (Theorem 4.1)
  - [ ] `BranchingDensity.lean` (Theorem 4.3)
- [ ] Создать `Stratified.lean` (агрегатор)
- [ ] Обновить импорты
- [ ] ✅ Проверить: `lake build` проходит

**Команды:**
```bash
mkdir -p Collatz/Stratified
git mv Collatz/Stratified.lean Collatz/Stratified/PreimageLayers.lean
git mv Collatz/Coordinates.lean Collatz/Stratified/Parametrization.lean
git mv Collatz/Cylinders.lean Collatz/Stratified/Cylinders.lean
# TODO: создать CompleteStratification.lean, BranchingDensity.lean
```

---

### Step 1.3: CycleExclusion/ (Appendix B) ⭐
**Цель:** Полная формализация Appendix B (ключевой результат)

- [ ] Создать `Collatz/CycleExclusion/` директорию
- [ ] Разбить `Cycles.lean` на 5 модулей:
  - [ ] `PeriodSum.lean` (telescoping lemma)
  - [ ] `PureE1Cycles.lean` (Theorem C.B)
  - [ ] `MixedCycles.lean` (SEDT-based)
  - [ ] `RepeatTrick.lean` (R_0 threshold)
  - [ ] `Main.lean` (main theorem)
- [ ] Создать `CycleExclusion.lean` (агрегатор)
- [ ] Обновить импорты
- [ ] ✅ Проверить: `lake build` проходит

**Команды:**
```bash
mkdir -p Collatz/CycleExclusion
# TODO: разбить Cycles.lean на 5 частей
git rm Collatz/Cycles.lean  # после разбиения
```

---

## 🎯 PRIORITY 2: Завершение теории (3-4 дня)

### Step 2.1: Epochs/ (Appendix A.E0-A.E2)
**Цель:** Структурировать теорию эпох

- [ ] Создать `Collatz/Epochs/` директорию
- [ ] Переименовать:
  - [ ] `Epoch.lean` → `Structure.lean`
  - [ ] `OrdFact.lean` → `OrdFact.lean` (переместить)
- [ ] Выделить из `Epoch.lean`:
  - [ ] `PhaseClasses.lean` (φ(E), Δ(J))
  - [ ] `Homogenization.lean` (affine evolution)
  - [ ] `TouchAnalysis.lean` (t-touches)
- [ ] Создать новые:
  - [ ] `LongEpochs.lean` (Theorem A.LONG.5)
- [ ] Создать `Epochs.lean` (агрегатор)
- [ ] ✅ Проверить: `lake build` проходит

---

### Step 2.2: Mixing/ (Appendix A.MIX)
**Цель:** Выделить теорию смешивания фаз

- [ ] Создать `Collatz/Mixing/` директорию
- [ ] Переместить `Semigroup.lean` → `Mixing/Semigroup.lean`
- [ ] Создать новые:
  - [ ] `PhaseMixing.lean` (Theorem A.HMix(t))
  - [ ] `TouchFrequency.lean` (p_t = Q_t^{-1})
- [ ] Создать `Mixing.lean` (агрегатор)
- [ ] ✅ Проверить: `lake build` проходит

---

### Step 2.3: Convergence/ (§4 + Appendix C) ⭐
**Цель:** Завершить формализацию главной теоремы

- [ ] Создать `Collatz/Convergence/` директорию
- [ ] Разбить `Convergence.lean` на 4 модуля:
  - [ ] `Coercivity.lean` (Lemma C.1)
  - [ ] `NoAttractors.lean` (no other attractors)
  - [ ] `MainTheorem.lean` (global convergence)
  - [ ] `FixedPoints.lean` (uniqueness)
- [ ] Создать `Convergence.lean` (агрегатор)
- [ ] ✅ Проверить: `lake build` проходит

---

## 🎯 PRIORITY 3: Документация (1-2 дня)

### Step 3.1: Utilities/
**Цель:** Централизовать вспомогательные модули

- [ ] Создать `Collatz/Utilities/` директорию
- [ ] Создать `Constants.lean` (Appendix D, централизованно)
- [ ] Создать `Notation.lean` (unified conventions)
- [ ] Переместить `Examples.lean` → `Utilities/Examples.lean`
- [ ] Создать `Utilities.lean` (агрегатор)
- [ ] ✅ Проверить: `lake build` проходит

---

### Step 3.2: Documentation/
**Цель:** Roadmap и Paper Mapping

- [ ] Создать `Collatz/Documentation/` директорию
- [ ] Создать `ProofRoadmap.lean`:
  ```lean
  /-!
  # Proof Structure Roadmap
  
  1. Setup (§2) → Foundations/
  2. Stratification (§3) → Stratified/
  3. Epoch Theory (App A.E0-E2) → Epochs/
  4. SEDT (App A.E3-E4) → SEDT/
  5. Mixing (App A.MIX) → Mixing/
  6. Cycle Exclusion (App B) → CycleExclusion/
  7. Convergence (§4 + App C) → Convergence/
  -/
  ```
- [ ] Создать `PaperMapping.lean`:
  ```lean
  /-!
  # Paper-to-Lean Mapping
  
  ## Section 2: Setup
  - Def 2.1 (T_odd) → Foundations.Basic.T_odd
  - Def 2.2 (depth_minus) → Foundations.TwoAdicDepth.depth_minus
  
  ## Section 3: Stratified
  - Thm 4.1 → Stratified.CompleteStratification.complete_stratification
  - Thm 4.3 → Stratified.BranchingDensity.branching_decomposition
  
  (full table...)
  -/
  ```
- [ ] ✅ Проверить: документация актуальна

---

## 🎯 PRIORITY 4: Полировка (1 день)

### Step 4.1: SEDT/ рефакторинг
**Цель:** Улучшить существующую модульность SEDT

- [ ] Выделить из `SEDT/Core.lean`:
  - [ ] `Constants.lean` (α, β₀, ε, C, L₀, K_glue)
  - [ ] `PotentialFunction.lean` (V(n))
- [ ] Разбить `SEDT/Theorems.lean`:
  - [ ] `EnvelopeTheorem.lean` (Main SEDT)
  - [ ] `Theorems.lean` (остальные)
- [ ] Обновить `SEDT.lean` (агрегатор)
- [ ] ✅ Проверить: `lake build` проходит

---

### Step 4.2: Root module
**Цель:** Обновить корневой Collatz.lean

- [ ] Обновить `Collatz.lean`:
  ```lean
  -- Root aggregating module
  import Collatz.Foundations
  import Collatz.Stratified
  import Collatz.Epochs
  import Collatz.SEDT
  import Collatz.Mixing
  import Collatz.CycleExclusion
  import Collatz.Convergence
  import Collatz.Utilities
  ```
- [ ] ✅ Проверить: `import Collatz` работает
- [ ] ✅ Проверить: все тесты проходят

---

### Step 4.3: Обновить README
**Цель:** Документировать новую структуру

- [ ] Обновить `README.md`:
  - [ ] Добавить раздел "Project Structure"
  - [ ] Добавить карту соответствия статье
  - [ ] Обновить примеры использования
  - [ ] Добавить ссылки на ProofRoadmap
- [ ] Создать `CONTRIBUTING.md` (guidelines)
- [ ] ✅ Проверить: документация актуальна

---

## 🎯 Final Verification

### Final checks
- [ ] ✅ `lake build` проходит без ошибок
- [ ] ✅ Все тесты проходят
- [ ] ✅ Нет `sorry` в критических модулях
- [ ] ✅ Документация актуальна
- [ ] ✅ Соответствие статье проверено
- [ ] ✅ Импорты оптимизированы
- [ ] ✅ Нет циклических зависимостей

### Metrics verification
- [ ] ✅ Папок: 9 (Foundations, Stratified, Epochs, SEDT, Mixing, CycleExclusion, Convergence, Utilities, Documentation)
- [ ] ✅ Файлов в корне: 1 (Collatz.lean)
- [ ] ✅ Каждая папка имеет агрегирующий модуль
- [ ] ✅ ProofRoadmap и PaperMapping созданы
- [ ] ✅ Utilities/Constants.lean централизует константы

---

## 🚀 Post-Migration

### After migration
- [ ] 🔄 Создать Pull Request
- [ ] 🔄 Code review
- [ ] 🔄 Получить approval
- [ ] 🔄 Merge в main
- [ ] 🔄 Обновить документацию проекта
- [ ] 🔄 Анонсировать изменения (если публичный проект)

### Follow-up tasks
- [ ] 📚 Написать blog post о реструктуризации
- [ ] 📚 Создать tutorial по навигации
- [ ] 📚 Обновить CI/CD для новой структуры
- [ ] 📚 Добавить структурные тесты (lint)

---

## 📊 Progress Tracker

### Priority 1 (Critical)
- [ ] Foundations/ (0/5 tasks)
- [ ] Stratified/ (0/7 tasks)
- [ ] CycleExclusion/ (0/6 tasks)

### Priority 2 (Theory completion)
- [ ] Epochs/ (0/7 tasks)
- [ ] Mixing/ (0/4 tasks)
- [ ] Convergence/ (0/5 tasks)

### Priority 3 (Documentation)
- [ ] Utilities/ (0/5 tasks)
- [ ] Documentation/ (0/3 tasks)

### Priority 4 (Polish)
- [ ] SEDT/ refactor (0/4 tasks)
- [ ] Root module (0/3 tasks)
- [ ] README update (0/4 tasks)

**Total Progress:** 0/53 tasks (0%)

---

## 📝 Notes & Blockers

### Blockers
- None yet

### Notes
- План готов к реализации
- Feedback от коллег ожидается
- Backup текущей структуры сделать перед началом

### Decisions log
- 2025-10-04: План создан, ожидание approval

---

**Статус:** ✅ План готов, ожидание начала миграции  
**Следующий шаг:** Получить feedback, создать feature branch  
**ETA:** 7-10 дней (при полной занятости на проекте)

