# Status Report: touch_onebit Lemma Implementation

**Дата:** 3 октября 2025, 09:00  
**Задача:** Task A.1 — Формализация touch_onebit (правильная версия touch bonus)  
**Статус:** ⏳ Awaiting Expert Response

---

## 📊 Краткое резюме

### ✅ **Что сделано:**

1. **Получен экспертный анализ** (от Anatoliy)
   - ❌ Старая аксиома **неверна** для t ≥ 4
   - ✅ Правильная формула: `depth⁻(r') = t - 1` (не `≤ 2`!)
   - 📚 Математическое доказательство понятно

2. **Создана структура доказательства**
   - ~200 строк кода в Lean 4
   - Следует экспертному outline
   - Основная логика корректна

3. **Выявлены проблемы с mathlib API**
   - ~40 compilation errors
   - Основная причина: неправильное использование mathlib леммов
   - Не хватает знаний о `Finsupp`, `factorization` API

4. **Создан подробный вопрос эксперту**
   - Файл: `EXPERT_QUESTION_2025-10-03_touch_bonus_IMPLEMENTATION.md`
   - Содержит конкретный код, ошибки, вопросы
   - Приоритетные секции выделены

---

## 🔥 Основные проблемы

### **Категория 1: Unknown identifiers (missing imports)**
- `ordProj_dvd` — не могу найти правильный import
- `Nat.pow_ne_zero` — не существует (нужна альтернатива)

### **Категория 2: Type mismatches (Finsupp vs projection)**
- `Nat.factorization_mul` возвращает `Finsupp`, нужна проекция на `2`
- `Nat.factorization_pow` возвращает `(t-1) • factorization 2`, нужно `= k`

### **Категория 3: API confusion**
- `Prime.factorization_self` field error
- `Even n` дает `n = k + k`, нужно `n = 2 * k`
- `3.` интерпретируется как scientific notation

---

## 📋 План действий

### **Сейчас:**
1. ⏳ Ждём ответа эксперта на вопрос
2. 📚 Expert может дать:
   - Правильные имена лемм
   - Corrected code sections
   - Альтернативную стратегию доказательства

### **После ответа эксперта:**
1. 🔧 Интеграция исправлений (~30-60 минут)
2. ✅ Компиляция без `sorry`
3. 🎯 Замена старой аксиомы на proven lemma
4. 📊 Обновление счётчика: 77% → 85% (if successful)

---

## 🎯 Ожидаемый результат

### **Цель:**
```lean
lemma touch_provides_onebit_bonus (r : ℕ) (t : ℕ) (ht : t ≥ 3) 
  (h_touch : depth_minus r = t) :
  ∃ (r' : ℕ),
    r' = (3 * r + 1) / 2 ∧
    depth_minus r' = t - 1
```

**Без `sorry`!** ✅

### **Impact:**
- ❌ Удалить неверную аксиому `touch_provides_multibit_bonus`
- ✅ Заменить на **proven lemma** с правильным bound
- 📈 Progress: 77% → 85% formalized
- 🔬 Математическая корректность восстановлена

---

## 💡 Уроки на будущее

1. **Mathlib API complexity:**
   - `Finsupp` требует глубокого понимания
   - Projection lemmas не всегда очевидны
   - Documentation gaps exist

2. **Expert consultation critical:**
   - Математическая корректность > Lean синтаксис
   - Expert feedback выявил фундаментальную ошибку рано
   - Лучше спросить раньше, чем тратить часы на неверное доказательство

3. **Incremental approach works:**
   - Создали структуру → выявили ошибки → focused question
   - Лучше чем "всё сразу или ничего"

---

## 📊 Текущий статус формализации

| Component | Status | Lemmas/Axioms | Notes |
|-----------|--------|---------------|-------|
| **Ord-Fact** | ✅ | 0 sorry, 0 axiom | Fully proven |
| **Semigroup** | ✅ | 0 sorry, 0 axiom | Fully proven |
| **SEDT** | ⚠️ | 0 sorry, 13 axiom | 6 proven, 4 SMT-verified, 3 pending |
| **touch_onebit** | 🔧 | 1 sorry | In progress (awaiting expert) |

**Overall:** 77% formal (will be 85% after touch_onebit completion)

---

## 🔗 Связанные файлы

1. **Expert questions:**
   - `EXPERT_QUESTION_2025-10-03_touch_bonus.md` (initial analysis)
   - `EXPERT_QUESTION_2025-10-03_touch_bonus_IMPLEMENTATION.md` (current question)

2. **Implementation:**
   - `Collatz/SEDT.lean:281-502` (current attempt)

3. **Previous reports:**
   - `2025-10-03_0800_full-formalization-plan.md`
   - `2025-10-03_0730_phase1-complete.md`

---

**Next Update:** После получения ответа эксперта

**Estimated Time to Completion:** 30-60 минут после expert response

