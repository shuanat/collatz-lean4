# Task A Complete: touch_provides_onebit_bonus — 100% Формализация

**Дата:** 3 октября 2025, 12:00  
**Статус:** ✅ ЗАВЕРШЕНО  
**Результат:** Полностью доказанная лемма без `sorry`

---

## 🎯 Что было сделано

### Проблема
Исходная аксиома `touch_provides_multibit_bonus` была **математически некорректной** для t ≥ 4:
- Утверждала: `depth⁻(r') ≤ 2` после t-touch
- Реальность: `depth⁻(r') = t - 1` (one-bit bonus, не multibit!)
- Контрпример: r=15, t=4 → r'=23 → depth⁻(r')=3 ≠ ≤ 2

### Решение от эксперта
Эксперт предоставил:
1. **Правильную математическую формулу**: `depth⁻(r') = t - 1` для t ≥ 3
2. **Ключевой инсайт**: Использовать мультипликативную идентичность `2*(r'+1) = 3*(r+1)` вместо division arithmetic
3. **Proof skeleton** с точными mathlib API lemmas

### Реализация
Полностью формализованная лемма `touch_provides_onebit_bonus`:

```lean
lemma touch_provides_onebit_bonus (r : ℕ) (t : ℕ) (ht : t ≥ 3) (h_touch : depth_minus r = t) :
  ∃ (r' : ℕ),
    r' = (3 * r + 1) / 2 ∧
    depth_minus r' = t - 1
```

---

## 🔧 Технические детали

### Основная стратегия доказательства

1. **Показать чётность `3r+1`** через parity lemmas
2. **Вывести ключевую идентичность**: `2*(r'+1) = 3*(r+1)` где `r' = (3r+1)/2`
3. **Применить factorization к обеим сторонам**:
   - Левая: `(2*(r'+1)).factorization 2 = 1 + (r'+1).factorization 2`
   - Правая: `(3*(r+1)).factorization 2 = 0 + t`
4. **Получить**: `(r'+1).factorization 2 = t - 1`

### Использованные mathlib lemmas

**Divisibility & Factorization:**
- `Nat.ordProj_dvd` — `p^(n.factorization p) ∣ n`
- `Nat.factorization_mul` — мультипликативность факторизации
- `Nat.Prime.factorization_pow` — факторизация степеней простых
- `Nat.factorization_eq_zero_of_not_dvd` — факторизация нечётных чисел

**Parity:**
- `even_iff_two_dvd` — `Even n ↔ 2 ∣ n`
- `Nat.not_odd_iff_even` — `¬Odd n ↔ Even n`
- `Nat.odd_mul` — произведение нечётных чисел нечётно
- `Even.add_odd` / `Odd.add_odd` — сложение чётности

**Arithmetic:**
- `Nat.mul_div_cancel'` — точное деление
- `Finsupp.add_apply` — сложение finsupp (для factorization)
- `Finsupp.single_eq_same` — вычисление single в точке

---

## 📊 Метрики

**Время работы:**
- Интеграция expert solution: ~2 часа
- Отладка API несоответствий: ~1.5 часа
- Итого: ~3.5 часа

**Сложность:**
- Количество API lemmas: 15+
- Строк кода proof: ~120 строк
- Ключевых шагов: 5 (parity → identity → factorization → projection → arithmetic)

**Результат:**
- ✅ 0 `sorry`
- ✅ 0 `axiom` (аксиома заменена леммой)
- ✅ Компилируется без ошибок
- ⚠️ 1 minor linter warning (исправлен)

---

## 🎓 Извлечённые уроки

### Что сработало отлично
1. **Мультипликативная идентичность** вместо division arithmetic — ключевой инсайт
2. **Прямое использование `congrArg`** для проекции factorization на prime 2
3. **Parity lemmas** из mathlib вместо custom reasoning
4. **`omega` tactic** для натуральной арифметики

### Подводные камни mathlib4 API
1. **`Nat.pow_ne_zero` не существует** — использовать `by decide` или `Nat.pow_pos`
2. **`even_iff_two_dvd.mpr` → `even_iff_two_dvd.2`** — использовать `.1` / `.2` вместо `.mp` / `.mpr`
3. **`Nat.Prime.factorization_pow`** требует явного `@` для типов
4. **`simpa [...] using`** часто упрощает слишком агрессивно → использовать `simp [...] at this; exact this`

### Ключевые API patterns
```lean
-- Factorization projection to prime p:
have hmul := Nat.factorization_mul ha hb
exact congrArg (fun f => f p) hmul

-- Parity via divisibility:
have hr_odd : Odd r := by
  by_contra h
  have : Even r := Nat.not_odd_iff_even.1 h
  -- ... derive contradiction

-- Power factorization:
have := @Nat.Prime.factorization_pow p k Nat.prime_p
have := congrArg (fun f => f p) this
-- now simplify with Finsupp.single_eq_same
```

---

## ✅ Checklist завершения

- [x] Proof компилируется без ошибок
- [x] 0 `sorry` placeholders
- [x] Все intermediate steps явно обоснованы
- [x] Linter warnings исправлены
- [x] Коммит создан с подробным сообщением
- [x] Expert solution файлы сохранены для reference
- [x] TODO list обновлён

---

## 🔜 Следующие шаги

**Immediate:**
- Task B: Доказать `short_epoch_potential_bounded` → lemma

**Strategic:**
- Task C: Assess `single_step_potential_bounded` формализация
- Phase 3: Final report + README update

---

## 📚 Артефакты

**Коммиты:**
- `a0a81dc` — feat(SEDT): complete 100% formalization of touch_provides_onebit_bonus

**Файлы:**
- `Collatz/SEDT.lean` (lines 292-415) — полное доказательство
- `EXPERT_QUESTION_2025-10-03_touch_bonus.md` — исходный вопрос эксперту
- `EXPERT_QUESTION_2025-10-03_touch_bonus_IMPLEMENTATION.md` — второй вопрос (API)
- `EXPERT_QUESTION_2025-10-03_IMPLEMENTATION_STATUS.md` — статус интеграции

---

## 🎉 Итог

**Task A.1, A.2, A.3 — ПОЛНОСТЬЮ ЗАВЕРШЕНЫ**

Аксиома `touch_provides_multibit_bonus` успешно заменена на **полностью доказанную лемму** `touch_provides_onebit_bonus` с правильной математической формулой `depth⁻(r') = t - 1`.

Это важный шаг к 100% формализации SEDT envelope theorem! 🚀

