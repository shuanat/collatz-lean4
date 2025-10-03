# Прогресс формализации three_pow_two_pow_sub_one_valuation

**Дата:** 2 октября 2025  
**Время:** 10:00 UTC

---

## 🎯 Цель

Формализовать лемму `three_pow_two_pow_sub_one_valuation`:

```lean
lemma three_pow_two_pow_sub_one_valuation (k : ℕ) (hk : k ≥ 1) :
  (3 : ℤ)^(2^k) ≡ 1 [ZMOD 2^(k+2)] ∧ 
  ¬((3 : ℤ)^(2^k) ≡ 1 [ZMOD 2^(k+3)])
```

---

## ⚠️ Основная проблема

**Несоответствие типов:**
- Лемма использует `Int.ModEq` (работает с `ℤ`)
- `pow_lift_double` работает с `ZMod (2^t)` (принимает `ℕ`)
- Конвертация между `Int.ModEq` и `ZMod` оказалась сложной

### Попытки конвертации:

1. **`Int.coe_nat_mod`** — не существует в mathlib4
2. **`ZMod.intCast_eq_intCast_iff`** — работает, но создаёт проблемы с типами:
   ```lean
   show ((3 : ℤ) : ZMod (2^(k+2)))^(2^k) = 1
   -- vs
   show (3 : ZMod (2^(k+2)))^(2^k) = 1  -- ожидается для pow_lift_double
   ```

3. **`push_cast` + `rfl`** — не закрывает цель из-за definitional неравенства

---

## 💡 Альтернативное решение

### Вариант A: Переформулировать лемму для натуральных чисел

Вместо `Int.ModEq` использовать `Nat.ModEq` или прямо `ZMod`:

```lean
lemma three_pow_two_pow_sub_one_valuation_nat (k : ℕ) (hk : k ≥ 1) :
  (3 : ZMod (2^(k+2)))^(2^k) = 1 ∧ 
  ¬((3 : ZMod (2^(k+3)))^(2^k) = 1) := by
  -- Прямая индукция с pow_lift_double
  sorry
```

Затем доказать вспомогательную лемму для конвертации к `Int.ModEq`.

### Вариант B: Создать helper леммы для конвертации

```lean
lemma int_modEq_to_zmod {a b n : ℕ} (h : (a : ℤ) ≡ (b : ℤ) [ZMOD (n : ℤ)]) :
  (a : ZMod n) = (b : ZMod n) := by
  sorry

lemma zmod_to_int_modEq {a b n : ℕ} (h : (a : ZMod n) = (b : ZMod n)) :
  (a : ℤ) ≡ (b : ℤ) [ZMOD (n : ℤ)] := by
  sorry
```

### Вариант C: Использовать LTE напрямую

Согласно экспертным рекомендациям, использовать `padicValNat_pow_sub_pow_of_even`:

```lean
import Mathlib.NumberTheory.Padics.PadicVal

lemma three_pow_two_pow_sub_one_valuation (k : ℕ) (hk : k ≥ 1) :
  ... := by
  -- Применяем LTE lemma
  have h_lte := padicValNat_pow_sub_pow_of_even 2 3 1 (2^k) ...
  -- Конвертируем valuation к делимости
  sorry
```

---

## 📊 Текущий статус

### Что работает:

✅ **Базовый случай `k=1`:**
```lean
| succ k ih =>
  by_cases hk_prev : k = 0
  · -- k = 0 → k+1 = 1
    subst hk_prev
    constructor
    · -- 3^2 ≡ 1 (mod 8): работает norm_num
      norm_num
    · -- ¬(3^2 ≡ 1 (mod 16)): работает norm_num
      intro h
      norm_num at this
```

### Что НЕ работает:

❌ **Индуктивный шаг — нижняя граница:**
- Конвертация `Int.ModEq` → `ZMod` для `pow_lift_double`
- Ошибка: `show ((3 : ℤ) : ZMod ...)^k = 1` не равно `show (3 : ZMod ...)^k = 1`

❌ **Индуктивный шаг — верхняя граница:**
- Получение противоречия из `3^{2k} ≡ 1 (mod 2^{k+4})`
- Проблема: нужно показать, что это противоречит IH

---

## 🔧 Рекомендуемый план действий

### Шаг 1: Создать helper леммы для конвертации типов

```lean
-- В Arithmetic.lean или OrdFact.lean
namespace Helper

lemma natCast_pow_zmod_eq_one {a n k : ℕ} :
  ((a : ℤ) : ZMod n)^k = 1 ↔ (a : ZMod n)^k = 1 := by
  constructor
  · intro h
    have : ((a : ℤ) : ZMod n)^k = ((a : ℕ) : ZMod n)^k := by
      congr 1
      simp
    rw [this] at h
    exact h
  · intro h
    have : ((a : ℕ) : ZMod n)^k = ((a : ℤ) : ZMod n)^k := by
      congr 1
      simp
    rw [← this]
    exact h

lemma int_modEq_iff_zmod {a b n : ℕ} :
  (a : ℤ) ≡ (b : ℤ) [ZMOD (n : ℤ)] ↔ (a : ZMod n) = (b : ZMod n) := by
  sorry  -- Нужно найти в mathlib4 или доказать

end Helper
```

### Шаг 2: Использовать helper леммы в доказательстве

```lean
have h_zmod : (3 : ZMod (2^(k+2)))^(2^k) = 1 := by
  rw [← Helper.natCast_pow_zmod_eq_one]
  rw [← Helper.int_modEq_iff_zmod]
  exact ih_lower
```

### Шаг 3: Доказать верхнюю границу через противоречие

Ключевая идея: если `x^2 = 1` в `ZMod (2^m)` для `m ≥ 2`, то `x ∈ {1, 2^m - 1}`.

---

## 📁 Файлы для изменения

1. **`Collatz/Arithmetic.lean`** — добавить helper леммы
2. **`Collatz/OrdFact.lean`** — использовать helper леммы

---

## ⏱️ Оценка времени

- Создание helper лемм: 0.5-1ч
- Завершение нижней границы: 0.5ч
- Завершение верхней границы: 1-1.5ч
- **Итого:** 2-3 часа

---

## 🚨 Альтернатива: Переписать сигнатуру

Если helper леммы окажутся слишком сложными, можно:

1. Изменить сигнатуру на `Nat.ModEq` или прямо `ZMod`
2. Обновить зависимости (`three_pow_Qt_eq_one`, `ord_three_mod_pow_two`)
3. Это потребует больше изменений, но проще технически

---

## 💭 Вывод

Основная техническая сложность — конвертация между `Int.ModEq` и `ZMod` для работы с `pow_lift_double`.

**Следующий шаг:** Создать и протестировать helper леммы для конвертации типов.

