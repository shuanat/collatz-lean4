# Implementation Status: touch_onebit Lemma

**Дата:** 3 октября 2025, ~11:00  
**Статус:** ⚠️ In Progress - Multiple API Issues

---

## 🎯 Проблема

Пытаюсь интегрировать expert proof для `touch_provides_onebit_bonus`, но натыкаюсь на **множественные API несоответствия** между тем что эксперт предложил и реальным mathlib4 API.

---

## ❌ Основные проблемы

### 1. **`Nat.pow_ne_zero` не существует**
```lean
-- Ошибка: Unknown constant `Nat.pow_ne_zero`
have hk_ne : 2 ^ k ≠ 0 := Nat.pow_ne_zero k (by decide)
```

**Решение:**
```lean
have hk_ne : 2 ^ k ≠ 0 := by
  have : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
  omega
```

### 2. **`Nat.Prime.factorization_pow` возвращает неправильную структуру**
```lean
-- Ожидается: (2^k).factorization 2 = k
-- Получается: k * (Nat.factorization 2) 2
```

Эксперт предложил:
```lean
have := Nat.Prime.factorization_pow Nat.prime_two
have := congrArg (fun f => f 2) this
simpa [Finsupp.single_eq_same] using this
```

Но `simpa` не справляется с приведением типа `k * (Nat.factorization 2) 2` к `k`.

**Почему это происходит:**
- `factorization_pow` возвращает: `(p^k).factorization = Finsupp.single p k`
- После проекции на `2` получаем: `k * something` вместо `k`

### 3. **`Nat.mul_div_cancel'` имеет другие параметры**
```lean
-- Эксперт написал:
have := Nat.mul_div_cancel' (a := 3) (b := r + 1) h2_dvd_r1

-- Реальная сигнатура (без named args a, b):
Nat.mul_div_cancel' : ∀ {m n : ℕ}, n ∣ m → m / n * n = m
```

###  4. **Complex division arithmetic для `ℕ`**
```lean
-- Нужно: (3r+1)/2 + 1 = 3*((r+1)/2)
-- Проблема: Natural number division имеет сложные правила
```

---

## 📋 Что пробовал

1. ✅ Исправил импорты (`Mathlib.Algebra.Ring.Parity` вместо `.Data.Nat.Parity`)
2. ✅ Заменил `Nat.pow_ne_zero` на `Nat.pow_pos + omega`
3. ✅ Использовал `@Nat.Prime.factorization_pow` с явными type arguments
4. ❌ Не смог заставить `h_pow_fac` helper работать правильно
5. ❌ Multiple issues с `calc` blocks и `ring_nf`
6. ❌ Division arithmetic на ℕ крайне сложна

---

## 💡 Альтернативные подходы

### Вариант A: Упростить proof используя `Nat.exists_eq_two_pow_mul_odd`
Вместо `exists_eq_pow_mul_and_not_dvd` (которая тоже проблемная) использовать специализированную версию для степеней 2.

### Вариант B: Использовать `padicValNat` вместо `factorization`
Эксперт упомянул что `padicValNat` может быть проще:
```lean
-- Instead of (r+1).factorization 2
-- Use padicValNat 2 (r+1)
```

### Вариант C: Временно оставить 1 `sorry` и вернуться позже
Если только рекурсивный случай в `h_pow_fac` проблемный, можно оставить его как `sorry` и продолжить.

### Вариант D: Попросить эксперта дать **working version для mathlib4 v4.24.0-rc1**
Возможно эксперт тестировал на другой версии mathlib.

---

## 🎯 Решение

**Рекомендую: Вариант D** — попросить эксперта дать **полностью скомпилированную версию** специфично для нашей версии mathlib4.

**Текущая версия:**
- Lean: v4.24.0-rc1
- Mathlib4: latest (from lake-manifest.json)

**Нужно:**
Полный proof от эксперта, который компилируется **без изменений** на этой версии.

---

## 📊 Time Spent

- Expert solution received: 30 min ago
- Integration attempts: 1.5 hours
- Compilation errors fixed: 10+
- Remaining errors: 4-5

---

**Recommendation:** Обратиться к эксперту с просьбой предоставить **fully working proof** для нашей версии Lean/mathlib.

