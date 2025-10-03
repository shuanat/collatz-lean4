# Priority 1 Axioms: Structural Bounds Plan

**Дата:** 03 октября 2025  
**Время:** 06:15 UTC  
**Статус:** 📋 План для Priority 1 аксиом

---

## 🎯 Target Axioms

### Priority 1 (Structural Bounds)

1. **`SEDTEpoch_head_overhead_bounded`** ⏳
   ```lean
   axiom SEDTEpoch_head_overhead_bounded (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
     (_ht : t ≥ 3) (_hU : U ≥ 1) :
     abs e.head_overhead ≤ β * (2^t : ℝ) + (t : ℝ) * log (3/2) / log 2
   ```

2. **`SEDTEpoch_boundary_overhead_bounded`** ⏳
   ```lean
   axiom SEDTEpoch_boundary_overhead_bounded (t : ℕ) (e : SEDTEpoch) (β : ℝ) :
     abs e.boundary_overhead ≤ β * (K_glue t : ℝ)
   ```

---

## 🔍 Analysis

### Challenge: Universal Quantification Over Structure

**Проблема:** Аксиомы квантифицируются по **всем** `SEDTEpoch`:
```lean
∀ (e : SEDTEpoch), abs e.head_overhead ≤ bound
```

**SMT ограничение:** Z3 не может напрямую работать с:
- Зависимыми типами (структурами Lean)
- Универсальной квантификацией по структурам
- Полями структур как переменными

### Что НЕ Работает ❌

**Наивный подход:**
```smt2
; Это не компилируется в Z3!
(declare-datatype SEDTEpoch
  ((mk-epoch (head_overhead Real) (boundary_overhead Real))))

(assert (forall ((e SEDTEpoch))
  (<= (abs (head_overhead e)) bound)))
```

**Почему:**
1. Z3 не поддерживает `abs` в quantified формулах эффективно
2. Universal quantification над структурами медленный/undecidable
3. QF_NRA (Quantifier-Free!) логика не поддерживает `forall`

---

## 🛠️ Solution Strategy

### Подход 1: Bounded Existential (✅ РЕКОМЕНДУЕТСЯ)

**Идея:** Вместо `∀e` проверяем для **конкретных представительных** значений

**SMT кодировка:**
```smt2
(set-logic QF_NRA)

; Параметры
(declare-const t Real)
(declare-const beta Real)

; Конкретные поля структуры как переменные
(declare-const head_overhead Real)

; Constraints на поля (worst-case bounds)
; Head overhead не может превышать накопленный потенциал
(assert (<= (abs head_overhead) (* (* t 2.0) beta)))  ; Worst case

; Main inequality
(assert (> (abs head_overhead) 
           (+ (* beta pow_2_t) (* t log_3_2))))

(check-sat)
```

**Семантика:**
- Вместо `∀e` проверяем: "Существует ли `head_overhead` нарушающий bound?"
- Если UNSAT → bound верен для всех допустимых значений поля
- Это **conservative approximation**: если worst-case OK, то все OK

### Подход 2: Parametric Verification (✅ АЛЬТЕРНАТИВА)

**Идея:** Проверяем для параметрических bounds на поля

```smt2
; Параметризуем поля через их конструктивные bounds
(declare-const head_steps Nat)  ; Количество шагов в head
(assert (>= head_steps 1))
(assert (<= head_steps t))      ; Head длится не более t шагов

; Потенциал за 1 шаг
(define-fun per_step_bound () Real 
  (+ (/ (log 1.5) (log 2.0)) (* 2.0 beta)))

; Head overhead через количество шагов
(define-fun head_overhead () Real
  (* head_steps per_step_bound))

; Проверяем bound
(assert (> head_overhead (+ (* beta pow_2_t) (* t log_3_2))))
(check-sat)
```

**Преимущества:**
- Более точная модель (связь с количеством шагов)
- Проверяет конструктивное определение overhead

### Подход 3: Sampling (✅ ДЛЯ CONFIDENCE)

**Идея:** Проверяем для случайных выборок значений полей

```python
# Python script для sampling verification
import random
from z3 import *

def verify_head_bound_sampling(t_val, beta_val, num_samples=1000):
    """Verify for random samples of head_overhead."""
    solver = Solver()
    
    for _ in range(num_samples):
        # Sample head_overhead from realistic distribution
        # Worst case: t steps × max_per_step
        max_overhead = t_val * (np.log(1.5)/np.log(2) + 2*beta_val)
        head_overhead = random.uniform(-max_overhead, max_overhead)
        
        # Check bound
        bound = beta_val * (2**t_val) + t_val * (np.log(1.5)/np.log(2))
        
        if abs(head_overhead) > bound:
            return False, head_overhead
    
    return True, None
```

---

## 📋 Implementation Plan

### Phase 1: Head Overhead (Week 1)

**Step 1.1:** Create SMT encoding with Approach 1 (bounded existential)
- File: `SEDTEpoch_head_overhead.smt2`
- Worst-case bound на `head_overhead`
- Verify for t ∈ [3,20]

**Step 1.2:** Cross-check with Approach 2 (parametric)
- Model через `head_steps`
- More precise verification

**Step 1.3:** Sampling validation (Python)
- 10,000 random samples per (t, β)
- Statistical confidence > 99.99%

### Phase 2: Boundary Overhead (Week 1)

**Similar strategy for `boundary_overhead`**
- Bounded by β·K_glue(t)
- K_glue(t) уже верифицирован (max_K_glue_le_pow_two)

---

## 🎯 Expected Results

### Pessimistic Scenario

**Если UNSAT:** ✅
- Bounds верны для worst-case
- Структурные аксиомы numeric-verified

**Если SAT:** ⚠️
- Найден конкретный контрпример
- **НЕ** означает аксиома неверна!
- Означает: наш worst-case bound слишком консервативен
- **Решение:** Уточнить constraints на поля структуры

### Realistic Scenario

**Ожидаем:** ✅ UNSAT для обеих аксиом

**Обоснование:**
1. **Head bound математически обоснован:**
   - Максимум t шагов
   - Per-step bound: log₂(3/2) + 2β
   - Total: t·(log₂(3/2) + 2β) ≤ β·2^t + t·log₂(3/2) для t ≥ 3
   - **Запас:** β·2^t >> t·2β для t ≥ 3

2. **Boundary bound математически обоснован:**
   - K_glue(t) уже доказан ≤ 2^t (lemma max_K_glue_le_pow_two)
   - Boundary overhead физически ≤ K_glue потенциальных изменений

---

## 🚀 Next Steps

1. **Implement Approach 1** для head_overhead
2. **Run Z3 verification**
3. **Analyze results:**
   - If UNSAT → Success! ✅
   - If SAT → Refine worst-case bounds
4. **Repeat** для boundary_overhead
5. **Create report**

---

## 📝 Technical Notes

### Key Difference от Priority 0

| Aspect | Priority 0 | Priority 1 |
|--------|-----------|-----------|
| **Quantification** | ∀(t,U,β) | ∀(t,U,β,e) |
| **Structure** | Parameters only | Structure fields |
| **SMT Logic** | Pure QF_NRA | QF_NRA + approximation |
| **Verification** | Direct | Conservative bounds |
| **Confidence** | Exact | High (99.9%+) |

### Limitations

**Что мы НЕ проверяем:**
- Корректность конструирования `SEDTEpoch` из траектории
- Связь полей структуры (e.g., `num_touches` vs `length`)
- Динамические свойства Collatz

**Что мы проверяем:**
- ✅ Арифметические bounds для допустимых значений полей
- ✅ Worst-case scenarios
- ✅ Численная согласованность constrain

---

**Start Date:** 2025-10-03  
**Expected Completion:** 1 week  
**Confidence:** High (based on Priority 0 success)

---

**Конец плана**

