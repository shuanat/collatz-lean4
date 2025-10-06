# SMT Solver Integration Plan for Collatz Lean4

**Дата:** 03 октября 2025  
**Время:** 05:00 UTC  
**Статус:** 📋 План разработан

---

## 🎯 Цель

Интегрировать Z3 и CVC5 SMT солверы для автоматической верификации численных неравенств и арифметических аксиом в `SEDT.lean`.

---

## 📊 Анализ Аксиом

### Категории Аксиом (13 total)

#### **A. Кандидаты для SMT Верификации (4)**

Эти аксиомы содержат **чистую арифметику** без сложной динамики:

1. **`t_log_bound_for_sedt`** ✅ ВЫСОКИЙ ПРИОРИТЕТ
   ```lean
   axiom t_log_bound_for_sedt (t U : ℕ) (β : ℝ)
     (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β ≥ 1) :
     (t : ℝ) * log (3/2) / log 2 ≤ β * ((2^t : ℝ) + (3*U : ℝ))
   ```
   **SMT подход:**
   - Экспортировать в SMT-LIB2 формат
   - Использовать Z3 с `(set-logic QF_NRA)` (нелинейная вещественная арифметика)
   - Верифицировать для конкретных значений t, U, β

2. **`sedt_overhead_bound`** ✅ ВЫСОКИЙ ПРИОРИТЕТ
   ```lean
   axiom sedt_overhead_bound (t U : ℕ) (β : ℝ) (ht : t ≥ 3) (hU : U ≥ 1) :
     β * (2^t : ℝ) + β * ((max (2 * 2^(t-2)) (3*t)) : ℝ) + (t : ℝ) * log (3/2) / log 2
     ≤ β * (C t U : ℝ)
   ```
   **SMT подход:**
   - Раскрыть `C(t,U) = 2·2^t + 3t + 3U`
   - Верифицировать для типичных параметров

3. **`SEDTEpoch_head_overhead_bounded`** ⚠️ СРЕДНИЙ ПРИОРИТЕТ
   ```lean
   axiom SEDTEpoch_head_overhead_bounded (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
     (_ht : t ≥ 3) (_hU : U ≥ 1) :
     abs e.head_overhead ≤ β * (2^t : ℝ) + (t : ℝ) * log (3/2) / log 2
   ```
   **SMT подход:**
   - Требует моделирования `SEDTEpoch` структуры
   - Верифицировать для worst-case overhead

4. **`SEDTEpoch_boundary_overhead_bounded`** ⚠️ СРЕДНИЙ ПРИОРИТЕТ
   ```lean
   axiom SEDTEpoch_boundary_overhead_bounded (t : ℕ) (e : SEDTEpoch) (β : ℝ) :
     abs e.boundary_overhead ≤ β * (K_glue t : ℝ)
   ```
   **SMT подход:**
   - Верифицировать для `K_glue(t) = max(2·2^{t-2}, 3t)`

#### **B. Требуют Динамического Анализа (5)**

Эти аксиомы включают сложную динамику Collatz и **не подходят для прямой SMT верификации**:

5. **`single_step_potential_bounded`** ❌ НЕ ДЛЯ SMT
   - Требует анализа функции `T_odd(r)` и `V(n)`
   - Зависит от траектории Collatz

6. **`plateau_touch_count_bounded`** ❌ НЕ ДЛЯ SMT
   - Требует фазового смешивания (phase mixing)
   - Статистическое свойство длинных траекторий

7. **`touch_provides_multibit_bonus`** ❌ НЕ ДЛЯ SMT
   - Зависит от `depth_minus(r)` и 2-adic valuation
   - Требует анализа конкретных траекторий

8. **`short_epoch_potential_bounded`** ❌ НЕ ДЛЯ SMT
   - Зависит от конкретной структуры epoch
   - Требует bounds analysis

9. **`period_sum_with_density_negative`** ❌ НЕ ДЛЯ SMT
   - Cycle exclusion theorem
   - Требует формализации Appendix B

#### **C. Экзистенциальные и Метатеоретические (4)**

Эти аксиомы **нельзя верифицировать через SMT** напрямую:

10. **`exists_very_long_epoch_threshold`** ❌ НЕ ДЛЯ SMT
    - Экзистенциальная аксиома (∃ L_crit)
    - Требует вычислительного поиска L_crit

11. **`sedt_bound_negative_for_very_long_epochs`** ⚠️ УСЛОВНО
    - Зависит от `exists_very_long_epoch_threshold`
    - Можно верифицировать для конкретных L, если известен L_crit

12. **`sedt_full_bound_technical`** ⚠️ УСЛОВНО
    - Комбинация других bounds
    - Можно свести к SMT после подстановки

13. **`sedt_negativity_from_bound`** ✅ ТРИВИАЛЬНО
    - Чисто логическое утверждение: `ΔV ≤ b < 0 → ΔV < 0`
    - Можно доказать в Lean напрямую без SMT

---

## 🔧 Технический План

### Phase 1: Setup (Week 1)

**1.1. Установка SMT солверов**

```bash
# Z3
sudo apt-get install z3  # или brew install z3 на macOS
z3 --version  # v4.12+

# CVC5
wget https://github.com/cvc5/cvc5/releases/latest/download/cvc5-Linux
chmod +x cvc5-Linux
./cvc5-Linux --version  # v1.0+
```

**1.2. Создание Python-скриптов для экспорта**

Структура:
```
scripts/smt/
├── README.md
├── export_axioms.py       # Экспорт аксиом в SMT-LIB2
├── verify_z3.py           # Запуск Z3 верификации
├── verify_cvc5.py         # Запуск CVC5 верификации
├── axioms/
│   ├── t_log_bound.smt2
│   ├── overhead_bound.smt2
│   └── ...
└── results/
    └── verification_report.json
```

### Phase 2: Экспорт Аксиом (Week 1-2)

**2.1. Создание SMT-LIB2 файлов**

Пример для `t_log_bound_for_sedt`:

```smt2
; t_log_bound_for_sedt.smt2
(set-logic QF_NRA)  ; Nonlinear Real Arithmetic
(set-option :produce-models true)

; Constants
(declare-const t Real)
(declare-const U Real)
(declare-const beta Real)

; Constraints
(assert (>= t 3))
(assert (>= U 1))
(assert (>= beta 1))

; Helper definitions
(define-fun log_3_2 () Real 0.585)  ; log(3/2)/log(2) ≈ 0.585
(define-fun two_pow_t () Real (^ 2 t))

; Main inequality (NEGATED for counterexample search)
(assert (not 
  (<= (* t log_3_2) 
      (* beta (+ two_pow_t (* 3 U))))))

(check-sat)
(get-model)
```

**2.2. Автоматизация экспорта**

```python
# export_axioms.py
def export_t_log_bound(output_dir: Path):
    """Export t_log_bound_for_sedt to SMT-LIB2."""
    template = """
    (set-logic QF_NRA)
    (declare-const t Real)
    (declare-const U Real)
    (declare-const beta Real)
    
    (assert (>= t 3))
    (assert (>= U 1))
    (assert (>= beta 1))
    
    ; Negated inequality
    (assert (not 
      (<= (* t {log_3_2}) 
          (* beta (+ (^ 2 t) (* 3 U))))))
    
    (check-sat)
    """
    
    log_3_2 = math.log(1.5) / math.log(2)
    
    output = template.format(log_3_2=log_3_2)
    (output_dir / "t_log_bound.smt2").write_text(output)
```

### Phase 3: Верификация (Week 2)

**3.1. Z3 Верификация**

```python
# verify_z3.py
import subprocess
from pathlib import Path

def verify_with_z3(smt_file: Path) -> dict:
    """Run Z3 on SMT-LIB2 file."""
    cmd = ["z3", "-smt2", str(smt_file), "-T:30"]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    
    return {
        "solver": "Z3",
        "file": smt_file.name,
        "sat": "unsat" in result.stdout.lower(),
        "time_ms": extract_time(result.stdout),
        "model": extract_model(result.stdout) if "sat" in result.stdout else None
    }

def main():
    axioms_dir = Path("scripts/smt/axioms")
    results = []
    
    for smt_file in axioms_dir.glob("*.smt2"):
        print(f"Verifying {smt_file.name}...")
        result = verify_with_z3(smt_file)
        results.append(result)
        
        if result["sat"]:
            print(f"  ✅ UNSAT (axiom holds)")
        else:
            print(f"  ❌ SAT (counterexample found!)")
            print(f"     Model: {result['model']}")
    
    # Save report
    import json
    Path("scripts/smt/results/verification_report.json").write_text(
        json.dumps(results, indent=2)
    )
```

**3.2. CVC5 Верификация (cross-check)**

```python
# verify_cvc5.py
def verify_with_cvc5(smt_file: Path) -> dict:
    """Run CVC5 on SMT-LIB2 file."""
    cmd = [
        "./cvc5-Linux",
        "--lang=smt2",
        "--produce-models",
        "--tlimit=30000",
        str(smt_file)
    ]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    
    return {
        "solver": "CVC5",
        "file": smt_file.name,
        "sat": "unsat" in result.stdout.lower(),
        "time_ms": extract_time(result.stdout),
        "model": extract_model(result.stdout) if "sat" in result.stdout else None
    }
```

### Phase 4: Интеграция с Lean (Week 3)

**4.1. Создание Lean wrapper**

```lean
-- scripts/lean_verify_axiom.lean
import Std.Data.String.Basic

/-- Run external SMT solver and check result -/
def verifySMT (axiomName : String) : IO Bool := do
  let result ← IO.Process.output {
    cmd := "python3"
    args := #["scripts/smt/verify_z3.py", axiomName]
  }
  return result.exitCode == 0

/-- Verify axiom with SMT and report -/
def checkAxiom (name : String) : IO Unit := do
  IO.println s!"Verifying axiom: {name}"
  let ok ← verifySMT name
  if ok then
    IO.println "  ✅ SMT verification passed"
  else
    IO.println "  ❌ SMT verification failed"
```

**4.2. CI Integration**

Добавить в `.github/workflows/lean.yml`:

```yaml
jobs:
  smt-verification:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Z3
        run: sudo apt-get update && sudo apt-get install -y z3
      
      - name: Install Python dependencies
        run: pip install pysmt z3-solver
      
      - name: Run SMT verification
        run: python scripts/smt/verify_z3.py
      
      - name: Upload results
        uses: actions/upload-artifact@v4
        with:
          name: smt-verification-results
          path: scripts/smt/results/
```

### Phase 5: Документация (Week 3)

**5.1. Обновить README**

Добавить секцию:

```markdown
## 🔬 SMT Verification

Numerical axioms in `SEDT.lean` are verified using Z3 and CVC5 SMT solvers.

### Run Verification

```bash
# Verify all axioms
python scripts/smt/verify_z3.py

# Verify specific axiom
python scripts/smt/verify_z3.py t_log_bound

# Cross-check with CVC5
python scripts/smt/verify_cvc5.py
```

### Results

See `scripts/smt/results/verification_report.json` for detailed results.
```

**5.2. Создать технический репорт**

`reports/YYYY-MM-DD_HHMM_smt-verification-complete.md`

---

## 🎯 Ожидаемые Результаты

### Immediate (Phase 1-3)

1. ✅ 4 аксиомы верифицированы через SMT (Z3 + CVC5)
2. ✅ Автоматические скрипты для экспорта и верификации
3. ✅ JSON репорт с результатами

### Medium-term (Phase 4-5)

4. ✅ CI интеграция (автоматическая верификация при push)
5. ✅ Документация и примеры использования
6. ✅ Cross-validation Z3 ↔ CVC5 для надежности

### Long-term

7. 🔄 Периодическая reverification при изменении аксиом
8. 🔄 Расширение на другие numerical lemmas
9. 🔄 Формализация SMT-verified axioms как Lean theorems (если возможно)

---

## ⚠️ Ограничения

### Что SMT **НЕ** может

1. **Динамические свойства Collatz** (траектории, циклы)
2. **Экзистенциальные утверждения** (∃ L_crit)
3. **Статистические свойства** (touch frequency, phase mixing)
4. **Комбинаторные bounds** (epoch структура)

### Что SMT **может**

1. ✅ Арифметические неравенства (linear/nonlinear)
2. ✅ Bounds для конкретных параметров (t, U, β)
3. ✅ Verification для finite domains
4. ✅ Counterexample search

---

## 📊 Приоритеты

| Приоритет | Аксиома | Сложность | Время |
|-----------|---------|-----------|-------|
| **P0** | `t_log_bound_for_sedt` | Low | 2h |
| **P0** | `sedt_overhead_bound` | Medium | 4h |
| **P1** | `SEDTEpoch_head_overhead_bounded` | Medium | 6h |
| **P1** | `SEDTEpoch_boundary_overhead_bounded` | Low | 3h |
| **P2** | `sedt_full_bound_technical` | High | 8h |
| **P2** | `sedt_bound_negative_for_very_long_epochs` | High | 8h (after L_crit) |

**Total Estimated Time:** 2-3 weeks

---

## 🚀 Next Steps

1. **Создать структуру директорий** (`scripts/smt/`)
2. **Установить Z3 и CVC5**
3. **Экспортировать первую аксиому** (`t_log_bound_for_sedt`)
4. **Запустить Z3 верификацию**
5. **Cross-check с CVC5**
6. **Создать репорт**

**Готовы начать?** Предлагаю начать с `t_log_bound_for_sedt` как самой простой аксиомы.

---

**Конец плана**

