# Lean4 Structure Analysis Report

**Дата:** 2025-10-05  
**Проект:** Collatz Lean4 Formalization  
**Цель:** Выявление дублирований, несоответствий и проблем в текущей структуре

## Executive Summary

Анализ текущей структуры Lean4 проекта выявил несколько критических проблем:
1. **Дублирование определений** между модулями
2. **Несоответствие именования** с бумажной нотацией
3. **Отсутствие централизованной архитектуры**
4. **Неправильные зависимости** между модулями

## Detailed Analysis

### 1. Code Duplications

#### 1.1 Two-adic Depth Definitions
**Проблема:** `depth_minus` определена в двух местах:
- `Collatz/Utilities/TwoAdicDepth.lean` (строка 20)
- `Collatz/Utilities/Constants.lean` (строка 139)

**Решение:** Централизовать в `Collatz/Foundations/Core.lean`

#### 1.2 Touch Definitions
**Проблема:** Множественные определения touch-условий:
- `Collatz/Epochs/TouchAnalysis.lean`: `t_touch_condition`
- `Collatz/Epochs/Core.lean`: `is_t_touch`
- `Collatz/Epochs/MultibitBonus.lean`: `is_touch_refined`
- `Collatz/Epochs/NumeratorCarry.lean`: `is_t_touch_numerator`

**Решение:** Унифицировать в `Collatz/Epochs/Core.lean`

#### 1.3 Touch Frequency Definitions
**Проблема:** Дублирование определений частоты касаний:
- `Collatz/Epochs/TouchAnalysis.lean`: `touch_frequency`
- `Collatz/Utilities/Constants.lean`: `p_touch`

**Решение:** Централизовать в `Collatz/Mixing/TouchFrequency.lean`

#### 1.4 Constants Duplication
**Проблема:** Константы определены в нескольких местах:
- `Collatz/Utilities/Constants.lean`: Основные константы
- `Collatz/Epochs/Core.lean`: Локальные константы
- `Collatz/SEDT/Core.lean`: SEDT-специфичные константы

**Решение:** Централизовать все константы в `Collatz/Utilities/Constants.lean`

### 2. Naming Inconsistencies

#### 2.1 Paper vs Code Notation
**Проблема:** Несоответствие между бумажной и кодовой нотацией:

| Paper Notation | Current Code | Correct Location |
|----------------|--------------|-------------------|
| `depth₋(n)` | `depth_minus` | `Collatz/Foundations/Core.lean` |
| `Q_t` | `Q_t` | ✅ Correct |
| `α(t,U)` | `α` | ✅ Correct |
| `β₀(t,U)` | `β₀` | ✅ Correct |
| `p_t` | `p_touch` | `Collatz/Mixing/TouchFrequency.lean` |
| `T_t` | `t_touch_condition` | `Collatz/Epochs/Core.lean` |

#### 2.2 Function Naming
**Проблема:** Непоследовательное именование функций:
- `is_t_touch` vs `t_touch_condition`
- `touch_frequency` vs `p_touch`
- `find_epoch_start` vs `construct_tepoch`

**Решение:** Унифицировать согласно бумажной нотации

### 3. Module Dependencies Issues

#### 3.1 Circular Dependencies
**Проблема:** Потенциальные циклические зависимости:
- `Collatz/Epochs/Core.lean` импортирует `Collatz/Utilities/Constants.lean`
- `Collatz/Utilities/Constants.lean` импортирует `