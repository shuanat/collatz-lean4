# Single Step Formalization Plan

**Статус:** ✅ **ЗАВЕРШЕНО** (3 октября 2025)  
**Goal:** Replace `single_step_potential_bounded` axiom with proven lemma  
**Strategy:** Follow expert solution (Anatoliy, 2025-10-03) step-by-step  
**Estimated time:** 4-6 hours  
**Actual time:** ~8 hours

---

## Phase 1: Helper Lemma - Depth Drop (CRITICAL)

**Lemma:** `depth_drop_one_shortcut`
```lean
lemma depth_drop_one_shortcut (r : ℕ) (hr_odd : Odd r) :
  depth_minus (T_shortcut r) + 1 = depth_minus r
```

**Key idea:** For odd r:
- r+1 = 2k (even)
- T(r)+1 = (3r+3)/2 = 3k
- ν₂(3k) = ν₂(k) (since ν₂(3)=0)
- ν₂(2k) = 1 + ν₂(k)
- Therefore: ν₂(T(r)+1) + 1 = ν₂(r+1)

**Required mathlib lemmas:**
- `Nat.exists_eq_mul_left_of_dvd` or `Even` API
- `Nat.factorization_mul`
- `Nat.Prime.factorization_pow`
- `Nat.factorization_eq_zero_of_not_dvd` (for ν₂(3)=0)

**Status:** ✅ ЗАВЕРШЕНО (3 октября 2025)

---

## Phase 2: Helper Lemma - Log Bound

**Lemma:** `log_part_le_one`
```lean
lemma log_part_le_one (r : ℕ) (hr : r > 0) (hr_odd : Odd r) :
  (log (T_shortcut r) - log r) / log 2 ≤ 1
```

**Key idea:**
- T(r)/r = (3r+1)/(2r) ≤ 2 for r ≥ 1
- log₂(T(r)/r) ≤ log₂(2) = 1

**Required mathlib lemmas:**
- `Real.log_div`
- `Real.log_le_log`
- Arithmetic bounds on (3r+1)/(2r)

**Status:** ✅ ЗАВЕРШЕНО (3 октября 2025)

---

## Phase 3: Main Lemma Combination

**Lemma:** `single_step_potential_bounded`
```lean
lemma single_step_potential_bounded (r : ℕ) (β : ℝ) 
  (hr : r > 0) (hr_odd : Odd r) (hβ : β ≥ 1) :
  single_step_ΔV r β ≤ log (3/2) / log 2 + β * 2
```

**Key steps:**
1. Unfold ΔV = log_part + β·depth_change
2. Use depth_drop_one → depth_change = -1
3. Use log_part_le_one → log_part ≤ 1
4. Combine: ΔV ≤ 1 - β
5. For β ≥ 1: 1 - β ≤ 0 ≤ log₂(3/2) + 2β

**Status:** ✅ ЗАВЕРШЕНО (3 октября 2025)

---

## Technical Challenges

### Challenge 1: ℕ vs ℤ vs ℝ casts
- ℕ subtraction is truncating
- Need to use ℤ for negative results
- Use `push_cast`, `norm_cast`, `exact_mod_cast`

### Challenge 2: Even/Odd API
- Prefer `Even (n)` over `∃ k, n = 2*k`
- Use `even_iff_two_dvd`, `Odd.add_one`, etc.

### Challenge 3: factorization API
- Use `Nat.factorization_mul` for products
- Use `Nat.Prime.factorization_pow` for powers
- Use `Nat.factorization_eq_zero_of_not_dvd` for coprime

---

## Checkpoints

- [x] Phase 1 compiles ✅
- [x] Phase 2 compiles ✅
- [x] Phase 3 compiles ✅
- [x] Remove axiom ✅
- [x] Full project builds ✅
- [x] Create completion report ✅

**Completion report:** `reports/2025-10/completion/2025-10-03_1700_single-step-complete-MAJOR-MILESTONE.md`

---

## Rollback Strategy

~~If stuck for > 30 min on any phase:~~
~~1. Save progress to separate branch~~
~~2. Ask for expert clarification~~
~~3. Consider hybrid approach (keep axiom for now)~~

**Не потребовалось** - все фазы завершены успешно.

---

## References

- Expert solution: `reports/2025-10/expert-queries/EXPERT_QUESTION_2025-10-03_single_step_bound.md`
- Attempt report: `reports/2025-10/completion/2025-10-03_1500_single-step-formalization-attempt.md`
- Completion report: `reports/2025-10/completion/2025-10-03_1700_single-step-complete-MAJOR-MILESTONE.md`
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/

---

## Итоги

✅ **План полностью выполнен 3 октября 2025**

Все 3 фазы успешно завершены:
1. ✅ Helper Lemma - Depth Drop
2. ✅ Helper Lemma - Log Bound  
3. ✅ Main Lemma Combination

Axiom `single_step_potential_bounded` заменен на proven lemma.

**Время выполнения:** ~8 часов (оценка была 4-6 часов)  
**Причина перерасхода:** Сложности с mathlib API и ℕ/ℝ арифметикой

