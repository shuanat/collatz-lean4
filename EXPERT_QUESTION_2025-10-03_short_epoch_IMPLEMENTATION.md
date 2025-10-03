# Expert Question: Implementation Issues for `short_epoch_potential_bounded`

**Date:** 2025-10-03  
**Context:** Implementing expert's Route B (piecewise on t) solution  
**Status:** Proof strategy correct, but compilation errors in Lean 4 code

---

## 🎯 Problem

Following the expert's guidance (Route B with case split on t), I've implemented the proof structure:
- **Small cases (t ∈ {3,4,5}):** L₀ = 10, show `10(c + 2β) ≤ β·C(t,U) + 2·2^{t-2}`
- **Large case (t ≥ 6):** L₀ = 2^{t-2}, split into two absorbed terms

But encountering multiple compilation errors that suggest API usage mistakes.

---

## 📋 Current Code Structure

```lean
/-- Constant c := log₂(3/2) for SEDT bounds -/
noncomputable def c : ℝ := log (3/2) / log 2

lemma c_pos : c > 0 := ...  -- ✅ compiles
lemma c_le_one : c ≤ 1 := ...  -- ✅ compiles

lemma short_epoch_potential_bounded (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β ≥ 1) (h_short : e.length < L₀ t U) :
  ∃ (ΔV : ℝ), abs ΔV ≤ β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ) := by
  -- Setup: ✅ works
  have h_c_pos : c > 0 := c_pos
  have h_c_le_one : c ≤ 1 := c_le_one
  have h_per_step_pos : c + β * 2 > 0 := ...
  
  let total_bound := (e.length : ℝ) * (c + β * 2)
  use total_bound
  
  have h_total_nonneg : total_bound ≥ 0 := ...
  rw [abs_of_nonneg h_total_nonneg]
  
  have h_bound_by_L0 : total_bound < (L₀ t U : ℝ) * (c + β * 2) := ...
  
  -- ❌ Main proof with errors below
  have h_main : (L₀ t U : ℝ) * (c + β * 2) ≤ β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ) := by
    have h_C_def : (C t U : ℝ) = 2 * (2^t : ℝ) + 3 * (t : ℝ) + 3 * (U : ℝ) := by
      unfold C; simp; ring
    
    by_cases ht_small : t ≤ 5
    · -- Small case branch (ERRORS HERE)
      ...
    · -- Large case branch (ERRORS HERE)
      ...
  
  linarith [h_bound_by_L0, h_main]
```

---

## ❌ Compilation Errors

### Error 1: `interval_cases` issues
```
error: Collatz/SEDT.lean:959:13: interval_cases t
error: omega could not prove the goal (t < 3 branches)
```

**My attempt:**
```lean
interval_cases t
· omega  -- t < 3
· omega  -- t < 3
· omega  -- t < 3
· -- t = 3 case
```

**Question:** How to properly handle `interval_cases` with `ht : t ≥ 3` constraint? Should I use a different tactic?

---

### Error 2: Type mismatch in `mul_le_mul_of_nonneg_left`
```
error: Collatz/SEDT.lean:959:57: Application type mismatch
  ?m.586 has type (0 : ℕ) ≤ 10
  but is expected to have type (0 : ℝ) ≤ 10
```

**My code:**
```lean
exact mul_le_mul_of_nonneg_left h_c_le_one (by norm_num : 0 ≤ 10)
```

**Attempted fix:**
```lean
exact mul_le_mul_of_nonneg_left h_c_le_one (by norm_num : (0 : ℝ) ≤ 10)
```

**Question:** Is this the correct way to specify real number type in `norm_num`?

---

### Error 3: `ring_nf` fails
```
error: Collatz/SEDT.lean:960:12: unsolved goals
⊢ β * 20 ≤ β * 20
```

**My code:**
```lean
apply add_le_add
· exact mul_le_mul_of_nonneg_left h_c_le_one (by norm_num : (0 : ℝ) ≤ 10)
· ring_nf
```

**Question:** Should I use `ring` or `linarith` instead? Or just `rfl`?

---

### Error 4: Cast issues with power arithmetic
```
error: Collatz/SEDT.lean:1033:12: Type mismatch
  this has type (2 : ℕ) ^ (t - 2) * 2 = 2 ^ (t - 1)
  but is expected to have type (2 : ℝ) ^ (t - 2) * 2 = 2 ^ (t - 1)
```

**My code:**
```lean
have : (2^(t-2) : ℕ) * 2 = 2^(t-1) := by
  calc (2^(t-2) : ℕ) * 2
      = 2^(t-2) * 2^1 := by norm_num
    _ = 2^((t-2) + 1) := by rw [← pow_add]
    _ = 2^(t - 1) := by rw [this]
exact this  -- ❌ type mismatch here
```

**Question:** How to properly convert ℕ arithmetic to ℝ? Should I use `norm_cast` somewhere?

---

### Error 5: `linarith` fails on simple inequality
```
error: Collatz/SEDT.lean:1046:42: linarith failed to find a contradiction
⊢ 2 ^ (t - 1) ≤ 2 * 2 ^ t
```

**My code:**
```lean
calc (2^(t-1) : ℝ)
    ≤ (2^(t-1) : ℝ) * 4 := by linarith [show (1 : ℝ) ≤ 4 by norm_num]
  _ = (2 * 2^t : ℝ) := by norm_cast; exact this
```

**Context:** I've proven `(2^(t-1) : ℕ) * 4 = 2 * 2^t`, but the cast to ℝ doesn't work.

**Question:** What's the right way to use this ℕ equality in ℝ context?

---

### Error 6: L₀ = 2^{t-2} for t ≥ 6
```
error: Collatz/SEDT.lean:1013:10: Type mismatch
  this has type 8 < 2 ^ (t - 2)
  but is expected to have type 10 < 2 ^ (t - 2)
```

**My code:**
```lean
have : 10 < 2^(t-2) := by
  have : 2^3 < 2^(t-2) := Nat.pow_lt_pow_right (by decide) (by omega : 3 < t - 2)
  norm_num at this  -- gives 8 < 2^(t-2), but we need 10 < ...
  exact this
```

**Question:** How to go from `8 < 2^(t-2)` (which is `2^3 < 2^(t-2)`) to `10 < 2^(t-2)`? Should I use transitivity?

---

## 🤔 Core Questions

### Q1. Proper `interval_cases` usage
For `ht : t ≥ 3` and `ht_small : t ≤ 5`, how do I properly enumerate t ∈ {3,4,5}?

**Options:**
- A) `interval_cases t <;> [tactic for each]`
- B) Manual `match t with | 3 => ... | 4 => ... | 5 => ...`
- C) Something else?

### Q2. ℕ → ℝ cast in arithmetic proofs
When I prove an equality like `(a : ℕ) * b = c` and want to use it in ℝ context, what's the pattern?

**Options:**
- A) `norm_cast` before/after the proof
- B) Prove it directly in ℝ using `calc` with casts
- C) Use `Nat.cast_mul`, `Nat.cast_pow`, etc. explicitly

### Q3. `linarith` with power inequalities
Why does `linarith` fail on `2^(t-1) ≤ 2 * 2^t`? Should I:
- A) Prove it as a separate lemma first
- B) Use `nlinarith` or `polyrith`
- C) Use `calc` with explicit steps

---

## 💡 What I Think I Need

1. **Clean examples** of `interval_cases` with constraints
2. **Pattern** for ℕ/ℝ cast in power arithmetic (`2^k` in both contexts)
3. **Tactics** for proving simple exponential inequalities (`2^(t-1) ≤ 2·2^t`)
4. **Best practice** for splitting cases with `by_cases` and `interval_cases` together

---

## 📎 Full Error Log

```
error: Collatz/SEDT.lean:935:22: No goals to be solved
error: Collatz/SEDT.lean:947:10: No goals to be solved
error: Collatz/SEDT.lean:954:76: No goals to be solved
error: Collatz/SEDT.lean:959:57: Application type mismatch
error: Collatz/SEDT.lean:960:12: unsolved goals (β * 20 ≤ β * 20)
error: Collatz/SEDT.lean:966-968:14: omega could not prove the goal
error: Collatz/SEDT.lean:969:12: No goals to be solved
error: Collatz/SEDT.lean:1013:10: Type mismatch (8 < ... vs 10 < ...)
error: Collatz/SEDT.lean:1018:98: No goals to be solved
error: Collatz/SEDT.lean:1022:55: Application type mismatch (Nat.cast_nonneg)
error: Collatz/SEDT.lean:1023:52: No goals to be solved
error: Collatz/SEDT.lean:1033:12: Type mismatch (ℕ vs ℝ)
error: Collatz/SEDT.lean:1046:42: linarith failed
error: Collatz/SEDT.lean:1047:49: No goals to be solved
error: Collatz/SEDT.lean:1049:64: linarith failed
error: Collatz/SEDT.lean:1050:83: unsolved goals
```

---

## 🎯 Ideal Solution

A **corrected code snippet** for the `h_main` proof that:
1. ✅ Handles `interval_cases` correctly for t ∈ {3,4,5}
2. ✅ Properly casts between ℕ and ℝ in power arithmetic
3. ✅ Uses appropriate tactics (`linarith`, `omega`, `norm_num`, etc.)
4. ✅ Compiles without errors in Lean 4

Or guidance on:
- Which parts to prove as helper lemmas first
- Alternative proof structure that's easier to formalize

---

## 📚 Context Files

- **Current file:** `Collatz/SEDT.lean` (lines 855-1057)
- **Constants:**
  - `L₀(t,U) = max(2^{t-2}, 10)`
  - `C(t,U) = 2·2^t + 3t + 3U`
  - `c = log₂(3/2) ≈ 0.585`

---

## 🙏 Thank You!

This is the last major hurdle for Task B. The mathematical proof is sound (per your Route B guidance), but I'm stuck on Lean 4 API usage. Any help would be greatly appreciated! 🚀

