# ZMod API Issues & Expert Consultation Request

**Date:** 2025-10-02  
**Project:** Collatz Conjecture Formalization in Lean 4  
**Lean Version:** 4.24.0-rc1  
**mathlib4:** latest

---

## Executive Summary

While formalizing the Ord-Факт theorem (`ord_{2^t}(3) = 2^{t-2}` for `t ≥ 3`), we encountered significant challenges working with the `ZMod` API, specifically around:

1. Type coercion between `ℕ` and `ZMod n`
2. Proving equalities involving casts `(a : ZMod n) = 0`
3. Conversion between divisibility statements and ZMod equality
4. Using `ring` tactic in `calc` chains with mixed types

Despite following expert recommendations and studying mathlib4 documentation, multiple proof attempts failed with type mismatches and tactic failures.

---

## Problem 1: Proving `(1 + 2^t)^2 = 1` in `ZMod (2^{t+1})`

### Mathematical Statement
For `t ≥ 1`, prove:
```lean
lemma one_plus_pow_two_sq (t : ℕ) (ht : t ≥ 1) :
  ((1 : ZMod (2^(t+1))) + (2^t : ℕ))^2 = 1
```

### Mathematical Strategy
1. Expand: `(1 + 2^t)^2 = 1 + 2·2^t + (2^t)^2`
2. Show `2·2^t = 2^{t+1} = 0` in `ZMod (2^{t+1})` via `ZMod.natCast_self`
3. Show `(2^t)^2 = 2^{2t} = 0` in `ZMod (2^{t+1})` via divisibility (`2^{t+1} ∣ 2^{2t}` for `t ≥ 1`)

### Failed Attempts

#### Attempt 1: Direct `calc` chain
```lean
calc ((1 : ZMod (2^(t+1))) + (2^t : ℕ))^2
    = 1 + 2 * (2^t : ZMod (2^(t+1))) + ((2^t : ℕ) : ZMod (2^(t+1)))^2 := by ring
  _ = 1 + 0 + 0 := by simp [h1, h2]
  _ = 1 := by ring
```

**Error:**
```
unsolved goals
⊢ 1 + ↑(2 ^ t) * 2 + ↑(2 ^ t) ^ 2 = 1 + ↑(2 ^ t) ^ 2 + 2 ^ t * 2
```

**Issue:** `ring` cannot unify the order of terms when mixing `ℕ` casts and `ZMod` operations.

#### Attempt 2: Using `ZMod.natCast_self`
```lean
have h1 : (2 * 2^t : ZMod (2^(t+1))) = 0 := by
  norm_cast
  convert ZMod.natCast_self (2^(t+1)) using 1
  rw [pow_succ]
  ring
```

**Error:**
```
Type mismatch
  ZMod.natCast_self (2^(t+1))
has type
  ↑(2^(t+1)) = 0
but is expected to have type
  2 * 2^t = 0
```

**Issue:** After `norm_cast`, the goal is `2 * 2^t = 0` but `ZMod.natCast_self` produces `↑(2^(t+1)) = 0`. The `convert` tactic should handle this, but the subsequent `ring` fails.

#### Attempt 3: Using `ZMod.natCast_eq_zero_iff`
```lean
have h2 : ((2^t : ℕ) : ZMod (2^(t+1)))^2 = 0 := by
  rw [← Nat.cast_pow, sq]
  rw [ZMod.natCast_eq_zero_iff]
  apply pow_dvd_pow 2
  omega
```

**Error:**
```
could not unify the conclusion of `pow_dvd_pow 2`
  2 ^ ?m.196 ∣ 2 ^ ?m.197
with the goal
  2 ^ (t + 1) ∣ 2 ^ t * 2 ^ t
```

**Issue:** After `sq` is expanded to `2^t * 2^t`, the `pow_dvd_pow` lemma doesn't recognize this as `2^(2*t)`. Manual rewriting attempts also failed.

#### Attempt 4: Expert-recommended pattern
Following the expert solution provided:
```lean
have h1 : (2 * 2^t : ZMod (2^(t+1))) = 0 := by
  norm_cast
  convert ZMod.natCast_self (2^(t+1)) using 1
  ring [pow_succ]  -- Syntax error: unexpected token '['
```

**Error:** `unexpected token '['; expected command`

**Issue:** The syntax `ring [pow_succ]` appears to be invalid in Lean 4.24.0-rc1.

---

## Problem 2: Proving Hensel Lifting for Powers of 2

### Mathematical Statement
```lean
lemma pow_lift_double {a k t : ℕ} (ha : Odd a) (ht : t ≥ 1) 
  (h : (a : ZMod (2^t))^k = 1) :
  (a : ZMod (2^(t+1)))^(2*k) = 1
```

### Strategy
From `h : (a : ZMod (2^t))^k = 1`, we need to show:
```lean
(a : ZMod (2^(t+1)))^k = 1 ∨ (a : ZMod (2^(t+1)))^k = 1 + (2^t : ℕ)
```

This requires using `ZMod.castHom` to lift from `ZMod (2^t)` to `ZMod (2^(t+1))`.

### Issue
Expert solution mentions using `ZMod.castHom` with divisibility condition `2^t ∣ 2^{t+1}`, but:

```lean
let φ : ZMod (2^(t+1)) →+* ZMod (2^t) :=
  ZMod.castHom (by refine ⟨2, ?_⟩; simp [pow_succ, mul_comm])
```

**Error:**
```
Application type mismatch: The argument ?m.154
has type
  2 ^ t ∣ 2 ^ (t + 1)
but is expected to have type
  2 ^ (t + 1) ∣ 2 ^ t
```

**Issue:** `ZMod.castHom` requires the **reverse** divisibility direction (larger modulus divides smaller), which is mathematically false for our case.

---

## Specific API Questions

### Q1: `ZMod.natCast_self` Type Mismatch
**Expected behavior:** `ZMod.natCast_self (n : ℕ)` should prove `(n : ZMod n) = 0`

**Observed behavior:** When used in context with `norm_cast`, produces type mismatch:
- Has type: `↑n = 0`
- Expected: `<some expression> = 0`

**Question:** What is the correct pattern to apply `ZMod.natCast_self` when the LHS is a non-trivial expression like `2 * 2^t`?

### Q2: `ZMod.natCast_eq_zero_iff` and `rw`
**Expected behavior:** `rw [ZMod.natCast_eq_zero_iff]` should convert `(a : ZMod n) = 0` to `n ∣ a`

**Observed behavior:**
```
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ↑?a = 0
in the target expression
  2 ^ (t * 2) = 0
```

**Question:** 
- Why doesn't `rw` find the pattern after `rw [← Nat.cast_pow, sq]`?
- Should we use `change` before `rw`? If so, what's the exact syntax?

### Q3: `ring` Tactic with ZMod
**Observed behavior:** In `calc` chains, `ring` often fails to unify terms when mixing:
- `(a : ZMod n)` (explicit cast)
- `a : ZMod n` (implicit cast from context)
- `↑a` (displayed cast)

**Question:** 
- Is there a `ring` variant that handles ZMod better?
- Should we normalize all casts first with `norm_cast` before using `ring`?
- What's the recommended pattern for `calc` chains with ZMod?

### Q4: `ZMod.castHom` Direction
**Documentation states:** `ZMod.castHom` is a homomorphism when "characteristic of target divides modulus of source"

**Question:**
- For lifting from `ZMod (2^t)` to `ZMod (2^{t+1})`, which direction is correct?
- The divisibility `2^t ∣ 2^{t+1}` holds, but error says we need `2^{t+1} ∣ 2^t`
- Are we misunderstanding the "up-casting" vs "down-casting" concept?

### Q5: `sq` and `pow_dvd_pow`
**Issue:** After `rw [sq]`, goal becomes `2^t * 2^t` instead of staying as `2^(2*t)`

**Question:**
- How to keep the expression as `2^(2*t)` for `pow_dvd_pow` to work?
- Is there a `simp` lemma that converts `a^n * a^n` to `a^(2*n)` automatically?

---

## What We've Tried

1. ✅ **Read documentation:**
   - `Mathlib.Data.ZMod.Basic` ([link](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Basic.html))
   - Expert solutions document (see attached)

2. ✅ **Followed expert patterns:**
   - Using `convert` with `ZMod.natCast_self`
   - Using `ZMod.natCast_eq_zero_iff` for divisibility
   - Using `norm_cast` before arithmetic

3. ❌ **Encountered blockers:**
   - Type mismatches even with `convert`
   - `rw` not finding patterns after seemingly correct setup
   - `ring` failing in `calc` chains
   - Syntax errors with `ring [lemma_name]`

---

## Minimal Reproducible Examples

### Example 1: `ZMod.natCast_self` with `convert`
```lean
import Mathlib.Data.ZMod.Basic

lemma test1 (t : ℕ) (ht : t ≥ 1) : (2 * 2^t : ZMod (2^(t+1))) = 0 := by
  norm_cast
  convert ZMod.natCast_self (2^(t+1)) using 1
  rw [pow_succ]
  ring  -- Should this close the goal? Currently fails.
```

### Example 2: `ZMod.natCast_eq_zero_iff` with `sq`
```lean
import Mathlib.Data.ZMod.Basic

lemma test2 (t : ℕ) (ht : t ≥ 1) : ((2^t : ℕ) : ZMod (2^(t+1)))^2 = 0 := by
  rw [← Nat.cast_pow, sq]
  rw [ZMod.natCast_eq_zero_iff]  -- Pattern not found!
  sorry
```

### Example 3: `calc` with `ring`
```lean
import Mathlib.Data.ZMod.Basic

lemma test3 (t : ℕ) (ht : t ≥ 1) : 
  ((1 : ZMod (2^(t+1))) + (2^t : ℕ))^2 = 1 := by
  calc ((1 : ZMod (2^(t+1))) + (2^t : ℕ))^2
      = 1 + 2 * (2^t : ZMod (2^(t+1))) + ((2^t : ℕ) : ZMod (2^(t+1)))^2 
        := by ring  -- Works
    _ = 1 + 0 + 0 := by sorry  -- How to prove this step?
    _ = 1 := by ring  -- Works
```

---

## Questions for Experts

1. **What is the canonical way to prove `(1 + 2^t)^2 = 1` in `ZMod (2^{t+1})`?**
   - Should we avoid `calc` chains entirely?
   - Is there a `decide`-like tactic that works for variable `t`?

2. **How to correctly use `ZMod.castHom` for lifting from smaller to larger modulus?**
   - Direction of divisibility requirement unclear
   - Example code for `2^t → 2^{t+1}` would be helpful

3. **Are there known issues with `ring` and ZMod in Lean 4.24.0-rc1?**
   - Should we use `ring_nf` instead?
   - Any workarounds for mixed-type `calc` chains?

4. **Is there a comprehensive tutorial/example for ZMod arithmetic proofs?**
   - The documentation has the API, but not enough proof patterns
   - Examples of proofs similar to ours would be invaluable

5. **Alternative approaches?**
   - Should we use `Fin` instead of `ZMod`?
   - Should we work entirely in `ℕ` with `Nat.ModEq` and convert at the end?
   - Should we prove these lemmas by `interval_cases` for small `t` and accept axioms for general case?

---

## Project Context

**Goal:** Formalize the foundational theorem for Collatz Conjecture analysis:
```lean
theorem ord_three_mod_pow_two (t : ℕ) (ht : t ≥ 3) :
  orderOf (3 : ZMod (2^t)) = 2^(t-2)
```

**Dependency chain:**
1. `one_plus_pow_two_sq` (current blocker)
2. `pow_lift_double` (depends on 1)
3. `three_pow_Qt_eq_one` (uses 2)
4. Main theorem (uses 3)

**Current status:** Stuck at step 1 with 2 `sorry` remaining in `Arithmetic.lean`

---

## Attached Files

- `Collatz/Arithmetic.lean` - Current implementation with `sorry`
- `Collatz/OrdFact.lean` - Main theorem file
- `EXPERT_SOLUTIONS_2025-10-01.md` - Previous expert consultation

---

## Request

We would greatly appreciate:

1. **Working example** of `one_plus_pow_two_sq` proof using current mathlib4 API
2. **Explanation** of the correct `ZMod.castHom` usage for power-of-2 moduli
3. **General guidance** on ZMod proof patterns in Lean 4
4. **Clarification** on when to use `norm_cast`, `simp`, `ring`, `convert`, `change`, etc. in ZMod contexts

Thank you for your time and expertise! 🙏

---

**Contact:** Anatoly Shumak (anatoliy.shumak@gmail.com)  
**Repository:** Collatz Conjecture Formalization (Lean 4)  
**Community:** Lean Zulip (можно опубликовать там, если нужно)

