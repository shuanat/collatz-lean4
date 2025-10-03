# Expert Question: Proving `max(2·2^{t-2}, 3t) ≤ 2^t` for t ≥ 4

**Context:** Lean 4 formalization of mathematical inequality

---

## Problem

I need to prove the following lemma in Lean 4:

```lean
lemma max_K_glue_le_pow_two (t : ℕ) (ht : t ≥ 4) : 
  max (2 * 2^(t-2)) (3*t) ≤ 2^t
```

**Mathematical fact:** For t ≥ 4, we have max(2·2^{t-2}, 3t) ≤ 2^t.

**Verification:**
- t=4: max(8, 12) = 12 ≤ 16 ✓
- t=5: max(16, 15) = 16 ≤ 32 ✓
- t=6: max(32, 18) = 32 ≤ 64 ✓
- t=7: max(64, 21) = 64 ≤ 128 ✓
- For t ≥ 8: both terms grow slower than 2^t

---

## What I've tried

### Approach 1: Pattern matching on small cases + induction

```lean
lemma max_K_glue_le_pow_two (t : ℕ) (ht : t ≥ 4) : 
  max (2 * 2^(t-2)) (3*t) ≤ 2^t := by
  match t with
  | 0 | 1 | 2 | 3 => omega  -- contradicts ht : t ≥ 4
  | 4 => norm_num  -- ✓ works
  | 5 => norm_num  -- ✓ works
  | 6 => norm_num  -- ✓ works
  | 7 => norm_num  -- ✓ works
  | t' + 8 =>
    -- Need to prove for t ≥ 8
    have h1 : 2 * 2^(t' + 8 - 2) ≤ 2^(t' + 8) := by
      -- This part works: 2·2^{t-2} = 2^{t-1} ≤ 2^t
      ...
    have h2 : 3 * (t' + 8) ≤ 2^(t' + 8) := by
      -- ❌ THIS IS THE PROBLEM
      -- Need: 3t ≤ 2^t for t ≥ 8
      calc 3 * (t' + 8)
          ≤ 4 * (t' + 8) := by omega
        _ ≤ 2 * 2^(t' + 8) := by
            have : 2 * (t' + 8) ≤ 2^(t' + 8) := two_mul_le_two_pow (t' + 8) (by omega)
            linarith [this]  -- ❌ FAILS: linarith can't bridge this gap
        _ = 2^(t' + 9) := by ...
        _ ≥ 2^(t' + 8) := ...  -- ❌ ERROR: Trans LE.le GE.ge
    ...
```

### Errors encountered:

1. **`linarith` failure:**
   ```
   linarith failed to find a contradiction
   this : 2 ^ (t' + 9) ≥ 2 ^ (t' + 8)
   h_tmp : 3 * (t' + 8) ≤ 2 ^ (t' + 9)
   a✝ : 2 ^ (t' + 8) < 3 * (t' + 8)
   ⊢ False
   ```

2. **`Trans` instance error:**
   ```
   invalid 'calc' step, failed to synthesize `Trans` instance
   Trans LE.le GE.ge
   ```

---

## Specific Questions

### Q1: How to properly handle transitivity with `≤` and `≥` in `calc` chains?

I have:
- `h_tmp : 3 * (t' + 8) ≤ 2^(t' + 9)`
- `this : 2^(t' + 9) ≥ 2^(t' + 8)`

Need to conclude: `3 * (t' + 8) ≤ 2^(t' + 8)`

**What's the idiomatic way to combine these?**

Options I'm aware of:
- `linarith [h_tmp, this]` — fails
- `calc` chain with mixed `≤`/`≥` — fails (Trans instance)
- Manual `le_trans` — unsure how to apply with `≥`

### Q2: Is there a better proof strategy for `max(a, b) ≤ c`?

Current approach:
```lean
have h1 : a ≤ c := ...
have h2 : b ≤ c := ...
have : max a b ≤ c := by
  rw [Nat.max_le]
  exact ⟨h1, h2⟩
```

Is this correct? Or is there a simpler tactic?

### Q3: Should I just leave this as an `axiom`?

Given that:
- The inequality is mathematically trivial (verified for all small t)
- The proof is getting complex due to technical issues
- I already have `two_mul_le_two_pow` proven

**Would it be acceptable to keep this as an axiom with a comment explaining it's easily verifiable but technically tedious?**

---

## Context: Why this matters

This lemma is part of a larger formalization of the SEDT (Scaled Epoch Drift Theorem) for the Collatz conjecture. The constant `K_glue(t) = max(2·2^{t-2}, 3t)` represents a boundary overhead bound.

**Current project status:**
- ✅ `two_mul_le_two_pow`: proven (2t ≤ 2^t for t ≥ 3)
- ❌ `max_K_glue_le_pow_two`: stuck
- 13 other axioms: used for complex technical inequalities

---

## Minimal Working Example

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- Already proven
lemma two_mul_le_two_pow (t : ℕ) (ht : t ≥ 3) : 2 * t ≤ 2^t := by
  match t with
  | 0 | 1 | 2 => omega
  | 3 => norm_num
  | 4 => norm_num
  | 5 => norm_num
  | t' + 6 =>
    have ih : 2 * (t' + 5) ≤ 2^(t' + 5) := two_mul_le_two_pow (t' + 5) (by omega)
    calc 2 * (t' + 6)
        = 2 * (t' + 5) + 2 := by ring
      _ ≤ 2^(t' + 5) + 2 := by linarith [ih]
      _ ≤ 2^(t' + 5) + 2^(t' + 5) := by
          have : 2 ≤ 2^(t' + 5) := by
            have : 2^1 ≤ 2^(t' + 5) := Nat.pow_le_pow_right (by decide) (by omega)
            simpa using this
          linarith
      _ = 2 * 2^(t' + 5) := by ring
      _ = 2^(t' + 6) := by
          rw [show t' + 6 = (t' + 5) + 1 by omega]
          rw [pow_succ]
          ring

-- Need to prove
lemma max_K_glue_le_pow_two (t : ℕ) (ht : t ≥ 4) : 
  max (2 * 2^(t-2)) (3*t) ≤ 2^t := by
  sorry
```

---

## What would help

1. **Concrete fix** for the `linarith`/`Trans` issues
2. **Alternative proof strategy** (omega? decide? different induction?)
3. **Advice on axiom usage** in this context
4. **Similar examples** from mathlib of `max(f(t), g(t)) ≤ h(t)` proofs

---

**Lean version:** v4.24.0-rc1  
**Mathlib:** latest (via Lake)

**Thank you!**

