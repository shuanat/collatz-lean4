# Expert Question: Help Implementing `touch_onebit` Lemma in Lean 4

**Date:** October 3, 2025  
**Context:** Implementing corrected touch bonus lemma based on expert feedback  
**Status:** Attempted implementation with ~40 compilation errors

---

## Background

Following expert analysis, we need to replace the incorrect `touch_provides_multibit_bonus` axiom with a correct proven lemma showing that at a t-touch (depth⁻(r) = t ≥ 3), the depth drops by **exactly 1 bit**, not to ≤ 2.

**Correct mathematical statement:**
```
depth⁻(r') = t - 1  (not ≤ 2 as previously axiomatized)
```

---

## Current Implementation Attempt

I've attempted to implement the proof following the expert's outline, but I'm encountering numerous compilation errors related to mathlib API usage. Here's the current code:

```lean
lemma touch_provides_onebit_bonus (r : ℕ) (t : ℕ) (ht : t ≥ 3) (h_touch : depth_minus r = t) :
  ∃ (r' : ℕ),
    r' = (3 * r + 1) / 2 ∧
    depth_minus r' = t - 1 := by
  -- Step 1: From depth⁻(r) = t, extract r+1 = 2^t * m with m odd
  have hfac : (r + 1).factorization 2 = t := by
    simpa [depth_minus] using h_touch
  
  have hdiv : 2^t ∣ r + 1 := by
    -- ERROR: Unknown identifier `ordProj_dvd`
    have := ordProj_dvd (r + 1) 2
    simp only [hfac] at this
    exact this
  
  -- Use odd-part decomposition: r+1 = 2^k * m with m odd
  have hr_pos : r + 1 ≠ 0 := by omega
  obtain ⟨k, m, hmOdd, hr_eq⟩ := Nat.exists_eq_two_pow_mul_odd hr_pos
  
  -- The exponent k must equal t (uniqueness of 2-adic decomposition)
  have hk : k = t := by
    have h1 : (r + 1).factorization 2 = k := by
      have : (2^k * m).factorization 2 = k := by
        have h_odd_fac : m.factorization 2 = 0 := by
          obtain ⟨j, hj⟩ := hmOdd
          have : ¬ 2 ∣ m := by
            intro h_div
            obtain ⟨q, hq⟩ := h_div
            rw [hq] at hj
            omega
          exact Nat.factorization_eq_zero_of_not_dvd this
        
        -- ERROR: factorization_mul returns Finsupp, not applied to 2
        have h_pow_fac : (2^k).factorization 2 = k := by
          cases k with
          | zero => simp [Nat.factorization_one]
          | succ n =>
            have : (2^(n+1)).factorization 2 = n + 1 := by
              rw [pow_succ]
              -- ERROR: factorization_mul type mismatch
              have h1 := Nat.factorization_mul (by omega : 0 < 2) (Nat.pow_pos (by omega : 0 < 2))
              simp [Nat.factorization_two] at h1
              have h2 : (2^n).factorization 2 = n := by
                sorry  -- recursive case
              rw [h2] at h1
              omega
            exact this
        
        calc (2^k * m).factorization 2
            = (2^k).factorization 2 + m.factorization 2 := by
              -- ERROR: Nat.pow_ne_zero doesn't exist, and type mismatch
              have hk_ne : 2^k ≠ 0 := Nat.pow_ne_zero k (by omega)
              have hm_ne : m ≠ 0 := by obtain ⟨j, hj⟩ := hmOdd; omega
              exact Nat.factorization_mul hk_ne hm_ne
          _ = k + 0 := by rw [h_pow_fac, h_odd_fac]
          _ = k := by omega
      rw [← hr_eq]
      exact this
    rw [h1] at hfac
    omega
  
  -- [... rest of proof with similar issues ...]
```

---

## Main Compilation Errors

### 1. **Missing `ordProj_dvd` identifier**
```
error: Collatz/SEDT.lean:291:12: Unknown identifier `ordProj_dvd`
```

**My understanding:** I need `ordProj[2] (r+1) = 2^((r+1).factorization 2)` divides `r+1`.

**Question:** 
- What's the correct import and usage for `ordProj_dvd`?
- Is it `Nat.ordProj_dvd` or in a different namespace?
- Do I need a specific import like `Mathlib.Data.Nat.Factorization.Basic`?

---

### 2. **`Nat.pow_ne_zero` doesn't exist**
```
error: Collatz/SEDT.lean:330:38: Unknown constant `Nat.pow_ne_zero`
```

**Question:**
- What's the correct lemma name for `n^k ≠ 0` when `n ≠ 0`?
- Should I use `Nat.pow_pos` and convert to `≠ 0`?

---

### 3. **`Nat.factorization_mul` type mismatch**
```
error: Type mismatch
  Nat.factorization_mul hk_ne hm_ne
has type
  (2 ^ k * m).factorization = (2 ^ k).factorization + m.factorization
but is expected to have type
  (2 ^ k * m).factorization 2 = (2 ^ k).factorization 2 + m.factorization 2
```

**My understanding:** `factorization_mul` returns a `Finsupp`, but I need to project to prime `2`.

**Question:**
- How do I properly apply `Nat.factorization_mul` and project to a specific prime?
- Is there a lemma like `(a * b).factorization p = a.factorization p + b.factorization p`?

---

### 4. **Prime factorization lemmas**
```
error: Invalid field `factorization_self`
```

**Question:**
- What's the correct lemma for `(p : ℕ).factorization p = 1` when `p` is prime?
- I tried `Nat.prime_two.factorization_self` but got a field error.
- Should it be `Prime.factorization_self` in a different namespace?

---

### 5. **`Nat.factorization_pow` returns `Finsupp`**
```
error: Type mismatch
  Nat.factorization_pow 2 (t - 1)
has type
  (2 ^ (t - 1)).factorization = (t - 1) • Nat.factorization 2
but is expected to have type
  (2 ^ (t - 1)).factorization 2 = (t - 1) * (Nat.factorization 2) 2
```

**Question:**
- How do I extract `(2^k).factorization 2 = k` from `Nat.factorization_pow`?
- Do I need to use `Finsupp.single` or a projection lemma?

---

### 6. **`Even` representation issues**
```
error: Type mismatch
  Eq.symm hp
has type
  p + p = 3 * 2 ^ (t - 1) * m
but is expected to have type
  2 * p = 3 * 2 ^ (t - 1) * m
```

**Context:** Proving `Even n` gives `∃ k, n = 2 * k`, but I get `n = k + k`.

**Question:**
- Is there a lemma to convert `n = k + k` to `n = 2 * k`?
- Or should I use a different `Even` representation?

---

### 7. **Mysterious `3.` scientific notation error**
```
error: failed to synthesize
  OfScientific ℕ

case h.right.calc.step
⊢ 3. = t - 1
```

**Question:**
- Why is `3.` being interpreted as scientific notation?
- This appears in a `calc` block where I write `3.factorization 2`.
- How should I properly reference `(3 : ℕ).factorization 2`?

---

## Specific Help Needed

### Priority 1: Correct mathlib lemma names
Can you provide the exact lemma names (with full namespace) for:

1. ✅ **Divisibility from factorization:**  
   `p^k ∣ n` given `n.factorization p ≥ k`

2. ✅ **Factorization of products (projected to prime):**  
   `(a * b).factorization p = a.factorization p + b.factorization p`

3. ✅ **Factorization of powers:**  
   `(p^k).factorization p = k` for prime `p`

4. ✅ **Prime's own factorization:**  
   `p.factorization p = 1` for prime `p`

5. ✅ **Power non-zero:**  
   `n^k ≠ 0` when `n ≠ 0`

### Priority 2: Proof skeleton corrections

Can you correct the key problematic sections:

**Section A: Converting factorization to divisibility (lines 289-293)**
```lean
have hdiv : 2^t ∣ r + 1 := by
  -- What's the correct way to get divisibility from factorization?
  sorry
```

**Section B: Proving `(2^k).factorization 2 = k` (lines 313-327)**
```lean
have h_pow_fac : (2^k).factorization 2 = k := by
  -- What's the correct approach? Induction? Direct lemma?
  sorry
```

**Section C: Applying `factorization_mul` correctly (lines 328-332)**
```lean
calc (2^k * m).factorization 2
    = (2^k).factorization 2 + m.factorization 2 := by
      -- How to properly use Nat.factorization_mul and project to prime 2?
      sorry
```

**Section D: Converting `Even` from `k + k` to `2 * k` (lines 394-404)**
```lean
obtain ⟨p, hp⟩ := h_prod_even  -- hp : 3 * 2^(t-1) * m = p + p
-- Need: 3 * 2^(t-1) * m = 2 * p
sorry
```

---

## What I've Already Tried

1. ✅ Found `Nat.exists_eq_two_pow_mul_odd` for odd-part decomposition
2. ✅ Used `Nat.factorization_eq_zero_of_not_dvd` for odd numbers
3. ✅ Attempted to use `Nat.factorization_mul` but hit type issues
4. ❌ Searched for `ordProj_dvd` but couldn't find correct import
5. ❌ Tried `Nat.pow_ne_zero` (doesn't exist)
6. ❌ Tried `Prime.factorization_self` (field error)

---

## My Current Understanding (Please Correct!)

1. **Factorization API:** `n.factorization : ℕ →₀ ℕ` is a `Finsupp` mapping primes to exponents.

2. **To get divisibility:** Should use `ordProj[p] n := p^(n.factorization p)` and `ordProj_dvd`.

3. **Projection to prime:** Need to apply the `Finsupp` to a specific prime `p : ℕ`.

4. **Prime lemmas:** Should be in `Nat.Prime` namespace, but field lookups fail.

---

## Ideal Response

Please provide one of:

**Option A:** Corrected code sections for Priority 2 (Sections A-D)

**Option B:** List of exact lemma names with examples for Priority 1

**Option C:** Completely rewritten proof using correct mathlib API

**Option D:** Alternative proof strategy that avoids these issues

---

## Full File Context

**Location:** `g:\Math\Collatz-Workspace\collatz-lean4\Collatz\SEDT.lean`

**Lines:** 281-502 (lemma `touch_provides_onebit_bonus`)

**Imports:** Currently using:
```lean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Field.Basic
import Collatz.Basic
import Collatz.Epoch
```

**Missing imports?** May need additional factorization imports.

---

## Thank You!

Any guidance on the correct mathlib API usage would be immensely helpful. This is the last remaining `sorry` in our proof (the `h2` recursive case), and correcting the compilation errors would complete the formalization.

**Expected time investment:** If you can provide corrected code for Sections A-D, I estimate 30-60 minutes to integrate and verify.

---

**References:**
- Previous expert analysis: `EXPERT_QUESTION_2025-10-03_touch_bonus.md`
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- Current status: 77% formalized (6 proven lemmas + 4 SMT-verified axioms)

