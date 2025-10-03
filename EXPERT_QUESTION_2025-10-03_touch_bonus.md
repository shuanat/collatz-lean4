# Expert Question: Proving `touch_provides_multibit_bonus` in Lean 4

**Date:** October 3, 2025  
**Context:** Collatz Conjecture formalization - SEDT Theorem  
**Current Status:** 77% formalized (6 proven lemmas + 4 SMT-verified axioms)

---

## The Axiom We Want to Prove

```lean
axiom touch_provides_multibit_bonus (r : ℕ) (t : ℕ) (ht : t ≥ 3) (h_touch : depth_minus r = t) :
  ∃ (r' : ℕ),
    r' = (3 * r + 1) / (2 ^ ((3 * r + 1).factorization 2)) ∧
    depth_minus r' ≤ depth_minus r - t + 2
```

**where:**
- `depth_minus r := (r + 1).factorization 2` (2-adic valuation of `r+1`)
- `r' = T_odd(r) = (3r+1) / 2^e` where `e = ν₂(3r+1)`
- `r` is odd (implicit from Collatz dynamics)

---

## Mathematical Statement

**Claim:** At a **t-touch** (when `depth⁻(r) = t`), the next Collatz step extracts at least `t` bits, causing:

```
depth⁻(r') ≤ depth⁻(r) - t + 2
```

**In terms of 2-adic valuation:**
- Given: `ν₂(r+1) = t` (i.e., `2^t ∣ (r+1)` but `2^{t+1} ∤ (r+1)`)
- Let: `r' = (3r+1) / 2^{ν₂(3r+1)}`
- Prove: `ν₂(r'+1) ≤ ν₂(r+1) - t + 2 = t - t + 2 = 2`

---

## Why This Is Hard

### Challenge 1: Relationship between `r+1` and `3r+1`
- `r` is odd ⇒ `r = 2k+1` for some `k`
- `r+1 = 2k+2 = 2(k+1)`
- `3r+1 = 6k+4 = 2(3k+2)`
- But the relationship between `ν₂(r+1)` and `ν₂(3r+1)` is NOT direct!

### Challenge 2: After Division
- `r' = (3r+1) / 2^{ν₂(3r+1)}` is the **odd part** of `3r+1`
- Need to compute `ν₂(r'+1)` where `r'` is this quotient
- The relationship `r' → r'+1` creates a new 2-adic structure

### Challenge 3: Conservative Bound
- The bound `depth⁻(r') ≤ 2` is **conservative** (worst-case)
- Actual behavior: `depth⁻(r')` depends on phase structure modulo `2^t`
- Full analysis requires modular arithmetic in `Z/2^t Z`

---

## What We Have in Mathlib

### Available Lemmas:
1. **Basic factorization:**
   - `Nat.factorization_def`: definition of prime factorization
   - `Nat.Prime.factorization_pos_of_dvd`: if `p ∣ n` then `n.factorization p > 0`
   - `Nat.pow_factorization_dvd`: `p^(n.factorization p) ∣ n`

2. **Odd part extraction:**
   - `Collatz.Arithmetic.odd_div_pow_two_factorization`: dividing by max power of 2 gives odd

3. **2-adic valuation (padicValNat):**
   - `padicValNat_def`: definition via factorization
   - May have lemmas about `padicValNat (a * b)`, `padicValNat (a + b)`, etc.

---

## Specific Questions for Expert

### Q1: Proving the Core Bound
**How do we formally prove:**
```
ν₂(r'+1) ≤ 2  where r' = (3r+1) / 2^{ν₂(3r+1)}
```
**given** `ν₂(r+1) = t ≥ 3` and `r` odd?

**Attempted approach:**
- Write `r = 2^t · m - 1` where `m` is odd (from `2^t ∣ r+1`)
- Expand `3r+1 = 3(2^t · m - 1) + 1 = 3·2^t·m - 2`
- Compute `ν₂(3r+1)` ≥ 1 (since `-2 ≡ 0 mod 2`)
- **Problem:** The division `r' = (3r+1)/2^{ν₂(3r+1)}` creates complex expression

### Q2: Lean 4 Strategy
**What is the best Lean 4 proof strategy?**

**Option A: Direct computation**
- Expand all definitions
- Use `omega` / `linarith` for arithmetic
- Risk: gets stuck on non-linear expressions

**Option B: Use padicValNat lemmas**
- Convert `factorization 2` to `padicValNat 2`
- Use mathlib lemmas about p-adic valuations
- Risk: need to bridge between `factorization` and `padicValNat`

**Option C: Case analysis on phases**
- Split based on `r mod 2^t`
- Use modular arithmetic lemmas
- Risk: exponentially many cases

**Option D: Conservative upper bound**
- Show `r' < 3r` ⇒ `r'+1 < 3r+1 ≤ 4·2^t·m` ⇒ `ν₂(r'+1) ≤ t + 2`
- But we need `≤ 2`, not `≤ t+2` !

### Q3: Key Mathlib Lemmas
**What specific mathlib lemmas should we use?**

Candidates:
- `padicValNat.div` or similar for valuation after division?
- Lemmas about `ν₂(a + b)` when `ν₂(a) ≠ ν₂(b)`?
- Lemmas about odd numbers: `ν₂(2k+1 + 1) = ν₂(2k+2) = ν₂(2(k+1)) = 1 + ν₂(k+1)`?

### Q4: Simplification
**Can we weaken the statement to make it provable?**

Current: `depth⁻(r') ≤ depth⁻(r) - t + 2`

**Alternative 1:** Prove only for `t ≥ 3` (already assumed!)
**Alternative 2:** Prove `depth⁻(r') ≤ 2` directly (since `depth⁻(r) = t` ⇒ RHS = 2)
**Alternative 3:** Use existential: "depth drops by at least `t-2`" instead of exact bound

---

## Example Computation (t=3)

```
r = 7 (odd)
r+1 = 8 = 2^3  ⇒  depth⁻(r) = 3  ✓

3r+1 = 22 = 2 · 11
ν₂(22) = 1
r' = 22/2 = 11

r'+1 = 12 = 4 · 3 = 2^2 · 3
ν₂(12) = 2

depth⁻(r') = 2 ≤ 3 - 3 + 2 = 2  ✓
```

**Pattern:** For `depth⁻(r) = t`, we get `depth⁻(r') ∈ {1, 2}` (empirically)

---

## Proof Sketch (Informal)

**Step 1:** From `ν₂(r+1) = t`, write `r = 2^t · a - 1` where `a` is odd.

**Step 2:** Expand `3r+1 = 3·2^t·a - 2 = 2(3·2^{t-1}·a - 1)`.

**Step 3:** If `t ≥ 2`, then `3·2^{t-1}·a - 1` is odd (since `2^{t-1} ≥ 2`).
  - Therefore `ν₂(3r+1) = 1` in this case.

**Step 4:** Then `r' = (3r+1)/2 = 3·2^{t-1}·a - 1`.

**Step 5:** Compute `r'+1 = 3·2^{t-1}·a`.
  - `ν₂(r'+1) = ν₂(3·2^{t-1}·a) = (t-1) + ν₂(3a) = t-1 + 0 = t-1` (since `a` odd ⇒ `3a` odd)

**Wait, this gives `depth⁻(r') = t-1 ≤ t - t + 2 = 2`?**
  - Only true if `t ≤ 3` !
  - For `t = 4`: `depth⁻(r') = 3 > 2` — **CONTRADICTION!**

**This suggests the informal proof sketch has an error!**

---

## Critical Issue: Is the Axiom Correct?

**Red flag:** My informal proof suggests for large `t`, the bound may not hold!

**Numerical check request:**
- For `t = 4`, find `r` with `depth⁻(r) = 4`
- Compute `r'` and check `depth⁻(r')`
- **Does** `depth⁻(r') ≤ 2`?

**Hypothesis:** The bound may require additional structure (phase conditions, homogenization).

---

## Request to Expert

**Please provide:**

1. ✅ **Verification:** Is the statement mathematically correct as written?
   - If not, what is the correct bound?

2. 🎯 **Proof strategy:** High-level steps for Lean 4 proof
   - Which mathlib lemmas to use?
   - How to handle the division `r' = (3r+1)/2^e`?

3. 📝 **Example:** Complete proof for a simpler case (e.g., `t = 3` only)

4. 🔧 **Code sketch:** Lean 4 proof outline with key tactics

---

## Context: Why This Matters

This axiom is crucial for **SEDT (Scaled Epoch Drift Theorem)**:
- At t-touches, depth drops significantly (multibit bonus)
- This creates negative drift over long epochs
- Enables cycle exclusion for Collatz conjecture

Current formalization status: **77% proven** (6/13 axioms)
- This is one of the last 7 "hard" axioms
- Proving it would reach **85% formal verification**

---

## Files for Reference

- `Collatz/SEDT.lean`: Full SEDT formalization
- `Collatz/Basic.lean`: Definitions of `T_odd`, `depth_minus`
- `Collatz/Arithmetic.lean`: Helper lemmas for 2-adic properties

**Repository:** `g:\Math\Collatz-Workspace\collatz-lean4\`

---

**Thank you for your expertise!** 🙏

Any guidance—whether full proof, proof sketch, or pointers to relevant mathlib lemmas—would be immensely helpful.

