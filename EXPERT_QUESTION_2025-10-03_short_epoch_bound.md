# Expert Question: Proving `short_epoch_potential_bounded` Lemma

**Date:** 2025-10-03  
**Context:** Collatz SEDT formalization in Lean 4  
**Goal:** Replace axiom with proven lemma

---

## 🎯 Problem Statement

We're trying to prove that **short epochs** (length L < L₀) have bounded potential change:

```lean
lemma short_epoch_potential_bounded (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hβ : β ≥ 1) (h_short : e.length < L₀ t U) :
  ∃ (ΔV : ℝ), abs ΔV ≤ β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ)
```

**Where:**
- `L₀(t,U) = max(2^{t-2}, 10)` — threshold for "long" epochs
- `C(t,U) = 2·2^t + 3t + 3U` — overhead constant
- Each Collatz step contributes at most `log₂(3/2) + 2β` to potential

---

## 📐 Current Proof Strategy

### Step 1: Bound per-step contribution
For each step, we have:
```
ΔV_step ≤ log₂(3/2) + 2β
```
(from `single_step_potential_bounded` axiom)

### Step 2: Sum over short epoch
For epoch of length L < L₀:
```
total_ΔV ≤ L × (log₂(3/2) + 2β)
        < L₀ × (log₂(3/2) + 2β)
```

### Step 3: Simplify using log₂(3/2) < 1
```
L₀ × (log₂(3/2) + 2β) ≤ L₀ × (1 + 2β)
                       ≤ L₀ × (3β)    (since β ≥ 1)
```

### Step 4: Expand L₀ bound
Since `L₀ = max(2^{t-2}, 10) ≤ 2^{t-2} + 10`:
```
L₀ × (3β) ≤ (2^{t-2} + 10) × (3β)
         = 2^{t-2} × (3β) + 30β
```

### Step 5: Simplify using 2^{t-2} × 4 = 2^t
We can write:
```
2^{t-2} × (3β) ≤ 2^{t-2} × (4β) = 2^t × β
```

So:
```
L₀ × (3β) ≤ 2^t × β + 30β
```

---

## ⚠️ THE PROBLEM

**We need to show:**
```
2^t × β + 30β ≤ β × (2·2^t + 3t + 3U) + 2·2^{t-2}
```

**Simplifying the RHS:**
```
β × (2·2^t + 3t + 3U) + 2·2^{t-2} = 2β·2^t + β·(3t + 3U) + 2·2^{t-2}
```

**So we need:**
```
β·2^t + 30β ≤ 2β·2^t + β·(3t + 3U) + 2·2^{t-2}
```

**Rearranging:**
```
30β ≤ β·2^t + β·(3t + 3U) + 2·2^{t-2}
```

**Problem:** For small `t` (e.g., t=3) or large `β` (e.g., β=10), the term `30β` can be larger than `2·2^{t-2}` (which is only 4 when t=3).

---

## 🤔 Questions for the Expert

### Q1. Is the bound correct?
Is the statement `abs(ΔV) ≤ β·C(t,U) + 2·2^{t-2}` mathematically correct for **all** t ≥ 3, U ≥ 1, β ≥ 1?

Or should we:
- **Option A:** Add stronger constraints (e.g., U ≥ 10, or β ≤ some function of t)?
- **Option B:** Use a looser bound (e.g., `β·C(t,U) + β·K` for some constant K)?
- **Option C:** The bound is correct but the proof path is wrong?

### Q2. Alternative proof strategies?
If the bound is correct, what's the cleanest way to prove the final inequality?

**Some ideas:**
1. **Case split** on t (t=3,4,5 explicitly, then t≥6 by induction)?
2. **Use that U ≥ 1** to absorb the `30β` term into `β·3U`?
3. **Weaker intermediate bounds** that are easier to prove?

### Q3. Mathematical context
In the paper, is there a specific lemma or inequality that establishes this bound? 

I'm working from:
- **Appendix A.E4** (SEDT envelope)
- **Appendix B** (cycle exclusion via epoch density)

But I couldn't find an explicit statement about short epoch bounds beyond "they don't contribute to cycle exclusion".

---

## 📊 Numerical Check

Let me verify the inequality for small cases:

**Case t=3, U=1, β=1:**
- LHS: `30β = 30`
- RHS: `β·2^3 + β·(3·3 + 3·1) + 2·2^{3-2} = 8 + 12 + 4 = 24`
- **FAIL:** 30 > 24 ❌

**Case t=3, U=10, β=1:**
- LHS: `30β = 30`
- RHS: `β·2^3 + β·(3·3 + 3·10) + 2·2^1 = 8 + 39 + 4 = 51`
- **PASS:** 30 ≤ 51 ✓

**Case t=5, U=1, β=1:**
- LHS: `30β = 30`
- RHS: `β·2^5 + β·(3·5 + 3·1) + 2·2^{5-2} = 32 + 18 + 16 = 66`
- **PASS:** 30 ≤ 66 ✓

**Conclusion:** The inequality **fails for (t=3, U=1, β≥2)** but works for larger t or U.

---

## 💡 Proposed Solutions

### Solution A: Add constraint U ≥ 10
```lean
lemma short_epoch_potential_bounded (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 10) (hβ : β ≥ 1) (h_short : e.length < L₀ t U) :
  ∃ (ΔV : ℝ), abs ΔV ≤ β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ)
```

**Proof:** Then `β·3U ≥ 3β·10 = 30β`, so the `30β` term is absorbed.

### Solution B: Weaken the bound
```lean
lemma short_epoch_potential_bounded (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hβ : β ≥ 1) (h_short : e.length < L₀ t U) :
  ∃ (ΔV : ℝ), abs ΔV ≤ β * (C t U : ℝ) + 30 * β
```

**Rationale:** The additive term should scale with β, not with 2^{t-2}.

### Solution C: Keep as axiom with SMT verification
Mark the final arithmetic step as an axiom and verify it numerically with Z3 for reasonable ranges of (t, U, β).

---

## 🔍 What We Need

**From the expert:**
1. **Correct statement** of the bound (with appropriate constraints)
2. **Hint or reference** to the paper section that justifies this bound
3. **Proof sketch** if the bound is correct but the proof path is wrong

**Optional:**
- Lean 4 code snippet if the proof is tricky
- Alternative formulation that's easier to formalize

---

## 📎 Related Code

**Current formalization (with one `sorry`):**
- File: `Collatz/SEDT.lean`
- Lines: 867-1006
- Status: All steps proven except final arithmetic inequality

**Constants:**
```lean
def L₀ (t U : ℕ) : ℕ := max (2^(t-2)) 10
def C (t U : ℕ) : ℕ := 2 * 2^t + 3 * t + 3 * U
def K_glue (t : ℕ) : ℕ := max (2 * 2^(t-2)) (3 * t)
```

**Available lemmas:**
- `single_step_potential_bounded` (axiom)
- `two_mul_le_two_pow` (proven: 2t ≤ 2^t for t≥3)
- `max_K_glue_le_pow_two` (proven: K_glue(t) ≤ 2^t for t≥4)

---

## 🙏 Thank You!

This is the last major piece needed to complete Task B in our aggressive 100% formalization plan. Any guidance would be greatly appreciated!

