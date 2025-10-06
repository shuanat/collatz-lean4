# Expert Solutions for Remaining Lemmas

**Date:** 2025-10-01  
**Source:** Lean/mathlib4 expert consultation  
**Status:** ✅ Complete solutions received

---

## Summary of Solutions

| Lemma | Approach | Key mathlib4 Lemmas | Complexity |
|-------|----------|---------------------|------------|
| `odd_is_generator` | Coprimality → Order = Group Size | `ZMod.addOrderOf_coe`, `Nat.coprime_pow_right_iff` | Medium |
| `pow_lift_double` | Divisibility via factorization | `Nat.ModEq`, divisibility lemmas | Medium |
| `three_pow_two_pow_sub_one_valuation` | 2-adic valuation (LTE) | `padicValNat_pow_sub_pow_of_even` | Low (using LTE) |

---

## Solution 1: `odd_is_generator`

### Mathematical Insight

**Key Fact:** In cyclic additive group `ZMod n`, element `d` generates the whole group iff `gcd(d.val, n) = 1`.

**Formula:** `addOrderOf((a : ZMod n)) = n / gcd(n, a)`

### Proof Strategy

1. **Oddness → Coprimality:** 
   - `Odd d.val` means `2 ∤ d.val`
   - Use `Nat.coprime_pow_right_iff`: `gcd(d.val, 2^(t-2)) = 1 ⟺ gcd(d.val, 2) = 1`
   - Since `2 ∤ d.val`, we have `gcd(d.val, 2) = 1` (by `Nat.Prime.coprime_iff_not_dvd`)

2. **Coprimality → Generator:**
   - By `ZMod.addOrderOf_coe`: `addOrderOf(d) = 2^(t-2) / gcd(2^(t-2), d.val) = 2^(t-2)` (since gcd = 1)
   - Element of order `n` in group of size `n` generates the whole group
   - Use Bézout: `x*d.val + y*2^(t-2) = 1` implies `x•d = 1` in `ZMod (2^(t-2))`
   - Since `1` generates the group, `AddSubgroup.closure {d} = ⊤`

### Lean Code Sketch

```lean
import Mathlib.Data.ZMod.Basic  -- for ZMod.addOrderOf_coe
import Mathlib.Data.Nat.GCD.Basic  -- for Nat.coprime_pow_right_iff

lemma odd_is_generator {t : ℕ} (ht : t ≥ 3) (d : ZMod (2^(t-2))) (h_odd : Odd d.val) :
  AddSubgroup.closure {d} = ⊤ := by
  have co : Nat.Coprime d.val (2^(t-2)) := by
    -- Odd implies coprime with 2^(t-2)
    rw [Nat.coprime_pow_right_iff (t-2) (by linarith)] 
    exact Nat.prime_two.coprime_iff_not_dvd.2 (Odd.not_even h_odd)
  
  -- Now use additive order formula: order(d) = 2^(t-2) since gcd = 1
  have order_full := ZMod.addOrderOf_coe' (2^(t-2)) (d.val) (Nat.pos_of_ne_zero two_pow_ne_zero)
  rw [Nat.gcd_comm] at order_full  -- put gcd in standard order
  rw [←Nat.gcd_eq_one_iff_coprime] at co
  rw [co] at order_full 
  
  -- order_full : addOrderOf d = 2^(t-2)
  -- In a finite cyclic group, an element of order equal to the group order generates the group:
  apply AddSubgroup.eq_top_of_subgroup_of_addOrderOf_eq _
  exact order_full.symm
```

**Note:** May need helper lemma `AddSubgroup.eq_top_of_subgroup_of_addOrderOf_eq`.

---

## Solution 2: `pow_lift_double`

### Mathematical Insight

**Hensel Lifting:** If `a^k ≡ 1 (mod 2^t)` and `a` is odd, then `a^(2k) ≡ 1 (mod 2^(t+1))`.

**Proof:** 
- `2^t | (a^k - 1)` from hypothesis
- `a` odd → `a^k` odd → `a^k + 1` even → `2 | (a^k + 1)`
- `a^(2k) - 1 = (a^k - 1)(a^k + 1)`
- Therefore: `2^(t+1) = 2^t · 2 | (a^k - 1)(a^k + 1) = a^(2k) - 1`

### Proof Strategy (Divisibility Approach)

**Recommended:** Use `Nat.ModEq` and divisibility, not `ZMod` residue analysis.

```lean
lemma pow_lift_double {a k t : ℕ} (ha : Odd a) (ht : t ≥ 1) (h : (a : ZMod (2^t))^k = 1) :
  (a : ZMod (2^(t+1)))^(2*k) = 1 := by
  -- Convert ZMod hypothesis to divisibility
  obtain ⟨m, hm⟩ : 2^t ∣ (a^k - 1) := Nat.ModEq.mp h  -- h : a^k ≡ 1 [MOD 2^t]
  
  -- a^k is odd (power of odd number)
  have : 2 ∣ (a^k + 1) := by 
    simp [←Nat.even_iff, Odd.pow ha k]  -- a^k is odd, so a^k+1 is even
  obtain ⟨m2, hm2⟩ : 2 ∣ (a^k + 1) := this
  
  -- Combine divisibilities
  have divis : 2^(t+1) ∣ (a^k - 1)*(a^k + 1) := 
    mul_dvd_mul hm hm2
  
  -- (a^k - 1)*(a^k + 1) = a^(2*k) - 1
  rw [← pow_mul, ← mul_comm] at divis
  
  -- Divisibility → congruence
  exact Nat.ModEq.of_dvd divis
```

**Alternative (if needed):** Use `ZMod.castHom` to relate `ZMod (2^(t+1))` and `ZMod (2^t)`, but divisibility approach is cleaner.

---

## Solution 3: `three_pow_two_pow_sub_one_valuation`

### Mathematical Insight

**Lifting-the-Exponent (LTE) for p=2:**

For odd `a` and even `m`:
$$\nu_2(a^m - 1) = \nu_2(a - 1) + \nu_2(a + 1) + \nu_2(m) - 1$$

For `a = 3`, `m = 2^k`:
- `ν_2(3 - 1) = ν_2(2) = 1`
- `ν_2(3 + 1) = ν_2(4) = 2`
- `ν_2(2^k) = k`
- Therefore: `ν_2(3^(2^k) - 1) = 1 + 2 + k - 1 = k + 2`

**This exactly means:**
- `2^(k+2) ∣ (3^(2^k) - 1)` ✓
- `2^(k+3) ∤ (3^(2^k) - 1)` ✓

### Proof Strategy (Using mathlib4 LTE)

**Best approach:** Use `padicValNat_pow_sub_pow_of_even` from `Mathlib.NumberTheory.Multiplicity`.

```lean
import Mathlib.NumberTheory.Multiplicity

lemma three_pow_two_pow_sub_one_valuation (k : ℕ) :
  (3 : ℤ)^(2^k) ≡ 1 [ZMOD 2^(k+2)] ∧ ¬((3 : ℤ)^(2^k) ≡ 1 [ZMOD 2^(k+3)]) := by
  -- Use LTE lemma
  have val := padicValNat_pow_sub_pow_of_even (x := 3) (y := 1) (n := 2^k) (by simp) 
  -- This gives: padicValNat 2 (3^(2^k) - 1) = k + 2
  
  rw [padicValNat.two_pow (by decide)] at val  -- simplify padicValNat 2 (2^k)
  -- Now val : padicValNat 2 (3^(2^k) - 1) = k + 2
  
  -- Valuation = k+2 means: 2^(k+2) divides, 2^(k+3) does not
  constructor
  · -- First part: 2^(k+2) ∣ (3^(2^k) - 1)
    exact padicValNat.dvd_iff.mpr (by rw [val]; exact Nat.le_refl _)
  · -- Second part: 2^(k+3) ∤ (3^(2^k) - 1)
    intro h
    have : padicValNat 2 (3^(2^k) - 1) ≥ k+3 := padicValNat.dvd_iff.mp h
    rw [val] at this
    omega  -- contradiction: k+2 ≥ k+3
```

### Alternative: Inductive Proof (if LTE not available)

**Base case (k=1):** `3^2 = 9 ≡ 1 (mod 8)` but not `(mod 16)` — prove by `decide`.

**Inductive step:**
- Assume `ν_2(3^(2^k) - 1) = k+2`
- Show `ν_2(3^(2^(k+1)) - 1) = k+3`
- Use: `3^(2^(k+1)) - 1 = (3^(2^k) - 1)(3^(2^k) + 1)`
- `ν_2(3^(2^k) - 1) = k+2` (IH)
- `ν_2(3^(2^k) + 1) = 1` (since `3^(2^k) ≡ 1 (mod 4)` → `3^(2^k) + 1 ≡ 2 (mod 4)`)
- Therefore: `ν_2(3^(2^(k+1)) - 1) = (k+2) + 1 = k+3` ✓

---

## Implementation Plan

### Phase 1: `odd_is_generator` (Est. 1-1.5h)

1. Add imports: `Mathlib.Data.ZMod.Basic`, `Mathlib.Data.Nat.GCD.Basic`
2. Prove coprimality using `Nat.coprime_pow_right_iff`
3. Apply `ZMod.addOrderOf_coe'` to get order formula
4. Show order = group size → generates whole group
5. **Potential issue:** May need to find/prove helper lemma for "order = size → generator"

### Phase 2: `pow_lift_double` (Est. 1-1.5h)

1. Use divisibility approach (cleaner than ZMod residues)
2. Convert ZMod hypothesis to `Nat.ModEq` / divisibility
3. Show `a^k` odd → `a^k + 1` even using `Odd.pow`
4. Use `mul_dvd_mul` to combine divisibilities
5. Apply algebraic identity `(a^k - 1)(a^k + 1) = a^(2k) - 1`
6. Convert back to `Nat.ModEq` or `ZMod` using `Nat.ModEq.of_dvd`

### Phase 3: `three_pow_two_pow_sub_one_valuation` (Est. 0.5-1h)

1. Add import: `Mathlib.NumberTheory.Multiplicity`
2. Apply `padicValNat_pow_sub_pow_of_even` for `x=3, y=1, n=2^k`
3. This directly gives `padicValNat 2 (3^(2^k) - 1) = k+2`
4. Convert valuation to divisibility statements using `padicValNat.dvd_iff`
5. **Fallback:** If LTE lemma issues, use induction (base cases work with `decide`)

### Total Estimated Time: 3-4 hours

---

## Key mathlib4 Lemmas Reference

### For `odd_is_generator`:
- `ZMod.addOrderOf_coe'` : `addOrderOf((a : ZMod n)) = n / gcd(n, a)`
- `Nat.coprime_pow_right_iff` : `gcd(a, b^k) = 1 ⟺ gcd(a, b) = 1`
- `Nat.Prime.coprime_iff_not_dvd` : For prime `p`, `gcd(a, p) = 1 ⟺ ¬(p | a)`
- `Nat.gcd_eq_one_iff_coprime` : `gcd(a, b) = 1 ⟺ Coprime a b`

### For `pow_lift_double`:
- `Nat.ModEq.mp` : Convert `ZMod` equality to `Nat.ModEq`
- `Nat.ModEq.of_dvd` : Convert divisibility to `Nat.ModEq`
- `Odd.pow` : `Odd a → Odd (a^k)`
- `mul_dvd_mul` : `a | b → c | d → a*c | b*d`

### For `three_pow_two_pow_sub_one_valuation`:
- `padicValNat_pow_sub_pow_of_even` : LTE for even exponents
  ```lean
  padicValNat 2 (x^n - y^n) + 1 = padicValNat 2 (x + y) + padicValNat 2 (x - y) + padicValNat 2 n
  ```
- `padicValNat.dvd_iff` : Connect valuation to divisibility
- `padicValNat.two_pow` : Simplify `padicValNat 2 (2^k)`

---

## Success Criteria

### After implementing these 3 solutions:

**Sorry count reduction:**
- `Semigroup.lean`: 1 → 0 sorry ✅
- `Arithmetic.lean`: 3 → 0 sorry ✅ (assuming `one_plus_pow_two_sq` follows from `pow_lift_double`)
- `OrdFact.lean`: 3 → 1 sorry (main theorem solvable after helpers)

**Total progress:** 8 → 3-4 sorry (50-62.5% reduction!)

**Remaining work:**
- `SEDT.lean`: 3 sorry (main theorem + corollaries) — PhD-level, can defer
- `OrdFact.lean`: 1 sorry (minimality proof) — may need circular dependency resolution

---

## Next Steps

1. ✅ **Start with `three_pow_two_pow_sub_one_valuation`** (easiest, LTE one-liner)
2. ✅ **Then `pow_lift_double`** (divisibility approach is clean)
3. ✅ **Finally `odd_is_generator`** (may need helper lemma hunting)

**Priority:** Get these 3 working → will unlock most of the formalization!

---

**Acknowledgment:** Huge thanks to the Lean/mathlib4 expert for these detailed solutions with specific lemma references! 🙏

