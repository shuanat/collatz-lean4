# Period Sum Formalization Plan - MAIN THEOREM

**Дата:** 3 октября 2025 (22:00 UTC)  
**Цель:** Формализовать `period_sum_with_density_negative` - KEY theorem для cycle exclusion  
**Статус:** 🎯 НАЧИНАЕМ ГЛАВНУЮ ЗАДАЧУ!

---

## 🎯 ЦЕЛЬ

Доказать:
```lean
theorem period_sum_with_density_negative (t U : ℕ) (epochs : List SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β > β₀ t U)
  (h_many_long : (epochs.filter (fun e => e.length ≥ L₀ t U)).length ≥
                  epochs.length / (2^(t-2) + 8*t*(2^t))) :
  ∃ (total_ΔV : ℝ), total_ΔV < 0
```

**Значение:** Если density long epochs достаточно высока → Σ ΔV < 0 → **NO CYCLES!** 🏆

---

## 📊 MATHEMATICAL STRATEGY

### High-Level Argument (from paper Appendix B):

1. **Split epochs:** long (L ≥ L₀) vs short (L < L₀)
2. **Long contribution:** Each long epoch has ΔV ≤ -ε·L + β·C
   - For L ≥ L_crit: -ε·L dominates, so ΔV < 0
   - But L₀ might be < L_crit, so we need density argument
3. **Short contribution:** Each short epoch has |ΔV| ≤ β·C + overhead
4. **Density key:** If #long / #total ≥ threshold, long negativity wins!

### Detailed Proof Steps:

**Step 1: Partition epochs**
```
epochs = long_epochs ++ short_epochs
where:
  long_epochs = epochs.filter (fun e => e.length ≥ L₀)
  short_epochs = epochs.filter (fun e => e.length < L₀)
```

**Step 2: Bound long contribution**
```
For each e ∈ long_epochs:
  ΔV_e ≤ -ε·e.length + β·C  (by sedt_envelope_bound ✅)

Sum over long:
  Σ_long ΔV ≤ -ε·Σ L_long + n_long·β·C
```

**Step 3: Bound short contribution**
```
For each e ∈ short_epochs:
  |ΔV_e| ≤ β·C + overhead  (by short_epoch_potential_bounded ✅)

Worst case (all positive):
  Σ_short ΔV ≤ n_short·(β·C + overhead)
```

**Step 4: Use density hypothesis**
```
Given: n_long / n_total ≥ 1/(Q_t + G_t)
where Q_t = 2^{t-2}, G_t = 8t·2^t

Key insight: 
  If density ≥ threshold, then:
  ε·Σ L_long > n_short·(β·C + overhead) + n_long·β·C
```

**Step 5: Combine**
```
Total ΔV = Σ_long + Σ_short
         ≤ (-ε·Σ L_long + n_long·β·C) + n_short·(β·C + overhead)
         = -ε·Σ L_long + (n_long + n_short)·β·C + n_short·overhead
         < 0  (by density argument!)
```

---

## 🛠️ IMPLEMENTATION PLAN

### Phase 1: Helper Lemmas (Foundation)

#### Lemma 1.1: List partition properties
```lean
lemma list_partition_sum {α : Type} (l : List α) (p : α → Bool) (f : α → ℝ) :
  (l.map f).sum = ((l.filter p).map f).sum + ((l.filter (fun x => !p x)).map f).sum
```

#### Lemma 1.2: Long epoch total length
```lean
lemma long_epochs_total_length (epochs : List SEDTEpoch) (L₀ : ℕ) :
  let long := epochs.filter (fun e => e.length ≥ L₀)
  ∃ (total_L : ℕ), total_L = (long.map SEDTEpoch.length).sum
```

#### Lemma 1.3: Density to count conversion
```lean
lemma density_to_count_bound (n_long n_total : ℕ) (threshold : ℝ)
  (h_density : (n_long : ℝ) ≥ (n_total : ℝ) * threshold) :
  -- useful bounds on n_long, n_short
```

---

### Phase 2: Epoch Contribution Bounds

#### Lemma 2.1: Long epoch contribution bound
```lean
lemma long_epoch_contribution_bound (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β > β₀ t U) (hβ_ge_one : β ≥ 1)
  (h_long : e.length ≥ L₀ t U) :
  ∃ (ΔV : ℝ), ΔV ≤ -(ε t U β) * (e.length : ℝ) + β * (C t U : ℝ)
```
**Already have:** `sedt_envelope_bound` ✅

#### Lemma 2.2: Short epoch contribution bound  
```lean
lemma short_epoch_contribution_bound (t U : ℕ) (e : SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β ≥ 1)
  (h_short : e.length < L₀ t U) :
  ∃ (ΔV : ℝ), abs ΔV ≤ β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ)
```
**Already have:** `short_epoch_potential_bounded` ✅

---

### Phase 3: Sum over Epochs

#### Lemma 3.1: Sum of long contributions
```lean
lemma sum_long_contributions (t U : ℕ) (epochs : List SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β > β₀ t U) (hβ_ge_one : β ≥ 1) :
  let long := epochs.filter (fun e => e.length ≥ L₀ t U)
  let total_L := (long.map SEDTEpoch.length).sum
  ∃ (sum_long : ℝ), 
    sum_long ≤ -(ε t U β) * (total_L : ℝ) + (long.length : ℝ) * β * (C t U : ℝ)
```

#### Lemma 3.2: Sum of short contributions
```lean
lemma sum_short_contributions (t U : ℕ) (epochs : List SEDTEpoch) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β ≥ 1) :
  let short := epochs.filter (fun e => e.length < L₀ t U)
  ∃ (sum_short : ℝ),
    sum_short ≤ (short.length : ℝ) * (β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ))
```

---

### Phase 4: Density Argument (KEY!)

#### Lemma 4.1: Minimum length for long epochs
```lean
lemma long_epochs_min_length (t U : ℕ) (epochs : List SEDTEpoch)
  (ht : t ≥ 3) (hU : U ≥ 1) :
  let long := epochs.filter (fun e => e.length ≥ L₀ t U)
  let total_L := (long.map SEDTEpoch.length).sum
  (total_L : ℝ) ≥ (long.length : ℝ) * (L₀ t U : ℝ)
```

#### Lemma 4.2: Density implies negativity (CORE LEMMA!)
```lean
lemma density_implies_negative_total (t U : ℕ) (n_long n_short : ℕ) 
  (total_L : ℕ) (β : ℝ)
  (ht : t ≥ 3) (hU : U ≥ 1) (hβ : β > β₀ t U) (hβ_ge_one : β ≥ 1)
  (h_density : (n_long : ℝ) ≥ ((n_long + n_short) : ℝ) / ((2^(t-2) : ℝ) + 8*(t : ℝ)*(2^t : ℝ)))
  (h_min_length : (total_L : ℝ) ≥ (n_long : ℝ) * (L₀ t U : ℝ)) :
  -(ε t U β) * (total_L : ℝ) + (n_long : ℝ) * β * (C t U : ℝ) 
    + (n_short : ℝ) * (β * (C t U : ℝ) + 2 * (2^(t-2) : ℝ)) < 0
```

**This is the KEY technical lemma!** Requires careful arithmetic with ε, β, C, L₀.

---

### Phase 5: Main Theorem Assembly

#### Final proof structure:
```lean
theorem period_sum_with_density_negative ... := by
  -- Step 1: Define long and short epochs
  let long := epochs.filter (fun e => e.length ≥ L₀ t U)
  let short := epochs.filter (fun e => e.length < L₀ t U)
  
  -- Step 2: Get bounds on long contributions
  have h_long_bound := sum_long_contributions t U epochs β ht hU hβ hβ_ge_one
  obtain ⟨sum_long, h_sum_long⟩ := h_long_bound
  
  -- Step 3: Get bounds on short contributions
  have h_short_bound := sum_short_contributions t U epochs β ht hU hβ_ge_one
  obtain ⟨sum_short, h_sum_short⟩ := h_short_bound
  
  -- Step 4: Total sum
  use sum_long + sum_short
  
  -- Step 5: Apply density argument (KEY!)
  have h_negative := density_implies_negative_total ...
  
  -- Step 6: Combine bounds
  calc sum_long + sum_short
      ≤ (... bound from long ...) + (... bound from short ...) := by ...
    _ < 0 := h_negative
```

---

## 📐 TECHNICAL CHALLENGES

### Challenge 1: List manipulation in Lean
**Issue:** Need to work with `List.filter`, `List.map`, `List.sum`

**Solution:**
- Use `List.sum_append` for partition
- Use `List.sum_map` for transformation
- Use `List.filter_append` for split

**Tactics:** `simp`, `rw`, `calc`

---

### Challenge 2: Real arithmetic with casts
**Issue:** `ℕ → ℝ` casts everywhere

**Solution:**
- Use `Nat.cast_*` lemmas
- `exact_mod_cast` tactic
- Explicit type annotations when needed

**Tactics:** `norm_cast`, `push_cast`, `exact_mod_cast`

---

### Challenge 3: Density inequality manipulation
**Issue:** Converting `n_long / n_total ≥ threshold` to useful form

**Solution:**
- Multiply both sides by n_total (positive)
- Rearrange to get `n_long ≥ threshold * n_total`
- Use with ε, C bounds

**Tactics:** `field_simp`, `mul_comm`, `linarith`

---

### Challenge 4: Combining multiple bounds
**Issue:** Many bounds to track and combine

**Solution:**
- Use `have` statements for intermediate results
- `calc` blocks for chaining
- `linarith` for final arithmetic

**Tactics:** `have`, `calc`, `linarith`, `omega`

---

## 🎯 ESTIMATED BREAKDOWN

| Phase | Description | Lemmas | Estimated Time |
|-------|-------------|--------|----------------|
| 1 | Helper lemmas (lists) | 3 | 1-2 hours |
| 2 | Epoch contribution bounds | 2 | 1 hour (mostly done ✅) |
| 3 | Sum over epochs | 2 | 2-3 hours |
| 4 | Density argument | 2 | 3-5 hours (KEY!) |
| 5 | Main theorem assembly | 1 | 2-3 hours |
| **Total** | | **10** | **10-14 hours** |

---

## 🚀 START STRATEGY

### Immediate (Session 3, ~3-4 hours):
1. ✅ Phase 1: Helper lemmas (list manipulation)
2. ✅ Phase 2: Verify we have contribution bounds
3. 🎯 Phase 3: Start sum_long_contributions

**Goal:** Get through Phases 1-2, start Phase 3

---

### This Week (~10 hours total):
1. ✅ Complete Phase 3 (sum over epochs)
2. 🎯 Start Phase 4 (density argument)
3. 🔧 Iterate on KEY technical lemma

**Goal:** Get density_implies_negative_total working

---

### Complete (total ~14 hours):
1. ✅ Finish Phase 4 (density argument)
2. ✅ Phase 5 (assembly)
3. 🎉 **MAIN THEOREM PROVEN!**

**Goal:** 🏆 **CYCLE EXCLUSION COMPLETE!**

---

## 📝 DEPENDENCIES CHECK

### Already Proven (we can use!):
- ✅ `sedt_envelope_bound` - long epoch bound
- ✅ `short_epoch_potential_bounded` - short epoch bound
- ✅ `epsilon_pos` - ε > 0
- ✅ `beta_zero_pos` - β₀ > 0
- ✅ `exists_very_long_epoch_threshold` - L_crit exists
- ✅ `two_mul_le_two_pow` - exponential growth
- ✅ `max_K_glue_le_pow_two` - K_glue bound

### Needed (will create):
- ⏳ List manipulation lemmas
- ⏳ Sum over epochs lemmas
- ⏳ Density argument lemmas (KEY!)

---

## 🎯 SUCCESS CRITERIA

### Minimum (working proof):
- ✅ Compiles without `sorry`
- ✅ Uses proven supporting lemmas
- ✅ Logical structure sound

### Target (high quality):
- ✅ All of minimum
- ✅ Clear proof structure
- ✅ Good documentation
- ✅ Efficient tactics

### Stretch (publication-ready):
- ✅ All of target
- ✅ Optimal proof organization
- ✅ Reusable helper lemmas
- ✅ Paper-compatible structure

**Aiming for:** **Target quality** (realistic for 10-14 hours)

---

## 📊 PROGRESS TRACKING

Will track in TODO:
- [ ] Phase 1: Helper lemmas
- [ ] Phase 2: Contribution bounds check
- [ ] Phase 3: Sum lemmas
- [ ] Phase 4: Density argument
- [ ] Phase 5: Main theorem

Updates after each phase completion!

---

## 🎊 MOTIVATION

**This is IT!** 🎯

Once we prove `period_sum_with_density_negative`:
- ✅ SEDT framework complete
- ✅ Cycle exclusion proven
- ✅ Main technical barrier overcome
- 🏆 **MAJOR MILESTONE FOR COLLATZ!**

**Let's do this!** 💪

---

**End of Plan - Ready to Implement!** 🚀

**Next:** Start Phase 1 (Helper Lemmas) immediately!

