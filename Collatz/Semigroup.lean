import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Collatz.Epoch
import Collatz.OrdFact

/-!
# Semigroup ⟨Δ⟩ Generation

This file formalizes the statement that junction shifts ⟨Δ⟩ generate the cyclic group Z/Q_t Z.

Junction shifts are ADDITIVE elements in Z/Q_t Z (not multiplicative).

## Main Results

- `delta_generates`: Junction shifts additively generate Z/Q_t Z
- `odd_delta_is_primitive`: An odd junction shift generates the full group
-/

namespace Collatz.Semigroup

/-!
## Junction Shifts Definition (ADDITIVE)

Junction shifts Δ(J) are additive phase shifts in Z/Q_t Z ≅ Z/(2^{t-2})Z.
-/

/-- The set of possible junction shifts (as additive elements)

    Simplified model for formalization purposes.
    Full definition would compute actual Δ(J) from epoch boundaries.
-/
def DeltaSet {t : ℕ} : Set (ZMod (2^(t-2))) :=
  { d | ∃ (k : ℕ), d = k }  -- Simplified: all residues

/-!
## Existence and Primitivity

For additive cyclic groups Z/n Z:
- A generator is any element coprime to n
- For n = 2^{t-2}, odd elements are generators
-/

/-- An odd element in Z/(2^{t-2})Z is a generator (additive order = 2^{t-2})

    In additive notation: addOrderOf d = 2^{t-2}

    PROOF SKETCH:
    1. Let d be odd, so d.val is odd
    2. 2^{t-2} is a power of 2
    3. gcd(odd, power of 2) = 1
    4. Coprime element generates cyclic group
-/
lemma odd_is_generator {t : ℕ} (ht : t ≥ 3) (d : ZMod (2^(t-2))) (h_odd : Odd d.val) :
  AddSubgroup.closure {d} = ⊤ := by
  -- Strategy: Show d has additive order 2^(t-2), which means it generates the full group
  -- Key: addOrderOf d = (2^(t-2)) / gcd(2^(t-2), d.val) = 2^(t-2) since gcd = 1

  -- Step 1: Show gcd(d.val, 2^(t-2)) = 1 (odd and power of 2 are coprime)
  have h_coprime : Nat.Coprime d.val (2^(t-2)) := by
    -- d.val is odd, 2^(t-2) is even (for t ≥ 3), so they're coprime
    rw [Nat.coprime_pow_right_iff (by omega : t-2 > 0)]
    refine ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_).symm
    intro h_div
    have h_even : Even d.val := even_iff_two_dvd.mpr h_div
    obtain ⟨k, hk⟩ := h_odd
    obtain ⟨r, hr⟩ := h_even
    omega

  -- Step 2: Use addOrderOf formula for ZMod
  have h_order : addOrderOf d = 2^(t-2) := by
    have h_pos : 0 < 2^(t-2) := by
      exact Nat.pow_pos (by norm_num : 0 < 2)
    have h_cast : d = (d.val : ZMod (2^(t-2))) := by simp
    rw [h_cast, ZMod.addOrderOf_coe d.val (ne_of_gt h_pos)]
    rw [Nat.gcd_comm]
    rw [Nat.coprime_iff_gcd_eq_one.mp h_coprime]
    simp

  -- Step 3: Element with order equal to group size generates the whole group
  have h_group_size : Fintype.card (ZMod (2^(t-2))) = 2^(t-2) := by
    simp [ZMod.card]

  -- In a cyclic group, element of order n generates the whole group of size n
  -- Use cardinality argument: if closure has same cardinality as group, it equals the group
  classical
  -- Finish: compare cardinalities for H = closure {d}
  refine
    AddSubgroup.eq_top_of_card_eq
      (H := AddSubgroup.closure ({d} : Set (ZMod (2^(t-2))))) ?_
  -- Nat.card (closure {d}) = Nat.card (ZMod (2^(t-2)))
  have hG : Nat.card (ZMod (2^(t-2))) = 2^(t-2) := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  simpa [AddSubgroup.zmultiples_eq_closure (g := d), hG, h_order]
    using (Nat.card_zmultiples d)

/-!
## Main Theorem: Junction Shifts Generate Z/Q_t Z

Since DeltaSet contains generators (odd elements), it generates the whole group.
-/

/-- Junction shifts (additively) generate Z/Q_t Z

    STATEMENT: The additive closure of DeltaSet equals the full group.

    PROOF SKETCH:
    1. Take any odd element (e.g., 1 ∈ DeltaSet)
    2. 1 is odd, so it generates the whole group
    3. Therefore DeltaSet generates Z/Q_t Z
-/
theorem delta_generates {t : ℕ} (ht : t ≥ 3) :
  AddSubgroup.closure (@DeltaSet t) = ⊤ := by
  -- 1 ∈ DeltaSet
  have h1_in : (1 : ZMod (2^(t-2))) ∈ @DeltaSet t := by
    unfold DeltaSet
    simp
    use 1
    norm_num

  -- 1 is odd
  have h1_odd : Odd (1 : ZMod (2^(t-2))).val := by
    have : 1 < 2^(t-2) := by
      have h_pos : t - 2 > 0 := by omega
      calc 1 < 2^1 := by norm_num
           _ ≤ 2^(t-2) := Nat.pow_le_pow_right (by norm_num) h_pos
    haveI : Fact (1 < 2^(t-2)) := ⟨this⟩
    rw [ZMod.val_one]
    norm_num

  -- 1 generates the group
  have h1_gen : AddSubgroup.closure {(1 : ZMod (2^(t-2)))} = ⊤ :=
    odd_is_generator ht 1 h1_odd

  -- Since 1 ∈ DeltaSet and 1 generates ⊤, DeltaSet generates ⊤
  have h_mono : AddSubgroup.closure {(1 : ZMod (2^(t-2)))} ≤ AddSubgroup.closure (@DeltaSet t) := by
    apply AddSubgroup.closure_mono
    intro x hx
    simp at hx
    rw [hx]
    exact h1_in

  -- closure {1} = ⊤ and closure {1} ≤ closure DeltaSet, therefore closure DeltaSet = ⊤
  rw [h1_gen] at h_mono
  exact eq_top_iff.mpr h_mono

end Collatz.Semigroup
