/-
Exact depth identity along an odd orbit.

With `r_k := T^[k] m` (odd `m`), define the "uncapped multibit gain"

    multibit_gain_on_orbit m i j := ∑_{k ∈ [i, j)} (if e(r_k) ≥ 2 then depth₋(r_{k+1}) else 0).

Then (`cumulative_depth_identity`)

    depth₋(r_j) − depth₋(r_i) + (j − i) = multibit_gain_on_orbit m i j.

This is a true identity about the orbit (it follows from F3: `e(r) = 1 ⇔
depth₋(r) ≥ 2`, and then `depth₋(T r) = depth₋(r) − 1`). Here "touch" means a
step with `e(r_k) ≥ 2` (equivalently `depth₋(r_k) = 1`); it is *not* the paper's
`t`-touch `r ≡ s_t (mod 2^t)`.

The identity shows that bounding the depth change from above is the same as
bounding `multibit_gain_on_orbit` from above. No such upper bound is proved; the
former consumers (`DepthBookkeeping`, `AperiodicGainBridge`, the
`SelectedCarryDepthSemantics` chain) only repackaged that missing bound as a
hypothesis and were deleted.
-/

import Collatz.SEDT.OrbitBridge

namespace Collatz.SEDT.OrbitDepth

open Collatz.Foundations
open Collatz.SEDT.OrbitBridge
open Finset

/-- Indicator of `e(T^[k] m) ≥ 2` (Bool form). -/
def isTouch (m k : ℕ) : Bool :=
  decide (2 ≤ step_type ((collatz_step^[k]) m))

/-- `depth₋(r_{k+1})` if `e(r_k) ≥ 2`, else `0`. -/
def touchDepth (m k : ℕ) : ℕ :=
  if 2 ≤ step_type ((collatz_step^[k]) m)
    then depth_minus ((collatz_step^[k + 1]) m)
    else 0

/-- **Uncapped multibit gain on orbit.** Cumulative sum of
`touchDepth` over `[i, j)`. -/
def multibit_gain_on_orbit (m i j : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico i j, touchDepth m k

/-- **U-capped multibit gain on orbit.** Cumulative sum of the
U-clipped touch depth over `[i, j)`. -/
def multibit_gain_on_orbit_capped (m U i j : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico i j,
    (if 2 ≤ step_type ((collatz_step^[k]) m)
      then min (depth_minus ((collatz_step^[k + 1]) m)) U
      else 0)

/-- **Capped ≤ uncapped.** Each summand of the capped variant is at
most the corresponding uncapped summand. -/
theorem multibit_gain_on_orbit_capped_le
    (m U i j : ℕ) :
    multibit_gain_on_orbit_capped m U i j ≤ multibit_gain_on_orbit m i j := by
  refine Finset.sum_le_sum ?_
  intro k _
  by_cases h : 2 ≤ step_type ((collatz_step^[k]) m)
  · simp [touchDepth, h, Nat.min_le_left]
  · simp [touchDepth, h]

/-- **Cumulative depth identity (orbit-side).**

For odd `m` and any `i ≤ j`,

    `(depth_minus r_j : ℤ) − depth_minus r_i + (j − i)`
        `= multibit_gain_on_orbit m i j`,

where `r_k = (collatz_step^[k]) m`. The proof inducts on `j` with
`i` fixed, using the per-step depth identities from `OrbitBridge`:

* **non-touch step** (`step_type r_k = 1`): `depth_minus r_{k+1} =
  depth_minus r_k − 1`, contribution `+1` from `j − i` and `−1` from
  the depth diff cancel; the touch indicator is `0`.

* **touch step** (`step_type r_k ≥ 2`): `depth_minus r_k = 1`, the
  depth diff increment is `depth_minus r_{k+1} − 1`, plus `+1` from
  `j − i` gives `depth_minus r_{k+1}`, exactly the touch contribution.
-/
theorem cumulative_depth_identity
    (m : ℕ) (hm : Odd m) (i j : ℕ) (hij : i ≤ j) :
    ((depth_minus ((collatz_step^[j]) m) : ℤ) -
        (depth_minus ((collatz_step^[i]) m) : ℤ)) +
        ((j - i : ℕ) : ℤ) =
      ((multibit_gain_on_orbit m i j : ℕ) : ℤ) := by
  induction j, hij using Nat.le_induction with
  | base =>
      simp [multibit_gain_on_orbit]
  | succ j hij' ih =>
      -- Inductive step: prove for j+1 from j.
      have hri_odd : Odd ((collatz_step^[j]) m) :=
        odd_iterates_of_odd hm j
      have hsucc_iter : (collatz_step^[j + 1]) m =
          collatz_step ((collatz_step^[j]) m) := by
        rw [Function.iterate_succ_apply']
      -- Split on step type at j.
      by_cases htouch : 2 ≤ step_type ((collatz_step^[j]) m)
      · -- Touch step: depth_minus r_j = 1.
        have hdj : depth_minus ((collatz_step^[j]) m) = 1 :=
          depth_minus_eq_one_of_step_type_ge_two _ hri_odd htouch
        -- Expand multibit_gain over Ico i (j+1) = Ico i j ∪ {j}.
        have hsplit :
            multibit_gain_on_orbit m i (j + 1)
              = multibit_gain_on_orbit m i j + touchDepth m j := by
          unfold multibit_gain_on_orbit
          rw [Finset.sum_Ico_succ_top hij', add_comm]
        have htd : touchDepth m j = depth_minus ((collatz_step^[j + 1]) m) := by
          simp [touchDepth, htouch]
        -- ih has the identity at index j; add increments and conclude.
        have hjsub : ((j + 1 - i : ℕ) : ℤ) = ((j - i : ℕ) : ℤ) + 1 := by
          have : j + 1 - i = (j - i) + 1 := by omega
          rw [this]; push_cast; ring
        rw [hsucc_iter] at *
        rw [hsplit, htd]
        push_cast
        rw [hjsub]
        have hdj' : ((depth_minus ((collatz_step^[j]) m) : ℕ) : ℤ) = 1 := by
          rw [hdj]; norm_num
        linarith [ih]
      · -- Non-touch step: step_type = 1, so depth_minus r_{j+1} = depth_minus r_j - 1.
        have hsone : step_type ((collatz_step^[j]) m) = 1 := by
          have hpos : 1 ≤ step_type ((collatz_step^[j]) m) :=
            step_type_odd_pos hri_odd
          omega
        have hdec :
            depth_minus (collatz_step ((collatz_step^[j]) m)) + 1
              = depth_minus ((collatz_step^[j]) m) :=
          depth_minus_collatz_step_of_step_type_one _ hri_odd hsone
        -- multibit_gain over Ico i (j+1) = multibit_gain over Ico i j (since j is non-touch).
        have hsplit :
            multibit_gain_on_orbit m i (j + 1)
              = multibit_gain_on_orbit m i j + touchDepth m j := by
          unfold multibit_gain_on_orbit
          rw [Finset.sum_Ico_succ_top hij', add_comm]
        have htd : touchDepth m j = 0 := by
          simp [touchDepth, htouch]
        have hjsub : ((j + 1 - i : ℕ) : ℤ) = ((j - i : ℕ) : ℤ) + 1 := by
          have : j + 1 - i = (j - i) + 1 := by omega
          rw [this]; push_cast; ring
        rw [hsucc_iter] at *
        rw [hsplit, htd]
        push_cast
        rw [hjsub]
        have hdec' :
            ((depth_minus (collatz_step ((collatz_step^[j]) m)) : ℕ) : ℤ) + 1
              = ((depth_minus ((collatz_step^[j]) m) : ℕ) : ℤ) := by
          have := hdec
          push_cast
          push_cast at this
          linarith
        linarith [ih]

end Collatz.SEDT.OrbitDepth
