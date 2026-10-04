/-
Base case `k = 0` of the auxiliary numerator, and per-step depth identities.

1. Base case. For the auxiliary sequence `N_k = 3^{k+1}(r₀+2) − 5·2^k`
   (`AffineNumerator`): `N_0 = 3r₀ + 1`, `d_0 = e(r₀)`, `M_0 = T(r₀)`. For
   `k ≥ 1`, `N_k` is **not** the orbit numerator: if `e(r_0) = … = e(r_{k−1}) = 1`
   the true identity is `2^k (3 r_k + 1) = 3^{k+1}(r₀ + 1) − 2^{k+1}`, while for
   odd `r₀` and `k ≥ 1` the number `N_k` is odd (so `d_k = 0`). Results about
   `N_k, d_k, M_k` for `k ≥ 1` therefore do not transfer to the orbit.

2. Per-step depth identities on the orbit (true, used by `OrbitDepth`): for odd
   `r`, `e(r) ≥ 2 ⇔ depth₋(r) = 1`, and if `e(r) = 1` then
   `depth₋(T r) + 1 = depth₋(r)`.
-/

import Collatz.SEDT.AffineNumerator
import Collatz.Foundations.Core

namespace Collatz.SEDT.OrbitBridge

open Collatz.SEDT.AffineNumerator
open Collatz.Foundations

/-- `N_0 = 3 r₀ + 1`. -/
theorem N_k_nat_zero (r₀ : ℕ) (hr : 1 ≤ r₀) :
    N_k_nat (r₀ : ℤ) 0 = 3 * r₀ + 1 := by
  have hrI : (1 : ℤ) ≤ (r₀ : ℤ) := by exact_mod_cast hr
  have hint : N_k_int (r₀ : ℤ) 0 = 3 * (r₀ : ℤ) + 1 := by
    unfold N_k_int; push_cast; ring
  have hcast : ((N_k_nat (r₀ : ℤ) 0 : ℕ) : ℤ) = 3 * (r₀ : ℤ) + 1 := by
    rw [N_k_nat_eq (r₀ : ℤ) hrI 0, hint]
  exact_mod_cast hcast

/-- `d_0 = e(r₀)`. -/
theorem d_k_zero (r₀ : ℕ) (hr : 1 ≤ r₀) :
    d_k (r₀ : ℤ) 0 = step_type r₀ := by
  unfold d_k step_type Collatz.Arithmetic.e
  rw [N_k_nat_zero r₀ hr]

/-- `M_0 = T(r₀)`. -/
theorem M_k_zero (r₀ : ℕ) (hr : 1 ≤ r₀) :
    M_k (r₀ : ℤ) 0 = collatz_step r₀ := by
  unfold M_k collatz_step
  rw [N_k_nat_zero r₀ hr, d_k_zero r₀ hr]

/-- For odd `r₀`, `d_0 = e(r₀) ≥ 1`. -/
theorem d_k_zero_pos_of_odd (r₀ : ℕ) (hr : OddPred r₀) :
    0 < d_k (r₀ : ℤ) 0 := by
  have hr1 : 1 ≤ r₀ := by
    rcases hr with ⟨m, hm⟩
    omega
  rw [d_k_zero r₀ hr1]
  exact step_type_odd_pos hr

/-! ## Per-step depth identities

For odd `r` with `s = depth₋(r) = ν₂(r + 1)`: if `s ≥ 2` then `e(r) = 1` and
`depth₋(T r) = s − 1`; if `s = 1` then `e(r) ≥ 2` and `depth₋(T r)` depends on
the residue of `r`. -/

/-- **Touch ↔ depth_minus = 1.** For odd `r`, `step_type r ≥ 2`
exactly when `depth_minus r = 1`. -/
theorem step_type_ge_two_iff_depth_eq_one (r : ℕ) (hr : Odd r) :
    2 ≤ step_type r ↔ depth_minus r = 1 := by
  -- `step_type r ≥ 2 ↔ 4 ∣ (3r+1) ↔ r ≡ 1 (mod 4) ↔ ν₂(r+1) = 1`.
  -- Forward and reverse via `Nat.factorization` and modular arithmetic.
  obtain ⟨k, hk⟩ := hr
  subst hk
  -- r = 2k + 1, so r + 1 = 2(k + 1), 3r + 1 = 6k + 4 = 2(3k + 2).
  unfold step_type Collatz.Arithmetic.e depth_minus
  have hsum1 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
  rw [hsum1]
  have hsum3 : 3 * (2 * k + 1) + 1 = 2 * (3 * k + 2) := by ring
  rw [hsum3]
  -- ν₂(2 * (k+1)) = 1 ↔ k+1 odd ↔ k even
  -- ν₂(2 * (3k+2)) ≥ 2 ↔ 3k+2 even ↔ k even
  have hkp1_pos : k + 1 ≠ 0 := Nat.succ_ne_zero k
  have h3k2_pos : 3 * k + 2 ≠ 0 := by omega
  rw [Nat.factorization_mul (by norm_num : (2:ℕ) ≠ 0) hkp1_pos,
      Nat.factorization_mul (by norm_num : (2:ℕ) ≠ 0) h3k2_pos]
  simp only [Finsupp.coe_add, Pi.add_apply,
    Nat.Prime.factorization_self Nat.prime_two]
  -- goal: 2 ≤ 1 + (3k+2).factorization 2 ↔ 1 + (k+1).factorization 2 = 1
  have hkparity := Nat.even_or_odd k
  rcases hkparity with hke | hko
  · -- k even
    obtain ⟨j, hj⟩ := hke
    subst hj
    have h1 : (j + j + 1).factorization 2 = 0 := by
      have hodd : Odd (j + j + 1) := ⟨j, by ring⟩
      exact Nat.factorization_eq_zero_of_not_dvd
        (by rcases hodd with ⟨m, hm⟩; omega)
    have h2 : (3 * (j + j) + 2).factorization 2 ≥ 1 := by
      have hdvd : 2 ∣ (3 * (j + j) + 2) := ⟨3 * j + 1, by ring⟩
      have hpos : 3 * (j + j) + 2 ≠ 0 := by omega
      exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos hdvd
    constructor
    · intro _
      have h1' : ((j + j) + 1).factorization 2 = 0 := h1
      omega
    · intro _
      omega
  · -- k odd
    obtain ⟨j, hj⟩ := hko
    subst hj
    have h1 : (2 * j + 1 + 1).factorization 2 ≥ 1 := by
      have hdvd : 2 ∣ (2 * j + 1 + 1) := ⟨j + 1, by ring⟩
      have hpos : 2 * j + 1 + 1 ≠ 0 := by omega
      exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos hdvd
    have h2 : (3 * (2 * j + 1) + 2).factorization 2 = 0 := by
      have hodd : Odd (3 * (2 * j + 1) + 2) := ⟨3 * j + 2, by ring⟩
      exact Nat.factorization_eq_zero_of_not_dvd
        (by rcases hodd with ⟨m, hm⟩; omega)
    constructor
    · intro h
      omega
    · intro h
      omega

/-- **Non-touch step type.** For odd `r` with `depth_minus r ≥ 2`,
`step_type r = 1`. -/
theorem step_type_eq_one_of_depth_ge_two
    (r : ℕ) (hr : Odd r) (hd : 2 ≤ depth_minus r) :
    step_type r = 1 := by
  by_contra h
  have hpos : 1 ≤ step_type r := step_type_odd_pos hr
  have hge : 2 ≤ step_type r := by omega
  have hd1 : depth_minus r = 1 :=
    (step_type_ge_two_iff_depth_eq_one r hr).mp hge
  omega

/-- **Touch depth.** For odd `r` with `step_type r ≥ 2`, `depth_minus r = 1`. -/
theorem depth_minus_eq_one_of_step_type_ge_two
    (r : ℕ) (hr : Odd r) (hs : 2 ≤ step_type r) :
    depth_minus r = 1 :=
  (step_type_ge_two_iff_depth_eq_one r hr).mp hs

/-- **Helper: factorization of `2^a * q` with `q` odd.** -/
private lemma factorization_two_pow_mul_odd
    (a : ℕ) {q : ℕ} (hq_pos : 0 < q) (hq_odd : Odd q) :
    (2 ^ a * q).factorization 2 = a := by
  have hpow_pos : (2 ^ a : ℕ) ≠ 0 := pow_ne_zero a (by norm_num)
  have hq_ne : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq_pos
  rw [Nat.factorization_mul hpow_pos hq_ne]
  rw [Nat.Prime.factorization_pow Nat.prime_two]
  have hfactq : q.factorization 2 = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    refine Or.inr (Or.inl ?_)
    rcases hq_odd with ⟨m, hm⟩; omega
  simp [Finsupp.single_apply, hfactq]

/-- **Per-step depth identity (non-touch case).**

For an odd `r` with `step_type r = 1`,

    `depth_minus (collatz_step r) + 1 = depth_minus r`.

**Proof.** When `step_type r = 1`, `collatz_step r = (3r+1)/2`, so
`(collatz_step r) + 1 = (3r+1)/2 + 1 = (3r+3)/2 = 3(r+1)/2`. Hence
`ν₂((collatz_step r) + 1) = ν₂(3(r+1)/2) = ν₂(r+1) − 1`, since `3` is
odd and `r + 1` is even. -/
theorem depth_minus_collatz_step_of_step_type_one
    (r : ℕ) (hr : Odd r) (hs : step_type r = 1) :
    depth_minus (collatz_step r) + 1 = depth_minus r := by
  -- `step_type r = 1` forces `depth_minus r ≥ 2` (touch ↔ depth = 1).
  have hd_ge : 2 ≤ depth_minus r := by
    by_contra h
    have hd_ge1 : 1 ≤ depth_minus r := depth_minus_odd_pos hr
    have hd_eq : depth_minus r = 1 := by omega
    have hge : 2 ≤ step_type r :=
      (step_type_ge_two_iff_depth_eq_one r hr).mpr hd_eq
    omega
  -- Write r + 1 = 2^d * q with q odd.
  have hrp1_pos : 0 < r + 1 := by omega
  have hrp1_ne : r + 1 ≠ 0 := by omega
  set d := (r + 1).factorization 2 with hd_def
  have hd_pos : 1 ≤ d := by rw [hd_def]; exact depth_minus_odd_pos hr
  have hrp1_dvd_pow : 2 ^ d ∣ r + 1 := Nat.ordProj_dvd (r + 1) 2
  obtain ⟨q, hq⟩ := hrp1_dvd_pow
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq_pos
    · exfalso; rw [hq0, Nat.mul_zero] at hq; omega
    · exact hq_pos
  have hq_odd : Odd q := by
    have hcop : ¬ 2 ∣ q := by
      intro hdvd
      have hpow_dvd : 2 ^ (d + 1) ∣ r + 1 := by
        rw [hq, pow_succ]
        exact Nat.mul_dvd_mul (dvd_refl _) hdvd
      have hle : d + 1 ≤ d :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hrp1_ne).mp hpow_dvd
      omega
    rcases Nat.even_or_odd q with he | ho
    · exfalso; obtain ⟨c, hc⟩ := he; exact hcop ⟨c, by omega⟩
    · exact ho
  -- Now `r = 2^d * q - 1`. Compute `collatz_step r + 1`.
  have hr_eq : r = 2 ^ d * q - 1 := by omega
  -- `step_type r = 1` ⇒ `collatz_step r = (3 r + 1) / 2`.
  have hstep_eq : collatz_step r = (3 * r + 1) / 2 := by
    unfold collatz_step; rw [hs, pow_one]
  -- `3 * r + 1 = 2 * (3 * 2^{d-1} * q - 1)` so `(3r+1)/2 = 3 * 2^{d-1} * q - 1`.
  have h3r_pos : 3 ≤ 3 * r := by
    have : 1 ≤ r := by obtain ⟨k, hk⟩ := hr; omega
    omega
  have hpow_ge : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hd_pos
  have hpow_split : (2 : ℕ) ^ d = 2 * 2 ^ (d - 1) := by
    have : (2 : ℕ) ^ d = 2 ^ (1 + (d - 1)) := by congr 1; omega
    rw [this, pow_add, pow_one]
  have h3r1_eq : 3 * r + 1 = 2 * (3 * 2 ^ (d - 1) * q - 1) := by
    have hrp1q : r + 1 = 2 * (2 ^ (d - 1) * q) := by
      rw [hq, hpow_split]; ring
    have hpow_pos1 : 1 ≤ 2 ^ (d - 1) := Nat.one_le_two_pow
    set f := 2 ^ (d - 1) * q with hf
    have hf_pos : 1 ≤ f := by
      have : 1 ≤ q := hq_pos
      nlinarith
    have h3eq : 3 * 2 ^ (d - 1) * q = 3 * f := by rw [hf]; ring
    rw [h3eq]
    have hr_from_f : r + 1 = 2 * f := hrp1q
    omega
  have hcs_plus1 :
      collatz_step r + 1 = 3 * 2 ^ (d - 1) * q := by
    rw [hstep_eq, h3r1_eq]
    have hpow_pos : 1 ≤ 2 ^ (d - 1) := Nat.one_le_two_pow
    have h3qpos_orig : 1 ≤ 3 * 2 ^ (d - 1) * q := by nlinarith
    set T := 3 * 2 ^ (d - 1) * q with hT
    have hTpos : 1 ≤ T := h3qpos_orig
    have hdiv : (2 * (T - 1)) / 2 = T - 1 :=
      Nat.mul_div_cancel_left (T - 1) (by norm_num : (0:ℕ) < 2)
    rw [hdiv]
    omega
  -- Now factorization 2 of `3 * 2^{d-1} * q` = d - 1.
  unfold depth_minus
  rw [hcs_plus1]
  have hrearr : (3 * 2 ^ (d - 1) * q : ℕ) = 2 ^ (d - 1) * (3 * q) := by ring
  rw [hrearr]
  have h3q_odd : Odd (3 * q) := Odd.mul (by decide) hq_odd
  have h3q_pos : 0 < 3 * q := by positivity
  rw [factorization_two_pow_mul_odd (d - 1) h3q_pos h3q_odd]
  omega

end Collatz.SEDT.OrbitBridge
