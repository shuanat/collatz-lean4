/-
Collatz Conjecture: SEDT Deep Formalization — Wave 1 of S7.2 Path 1.algebraic.

This module realises the algebraic core of paper Lemma D.10.b on top of the
existing local tail semantic slot
`Collatz.Mixing.SelectedTailTouchSemantics`.

It introduces the minimal honest semantic interface
`LocalAffinePairSemantics m t i` capturing the inputs of the algebraic
homogenization toolkit (`Collatz.SEDT.Homogenization`):

* an integer-lift sequence `M` of the actual orbit residue mod `2^t`,
* a homogenizer sequence `u` ("particular solution") with the same affine
  forcing,
* a common forcing term `c`,
* the affine update equations on both sequences mod `2^t`,
* `Q_t`-periodicity of the homogenizer mod `2^t` (paper D.10.b: the
  homogenizer is constant on admissible tails, encoded here as periodicity),
* the realisation equation `M k ≡ orbit value`,
* the **revised** Wave 2E paper Definition F.0.1 admissibility predicate
  `AdmissibleTailF01 t Mentry v` on the algebraic data
  `(Mentry, v) := (M 0 - u 0, u t)` projected to `ZMod (2^t)`, tied to the
  carrier sequences by the bridge fields `Mentry_eq`, `v_eq`,
* the **late-regime flush guard** `c k ≡ 0 (mod 2^t)` for `k ≥ t`, which
  encodes the paper's "the forcing term vanishes after the plateau entry"
  step (Wave 2D §2.1) and is the missing data slot needed to derive
  `u (t + j) ≡ 3^j · u t (mod 2^t)` from `affineUpdateU` alone.

`Q_t`-periodicity of `selected_segment_tail_touch` follows by a real proof
combining `homogenization_principle`, `homogenized_periodic_of_order_dvd`
and the order bridge `three_pow_Qt_modEq_one`. **Wave 2G upgrade.** The
per-period touch count `1` is now a *derived theorem*
(`LocalAffinePairSemantics.one_touch_per_period`) obtained from the
`AdmissibleTailF01.touch_count_eq_one_of_realized` bridge applied to the
honest fields above; it is no longer carried as an independent paper input.

This is the algebraic-side discharge of `R-F6`; the residual that remains
after this module is the orbit-side `R-D10b` (existence of a
`LocalAffinePairSemantics` for every admissible tail of the actual Collatz
orbit, including the flush guard and the algebraic admissibility witness),
tracked as `R-OrbitSideAdmissibleDensity` in `docs/residual-budget.md`.
-/

import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Collatz.SEDT.Homogenization
import Collatz.Epochs.OrdFact
import Collatz.Mixing.AdmissibleTail
import Collatz.Mixing.AdmissibleTailBridge
import Collatz.Mixing.TouchFrequencyLocal
import Collatz.Mixing.PhaseMixing

namespace Collatz.Mixing

open Collatz.Epochs

/-- **Local affine pair semantics on a selected admissible tail** (paper
Lemma D.10.b, algebraic interface).

Captures the *minimal honest inputs* needed by the algebraic homogenization
toolkit (`Collatz.SEDT.Homogenization`) plus the per-period touch count to
derive a `SelectedTailTouchSemantics` slot.

Fields:
* `M k` — integer lift of the actual orbit value `(collatz_step^[i+k]) m`
  modulo `2 ^ t`.
* `u k` — paper "homogenizer" / particular solution.
* `c k` — common forcing term in the affine updates of `M` and `u`.
* `t_ge_three` — algebraic backbone needs the period `Q_t t = 2^(t-2)`,
  which forces `t ≥ 3`.
* `affineUpdateM`, `affineUpdateU` — affine update equations modulo `2 ^ t`.
* `uPeriodic` — paper-input: the homogenizer is `Q_t`-periodic mod `2^t`.
  The algebraic toolkit only periodises the **difference** `M − u`; without
  this slot one cannot lift periodicity to `M` itself. This is the honest
  paper input on the homogenizer side of D.10.b.
* `realized` — connects integer lift `M k` to the actual orbit residue.
* `Mentry` — algebraic numerator residue at the plateau entry, `M 0 mod 2^t`
  (cf. Wave 2D §2: `M_{k_start} mod 2^t`). Carried explicitly so that the
  revised paper Definition F.0.1 admissibility (`AdmissibleTailF01`) can be
  stated as honest field data on this structure rather than implicit
  conjunction with the orbit-side construction. Tied to `M`, `u` by
  `Mentry_eq`.
* `v` — late-regime per-plateau homogenizer freeze value, `u t mod 2^t`
  (cf. Wave 2D §2.1: `v := u_{k_start + t}`). After step `t` the forcing
  `c_k` vanishes and `u_{k_start + t + j} = v · 3^j (mod 2^t)`. Tied to
  `u` by `v_eq`.
* `Mentry_eq`, `v_eq` — **Wave 2G bridge fields**: tie the abstract
  `Mentry, v ∈ ZMod (2^t)` to the carrier sequences `M, u` via the natural
  identifications `Mentry := M 0 - u 0` and `v := u t`. These are the
  data slots that promote `admissible` from a free `ZMod (2^t)` statement
  into an honest constraint on the orbit-realised algebraic data.
* `admissible : AdmissibleTailF01 t Mentry v` — the **revised** Wave 2E
  paper Definition F.0.1: `s_t · (v + 3^t · M_entry)⁻¹ ∈ ⟨3⟩` in
  `(ZMod (2^t))ˣ`, i.e. `∃ n, s_t = 3^n · (v + 3^t · M_entry)`. Replaces
  the old, empirically-unsupported "single-residue coset on `M̃_{k_start}`
  alone" form (cf. `collatz-verification/research/wave2-d10b-empirical/
  REPORT-reverse-engineering.md`).
* `flushGuard` — **Wave 2G honest paper input**: the late-regime forcing
  vanishes, `c k ≡ 0 (mod 2^t)` for `k ≥ t`. This encodes the paper
  `Wave 2D §2.1` step "after the plateau entry the homogenizer is frozen
  modulo `2^t`" and is the algebraic data slot needed to derive
  `u (t + j) ≡ 3^j · u t (mod 2^t)` from `affineUpdateU` alone. With this
  field, the late-window touch count `= 1` becomes a *derived theorem*
  (`one_touch_per_period`) rather than an independent paper input. -/
structure LocalAffinePairSemantics (m t i : ℕ) where
  M : ℕ → ℤ
  u : ℕ → ℤ
  c : ℕ → ℤ
  t_ge_three : 3 ≤ t
  affineUpdateM :
    ∀ k, M (k + 1) ≡ 3 * M k + c k [ZMOD ((2 : ℤ) ^ t)]
  affineUpdateU :
    ∀ k, u (k + 1) ≡ 3 * u k + c k [ZMOD ((2 : ℤ) ^ t)]
  uPeriodic :
    ∀ k, u (k + Q_t t) ≡ u k [ZMOD ((2 : ℤ) ^ t)]
  realized :
    ∀ k,
      ((selected_segment_value m (i + k) : ℕ) : ℤ) ≡ M k [ZMOD ((2 : ℤ) ^ t)]
  /-- Plateau-entry algebraic residue `M 0 mod 2^t` (Wave 2D §2). -/
  Mentry : ZMod (2 ^ t)
  /-- Late-regime homogenizer freeze value `u t mod 2^t` (Wave 2D §2.1). -/
  v : ZMod (2 ^ t)
  /-- Wave 2G bridge: identify `Mentry` with `M 0 - u 0 (mod 2^t)`. -/
  Mentry_eq : Mentry = ((M 0 - u 0 : ℤ) : ZMod (2 ^ t))
  /-- Wave 2G bridge: identify `v` with `u t (mod 2^t)`. -/
  v_eq : v = ((u t : ℤ) : ZMod (2 ^ t))
  /-- Revised paper Definition F.0.1 admissibility (Wave 2E):
  `s_t · (v + 3^t · M_entry)⁻¹ ∈ ⟨3⟩` in `(ZMod (2^t))ˣ`. Replaces the old
  canonical paper F.0.1 (random-baseline empirically). -/
  admissible : AdmissibleTailF01 t Mentry v
  /-- Wave 2G honest paper input: late-regime flush guard. The forcing
  `c k` vanishes modulo `2^t` for `k ≥ t` (paper Wave 2D §2.1). -/
  flushGuard :
    ∀ k, t ≤ k → c k ≡ 0 [ZMOD ((2 : ℤ) ^ t)]

/-- **Wave 2G derived theorem — late-window touchCount = 1 from the local
algebraic data plus admissibility plus the late-regime flush guard.**

This is the orbit-faithful end-to-end discharge of the local algebraic
stack: under the revised paper Definition F.0.1 admissibility predicate
`AdmissibleTailF01 t Mentry v` and the late-regime flush guard
`c k ≡ 0 (k ≥ t)`, exactly one `Q_t`-periodic touch occurs in the
canonical window. Replaces the previous honest carrier
`one_touch_per_period_input` field of `LocalAffinePairSemantics`. -/
theorem LocalAffinePairSemantics.one_touch_per_period
    {m t i : ℕ} (h : LocalAffinePairSemantics m t i) :
    Collatz.SEDT.TouchDensity.touchCount
      (selected_segment_tail_touch m t i) (Q_t t) = 1 :=
  AdmissibleTailF01.touch_count_eq_one_of_realized h.t_ge_three
    h.M h.u h.c h.affineUpdateM h.affineUpdateU h.uPeriodic h.realized
    h.flushGuard h.Mentry_eq h.v_eq h.admissible

/-- **Constructor (Wave 1 of S7.2 Path 1.algebraic; Wave 2E/Wave 2G field
upgrades).** The local affine pair semantics produces the honest local
tail touch semantics consumed by the F.6 stack. Both fields of
`SelectedTailTouchSemantics` are now **fully derived** from the algebraic
data:

* `periodic` — proved via the real algebraic homogenization toolkit
  (`homogenization_principle`, `homogenized_periodic_of_order_dvd`,
  `three_pow_Qt_modEq_one`).
* `one_touch_per_period` — derived via
  `LocalAffinePairSemantics.one_touch_per_period`, which discharges the
  late-window touchCount = 1 obligation from the revised paper Definition
  F.0.1 admissibility predicate (`admissible`) plus the late-regime flush
  guard (`flushGuard`) and the `Mentry`/`v` bridge fields. Wave 2G
  closes the previously-open algebraic-stack gap; the only remaining
  residual on this side is the orbit-side existence of a
  `LocalAffinePairSemantics` for every admissible tail, tracked as
  `R-OrbitSideAdmissibleDensity` in `docs/residual-budget.md`. -/
def selectedTailTouchSemantics_of_localAffinePair
    {m t i : ℕ} (h : LocalAffinePairSemantics m t i) :
    SelectedTailTouchSemantics m t i := by
  set n : ℤ := (2 : ℤ) ^ t with hndef
  -- Step 1: homogenized difference Mtilde := M − u satisfies the homogeneous
  -- update mod n.
  let Mtilde : ℕ → ℤ := fun k => h.M k - h.u k
  have hstep : ∀ j, Mtilde (j + 1) ≡ 3 * Mtilde j [ZMOD n] := by
    intro j
    exact Collatz.SEDT.Homogenization.homogenization_principle
      n h.M h.u h.c j (h.affineUpdateM j) (h.affineUpdateU j)
  -- Step 2: Q_t-periodicity of Mtilde from `3^(Q_t) ≡ 1 (mod 2^t)`.
  have hord : (3 : ℤ) ^ (Q_t t) ≡ 1 [ZMOD n] :=
    Collatz.OrdFact.three_pow_Qt_modEq_one h.t_ge_three
  have hMtildePer :
      ∀ k, Mtilde (k + Q_t t) ≡ Mtilde k [ZMOD n] :=
    Collatz.SEDT.Homogenization.homogenized_periodic_of_order_dvd
      n Mtilde (Q_t t) hstep hord
  -- Step 3: combine Mtilde-periodicity with uPeriodic to get M-periodicity.
  have hMPer : ∀ k, h.M (k + Q_t t) ≡ h.M k [ZMOD n] := by
    intro k
    have hMt : Mtilde (k + Q_t t) ≡ Mtilde k [ZMOD n] := hMtildePer k
    have hu : h.u (k + Q_t t) ≡ h.u k [ZMOD n] := h.uPeriodic k
    have hsum :
        Mtilde (k + Q_t t) + h.u (k + Q_t t) ≡ Mtilde k + h.u k [ZMOD n] :=
      hMt.add hu
    have heqL :
        Mtilde (k + Q_t t) + h.u (k + Q_t t) = h.M (k + Q_t t) := by
      simp [Mtilde]
    have heqR : Mtilde k + h.u k = h.M k := by simp [Mtilde]
    rw [heqL, heqR] at hsum
    exact hsum
  -- Step 4: discharge the SelectedTailTouchSemantics slot.
  refine
    { periodic := ?_
      one_touch_per_period := ?_ }
  · intro k
    -- Bridge orbit values via `realized` and M-periodicity.
    have hRk :
        ((selected_segment_value m (i + k) : ℕ) : ℤ) ≡ h.M k [ZMOD n] :=
      h.realized k
    have hRkQ :
        ((selected_segment_value m (i + (k + Q_t t)) : ℕ) : ℤ) ≡
          h.M (k + Q_t t) [ZMOD n] := h.realized (k + Q_t t)
    have hMpk : h.M (k + Q_t t) ≡ h.M k [ZMOD n] := hMPer k
    have hint :
        ((selected_segment_value m (i + (k + Q_t t)) : ℕ) : ℤ) ≡
          ((selected_segment_value m (i + k) : ℕ) : ℤ) [ZMOD n] :=
      (hRkQ.trans hMpk).trans hRk.symm
    -- Translate to Nat.ModEq via the cast bridge.
    have hcastPow : ((2 ^ t : ℕ) : ℤ) = (2 : ℤ) ^ t := by push_cast; ring
    have hintNat :
        ((selected_segment_value m (i + (k + Q_t t)) : ℕ) : ℤ) ≡
          ((selected_segment_value m (i + k) : ℕ) : ℤ) [ZMOD ((2 ^ t : ℕ) : ℤ)] := by
      rw [hcastPow]; exact hint
    have hNat :
        selected_segment_value m (i + (k + Q_t t)) ≡
          selected_segment_value m (i + k) [MOD 2 ^ t] := by
      exact_mod_cast hintNat
    have hmod :
        selected_segment_value m (i + (k + Q_t t)) % 2 ^ t =
          selected_segment_value m (i + k) % 2 ^ t := hNat
    -- Conclude the iff on the touch predicate.
    constructor
    · intro hk
      -- hk : selected_segment_tail_touch m t i (k + Q_t t)
      -- unfolds to: selected_segment_value m (i + (k + Q_t t)) % 2^t = s_t t
      show selected_segment_t_touch m (i + k) t
      have hkres :
          selected_segment_value m (i + (k + Q_t t)) % 2 ^ t =
            Collatz.Epochs.s_t t := hk
      rw [hmod] at hkres
      exact hkres
    · intro hk
      show selected_segment_t_touch m (i + (k + Q_t t)) t
      have hkres :
          selected_segment_value m (i + k) % 2 ^ t =
            Collatz.Epochs.s_t t := hk
      rw [← hmod] at hkres
      exact hkres
  · exact h.one_touch_per_period

/-- Public residual wrapper for the existence of a `LocalAffinePairSemantics`
on a fixed admissible-tail anchor. -/
def LocalAffinePairResidual (m t i : ℕ) : Prop :=
  Nonempty (LocalAffinePairSemantics m t i)

/-- Bundled paper-D.10.b input over a family of admissible tails: each tail
window `[tailStart L, tailStop L)` is supplied with a local affine pair
semantics. This is the orbit-side aggregate consumed by the F.6 theorem
source. -/
structure AdmissibleTailLocalAffinePairData (n t : ℕ) where
  tailStart : ℕ → ℕ
  tailStop : ℕ → ℕ
  tailOrdered : ∀ L : ℕ, tailStart L ≤ tailStop L
  tailPair : ∀ L : ℕ, LocalAffinePairSemantics n t (tailStart L)

/-- **Algebraic constructor of the F.6 admissible-tail theorem source from
the paper-D.10.b local affine pair data.** This realises the previously
opaque F.6 theorem source via the algebraic homogenization toolkit, leaving
only the orbit-side D.10.b supply (`AdmissibleTailLocalAffinePairData`) as
an open math residual. -/
noncomputable def admissibleTailTouchFrequencyTheoremSource_of_localAffinePair
    {n t : ℕ} (d : AdmissibleTailLocalAffinePairData n t) :
    AdmissibleTailTouchFrequencyTheoremSource n t :=
  { tailStart := d.tailStart
    tailStop := d.tailStop
    tailOrdered := d.tailOrdered
    tailSemantics := fun L =>
      selectedTailTouchSemantics_of_localAffinePair (d.tailPair L) }

/-- Paper-D.10.b residual at the bundle level. -/
def AdmissibleTailLocalAffinePairResidual (n t : ℕ) : Prop :=
  Nonempty (AdmissibleTailLocalAffinePairData n t)

/-- **Algebraic discharge of `R-F6` modulo `R-D10b`.** Once the orbit-side
local affine pair data exists on admissible tails, the F.6 admissible-tail
touch-frequency residual follows mechanically through the algebraic
homogenization toolkit. -/
theorem admissibleTailTouchFrequencyResidual_of_localAffinePairResidual
    {n t : ℕ} (h : AdmissibleTailLocalAffinePairResidual n t) :
    AdmissibleTailTouchFrequencyResidual n t :=
  ⟨admissibleTailTouchFrequencyTheoremSource_of_localAffinePair
    (Classical.choice h)⟩

end Collatz.Mixing
