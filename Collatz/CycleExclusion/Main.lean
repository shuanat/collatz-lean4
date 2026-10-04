import Collatz.CycleExclusion.CycleDefinition
import Collatz.CycleExclusion.PeriodSum
import Collatz.CycleExclusion.MixedCycles
import Collatz.CycleExclusion.PureE1Cycles

/-!
# Cycle layer: basic predicates

This module only contains definitions and elementary facts. It does **not**
contain a cycle-exclusion theorem: excluding nontrivial cycles of the odd-step
map is an open problem and appears in the convergence layer only as an explicit
hypothesis (`NoNontrivialCycleOnOrbit`, `NoNontrivialCycles`, see
`Collatz/CycleExclusion/PeriodicTailBridge.lean`).

History: an earlier version exposed `main_cycle_exclusion` /
`no_nontrivial_cycles` under the premise package `exclusion_premises`, which
was unsatisfiable for every cycle (the period sum is identically `0`, which
contradicts the other two conjuncts). Those declarations were removed.
-/

namespace Collatz.CycleExclusion

/-- A trivial cycle has one-node orbit rooted at 1. -/
def Cycle.is_trivial (c : Cycle) : Prop :=
  c.len = 0 ∧ cycle_node c 0 = 1

/-- A genuine closed cycle with at least two nodes. (Note: nodes are not
required to be distinct, so a valid cycle of length `> 0` may still traverse the
fixed point `1` several times.) -/
def Cycle.is_nontrivial (c : Cycle) : Prop :=
  is_valid_cycle c ∧ c.len > 0

lemma nontrivial_has_positive_length {c : Cycle} (h : c.is_nontrivial) : c.len > 0 := h.2

lemma trivial_cycle_not_nontrivial (c : Cycle) (htriv : c.is_trivial) : ¬ c.is_nontrivial := by
  intro hnon
  have hlen0 : c.len = 0 := htriv.1
  have hpos : c.len > 0 := nontrivial_has_positive_length hnon
  omega

/-- The trivial cycle object exists (existence only, no uniqueness claim). -/
theorem trivial_cycle_exists : ∃ c : Cycle, c.is_trivial := by
  refine ⟨{ len := 0, atIdx := fun _ => 1 }, ?_⟩
  simp [Cycle.is_trivial, cycle_node]

/-- Eventual periodicity of the odd-step orbit of `m` (periods need not be
minimal). -/
def orbit_eventually_periodic (m : ℕ) : Prop :=
  ∃ k p : ℕ, 0 < p ∧
    ∀ n : ℕ,
      (Collatz.Foundations.collatz_step^[k + n + p]) m =
      (Collatz.Foundations.collatz_step^[k + n]) m

/-- The orbit of `1` is eventually periodic (it is constant). -/
theorem orbit_eventually_periodic_one : orbit_eventually_periodic 1 :=
  ⟨0, 1, Nat.one_pos, fun i => by rw [iterate_collatz_step_one, iterate_collatz_step_one]⟩

/-- Pack the existential periodic-tail contract into a structured witness. -/
noncomputable def orbit_periodic_tail_witness_of_eventual
    (m : ℕ) (hper : orbit_eventually_periodic m) :
    OrbitPeriodicTailWitness m := by
  classical
  let k : ℕ := Classical.choose hper
  let hk : ∃ p : ℕ, 0 < p ∧
      ∀ n : ℕ,
        (Collatz.Foundations.collatz_step^[k + n + p]) m =
        (Collatz.Foundations.collatz_step^[k + n]) m := Classical.choose_spec hper
  let p : ℕ := Classical.choose hk
  let hpkg : 0 < p ∧
      ∀ n : ℕ,
        (Collatz.Foundations.collatz_step^[k + n + p]) m =
        (Collatz.Foundations.collatz_step^[k + n]) m := Classical.choose_spec hk
  exact
    { start := k
      period := p
      period_pos := hpkg.1
      periodic := hpkg.2 }

/-- A periodic-tail witness is exactly a proof of eventual periodicity. -/
theorem orbit_eventually_periodic_of_witness {m : ℕ} (hw : OrbitPeriodicTailWitness m) :
    orbit_eventually_periodic m :=
  ⟨hw.start, hw.period, hw.period_pos, hw.periodic⟩

end Collatz.CycleExclusion
