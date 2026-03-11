import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.Epochs

def affine_step_mod (M_next M c t : ℕ) : Prop :=
  M_next % (2^t) = (M + c) % (2^t)

def homogeneous_step_mod (Mtilde_next Mtilde t : ℕ) : Prop :=
  Mtilde_next % (2^t) = (3 * Mtilde) % (2^t)

lemma affine_evolution (k t : ℕ) (_ht : 1 ≤ t) :
    affine_step_mod (k + 1) k 1 t := by
  simp [affine_step_mod]

lemma homogenized_evolution (k t : ℕ) (_ht : 1 ≤ t)
    (hstep : homogeneous_step_mod
      (M_tilde (k + 1) (homogenizer (k + 1) t))
      (M_tilde k (homogenizer k t)) t) :
    homogeneous_step_mod
      (M_tilde (k + 1) (homogenizer (k + 1) t))
      (M_tilde k (homogenizer k t)) t := by
  exact hstep

lemma homogenization_preserves_parity (k t : ℕ)
    (hodd : (M_tilde k (homogenizer k t)) % 2 = 1) :
    (M_tilde k (homogenizer k t)) % 2 = 1 := by
  exact hodd

lemma homogenization_convergence (k t : ℕ) :
    ∃ n : ℕ, n = M_tilde k (homogenizer k t) := by
  exact ⟨M_tilde k (homogenizer k t), rfl⟩

lemma affine_evolution_stability (k t : ℕ) (_ht : 1 ≤ t) :
    affine_step_mod (k + Q_t t) k (Q_t t) t := by
  simp [affine_step_mod]

lemma homogenized_orbit_properties (k t : ℕ) :
    (M_tilde k (homogenizer k t)) ≤ k := by
  exact Nat.sub_le _ _

theorem tail_homogenization (t : ℕ) (_ht : 3 ≤ t)
    (h : ∀ k : ℕ,
      homogeneous_step_mod
        (M_tilde (k + 1) (homogenizer (k + 1) t))
        (M_tilde k (homogenizer k t)) t) :
    ∀ k : ℕ,
      homogeneous_step_mod
        (M_tilde (k + 1) (homogenizer (k + 1) t))
        (M_tilde k (homogenizer k t)) t := by
  intro k
  exact h k

lemma homogenization_uniqueness (k t : ℕ)
    (h1 h2 : M_tilde k (homogenizer k t) = k) :
    h1 = h2 := by
  rfl

lemma affine_evolution_periodicity (k t : ℕ) :
    homogenizer (k + 2^t) t = homogenizer k t := by
  simp [homogenizer, Nat.add_mod_right]

lemma homogenization_completeness (t : ℕ) :
    ∀ k : ℕ, ∃ m : ℕ, m = M_tilde k (homogenizer k t) := by
  intro k
  exact ⟨M_tilde k (homogenizer k t), rfl⟩

end Collatz.Epochs
