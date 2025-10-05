/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Aliases System

This file provides convenient aliases and abbreviations for commonly used
definitions across all Collatz modules, ensuring consistent naming.
-/
import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.SEDT.Core

namespace Collatz.Epochs.Aliases

/-!
## Global Aliases

Convenient aliases for commonly used definitions across all modules.
-/

-- Import all core modules
open Collatz.Foundations
open Collatz.Epochs
open Collatz.SEDT

/-!
## Foundations Aliases

Short names for foundational definitions.
-/

-- Basic definitions
abbrev Depth := depth_minus
abbrev StepType := step_type
abbrev CollatzStep := collatz_step
abbrev Orbit (r : ℕ) : List ℕ := sorry -- TODO: Implement orbit as list

/-!
## Epochs Aliases

Short names for epoch-related definitions.
-/

-- Epoch structure
abbrev Epoch (t : ℕ) := TEpoch t
abbrev Touch (n t : ℕ) := is_t_touch n t
abbrev IsTTouch (n t : ℕ) := is_t_touch n t

-- Touch analysis
abbrev MTilde (k t : ℕ) := M_tilde k t
abbrev ST (t : ℕ) := s_t t
abbrev TT (t : ℕ) := T_t t
abbrev PTouch (t : ℕ) : ℝ := p_touch t
abbrev QT (t : ℕ) := Q_t t

-- Phase and junction
abbrev PhaseClass := phase_class
abbrev PhaseShift := phase_shift
abbrev PrimitiveJunction := is_primitive_junction

-- Homogenization
abbrev Homogenized := M_tilde
abbrev Homogenizer := homogenizer

-- Epoch functions
abbrev EpochIsLong (E : TEpoch t) : Prop := sorry -- TODO: Implement epoch is_long
abbrev EpochLength (E : TEpoch t) : ℕ := sorry -- TODO: Implement epoch length
abbrev LongEpochThreshold (t : ℕ) : ℕ := sorry -- TODO: Implement L₀

/-!
## SEDT Aliases

Short names for SEDT-related definitions.
-/

-- SEDT constants (noncomputable)
noncomputable abbrev SlopeParam := α
noncomputable abbrev NegativityThreshold := β₀
noncomputable abbrev DriftConstant := C
noncomputable abbrev DriftDiscrepancy := C
abbrev GlueConstant := K_glue

-- SEDT envelope (noncomputable)
noncomputable abbrev DriftRate := SEDT.ε
noncomputable abbrev SEDTEnvelope := SEDT.sedt_envelope

-- SEDT potential (noncomputable)
noncomputable abbrev AugmentedPotential := SEDT.augmented_potential
noncomputable abbrev PotentialChange := SEDT.potential_change

end Collatz.Epochs.Aliases
