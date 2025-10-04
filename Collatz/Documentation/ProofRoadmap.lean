/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Proof Structure Roadmap

This file provides a roadmap of the proof structure and dependencies:
- Proof flow from setup to main theorem
- Module dependencies
- Key lemmas and theorems
-/
import Mathlib.Data.Nat.Basic

namespace Collatz.Documentation

-- Proof Structure Roadmap

-- 1. Setup (§2) → Foundations/
-- Basic definitions and properties:
-- - T_odd function
-- - Arithmetic properties
-- - Two-adic depth
-- - Step classification

-- 2. Stratification (§3) → Stratified/
-- Stratified decomposition:
-- - Preimage layers
-- - Parametrization
-- - Cylinders
-- - Complete stratification (Theorem 4.1)
-- - Branching density (Theorem 4.3)

-- 3. Epoch Theory (App A.E0-E2) → Epochs/
-- Epoch structure and properties:
-- - Epoch definition
-- - Order of 3 modulo powers of 2
-- - Phase classes
-- - Homogenization
-- - Touch analysis
-- - Long epochs (Theorem A.LONG.5)

-- 4. SEDT (App A.E3-E4) → SEDT/
-- Stochastic Ergodic Drift Theory:
-- - SEDT axioms
-- - Core SEDT theory
-- - SEDT theorems
-- - Potential function
-- - Drift analysis

-- 5. Mixing (App A.MIX) → Mixing/
-- Phase mixing theory:
-- - Semigroup structure
-- - Phase mixing (Theorem A.HMix(t))
-- - Touch frequency (p_t = Q_t^{-1})

-- 6. Cycle Exclusion (App B) → CycleExclusion/
-- Cycle exclusion theory:
-- - Cycle definition
-- - Period sum (telescoping lemma)
-- - Pure E1 cycles (Theorem C.B)
-- - Mixed cycles (SEDT-based)
-- - Repeat trick (R_0 threshold)
-- - Main cycle exclusion theorem

-- 7. Convergence (§4 + App C) → Convergence/
-- Main convergence theorem:
-- - Coercivity (Lemma C.1)
-- - No attractors (no other attractors)
-- - Main theorem (global convergence)
-- - Fixed points (uniqueness)

end Collatz.Documentation
