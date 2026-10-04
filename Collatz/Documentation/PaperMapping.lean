/-
Paper-to-Lean navigation (short). The authoritative status table is
`PaperCodeMapping.lean`.
-/
import Mathlib.Data.Nat.Basic

namespace Collatz.Documentation

-- Section 2: Setup
-- Def 2.1 (odd map T) → Foundations.Core.collatz_step (alias Basic.T_odd)
-- Def 2.2 (depth₋) → Foundations.Core.depth_minus
-- Def 2.3 (e function) → Foundations.Core.step_type (= Foundations.Arithmetic.e)

-- Section 3: Stratified preimage geometry → not formalized

-- Appendix B: Lemma B.2 → Epochs.OrdFact.orderOf_three_eq_pow_two (proved)
-- Appendix C: depth dynamics → SEDT.OrbitBridge, SEDT.OrbitDepth (proved, orbit-level)
-- Appendix D: auxiliary sequence N_k → SEDT.AffineNumerator (algebra only; not the
--   orbit numerator for k ≥ 1)
-- Appendix E: SEDT (E.2 withdrawn) → only the constants and envelope expression in
--   SEDT.Core; the envelope appears as a hypothesis in Convergence.Coercivity
-- Appendix F: F.0.1 / F.6 per plateau → Mixing.AdmissibleTail, Mixing.AdmissibleTailBridge
--   (algebra in ZMod (2^t)); F.6 aggregate → Mixing.AggregateTouchRate (open, unused)
-- Appendix G: G.5c pure form → Epochs.G.PhaseUniqueness.phase_uniqueness_pure_mod_Qt
-- Appendix H: cycle exclusion (withdrawn) → open hypothesis
--   CycleExclusion.NoNontrivialCycles; proved: CycleExclusion.no_pure_e1_cycle
-- Appendix I: conditional endpoints → Convergence.MainTheorem
--   (collatz_of_no_cycles_and_bounded, collatz_convergence_modulo_explicit_residuals);
--   fixed point → Convergence.FixedPoints.fixed_point_eq_one (proved)

end Collatz.Documentation
