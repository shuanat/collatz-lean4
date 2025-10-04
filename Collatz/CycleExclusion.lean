/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Cycle Exclusion module aggregator

This module aggregates all cycle exclusion definitions and properties from Appendix B:
- Cycle definitions and properties
- Period sum arguments (telescoping lemma)
- Pure E=1 cycles analysis
- Mixed cycles analysis (SEDT-based)
- Repeat trick analysis
- Main cycle exclusion theorem
-/
import Collatz.CycleExclusion.Main
import Collatz.CycleExclusion.PeriodSum
import Collatz.CycleExclusion.PureE1Cycles
import Collatz.CycleExclusion.MixedCycles
import Collatz.CycleExclusion.RepeatTrick

-- This module aggregates all cycle exclusion definitions and properties from Appendix B
-- All definitions are available through their respective modules:
-- - Collatz.CycleExclusion.Main
-- - Collatz.CycleExclusion.PeriodSum
-- - Collatz.CycleExclusion.PureE1Cycles
-- - Collatz.CycleExclusion.MixedCycles
-- - Collatz.CycleExclusion.RepeatTrick
