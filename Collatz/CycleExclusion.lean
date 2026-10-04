/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Cycle Exclusion module aggregator

Cycle-layer aggregator. Contents:
- Cycle definitions and properties
- Period sum (telescoping identity, no content)
- Pure e=1 cycles (proved impossible: `no_pure_e1_cycle`)
- Mixed cycles (definition only)
- Periodic tails, and the OPEN hypotheses `NoNontrivialCycleOnOrbit` /
  `NoNontrivialCycles` (no cycle-exclusion theorem is proved here)
-/
import Collatz.CycleExclusion.Main
import Collatz.CycleExclusion.PeriodSum
import Collatz.CycleExclusion.PureE1Cycles
import Collatz.CycleExclusion.MixedCycles
import Collatz.CycleExclusion.PeriodicTailBridge

-- All definitions are available through their respective modules:
-- - Collatz.CycleExclusion.Main
-- - Collatz.CycleExclusion.PeriodSum
-- - Collatz.CycleExclusion.PureE1Cycles
-- - Collatz.CycleExclusion.MixedCycles
-- - Collatz.CycleExclusion.PeriodicTailBridge
