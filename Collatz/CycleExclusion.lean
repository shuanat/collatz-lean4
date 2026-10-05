/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Cycle Exclusion module aggregator

Cycle-layer aggregator. Contents:
- Cycle definitions and properties
- Period sum (telescoping identity, no content)
- Pure e=1 cycles (proved impossible: `no_pure_e1_cycle`)
- Mixed cycles (definition only)
- Block form of the cycle equation (Proposition H.7(a),(c); an equivalent
  reformulation of the cycle condition, it excludes no cycle)
- Periodic tails, and the OPEN hypotheses `NoNontrivialCycleOnOrbit` /
  `NoNontrivialCycles` (no cycle-exclusion theorem is proved here)
-/
import Collatz.CycleExclusion.Main
import Collatz.CycleExclusion.PeriodSum
import Collatz.CycleExclusion.PureE1Cycles
import Collatz.CycleExclusion.MixedCycles
import Collatz.CycleExclusion.PeriodicTailBridge
import Collatz.CycleExclusion.BlockEquation

-- All definitions are available through their respective modules:
-- - Collatz.CycleExclusion.Main
-- - Collatz.CycleExclusion.PeriodSum
-- - Collatz.CycleExclusion.PureE1Cycles
-- - Collatz.CycleExclusion.MixedCycles
-- - Collatz.CycleExclusion.PeriodicTailBridge
