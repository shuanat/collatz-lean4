/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Mixing Theory Aggregator

This module aggregates all mixing theory components from Appendix A.MIX:
- Phase mixing analysis
- Touch frequency analysis
- Semigroup theory
-/
import Collatz.Mixing.AdmissibleTail
import Collatz.Mixing.Semigroup
import Collatz.Mixing.PhaseMixing
import Collatz.Mixing.TouchFrequency
import Collatz.Mixing.TouchFrequencyLocal
import Collatz.Mixing.TouchFrequencyHomogenization
import Collatz.Mixing.TouchFrequencyBridge
import Collatz.Mixing.AggregateTouchRate

-- This module aggregates all mixing theory definitions and properties from Appendix A.MIX
-- All definitions are available through their respective modules:
-- - Collatz.Mixing.Semigroup
-- - Collatz.Mixing.PhaseMixing
-- - Collatz.Mixing.TouchFrequency
