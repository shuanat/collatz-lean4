/-
Production surface for collatz-lean4.
Only modules intended for stable consumption are imported here.
-/
import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.Epochs.APStructure
import Collatz.Epochs.Homogenization
import Collatz.Epochs.NumeratorCarry
import Collatz.Epochs.LongEpochs
import Collatz.SEDT.Core
import Collatz.SEDT.Axioms
import Collatz.SEDT.Theorems
import Collatz.SEDT.AffineNumerator
import Collatz.SEDT.OrbitBridge
import Collatz.SEDT.Homogenization
import Collatz.SEDT.TouchDensity
import Collatz.SEDT.MultibitBonus
import Collatz.SEDT.LinearSurplus
import Collatz.SEDT.LinearSurplusReal
import Collatz.SEDT.OrbitDepth
import Collatz.SEDT.DepthBookkeeping
import Collatz.SEDT.AperiodicGainBridge
import Collatz.Mixing.AdmissibleTail
import Collatz.Mixing.Semigroup
import Collatz.Mixing.PhaseMixing
import Collatz.Mixing.TouchFrequency
import Collatz.Mixing.TouchFrequencyLocal
import Collatz.Mixing.TouchFrequencyHomogenization
import Collatz.Mixing.TouchFrequencyBridge
import Collatz.CycleExclusion.CycleDefinition
import Collatz.CycleExclusion.PeriodSum
import Collatz.CycleExclusion.PureE1Cycles
import Collatz.CycleExclusion.MixedCycles
import Collatz.CycleExclusion.RepeatTrick
import Collatz.CycleExclusion.Main
import Collatz.CycleExclusion.PeriodicTailBridge
import Collatz.Convergence.Coercivity
import Collatz.Convergence.FixedPoints
import Collatz.Convergence.NoAttractors
import Collatz.Convergence.MainTheorem
import Collatz.Convergence.UnconditionalModuloOrbitWitnesses
