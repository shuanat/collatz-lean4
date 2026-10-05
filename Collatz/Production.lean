/-
Production surface for collatz-lean4: every module that is built by
`lake build Collatz`. Nothing here proves the Collatz conjecture; see README.md.
-/
import Collatz.Foundations.Core
import Collatz.Foundations.Basic
import Collatz.Foundations.StepClassification
import Collatz.Foundations.TwoAdicDepth
import Collatz.Foundations.OddPart
import Collatz.Layers.PreimageLayers
import Collatz.Blocks.BlockStep
import Collatz.Epochs.Core
import Collatz.Epochs.OrdFact
import Collatz.Epochs.LongEpochs
import Collatz.Epochs.G.PhaseUniqueness
import Collatz.Epochs.G.F3ConditionalResiduals
import Collatz.SEDT.Core
import Collatz.SEDT.AffineNumerator
import Collatz.SEDT.OrbitBridge
import Collatz.SEDT.OrbitDepth
import Collatz.SEDT.Homogenization
import Collatz.SEDT.TouchDensity
import Collatz.SEDT.MultibitBonus
import Collatz.SEDT.LinearSurplus
import Collatz.SEDT.LinearSurplusReal
import Collatz.Mixing.AdmissibleTail
import Collatz.Mixing.AdmissibleTailBridge
import Collatz.Mixing.AggregateTouchRate
import Collatz.CycleExclusion.CycleDefinition
import Collatz.CycleExclusion.PeriodSum
import Collatz.CycleExclusion.PureE1Cycles
import Collatz.CycleExclusion.MixedCycles
import Collatz.CycleExclusion.Main
import Collatz.CycleExclusion.PeriodicTailBridge
import Collatz.CycleExclusion.BlockEquation
import Collatz.Convergence.Coercivity
import Collatz.Convergence.FixedPoints
import Collatz.Convergence.NoAttractors
import Collatz.Convergence.MainTheorem
