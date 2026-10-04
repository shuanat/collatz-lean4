/-
SEDT-layer aggregator.

* `SEDT.Core`: constants `α, β₀, C, L₀, ε` and the envelope expression. The
  paper's Theorem E.2 (SEDT) is false as stated and is not formalized.
* `AffineNumerator`, `OrbitBridge`, `OrbitDepth`: algebra of the auxiliary
  sequence `N_k = 3^{k+1}(r₀+2) − 5·2^k` (not the orbit numerator for `k ≥ 1`),
  its base case `k = 0`, and the exact orbit depth identity.
* `Homogenization`, `TouchDensity`, `MultibitBonus`, `LinearSurplus`,
  `LinearSurplusReal`: abstract counting / congruence lemmas with explicit
  hypotheses; no orbit-level instance of those hypotheses is proved.
-/
import Collatz.SEDT.Core
import Collatz.SEDT.AffineNumerator
import Collatz.SEDT.OrbitBridge
import Collatz.SEDT.OrbitDepth
import Collatz.SEDT.Homogenization
import Collatz.SEDT.TouchDensity
import Collatz.SEDT.MultibitBonus
import Collatz.SEDT.LinearSurplus
import Collatz.SEDT.LinearSurplusReal
