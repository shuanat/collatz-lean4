/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Main entry point for the production API.
-/
import Collatz.Production

-- S7.1 Appendix-G modules (G.5c pure core + paper-cited orbit-side residuals).
import Collatz.Epochs.G.PhaseUniqueness
import Collatz.Epochs.G.Residuals
import Collatz.Epochs.G.F3ConditionalResiduals
import Collatz.Epochs.G.G5Assembly

namespace Collatz

-- Re-export stable namespaces through main entry point.
open Collatz.Foundations
open Collatz.Epochs
open Collatz.SEDT

end Collatz
