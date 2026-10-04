/-
Collatz formalization: main entry point.
This library does NOT prove the Collatz conjecture. Its convergence theorems are
conditional on explicitly named open hypotheses; see README.md and
`Collatz/Convergence/MainTheorem.lean`.
-/
import Collatz.Production

namespace Collatz

-- Re-export stable namespaces through main entry point.
open Collatz.Foundations
open Collatz.Epochs
open Collatz.SEDT

end Collatz
