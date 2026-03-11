/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Main entry point for the production API.
-/
import Collatz.Production

namespace Collatz

-- Re-export stable namespaces through main entry point.
open Collatz.Foundations
open Collatz.Epochs
open Collatz.SEDT

end Collatz
