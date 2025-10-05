/-
Collatz Conjecture: Epoch-Based Deterministic Framework
Constants Registry (Appendix D)

This file centralizes all mathematical constants used in the Collatz formalization
using the centralized Core.lean architecture.
-/
import Collatz.Foundations.Core
import Collatz.Epochs.Core
import Collatz.Epochs.Aliases
import Collatz.SEDT.Core

namespace Collatz.Utilities

-- Use centralized definitions from Core.lean
open Collatz.Foundations (depth_minus step_type collatz_step)
open Collatz.Epochs (Q_t is_t_touch M_tilde s_t T_t p_touch)
open Collatz.SEDT (α β₀ C L₀ K_glue ε)

/-!
## Constants Registry

All constants are now centralized in Core modules:
- `Q_t` - Order of 3 modulo 2^t (in Epochs.Core)
- `α`, `β₀`, `C`, `L₀`, `K_glue`, `ε` - SEDT constants (in SEDT.Core)
- `depth_minus`, `step_type`, `collatz_step` - Foundation definitions (in Foundations.Core)
- `is_t_touch`, `M_tilde`, `s_t`, `T_t`, `p_touch` - Epoch definitions (in Epochs.Core)

This file now serves as a registry and provides convenient access to all constants.
-/

-- All constants are available through the open statements above

end Collatz.Utilities
