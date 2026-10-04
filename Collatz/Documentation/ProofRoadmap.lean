/-
Proof roadmap for collatz-lean4.
-/

namespace Collatz.Documentation

/-!
## Intended chain (NOT closed)

`D.1 -> {E.2, F.6/F.7, G.5} -> H.main -> I.1`

None of these links is formalized unconditionally; see `PaperCodeMapping.lean`
for the current status.

In the corrected paper E.2, F.3/F.4, G.5 and the proof of H.main are withdrawn;
the chain above is therefore not a proof outline any more.

## Acceptance

- `lake build Collatz` passes.
- CI chain gate rejects placeholder proofs and extra axioms in chain files.
- `Collatz/Tests/ResidualSanity.lean` shows every hypothesis of every public
  convergence theorem holds for `n = 1`.
-/

end Collatz.Documentation
