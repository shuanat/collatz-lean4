# collatz-lean4 — Lean 4 formalization

Workspace-wide rules: `../CLAUDE.md` and `../.claude/rules/lean.md` (loaded automatically when
working on files here). This file adds repository specifics.

## What is formalized (status 2026-10)

- Proved: elementary facts — ord_{2^t}(3) = 2^{t−2} (`Epochs/OrdFact.lean`), depth/valuation
  identities (`SEDT/OrbitDepth.lean`, `SEDT/OrbitBridge.lean`), log-growth bounds
  (`Foundations/Core.lean`), bounded ⇒ eventually periodic, and the honest top-level equivalence
  `collatz_iff_no_cycles_and_bounded` (`Convergence/MainTheorem.lean`).
- Formal refutations: `false_of_orbit_epoch_sedt_envelope` (the former SEDT envelope fails on
  every long-epoch stream); `Tests/VacuityRegression.lean` documents the earlier vacuous
  hypotheses.
- Not formalized: any proof of the Collatz conjecture (none exists).

## Build and tests (PowerShell)

```powershell
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build Collatz Collatz.Tests.ResidualSanity Collatz.Tests.VacuityRegression Collatz.Tests.AxiomCheck
```

- `Tests/ResidualSanity.lean`: every hypothesis of every public convergence theorem holds at n = 1.
- `Tests/VacuityRegression.lean`: machine-checked facts about withdrawn/vacuous formulations.
- `Tests/AxiomCheck.lean`: `#print axioms` for the public surface.

## Pointers

- `README.md`, `ACTIVE_FRONTIER.md` (status block at the top), `Collatz/Documentation/PaperCodeMapping.lean`,
  `../docs/residual-budget.md`.
- `collatz_step` is the odd-to-odd map T(n) = (3n+1)/2^{ν₂(3n+1)}, not the mixed Collatz step.
- Subagents: `lean-formalizer` (writes proofs), `lean-auditor` (checks meaning); skills
  `build-lean`, `lean-vacuity-audit`, `lean-statement-design`.
