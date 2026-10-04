# Collatz Lean4 Notes

Short working note for agent/tooling sessions in this repository.

## Build

```bash
lake build Collatz
```

## Main Entry Points

- `Collatz.lean`
- `Collatz/Production.lean`
- `Collatz/Convergence/MainTheorem.lean`

## Documentation To Prefer

- `README.md`
- `ACTIVE_FRONTIER.md`
- `SEMANTIC_HARDENING_PLAN.md`
- `Collatz/Documentation/PaperCodeMapping.lean`
- `../docs/reports/collatz-lean4/`

## Important Semantic Note

- `collatz_step` is the odd-step map used by the current Lean formalization.
  It is not the full mixed even/odd Collatz step.
