# Collatz Lean4 Formalization

Lean 4 workspace for the current Collatz SEDT proof chain.

## Scope

The maintained proof-chain target is:

`D.1 -> {E.2, F.6/F.7, G.5} -> H.main -> I.1`

## Production Entry

- `Collatz.lean`
- `Collatz/Production.lean`

## Build

```bash
lake build Collatz
```

## Active Documentation

- `Collatz/Documentation/PaperCodeMapping.lean`:
  primary maintained paper-to-code map.
- `ACTIVE_FRONTIER.md`:
  active local milestone and residual log.
- `SEMANTIC_HARDENING_PLAN.md`:
  historical hardening log for the theorem-interface cleanup.
- `../docs/reports/collatz-lean4/`:
  repo-level review and audit reports.
- `scripts/smt/README.md`:
  historical/experimental SMT cross-check tooling notes.

## Notes

- `collatz_step` is the odd-step Collatz map used by the current formalization.
- Legacy generated Markdown architecture packs were removed after drifting away
  from the actual codebase. For current structure, prefer the `.lean`
  documentation modules and the reports listed above.

## Verified Gate Policy

CI enforces proof-chain hygiene for core theorem modules:

- no `sorry`
- no `axiom`

Gate is configured in `.github/workflows/lean.yml`.
