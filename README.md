# Collatz Lean4 Formalization

Lean 4 formalization workspace for the Collatz SEDT proof chain.

## Proof Chain Scope

The project tracks and validates the chain:

`D.1 -> {E.2, F.6/F.7, G.5} -> H.main -> I.1`

## Production Entry

- `Collatz.lean`
- `Collatz/Production.lean`

## Verified Gate Policy

CI enforces proof-chain hygiene for core theorem modules:

- no `sorry`
- no `axiom`

Gate is configured in `.github/workflows/lean.yml`.

## Build

```bash
lake build Collatz
```

## Mapping Sources

- Lean mapping: `Collatz/Documentation/PaperCodeMapping.lean`
- Paper index: `../collatz-paper/paper/src/md/appendices/internal/INDEX.md`
