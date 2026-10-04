# Documentation Index

This directory is now primarily a home for `.lean` documentation modules rather
than standalone generated Markdown manuals.

## Maintained Sources

- `PaperCodeMapping.lean`:
  primary maintained paper-to-code map for the current project state.
- `ProofRoadmap.lean`:
  short proof-closure checklist.
- `ProofStructure.lean`:
  broader proof-structure notes; useful, but may lag implementation.

## Historical / Verify Before Relying

- `PaperMapping.lean`:
  older paper-navigation file. Cross-check it against the current codebase
  before treating it as authoritative.

## Markdown Sources Outside This Folder

- `../../README.md`:
  repository overview.
- `../../ACTIVE_FRONTIER.md`:
  active local milestone and residual log.
- `../../SEMANTIC_HARDENING_PLAN.md`:
  historical hardening log.
- `../../../docs/reports/collatz-lean4/`:
  external audit and review reports.

## Cleanup Note

The following legacy Markdown files were removed from this directory because
they had drifted far from the current Lean codebase and contained stale or
non-compiling examples:

- `Architecture.md`
- `TechnicalDetails.md`
- `TargetArchitecture.md`
- `UsageExamples.md`
