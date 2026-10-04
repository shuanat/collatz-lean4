# Documentation Index

This directory is now primarily a home for `.lean` documentation modules rather
than standalone generated Markdown manuals.

## Maintained Sources

- `PaperCodeMapping.lean`:
  primary maintained paper-to-code map for the current project state.
- `ProofRoadmap.lean`:
  short proof-closure checklist.

- `PaperMapping.lean`:
  short paper-section → module navigation (status lives in `PaperCodeMapping.lean`).

## Markdown Sources Outside This Folder

- `../../README.md`:
  repository overview.
- `../../ACTIVE_FRONTIER.md`:
  status block at the top; the log below it is historical.
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
- `ProofStructure.lean` (removed 2026-10: described a proof chain through
  deleted placeholder modules)
