# Cursor Commands for Collatz Lean4 Project

This directory contains custom commands for working with the Collatz Lean4 formalization project. These commands are automatically available in Cursor chat when you type `/`.

## How to Use Commands

1. **In Cursor chat**: Type `/` and you'll see all available commands
2. **Select a command**: Click on the command you want to use
3. **Follow instructions**: Each command provides specific guidance for the task

## Available Commands

### Planning and Execution
- **`/create-plan`** - Create comprehensive, executable plan for any complex task using full AGI capabilities
- **`/execute-plan`** - Execute a plan created by `/create-plan` with automatic progress tracking and quality assurance

### Formalization (Planned)
- **`/formalize-theorem`** - Create Lean4 formalization from informal mathematical statement
- **`/verify-proof`** - Verify Lean4 proof correctness and completeness
- **`/refactor-lean`** - Refactor Lean4 code for clarity and maintainability
- **`/build-lean`** - Build Lean4 project with comprehensive error checking

## Command Structure

Each command is a Markdown file that contains:
- **Overview**: What the command does
- **Usage**: Command syntax and examples
- **Capabilities**: Detailed features
- **Guidelines**: Best practices for this domain
- **Quality Standards**: Expected outcomes
- **Troubleshooting**: Common issues

## Universal Commands

The planning commands (`/create-plan`, `/execute-plan`) work across **all projects** in the workspace:
- **collatz-paper**: Research paper and analysis
- **collatz-lean4**: Formal theorem proving (this project)
- **agi-cursor-agent**: AGI rules system

Commands automatically detect project context and adapt to Lean4 formalization needs.

## Planning for Lean4 Work

### `/create-plan` for Formalization
When creating plans for Lean4 work, AGI automatically:
- Analyzes theorem structure and dependencies
- Identifies required lemmas and tactics
- Plans proof strategy step-by-step
- Estimates formalization effort
- Identifies potential blockers (sorry, axioms)
- Plans build and verification steps

**Example Usage**:
```
/create-plan Formalize SEDT envelope theorem in Lean4
/create-plan Prove short_epoch_bound lemma with all sorry resolved
/create-plan Refactor Collatz.SEDT module structure
```

### `/execute-plan` for Formalization
Executes formalization plans with:
- Step-by-step Lean4 code writing
- Continuous build verification
- Tactic application and proof search
- Sorry resolution tracking
- Error handling and debugging
- Quality assurance (no warnings, proper documentation)

**Example Usage**:
```
/execute-plan plans/2025-01/2025-01-15_sedt-theorem-formalization-plan.md
```

## Integration with Lean4

Commands leverage AGI capabilities for Lean4:

### Formalization Expertise
- **Lean4 Syntax**: Proper syntax and idioms
- **Tactic Usage**: Effective tactic selection (omega, linarith, simp, etc.)
- **Mathlib Integration**: Use existing theorems
- **Structure**: Clean module organization
- **Documentation**: Clear comments and docstrings

### Quality Standards
- ✅ No `sorry` in completed proofs
- ✅ No compiler warnings
- ✅ All theorems documented
- ✅ Build succeeds (`lake build`)
- ✅ Proper imports and dependencies
- ✅ Consistent naming conventions

### Common Patterns
- Bridge between ℕ and ℝ for arithmetic
- Handle boundary cases explicitly
- Use `calc` blocks for long chains
- Prefer `omega` for natural number arithmetic
- Use `linarith` for linear inequalities

## File Management

### Plan Storage
Formalization plans stored in: `plans/{YYYY-MM}/`

Naming convention: `{YYYY-MM-DD}_{HHMM}_{theorem}-formalization-plan.md`

Example: `plans/2025-01/2025-01-15_sedt-theorem-formalization-plan.md`

### Report Storage
Execution reports stored in: `reports/{YYYY-MM}/`

Naming convention: `{YYYY-MM-DD}_{HHMM}_{theorem}-formalization-execution.md`

## Integration with Paper Project

Formalization work coordinates with `collatz-paper` project:
- Validates mathematical claims in paper
- Provides formal proofs for theorems
- Identifies gaps or errors in informal proofs
- Generates machine-verified certificates

AGI automatically maintains consistency between projects.

## Best Practices for Lean4 Commands

### Before Creating Plan
- Review paper section for theorem statement
- Identify dependencies (lemmas, definitions)
- Check if similar theorems exist in codebase
- Estimate complexity (simple/moderate/complex)

### During Execution
- Trust AGI's tactic selection
- Review intermediate proof states
- Provide feedback if approach not working
- Let AGI handle sorry resolution

### After Completion
- Run full build to verify
- Check for warnings
- Review proof for clarity
- Update PROGRESS.md if major milestone

## Creating New Commands

To add Lean4-specific commands:
1. Create command in AGI project: `agi-cursor-agent/.cursor/commands/`
2. Use universal format for cross-project compatibility
3. Include Lean4-specific guidelines and examples
4. Document integration with formalization workflow
5. Update this file with new command

## Safety and Standards

- All safety rules apply (no destructive git ops)
- Follow Lean4 style guidelines
- Maintain mathematical rigor
- Document all non-trivial proofs
- Reference paper sections in comments
- Keep formalization synchronized with paper

## Notes

- Plans and reports integrate with existing project structure
- AGI adapts strategies based on Lean4 context
- Continuous learning improves formalization over time
- Commands respect Lake build system
- Mathlib4 dependencies properly managed

