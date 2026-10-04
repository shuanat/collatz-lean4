# SMT Solver Integration for Historical SEDT Checks

This directory contains standalone scripts for numerical cross-checks related to
the older SEDT-axiom closure phase.

These scripts are **not** part of the current Lean production proof chain.
Treat them as experimental or historical support tooling.

## 📁 Structure

```
smt/
├── README.md                 # This file
├── INSTALL.md                # Optional solver installation notes
├── verify_z3.py              # Run Z3 verification
├── axioms/                   # SMT-LIB2 files for historical checks
│   ├── t_log_bound.smt2
│   ├── overhead_bound.smt2
│   └── ...
└── results/                  # Verification results
    └── verification_report.json
```

## Status

- current source of truth for the formal development is `Collatz/SEDT/*.lean`
- the names in this folder still reflect the older "axioms" phase
- production build does not depend on anything in `scripts/smt/`

## 🎯 Supported Checks

### Priority 0 (Arithmetic only)

- ✅ `t_log_bound_for_sedt`
- ✅ `sedt_overhead_bound`

### Priority 1 (Requires structure modeling)

- ⏳ `SEDTEpoch_head_overhead_bounded`
- ⏳ `SEDTEpoch_boundary_overhead_bounded`

### Priority 2 (Complex / dependent)

- ⏳ `sedt_full_bound_technical`
- ⏳ `sedt_bound_negative_for_very_long_epochs`

## 🚀 Usage

### Prerequisites

```bash
# Install Z3
# Windows: choco install z3
# macOS: brew install z3
# Linux: sudo apt-get install z3

# Install Python dependencies
pip install pysmt z3-solver
```

### Run Verification

```bash
# Verify with Z3
python verify_z3.py

# View results
python -m json.tool results/verification_report.json
```

## 📊 Expected Results

Each verification produces:

- **UNSAT**: Axiom holds (no counterexample found)
- **SAT**: Counterexample found (axiom may be incorrect!)
- **UNKNOWN**: Solver timeout or undecidable

## 🔧 Technical Notes

### SMT-LIB2 Logics

- `QF_NRA`: Quantifier-Free Nonlinear Real Arithmetic
- `QF_LRA`: Quantifier-Free Linear Real Arithmetic
- `QF_NIA`: Quantifier-Free Nonlinear Integer Arithmetic

### Approximations

For transcendental functions:

- `log(3/2) ≈ 0.4055`
- `log(3/2)/log(2) ≈ 0.585`

We use Taylor series or rational approximations for SMT encoding.

### Timeouts

- Z3: 30 seconds per query

## 📝 Adding New Checks

1. Add or update an SMT-LIB2 file in `axioms/`
2. Run `python verify_z3.py`
3. Document workflow changes and limitations here

## 🔗 References

- [Z3 Guide](https://github.com/Z3Prover/z3/wiki)
- [CVC5 Documentation](https://cvc5.github.io/)
- [SMT-LIB Standard](http://smtlib.cs.uiowa.edu/)

---

Historical material from October 2025; reviewed and trimmed during Markdown
cleanup in April 2026.
