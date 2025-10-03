# SMT Solver Integration for SEDT Axioms

This directory contains scripts and files for verifying numerical axioms from `Collatz/SEDT.lean` using Z3 and CVC5 SMT solvers.

## 📁 Structure

```
smt/
├── README.md                 # This file
├── export_axioms.py          # Export Lean axioms to SMT-LIB2
├── verify_z3.py              # Run Z3 verification
├── verify_cvc5.py            # Run CVC5 verification (cross-check)
├── axioms/                   # SMT-LIB2 files for each axiom
│   ├── t_log_bound.smt2
│   ├── overhead_bound.smt2
│   └── ...
└── results/                  # Verification results
    └── verification_report.json
```

## 🎯 Supported Axioms

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
# Export axioms to SMT-LIB2
python export_axioms.py

# Verify with Z3
python verify_z3.py

# Cross-check with CVC5 (if installed)
python verify_cvc5.py

# View results
cat results/verification_report.json
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
- CVC5: 30 seconds per query

## 📝 Adding New Axioms

1. Add SMT-LIB2 file to `axioms/`
2. Update `export_axioms.py` with export function
3. Run verification
4. Document results

## 🔗 References

- [Z3 Guide](https://github.com/Z3Prover/z3/wiki)
- [CVC5 Documentation](https://cvc5.github.io/)
- [SMT-LIB Standard](http://smtlib.cs.uiowa.edu/)

---

**Last Updated:** October 3, 2025

