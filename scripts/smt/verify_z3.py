#!/usr/bin/env python3
"""
SMT Verification using Z3 for SEDT Axioms

This script verifies numerical axioms from Collatz/SEDT.lean by:
1. Loading SMT-LIB2 files from axioms/
2. Running Z3 solver on each file
3. Collecting results (UNSAT = axiom holds, SAT = counterexample)
4. Generating JSON report

Usage:
    python verify_z3.py                  # Verify all axioms
    python verify_z3.py t_log_bound      # Verify specific axiom
"""

import subprocess
import json
import time
from pathlib import Path
from typing import Dict, List, Optional
import sys

# ==== Configuration ====

AXIOMS_DIR = Path(__file__).parent / "axioms"
RESULTS_DIR = Path(__file__).parent / "results"
Z3_TIMEOUT_MS = 30000  # 30 seconds

# ==== Z3 Verification ====

def verify_with_z3(smt_file: Path, timeout_ms: int = Z3_TIMEOUT_MS) -> Dict:
    """
    Run Z3 on SMT-LIB2 file and parse result.
    
    Returns:
        dict with keys:
            - solver: "Z3"
            - file: filename
            - result: "UNSAT" | "SAT" | "UNKNOWN" | "ERROR"
            - time_ms: solving time in milliseconds
            - model: counterexample model (if SAT)
            - error: error message (if ERROR)
    """
    print(f"  Running Z3 on {smt_file.name}...", end=" ", flush=True)
    
    start_time = time.time()
    
    try:
        cmd = [
            "z3",
            "-smt2",
            str(smt_file),
            f"-T:{timeout_ms // 1000}",  # Z3 timeout in seconds
        ]
        
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=(timeout_ms // 1000) + 5  # Python timeout > Z3 timeout
        )
        
        elapsed_ms = int((time.time() - start_time) * 1000)
        
        stdout = result.stdout.strip()
        stderr = result.stderr.strip()
        
        # Parse result
        if "unsat" in stdout.lower():
            print("[OK] UNSAT (axiom holds)")
            return {
                "solver": "Z3",
                "file": smt_file.name,
                "result": "UNSAT",
                "time_ms": elapsed_ms,
                "model": None,
                "error": None
            }
        elif "sat" in stdout.lower() and "unsat" not in stdout.lower():
            # Extract model
            model = extract_model(stdout)
            print("[FAIL] SAT (counterexample found!)")
            return {
                "solver": "Z3",
                "file": smt_file.name,
                "result": "SAT",
                "time_ms": elapsed_ms,
                "model": model,
                "error": None
            }
        elif "unknown" in stdout.lower():
            print("[WARN] UNKNOWN (timeout or undecidable)")
            return {
                "solver": "Z3",
                "file": smt_file.name,
                "result": "UNKNOWN",
                "time_ms": elapsed_ms,
                "model": None,
                "error": stderr if stderr else "Z3 returned UNKNOWN"
            }
        else:
            print("[WARN] UNKNOWN (unexpected output)")
            return {
                "solver": "Z3",
                "file": smt_file.name,
                "result": "UNKNOWN",
                "time_ms": elapsed_ms,
                "model": None,
                "error": f"Unexpected output: {stdout[:200]}"
            }
            
    except subprocess.TimeoutExpired:
        elapsed_ms = timeout_ms
        print(f"[WARN] TIMEOUT ({timeout_ms/1000}s)")
        return {
            "solver": "Z3",
            "file": smt_file.name,
            "result": "TIMEOUT",
            "time_ms": elapsed_ms,
            "model": None,
            "error": f"Timeout after {timeout_ms}ms"
        }
    except FileNotFoundError:
        print("[ERROR] Z3 not found")
        return {
            "solver": "Z3",
            "file": smt_file.name,
            "result": "ERROR",
            "time_ms": 0,
            "model": None,
            "error": "Z3 not found. Please install Z3: https://github.com/Z3Prover/z3"
        }
    except Exception as e:
        print(f"[ERROR] {str(e)}")
        return {
            "solver": "Z3",
            "file": smt_file.name,
            "result": "ERROR",
            "time_ms": 0,
            "model": None,
            "error": str(e)
        }

def extract_model(stdout: str) -> Optional[Dict]:
    """
    Extract counterexample model from Z3 output.
    
    Format:
        (model
          (define-fun t () Real 3.0)
          (define-fun U () Real 1.0)
          ...
        )
    """
    if "(model" not in stdout:
        return None
    
    model = {}
    lines = stdout.split('\n')
    
    for line in lines:
        line = line.strip()
        if "define-fun" in line:
            # Parse: (define-fun t () Real 3.0)
            try:
                parts = line.split()
                if len(parts) >= 5:
                    var_name = parts[1]
                    value_str = parts[-1].rstrip(')')
                    # Try to parse as number
                    try:
                        value = float(value_str)
                        model[var_name] = value
                    except ValueError:
                        model[var_name] = value_str
            except:
                continue
    
    return model if model else None

# ==== Main Verification ====

def verify_axiom(axiom_name: str) -> Dict:
    """Verify a single axiom by name (without .smt2 extension)."""
    smt_file = AXIOMS_DIR / f"{axiom_name}.smt2"
    
    if not smt_file.exists():
        print(f"[ERROR] {smt_file} not found")
        return {
            "solver": "Z3",
            "file": f"{axiom_name}.smt2",
            "result": "ERROR",
            "time_ms": 0,
            "model": None,
            "error": f"File not found: {smt_file}"
        }
    
    return verify_with_z3(smt_file)

def verify_all() -> List[Dict]:
    """Verify all axioms in axioms/ directory."""
    smt_files = sorted(AXIOMS_DIR.glob("*.smt2"))
    
    if not smt_files:
        print("[WARN] No SMT files found in axioms/")
        return []
    
    print(f"Found {len(smt_files)} axiom(s) to verify:\n")
    
    results = []
    for smt_file in smt_files:
        result = verify_with_z3(smt_file)
        results.append(result)
    
    return results

def save_report(results: List[Dict]):
    """Save verification results to JSON report."""
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    
    report = {
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
        "solver": "Z3",
        "total_axioms": len(results),
        "results": results,
        "summary": {
            "UNSAT": sum(1 for r in results if r["result"] == "UNSAT"),
            "SAT": sum(1 for r in results if r["result"] == "SAT"),
            "UNKNOWN": sum(1 for r in results if r["result"] == "UNKNOWN"),
            "TIMEOUT": sum(1 for r in results if r["result"] == "TIMEOUT"),
            "ERROR": sum(1 for r in results if r["result"] == "ERROR"),
        }
    }
    
    report_file = RESULTS_DIR / "verification_report_z3.json"
    report_file.write_text(json.dumps(report, indent=2))
    
    print(f"\nReport saved to: {report_file}")
    return report

def print_summary(report: Dict):
    """Print summary statistics."""
    summary = report["summary"]
    total = report["total_axioms"]
    
    print("\n" + "="*60)
    print("VERIFICATION SUMMARY")
    print("="*60)
    print(f"Total axioms:     {total}")
    print(f"  [OK] UNSAT:     {summary['UNSAT']} (axiom holds)")
    print(f"  [FAIL] SAT:     {summary['SAT']} (counterexample found)")
    print(f"  [WARN] UNKNOWN: {summary['UNKNOWN']} (undecidable)")
    print(f"  [WARN] TIMEOUT: {summary['TIMEOUT']} (exceeded time limit)")
    print(f"  [ERROR] ERROR:  {summary['ERROR']} (verification error)")
    print("="*60)
    
    # Detailed counterexamples
    if summary['SAT'] > 0:
        print("\n[WARNING] COUNTEREXAMPLES FOUND:")
        for result in report["results"]:
            if result["result"] == "SAT":
                print(f"\n  File: {result['file']}")
                print(f"  Model: {result['model']}")

# ==== CLI ====

def main():
    """Main entry point."""
    print("="*60)
    print("SMT Verification for SEDT Axioms (Z3)")
    print("="*60)
    print()
    
    # Parse arguments
    if len(sys.argv) > 1:
        # Verify specific axiom
        axiom_name = sys.argv[1].replace(".smt2", "")
        print(f"Verifying axiom: {axiom_name}\n")
        result = verify_axiom(axiom_name)
        results = [result]
    else:
        # Verify all axioms
        print("Verifying all axioms...\n")
        results = verify_all()
    
    # Save and print report
    if results:
        report = save_report(results)
        print_summary(report)
        
        # Exit code: 0 if all UNSAT, 1 if any SAT/ERROR
        if report["summary"]["SAT"] > 0 or report["summary"]["ERROR"] > 0:
            sys.exit(1)
        else:
            sys.exit(0)
    else:
        print("⚠️ No verification results")
        sys.exit(1)

if __name__ == "__main__":
    main()

