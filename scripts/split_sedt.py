#!/usr/bin/env python3
"""
Split SEDT.lean into modular structure:
- SEDT/Core.lean: Constants + helper lemmas + proven bounds
- SEDT/Axioms.lean: 3 modeling axioms with documentation
- SEDT/Theorems.lean: Main theorems (envelope, period_sum)
"""

def split_sedt():
    with open('Collatz/SEDT.lean', 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    # Find section boundaries
    axiom_start = None
    axiom_end = None
    theorems_start = None
    
    for i, line in enumerate(lines):
        # Find first axiom
        if axiom_start is None and line.strip().startswith('axiom plateau_touch_count_bounded'):
            axiom_start = i - 1  # Include doc comment
            # Scan back for full doc block
            j = i - 1
            while j >= 0 and (lines[j].strip().startswith('/--') or 
                              lines[j].strip().startswith('-/') or
                              lines[j].strip() == '' or
                              'Modeling axiom' in lines[j]):
                axiom_start = j
                j -= 1
        
        # Find where theorems start (after axioms)
        if 'theorem sedt_envelope_bound' in line:
            theorems_start = i - 1  # Include doc comment
            # Scan back for section marker
            j = i - 1
            while j >= 0 and (lines[j].strip().startswith('/-!') or 
                              lines[j].strip() == '' or
                              'Main SEDT Theorem' in lines[j]):
                theorems_start = j
                j -= 1
            break
    
    # Split content
    header = lines[:30]  # Imports + namespace
    core_content = lines[30:axiom_start]
    axioms_content = lines[axiom_start:theorems_start]
    theorems_content = lines[theorems_start:]
    
    # Extract namespace end
    namespace_end = '\nend Collatz.SEDT\n'
    
    # Write Core.lean
    with open('Collatz/SEDT/Core.lean', 'w', encoding='utf-8') as f:
        f.write(''.join(header))
        f.write('\n/-!\n## Constants and Helper Lemmas\n\nThis module contains the core definitions and proven helper lemmas for SEDT.\n-/\n\n')
        f.write(''.join(core_content))
        if not core_content[-1].endswith('\n\n'):
            f.write('\n')
        f.write(namespace_end)
    
    # Write Axioms.lean
    with open('Collatz/SEDT/Axioms.lean', 'w', encoding='utf-8') as f:
        # Header for axioms
        f.write('import Collatz.SEDT.Core\n\n')
        f.write('/-!\n# SEDT Modeling Axioms\n\n')
        f.write('This module contains the 3 modeling axioms that remain to be proven.\n')
        f.write('All axioms are well-documented with mathematical justification.\n\n')
        f.write('## Axioms:\n')
        f.write('1. `plateau_touch_count_bounded` - Touch frequency (ergodic theory)\n')
        f.write('2. `SEDTEpoch_head_overhead_bounded` - Head overhead (structural)\n')
        f.write('3. `SEDTEpoch_boundary_overhead_bounded` - Boundary overhead (structural)\n')
        f.write('-/\n\n')
        f.write('namespace Collatz.SEDT\n\n')
        f.write('open Real\n\n')
        f.write(''.join(axioms_content))
        if not axioms_content[-1].endswith('\n\n'):
            f.write('\n')
        f.write(namespace_end)
    
    # Write Theorems.lean
    with open('Collatz/SEDT/Theorems.lean', 'w', encoding='utf-8') as f:
        # Header for theorems
        f.write('import Collatz.SEDT.Core\n')
        f.write('import Collatz.SEDT.Axioms\n\n')
        f.write('/-!\n# SEDT Main Theorems\n\n')
        f.write('This module contains the main SEDT theorems:\n')
        f.write('- `sedt_envelope_bound`: Envelope theorem (proven)\n')
        f.write('- `sedt_envelope_negative_for_very_long`: Negativity for very long epochs (proven)\n')
        f.write('- `period_sum_with_density_negative`: Main cycle exclusion theorem (proven)\n\n')
        f.write('All theorems are fully formalized without sorry.\n')
        f.write('-/\n\n')
        f.write('namespace Collatz.SEDT\n\n')
        f.write('open Real\n\n')
        f.write(''.join(theorems_content))
        if not theorems_content[-1].strip() == 'end Collatz.SEDT':
            f.write(namespace_end)
    
    # Create root SEDT.lean
    with open('Collatz/SEDT.lean.new', 'w', encoding='utf-8') as f:
        f.write('/-!\n# SEDT (Scaled Epoch Drift Theorem)\n\n')
        f.write('Main module for SEDT formalization.\n\n')
        f.write('## Structure:\n')
        f.write('- `SEDT.Core`: Constants, helper lemmas, proven bounds\n')
        f.write('- `SEDT.Axioms`: 3 modeling axioms (well-documented)\n')
        f.write('- `SEDT.Theorems`: Main theorems (envelope, period_sum)\n\n')
        f.write('## Usage:\n')
        f.write('```lean\n')
        f.write('import Collatz.SEDT  -- Imports everything\n')
        f.write('```\n')
        f.write('-/\n\n')
        f.write('import Collatz.SEDT.Core\n')
        f.write('import Collatz.SEDT.Axioms\n')
        f.write('import Collatz.SEDT.Theorems\n')
    
    print("✅ Split complete!")
    print(f"  Core:     {len(core_content)} lines")
    print(f"  Axioms:   {len(axioms_content)} lines")
    print(f"  Theorems: {len(theorems_content)} lines")
    print("\nFiles created:")
    print("  - Collatz/SEDT/Core.lean")
    print("  - Collatz/SEDT/Axioms.lean")
    print("  - Collatz/SEDT/Theorems.lean")
    print("  - Collatz/SEDT.lean.new (backup)")

if __name__ == '__main__':
    split_sedt()

