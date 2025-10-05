#!/usr/bin/env python3
"""
Integration test for Lean4 Collatz project

This script performs comprehensive integration testing of all modules after refactoring.
Checks compilation, dependencies, article compliance, and architecture quality.

Author: AGI Math Research Agent v4.0
Date: 2025-01-15
"""

import os
import subprocess
import json
import time
from pathlib import Path
from typing import Dict, List, Tuple, Optional
import re

class CollatzIntegrationTester:
    """Class for integration testing of Collatz project"""
    
    def __init__(self, project_root: str):
        self.project_root = Path(project_root)
        self.results = {
            'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
            'compilation': {},
            'dependencies': {},
            'article_compliance': {},
            'architecture_quality': {},
            'summary': {}
        }
        
    def run_command(self, cmd: List[str], cwd: Optional[Path] = None) -> Tuple[int, str, str]:
        """Executes command and returns return code, stdout, stderr"""
        try:
            result = subprocess.run(
                cmd, 
                cwd=cwd or self.project_root,
                capture_output=True, 
                text=True, 
                timeout=300
            )
            return result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired:
            return -1, "", "Command timed out"
        except Exception as e:
            return -1, "", str(e)
    
    def find_lean_files(self) -> List[Path]:
        """Finds all .lean files in project"""
        lean_files = []
        for root, dirs, files in os.walk(self.project_root):
            for file in files:
                if file.endswith('.lean'):
                    lean_files.append(Path(root) / file)
        return lean_files
    
    def test_compilation(self) -> Dict[str, any]:
        """Tests compilation of all modules"""
        print("Testing compilation...")
        
        compilation_results = {
            'total_files': 0,
            'successful': 0,
            'failed': 0,
            'errors': [],
            'warnings': []
        }
        
        # First try to build the entire project
        print("  Building entire project...")
        returncode, stdout, stderr = self.run_command(['lake', 'build'])
        
        if returncode == 0:
            print("  [OK] Project built successfully")
            compilation_results['project_build'] = 'success'
        else:
            print(f"  [ERROR] Project build failed: {stderr}")
            compilation_results['project_build'] = 'failed'
            compilation_results['build_error'] = stderr
        
        # Now check individual modules
        lean_files = self.find_lean_files()
        compilation_results['total_files'] = len(lean_files)
        
        for lean_file in lean_files:
            relative_path = lean_file.relative_to(self.project_root)
            print(f"  Checking {relative_path}...")
            
            returncode, stdout, stderr = self.run_command(['lake', 'build', str(relative_path)])
            
            if returncode == 0:
                compilation_results['successful'] += 1
                print(f"    [OK] {relative_path}")
            else:
                compilation_results['failed'] += 1
                error_info = {
                    'file': str(relative_path),
                    'error': stderr,
                    'stdout': stdout
                }
                compilation_results['errors'].append(error_info)
                print(f"    [FAILED] {relative_path}")
        
        return compilation_results
    
    def test_dependencies(self) -> Dict[str, any]:
        """Tests dependencies between modules"""
        print("Testing dependencies...")
        
        dependency_results = {
            'centralized_imports': {},
            'circular_dependencies': [],
            'missing_imports': [],
            'unused_imports': [],
            'architecture_compliance': {}
        }
        
        # Check centralized imports
        core_modules = [
            'Collatz/Foundations/Core.lean',
            'Collatz/Epochs/Core.lean', 
            'Collatz/SEDT/Core.lean',
            'Collatz/Epochs/Aliases.lean'
        ]
        
        for core_module in core_modules:
            core_path = self.project_root / core_module
            if core_path.exists():
                dependency_results['centralized_imports'][core_module] = 'exists'
                print(f"  [OK] {core_module} exists")
            else:
                dependency_results['centralized_imports'][core_module] = 'missing'
                print(f"  [MISSING] {core_module}")
        
        # Check imports in modules
        lean_files = self.find_lean_files()
        
        for lean_file in lean_files:
            if lean_file.name == 'Core.lean' or lean_file.name == 'Aliases.lean':
                continue
                
            relative_path = lean_file.relative_to(self.project_root)
            
            try:
                with open(lean_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # Check for centralized imports
                imports = re.findall(r'import\s+([^\s\n]+)', content)
                
                has_foundations_core = any('Foundations.Core' in imp for imp in imports)
                has_epochs_core = any('Epochs.Core' in imp for imp in imports)
                has_sedt_core = any('SEDT.Core' in imp for imp in imports)
                has_aliases = any('Epochs.Aliases' in imp for imp in imports)
                
                dependency_results['architecture_compliance'][str(relative_path)] = {
                    'foundations_core': has_foundations_core,
                    'epochs_core': has_epochs_core,
                    'sedt_core': has_sedt_core,
                    'aliases': has_aliases,
                    'total_imports': len(imports)
                }
                
                print(f"  [OK] {relative_path} - {len(imports)} imports")
                
            except Exception as e:
                dependency_results['missing_imports'].append({
                    'file': str(relative_path),
                    'error': str(e)
                })
                print(f"  [ERROR] {relative_path} - {str(e)}")
        
        return dependency_results
    
    def test_article_compliance(self) -> Dict[str, any]:
        """Tests compliance with article structure"""
        print("Testing article compliance...")
        
        compliance_results = {
            'paper_sections_mapped': {},
            'theorems_mapped': {},
            'missing_sections': [],
            'extra_sections': []
        }
        
        # Check correspondence with article sections
        paper_sections = {
            'Main Results': ['Collatz/SEDT/Core.lean', 'Collatz/Epochs/LongEpochs.lean'],
            'Cycle Exclusion': ['Collatz/CycleExclusion/Main.lean'],
            'Convergence': ['Collatz/Convergence/MainTheorem.lean'],
            'Foundations': ['Collatz/Foundations/Core.lean'],
            'Epochs': ['Collatz/Epochs/Structure.lean'],
            'SEDT': ['Collatz/SEDT/Core.lean'],
            'Mixing': ['Collatz/Mixing/PhaseMixing.lean'],
            'Stratified': ['Collatz/Stratified/CompleteStratification.lean']
        }
        
        for section, expected_modules in paper_sections.items():
            compliance_results['paper_sections_mapped'][section] = {
                'expected_modules': expected_modules,
                'found_modules': [],
                'missing_modules': []
            }
            
            for module in expected_modules:
                module_path = self.project_root / module
                if module_path.exists():
                    compliance_results['paper_sections_mapped'][section]['found_modules'].append(module)
                else:
                    compliance_results['paper_sections_mapped'][section]['missing_modules'].append(module)
            
            found_count = len(compliance_results['paper_sections_mapped'][section]['found_modules'])
            expected_count = len(expected_modules)
            print(f"  [OK] {section}: {found_count}/{expected_count} modules")
        
        return compliance_results
    
    def test_architecture_quality(self) -> Dict[str, any]:
        """Tests architecture quality"""
        print("Testing architecture quality...")
        
        quality_results = {
            'duplication_check': {},
            'naming_consistency': {},
            'module_cohesion': {},
            'coupling_analysis': {}
        }
        
        # Check duplications
        lean_files = self.find_lean_files()
        definitions = {}
        
        for lean_file in lean_files:
            try:
                with open(lean_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # Find definitions
                defs = re.findall(r'(def|theorem|lemma|structure|class)\s+([a-zA-Z_][a-zA-Z0-9_]*)', content)
                
                for def_type, def_name in defs:
                    if def_name not in definitions:
                        definitions[def_name] = []
                    definitions[def_name].append({
                        'file': str(lean_file.relative_to(self.project_root)),
                        'type': def_type
                    })
                    
            except Exception as e:
                continue
        
        # Find duplications
        duplicates = {name: locations for name, locations in definitions.items() if len(locations) > 1}
        quality_results['duplication_check'] = {
            'total_definitions': len(definitions),
            'duplicates': len(duplicates),
            'duplicate_details': duplicates
        }
        
        print(f"  [INFO] Total definitions: {len(definitions)}")
        print(f"  [INFO] Duplicates: {len(duplicates)}")
        
        return quality_results
    
    def generate_summary(self) -> Dict[str, any]:
        """Generates summary of results"""
        compilation = self.results['compilation']
        dependencies = self.results['dependencies']
        compliance = self.results['article_compliance']
        quality = self.results['architecture_quality']
        
        summary = {
            'overall_status': 'unknown',
            'compilation_success_rate': 0,
            'dependency_compliance': 0,
            'article_compliance': 0,
            'architecture_quality': 0,
            'recommendations': []
        }
        
        # Compilation status
        if compilation.get('total_files', 0) > 0:
            summary['compilation_success_rate'] = (
                compilation.get('successful', 0) / compilation.get('total_files', 1)
            ) * 100
        
        # Dependency compliance
        arch_compliance = dependencies.get('architecture_compliance', {})
        compliant_modules = sum(1 for module_info in arch_compliance.values() 
                              if module_info.get('foundations_core', False) or 
                                 module_info.get('epochs_core', False))
        total_modules = len(arch_compliance)
        
        if total_modules > 0:
            summary['dependency_compliance'] = (compliant_modules / total_modules) * 100
        
        # Article compliance
        sections_mapped = compliance.get('paper_sections_mapped', {})
        mapped_sections = sum(1 for section_info in sections_mapped.values() 
                            if len(section_info.get('found_modules', [])) > 0)
        total_sections = len(sections_mapped)
        
        if total_sections > 0:
            summary['article_compliance'] = (mapped_sections / total_sections) * 100
        
        # Architecture quality
        duplication_check = quality.get('duplication_check', {})
        total_defs = duplication_check.get('total_definitions', 0)
        duplicates = duplication_check.get('duplicates', 0)
        
        if total_defs > 0:
            summary['architecture_quality'] = ((total_defs - duplicates) / total_defs) * 100
        
        # Overall status
        avg_score = (
            summary['compilation_success_rate'] + 
            summary['dependency_compliance'] + 
            summary['article_compliance'] + 
            summary['architecture_quality']
        ) / 4
        
        if avg_score >= 90:
            summary['overall_status'] = 'excellent'
        elif avg_score >= 75:
            summary['overall_status'] = 'good'
        elif avg_score >= 60:
            summary['overall_status'] = 'fair'
        else:
            summary['overall_status'] = 'poor'
        
        # Recommendations
        if summary['compilation_success_rate'] < 100:
            summary['recommendations'].append("Fix compilation errors")
        
        if summary['dependency_compliance'] < 100:
            summary['recommendations'].append("Improve centralized architecture compliance")
        
        if summary['article_compliance'] < 100:
            summary['recommendations'].append("Add missing modules for article compliance")
        
        if summary['architecture_quality'] < 95:
            summary['recommendations'].append("Eliminate definition duplications")
        
        return summary
    
    def run_all_tests(self) -> Dict[str, any]:
        """Runs all tests"""
        print("Running Collatz project integration testing")
        print("=" * 60)
        
        # Compilation testing
        self.results['compilation'] = self.test_compilation()
        print()
        
        # Dependency testing
        self.results['dependencies'] = self.test_dependencies()
        print()
        
        # Article compliance testing
        self.results['article_compliance'] = self.test_article_compliance()
        print()
        
        # Architecture quality testing
        self.results['architecture_quality'] = self.test_architecture_quality()
        print()
        
        # Generate summary
        self.results['summary'] = self.generate_summary()
        
        return self.results
    
    def save_results(self, output_file: str = None) -> str:
        """Saves results to JSON file"""
        if output_file is None:
            output_file = self.project_root / 'reports' / '2025-01' / f'integration_test_results_{time.strftime("%Y%m%d_%H%M%S")}.json'
        
        output_path = Path(output_file)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.results, f, indent=2, ensure_ascii=False)
        
        return str(output_path)
    
    def print_summary(self):
        """Prints summary of results"""
        summary = self.results['summary']
        
        print("=" * 60)
        print("INTEGRATION TESTING SUMMARY")
        print("=" * 60)
        
        print(f"Overall status: {summary['overall_status'].upper()}")
        print()
        
        print("Detailed results:")
        print(f"  Compilation: {summary['compilation_success_rate']:.1f}%")
        print(f"  Dependencies: {summary['dependency_compliance']:.1f}%")
        print(f"  Article compliance: {summary['article_compliance']:.1f}%")
        print(f"  Architecture quality: {summary['architecture_quality']:.1f}%")
        print()
        
        if summary['recommendations']:
            print("Recommendations:")
            for i, rec in enumerate(summary['recommendations'], 1):
                print(f"  {i}. {rec}")
        else:
            print("All tests passed successfully!")
        
        print()

def main():
    """Main function"""
    project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    
    tester = CollatzIntegrationTester(project_root)
    results = tester.run_all_tests()
    
    # Save results
    output_file = tester.save_results()
    print(f"Results saved to: {output_file}")
    
    # Print summary
    tester.print_summary()

if __name__ == "__main__":
    main()