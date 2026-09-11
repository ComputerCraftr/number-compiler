import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import xml.etree.ElementTree as ET
from devtools.checks.test_run_evidence import source_fingerprint

root=Path.cwd()
out=root/'results/current/clock-coordinate-growth-2026-09-10/final'
out.mkdir(exist_ok=True)
frozen=source_fingerprint(root)
manifest={'source_fingerprint':frozen,'theories':{},'jobs':[]}
for p in sorted((root/'devtools/proofs/isabelle/temporal_clocks').glob('*.thy')):
    manifest['theories'][str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(out/'source-freeze.json').write_text(json.dumps(manifest,indent=2)+'\n')
pytest=[sys.executable,'-m','pytest','-q','-m','validation or not validation']
jobs=[
 ('isabelle',['/Applications/Isabelle2025-2.app/bin/isabelle','build','-v','-c','-d','devtools/proofs/isabelle','Temporal_Clock_Jumps']),
 ('focused',pytest+[
   'tests/sequences/collatz/test_inverse_three_clock.py',
   'tests/sequences/collatz/test_hensel_occurrence.py',
   'tests/sequences/power_numbers/test_two_primary_clock.py',
   'tests/validation/research/power_numbers/test_two_primary_phase_clock.py',
   'tests/validation/proofs/test_special_power_monoid.py',
   'tests/validation/research/algebra/test_decimal_root_tangent.py',
   'tests/validation/proofs/test_temporal_clock_jumps.py',
   'tests/arithmetic/carry/test_jet_cylinder.py',
   'tests/arithmetic/formula/test_event_memory.py']),
 ('decimal-audit',[sys.executable,'-m','devtools.proofs.decimal_root_tangent_audit']),
 ('collatz-audit',[sys.executable,'-m','devtools.proofs.collatz_inverse_three_clock_probe']),
 ('power-audit',[sys.executable,'-m','devtools.benchmarks.two_primary_phase_clock_probe']),
 ('public-cache',[sys.executable,'-m','devtools.benchmarks.clock_key_growth_probe']),
 ('policy-structural',pytest+['tests/repository/test_repository_policy.py']),
 ('policy-boundary',pytest+['tests/repository/test_proof_production_boundary.py']),
 ('mypy',[sys.executable,'-m','mypy','src','devtools','tests']),
 ('ruff',[sys.executable,'-m','ruff','check','src','devtools','tests']),
]
env=dict(os.environ,ISABELLE_IDENTIFIER='number-compiler-ports-proof')
jobs.sort(key=lambda item: 0 if item[0] == 'mypy' else 1)
prior_manifest = out/'manifest.json'
if prior_manifest.exists():
    prior = json.loads(prior_manifest.read_text())
    assert prior['source_fingerprint'] == frozen
    assert prior['theories'] == manifest['theories']
    manifest = prior
completed = {row['name'] for row in manifest['jobs']}
for name,command in jobs:
    if name in completed:
        continue
    print(name,flush=True)
    if 'pytest' in command:
        command+=['--junitxml',str(out/f'{name}.junit.xml')]
    output=out/f'{name}.json' if name.endswith('-audit') or name=='public-cache' else out/f'{name}.log'
    guard=out/f'{name}.guard.json'
    subprocess.run([sys.executable,'-m','devtools.checks.process_guard','--output',str(output),'--report',str(guard),'--',*command],env=env,check=True)
    assert source_fingerprint(root)==frozen
    row={'name':name,'command':command,'guard':json.loads(guard.read_text())}
    if 'pytest' in command:
        cases=ET.parse(out/f'{name}.junit.xml').findall('.//testcase')
        assert all(c.find('failure') is None and c.find('error') is None and c.find('skipped') is None for c in cases)
        row['passed_tests']=len(cases)
    manifest['jobs'].append(row)
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('All frozen guarded jobs verified.',flush=True)
