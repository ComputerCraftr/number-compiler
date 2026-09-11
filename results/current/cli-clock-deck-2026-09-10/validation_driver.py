import hashlib
import json
from pathlib import Path
import subprocess
import sys
import xml.etree.ElementTree as ET

from devtools.checks.test_run_evidence import source_fingerprint

root=Path.cwd()
out=root/'results/current/cli-clock-deck-2026-09-10/final2'
out.mkdir(exist_ok=True)
frozen=source_fingerprint(root)
theory=root/'devtools/proofs/isabelle/Port_Valued_Mealy.thy'
theory_sha=hashlib.sha256(theory.read_bytes()).hexdigest()
assert theory_sha=='ec03d370c780df87560726d2dcfece458a5fecfeb53f65da294894d21c71c0d8'
manifest={'source_fingerprint':frozen,'theory_sha256':theory_sha,'jobs':[]}
(out/'source-freeze.json').write_text(json.dumps(manifest,indent=2)+'\n')
pytest=[sys.executable,'-m','pytest','-q','-m','validation or not validation']
jobs=[
 ('cli',pytest+['tests/api/test_cli_render_paths.py','tests/api/test_cli_adversarial.py']),
 ('api',pytest+['tests/api/test_number_api.py','tests/api/test_nonbinary_collatz_boundary.py','tests/api/test_fast_path_cutover.py']),
 ('owners',pytest+['tests/arithmetic/carry/test_jet_cylinder.py','tests/arithmetic/carry/test_carry_monoid.py','tests/sequences/collatz/test_harmonic_ports.py']),
 ('decimal-research',pytest+['tests/validation/proofs/reverse_add/test_decimal_clock_cylinder_audit.py']),
 ('power-research',pytest+['tests/validation/research/power_numbers/test_square_consumer_congruence.py']),
 ('policy',pytest+['tests/repository/test_repository_policy.py','tests/repository/test_proof_production_boundary.py']),
 ('mypy',[sys.executable,'-m','mypy','src','devtools','tests']),
 ('measurement',[sys.executable,'results/current/cli-clock-deck-2026-09-10/measurement.py']),
 ('public-cache',[sys.executable,'-m','devtools.benchmarks.clock_key_growth_probe']),
]
jobs.sort(key=lambda item: 0 if item[0] == 'mypy' else 1 if item[0] == 'measurement' else 2)
for name,command in jobs:
 print(name,flush=True)
 if 'pytest' in command:
  command += ['--junitxml',str(out/f'{name}.junit.xml')]
 output=out/(name+('.log' if 'pytest' in command or name=='mypy' else '.json'))
 guard=out/f'{name}.guard.json'
 subprocess.run([sys.executable,'-m','devtools.checks.process_guard','--output',str(output),'--report',str(guard),'--',*command],check=True)
 assert source_fingerprint(root)==frozen
 row={'name':name,'command':command,'guard':json.loads(guard.read_text())}
 if 'pytest' in command:
  cases=ET.parse(out/f'{name}.junit.xml').findall('.//testcase')
  assert all(c.find('failure') is None and c.find('error') is None and c.find('skipped') is None for c in cases)
  row['passed_tests']=len(cases)
 manifest['jobs'].append(row)
 (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('All frozen guarded jobs verified.',flush=True)
