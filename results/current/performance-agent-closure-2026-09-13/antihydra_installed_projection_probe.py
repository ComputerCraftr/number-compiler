import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path.cwd()))
from devtools.benchmarks.cli_startup import _install

probe = """
import contextlib,io,json
from time import perf_counter
from number_compiler.api.cli import main
from number_compiler.sequences.antihydra.observers import SpaceTimeProjection
original=SpaceTimeProjection.evaluate
calls=[]
def measured(self):
    value=original(self)
    calls.append(dict(self.result.ledger.counters))
    return value
SpaceTimeProjection.evaluate=measured
rows=[]
for trial in range(5):
    stdout,stderr=io.StringIO(),io.StringIO()
    start=perf_counter()
    with contextlib.redirect_stdout(stdout),contextlib.redirect_stderr(stderr):
        status=main(['antihydra','--nth','2048','--no-value','--info','spacetime','--modulus','3','--format','json'])
    if status or stderr.getvalue(): raise AssertionError((status,stderr.getvalue()))
    packet=json.loads(stdout.getvalue())
    rows.append({'seconds':perf_counter()-start,'packet':packet,'work':calls[-1]})
if len(calls)!=5: raise AssertionError('CLI did not consume one projection per request')
print(json.dumps({'trials':rows,'projection_calls':len(calls)}))
"""
env = dict(os.environ)
env.pop("PYTHONPATH", None)
env.pop("MYPYPATH", None)
reports = {}
with tempfile.TemporaryDirectory(prefix="antihydra-installed-projection-") as directory:
    work = Path(directory)
    for name, wheel in [
        (
            "baseline",
            "/tmp/prime-source-wheels-owned/number_compiler-0.59.9-py3-none-any.whl",
        ),
        (
            "candidate",
            "/tmp/performance-agent-final-wheel/number_compiler-0.59.9-py3-none-any.whl",
        ),
    ]:
        python = _install(Path(wheel), work / name, env)
        p = subprocess.run(
            [str(python), "-I", "-c", probe],
            cwd=work,
            env=env,
            capture_output=True,
            text=True,
            check=True,
            timeout=15,
        )
        reports[name] = json.loads(p.stdout)
values = []
for report in reports.values():
    for row in report["trials"]:
        value = dict(row["packet"]["info"]["spacetime"]["value"])
        # This field counts sampled implementation sweeps, not a semantic lane.
        value.pop("sampled_sweep_classes")
        values.append(value)
if any(value != values[0] for value in values):
    raise AssertionError("CLI spacetime semantics differ")
print(json.dumps({"reports": reports, "semantic_match": True}))
