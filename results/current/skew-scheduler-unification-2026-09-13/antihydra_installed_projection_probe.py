from pathlib import Path
import contextlib
import json
import os
import statistics
import sys
import tempfile
import subprocess

sys.path.insert(0, str(Path.cwd()))
from devtools.benchmarks.cli_startup import _install

probe = """
import contextlib,io,json,sys
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
for trial in range(5):
    if sys.stdin.readline().strip() != 'run': raise RuntimeError('missing paired request')
    stdout,stderr=io.StringIO(),io.StringIO()
    start=perf_counter()
    with contextlib.redirect_stdout(stdout),contextlib.redirect_stderr(stderr):
        status=main(['antihydra','--nth','2048','--no-value','--info','spacetime','--modulus','3','--format','json'])
    elapsed=perf_counter()-start
    if status or stderr.getvalue(): raise AssertionError((status,stderr.getvalue()))
    packet=json.loads(stdout.getvalue())
    print(json.dumps({'seconds':elapsed,'packet':packet,'work':calls[-1]}),flush=True)
if len(calls)!=5: raise AssertionError('CLI did not consume one projection per request')
"""
env = dict(os.environ)
env.pop("PYTHONPATH", None)
env.pop("MYPYPATH", None)
reports = {"baseline": [], "candidate": []}
with tempfile.TemporaryDirectory(prefix="skew-antihydra-installed-") as directory:
    work = Path(directory)
    interpreters = {
        name: _install(Path(wheel), work / name, env)
        for name, wheel in [
            (
                "baseline",
                "/tmp/performance-agent-final-wheel/number_compiler-0.59.9-py3-none-any.whl",
            ),
            (
                "candidate",
                "/tmp/skew-unification-final-wheel-5/number_compiler-0.59.9-py3-none-any.whl",
            ),
        ]
    }
    with contextlib.ExitStack() as stack:
        children = {
            name: stack.enter_context(
                subprocess.Popen(
                    [str(py), "-I", "-c", probe],
                    cwd=work,
                    env=env,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                )
            )
            for name, py in interpreters.items()
        }
        for trial in range(5):
            order = tuple(children) if trial % 2 == 0 else tuple(reversed(children))
            for name in order:
                child = children[name]
                child.stdin.write("run\n")
                child.stdin.flush()
                line = child.stdout.readline()
                if not line:
                    raise RuntimeError((name, child.stderr.read()))
                reports[name].append(json.loads(line))
        for child in children.values():
            if child.wait(timeout=5):
                raise RuntimeError(child.stderr.read())
values = []
for rows in reports.values():
    for row in rows:
        value = dict(row["packet"]["info"]["spacetime"]["value"])
        value.pop("sampled_sweep_classes")
        values.append(value)
if any(value != values[0] for value in values):
    raise AssertionError("CLI spacetime semantics differ")
before = statistics.median(row["seconds"] for row in reports["baseline"])
after = statistics.median(row["seconds"] for row in reports["candidate"])
tolerance = max(before * 0.1, 0.001)
print(
    json.dumps(
        {
            "reports": reports,
            "semantic_match": True,
            "baseline_median_seconds": before,
            "candidate_median_seconds": after,
            "tolerance_seconds": tolerance,
            "passes": after <= before + tolerance,
            "scope": "Five paired cold queries in each installed process; every CLI request creates its own run. First sample also includes lazy imports.",
        }
    )
)
