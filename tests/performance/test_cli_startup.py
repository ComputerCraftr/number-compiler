"""Cold commands must not construct unrelated family runtime modules."""

from __future__ import annotations

import json
import subprocess
import sys

import pytest


@pytest.mark.parametrize("arguments", [
    ["--list-families"], ["antihydra", "--help"],
    ["fermat", "--nth", "0"], ["mersenne", "--nth", "1"],
    ["prime", "--nth", "0"], ["antihydra", "--nth", "64"],
    ["196", "--nth", "4"], ["collatz", "--nth", "4", "--seed", "27"],
    ["fermat", "--nth", "0", "--no-value", "--info", "primality"],
    ["mersenne", "--nth", "11", "--no-value", "--info", "factor"],
    ["antihydra", "--nth", "64", "--no-value", "--info", "metrics"],
])
def test_cold_cli_does_not_import_unrequested_runtime_work(arguments: list[str]) -> None:
    script = """
import importlib.abc
import json
import sys

forbidden = {
    'number_compiler.resources.metric_records',
    'number_compiler.sequences.collatz.block_power',
    'number_compiler.sequences.reverse_add.power',
    'number_compiler.api.cylinder_observation',
    'number_compiler.api.sequence_compiler',
}
arguments = json.loads(sys.argv[1])
if arguments[0] in ('fermat', 'mersenne') and '--info' in arguments:
    forbidden.remove('number_compiler.api.sequence_compiler')
    forbidden.update({
        'number_compiler.sequences.collatz.orbit',
        'number_compiler.sequences.reverse_add.digits',
        'number_compiler.sequences.prime.lane_quotient',
    })
if arguments[0] == '196':
    forbidden.remove('number_compiler.sequences.reverse_add.power')
    # Shared primitive admission checks recognize the exact Collatz atom type.
    # Its module may load; neither family's large metric schema is demanded.
    forbidden.remove('number_compiler.sequences.collatz.block_power')
if arguments[0] == 'collatz':
    forbidden.remove('number_compiler.sequences.collatz.block_power')
class RejectForeignRuntime(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        if fullname in forbidden:
            raise AssertionError('unrequested runtime import: ' + fullname)
sys.meta_path.insert(0, RejectForeignRuntime())
from number_compiler.api.cli import main
assert main(arguments) == 0
"""
    completed = subprocess.run(
        [sys.executable, "-c", script, json.dumps(arguments)],
        capture_output=True, text=True, check=False, timeout=5,
    )
    assert completed.returncode == 0, completed.stderr


def test_public_facades_keep_export_identity_without_eager_resolution() -> None:
    script = """
import sys
import number_compiler
import number_compiler.api as api
assert 'number_compiler.api.number_api' not in sys.modules
assert set(number_compiler.__all__) <= set(dir(number_compiler))
assert 'number_compiler.api.number_api' not in sys.modules
from number_compiler.api.number_api import NumberCompiler
assert number_compiler.NumberCompiler is api.NumberCompiler is NumberCompiler
assert number_compiler.NumberCompiler is NumberCompiler
for facade in (number_compiler, api):
    try:
        facade.resolve_export
    except AttributeError:
        pass
    else:
        raise AssertionError('private export resolver exposed on public facade')
try:
    number_compiler.not_a_public_export
except AttributeError:
    pass
else:
    raise AssertionError('unknown public export accepted')
"""
    completed = subprocess.run(
        [sys.executable, "-c", script], capture_output=True, text=True,
        check=False, timeout=5,
    )
    assert completed.returncode == 0, completed.stderr
