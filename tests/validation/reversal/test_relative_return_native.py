"""Source-checked two-tick interiors retain their physical boundary cones."""

from __future__ import annotations

import json
import os
import subprocess

import pytest

pytestmark = pytest.mark.validation


def _literal(seed: str, multiplier: int, ticks: int) -> str:
    value = int(seed)
    for _ in range(ticks):
        value = multiplier * int(str(value)[::-1])
    return str(value)


@pytest.mark.parametrize("multiplier", (2, 5))
@pytest.mark.parametrize("ticks", (128, 129))
def test_checked_relative_interior_and_mutated_halo(
    multiplier: int, ticks: int
) -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    motif = "0333329666667"
    if multiplier == 5:
        motif = motif[::-1]
    source = "17" + motif * 94 + "88"
    center = len(source) // 2
    mutant = source[:center] + "5" + source[center + 1 :]
    result, work = native.multiply(source, multiplier, ticks, 3)
    changed, changed_work = native.multiply(mutant, multiplier, ticks, 3)
    assert result == _literal(source, multiplier, ticks)
    assert changed == _literal(mutant, multiplier, ticks)
    assert work[0] < changed_work[0]
    assert work[2] == work[3] == 0


@pytest.mark.parametrize("prefix", (1, 137, 611))
def test_relative_return_is_found_after_nonmatching_prefix(prefix: int) -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    motif = "0333329666667"
    source = "17" + "5" * prefix + motif * 94 + "88"
    result, work = native.multiply(source, 2, 128, 3)
    assert result == _literal(source, 2, 128)
    assert work[0] < 14000


@pytest.mark.parametrize(
    ("multiplier", "core", "ticks"),
    (
        (2, "0333329666667" * 90, 128),
        (5, "7666669233330" * 90, 128),
        (2, "1" * 1800, 144),
        (5, "1" * 1800, 144),
    ),
)
def test_installed_cli_enters_the_checked_relative_endpoint(
    multiplier: int, core: str, ticks: int
) -> None:
    python = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not python:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel venv")
    assert os.path.isabs(python)
    program = """\
import pathlib, sys, sysconfig
import number_compiler
if sys.argv[1] == '2rev10':
    from number_compiler.kernels import _reflected_multiply as native
else:
    from number_compiler.kernels import _reverse_quotients as native
from number_compiler.api.cli import main
roots = [pathlib.Path(sysconfig.get_path(key)).resolve() for key in ('purelib', 'platlib')]
for module in (number_compiler, native):
    assert any(pathlib.Path(module.__file__).resolve().is_relative_to(root) for root in roots)
calls = []
def profile(frame, event, arg):
    if event == 'c_call' and arg is native.multiply:
        calls.append(1)
sys.setprofile(profile)
try: status = main(sys.argv[1:])
finally: sys.setprofile(None)
print('NATIVE_C_CALLS',len(calls),file=sys.stderr)
raise SystemExit(status)
"""
    source = "17" + core + "88"
    env = dict(
        os.environ,
        NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY="1",
        NUMBER_COMPILER_ENABLE_NATIVE_REVERSE="1",
    )
    result = subprocess.run(
        [
            python,
            "-I",
            "-c",
            program,
            f"{multiplier}rev10",
            "--seed",
            source,
            "--nth",
            str(ticks),
            "--max-steps",
            str(ticks),
            "--max-state-bits",
            "8192",
            "--max-output-bits",
            "8192",
            "--format",
            "json",
        ],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )
    assert int(result.stderr.strip().split("NATIVE_C_CALLS ")[-1]) > 0
    assert json.loads(result.stdout)["value"] == _literal(source, multiplier, ticks)


@pytest.mark.parametrize("multiplier", (2, 5))
@pytest.mark.parametrize("steps", (144, 145))
def test_uniform_clock_with_exact_fringe(multiplier: int, steps: int) -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    for digit in "0123456789":
        middle = digit * 1800
        for source in (
            "17" + middle + "88",
            "17" + middle[:900] + "4" + middle[901:] + "880",
        ):
            actual, work = native.multiply(source, multiplier, steps, 3)
            assert actual == _literal(source, multiplier, steps)
            assert work[2] == work[3] == 0
            if source.endswith("88"):
                assert work[0] < 7000


@pytest.mark.parametrize(
    ("m", "seed", "cut", "before", "after"),
    (
        (2, 196, 14, 9, 7),
        (2, 73, 14, 0, 8),
        (2, 12345, 13, 1, 3),
        (5, 196, 1, 2, 6),
        (5, 73, 2, 8, 2),
    ),
)
def test_144_four_tick_blocks_do_not_lift_equal_low_annuli(
    m: int, seed: int, cut: int, before: int, after: int
) -> None:
    source = int(_literal(str(seed), m, 160))
    target = int(_literal(str(source), m, 4 * 144))
    assert source % 10**cut == target % 10**cut
    assert source // 10**cut % 10 == before != after == target // 10**cut % 10
    if m == 2 and seed == 73:
        j, rem = divmod(160 * source - int(_literal(str(source), m, 4)), 198)
        k, rem2 = divmod(160 * target - int(_literal(str(target), m, 4)), 198)
        assert rem == rem2 == 0
        assert j % 10**cut == k % 10**cut
        assert (j // 10**cut % 10, k // 10**cut % 10) == (0, 4)


@pytest.mark.parametrize("blocks", (12, 36, 72, 144, 288))
def test_seed196_four_tick_projection_has_a_limited_annulus(blocks: int) -> None:
    source = int(_literal("196", 2, 160))
    target = int(_literal(str(source), 2, 4 * blocks))
    assert source % 10**14 == target % 10**14
    assert source % 10**15 != target % 10**15
    defects: list[int] = []
    for value in (source, target):
        defect, remainder = divmod(160 * value - int(_literal(str(value), 2, 4)), 198)
        assert remainder == 0
        defects.append(defect)
    first, second = defects
    assert first % 10**15 == second % 10**15
    assert first % 10**16 != second % 10**16


def test_installed_supplied_period_checks_each_oriented_word_once() -> None:
    python = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not python:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the wheel venv")
    program = """\
from contextlib import redirect_stdout
from io import StringIO
import json
from unittest.mock import patch
from number_compiler.api.cli import main
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.double_reverse import protected_temporal_bank as bank

for motif, admitted in [('0332966666667', True),
                        ('0'+'3'*60+'29'+'6'*64+'7', True),
                        ('0123456789012', False)]:
    work = {}
    bump = ResourceLedger.bump
    def count(self, key, amount=1):
        work[key] = work.get(key, 0) + amount
        return bump(self, key, amount)
    buf = StringIO()
    with patch.object(ResourceLedger, 'bump', count), redirect_stdout(buf), \\
         patch.object(bank, 'advance_periodic_state', side_effect=AssertionError('replay')):
        rc = main(['2rev10', '--seed', '17'+motif*(1800//len(motif))+'88',
                   '--nth', '576', '--max-state-bits', '16384', '--no-value',
                   '--info', 'temporal.grammar', '--temporal-grammar-position', '350',
                   '--temporal-grammar-period', str(len(motif)), '--format', 'json'],
                  shared_cache=False)
    packet = json.loads(buf.getvalue())['info']['temporal.grammar']
    assert rc == (0 if admitted else 3)
    assert packet['status'] == ('available' if admitted else 'unavailable')
    prefix = 'double_reverse_periodic_bank_'
    assert work[prefix+'relative_checks'] == len(motif)
    assert work.get(prefix+'relative_actions', 0) == int(admitted)
    assert work.get(prefix+'temporal_states', 0) == 0
    if admitted:
        assert packet['f_steps'] == 288 and packet['motif'] == []
"""
    subprocess.run([python, "-I", "-c", program], check=True, timeout=60)
