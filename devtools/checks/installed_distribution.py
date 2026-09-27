"""Validate a built wheel in an isolated environment outside the source checkout."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import zipfile
from pathlib import Path
from time import perf_counter


def validate_wheel_contents(wheel: Path, source: Path) -> list[str]:
    """Reject stale build products and missing or changed package resources."""
    expected = {
        path.relative_to(source).as_posix(): path
        for path in (source / "number_compiler").rglob("*")
        if path.is_file()
        and "__pycache__" not in path.parts
        and path.name != ".DS_Store"
    }
    with zipfile.ZipFile(wheel) as archive:
        members = archive.namelist()
        packaged = {
            name
            for name in members
            if name.startswith("number_compiler/") and not name.endswith("/")
        }
        if packaged != set(expected):
            raise ValueError(
                {
                    "extra_package_files": sorted(packaged - expected.keys()),
                    "missing_package_files": sorted(expected.keys() - packaged),
                }
            )
        for name, path in expected.items():
            if archive.read(name) != path.read_bytes():
                raise ValueError(f"wheel contains stale package content: {name}")
    return members


def verify_wheel(wheel: Path) -> dict[str, object]:
    """Check package contents, resource admission, public imports, and the CLI."""
    wheel = wheel.resolve(strict=True)
    from devtools.paths import repository_root

    members = validate_wheel_contents(wheel, repository_root() / "src")
    if any(
        name.startswith(("devtools/", "tests/", "research/", "bench/"))
        for name in members
    ):
        raise ValueError("developer packages leaked into the installed distribution")
    if "number_compiler/py.typed" not in members:
        raise ValueError("installed distribution has no typing marker")
    resources = [
        name
        for name in members
        if name.startswith("number_compiler/kernels/") and name.endswith(".zlib")
    ]
    if not resources:
        raise ValueError("installed distribution has no immutable kernel resources")
    if any(Path(name).name.startswith("base10_t2_") for name in resources):
        raise ValueError("retired reverse/add proof-machine resource was packaged")
    environment = dict(os.environ)
    environment.pop("PYTHONPATH", None)
    environment.pop("MYPYPATH", None)
    with tempfile.TemporaryDirectory(
        prefix="number-compiler-wheel-check-"
    ) as directory:
        work = Path(directory)
        venv = work / "environment"
        subprocess.run(
            [sys.executable, "-m", "venv", str(venv)],
            check=True,
            env=environment,
            capture_output=True,
            text=True,
        )
        python = venv / ("Scripts/python.exe" if os.name == "nt" else "bin/python")
        subprocess.run(
            [
                str(python),
                "-m",
                "pip",
                "install",
                "--no-deps",
                "--no-index",
                str(wheel),
            ],
            cwd=work,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        )
        smoke = subprocess.run(
            [
                str(python),
                "-I",
                "-c",
                """
import json
import sys
from contextlib import redirect_stdout
from io import StringIO
from importlib.util import find_spec
from importlib.resources import files
import number_compiler as api
from number_compiler.arithmetic.contracts.physical_collatz_kernel import PhysicalCollatzFourBlockEffect
assert all(hasattr(api, name) for name in api.__all__)
assert not hasattr(api, 'ComposedBlockEffect')
assert api.ReverseAddPoweredTerm(196, 0).digit(0) == 6
kernel = PhysicalCollatzFourBlockEffect()
assert kernel.left_count > 0 and kernel.right_count > 0
for removed in ('classical_ceiling', 'digit_power'):
    assert find_spec('number_compiler.sequences.power_numbers.' + removed) is None
for removed in (
    'sequences.collatz.clocked_target_seam',
    'hashlife.execution.continuations.higher_input',
    'hashlife.actions.power',
    'hashlife.actions.native_power',
    'hashlife.execution.cascade',
    'hashlife.execution.cascade_power',
    'hashlife.execution.powered_local_codec',
    'hashlife.execution.temporal_leaf_diamond',
    'hashlife.execution.diamond_reverse_kernel',
    'hashlife.execution.diamond_reverse_expression',
    'sequences.reverse_add.source_carry',
    'sequences.reverse_add.source_length',
    'sequences.reverse_add.factored_planes',
    'sequences.reverse_add.factored_carrier',
    'sequences.reverse_add.factored_power',
    'sequences.reverse_add.cocycle_carrier',
    'sequences.reverse_add.coordinate_program',
    'sequences.reverse_add.field_action',
    'sequences.reverse_add.higher_schema',
    'sequences.reverse_add.cocycle_temporal',
    'sequences.reverse_add.threshold_cocycle',
    'sequences.reverse_add.domain',
    'sequences.reverse_add.local_interface',
    'sequences.reverse_add.frobenius_sectors',
    'sequences.reverse_add.tile_sector_observation',
    'resources.cocycle_temporal_payload_audit',
    'sequences.reverse_add.higher_interface',
):
    assert find_spec('number_compiler.' + removed) is None
assert not any(name == 'devtools' or name.startswith('devtools.') for name in sys.modules)
from number_compiler.api.cli import main
from number_compiler.sequences.comma.power import CommaTerm
assert CommaTerm(20000).materialize() == 1039404
from unittest.mock import patch
captured = StringIO()
with patch('number_compiler.sequences.comma.certificates._verify', side_effect=AssertionError('report replayed admission')):
    with redirect_stdout(captured):
        assert main(['a367620', '--nth', '20000', '--no-value', '--info', 'certificate', '--format', 'json']) == 0
comma_status = json.loads(captured.getvalue())
assert comma_status['index_unit'] == 'oeis_index'
assert comma_status['value'] is None
assert comma_status['info']['certificate']['runtime_verified'] is False
assert comma_status['info']['certificate']['isabelle_instance_checked'] is False
captured = StringIO()
with redirect_stdout(captured):
    assert main(['a367620', '--nth', '412987860']) == 0
assert captured.getvalue().strip() == '19999999999'
assert not any(name == 'devtools' or name.startswith('devtools.') for name in sys.modules)
from number_compiler.sequences.antihydra import runtime
def forbidden_roof(*args, **kwargs):
    raise AssertionError('arithmetic CLI requested physical execution')
runtime.physical_roof = forbidden_roof
runtime.AntihydraArithmeticTerm.physical_run = forbidden_roof
original_arithmetic_result = runtime.AntihydraArithmeticTerm.result
arithmetic_terms = []
def traced_arithmetic_result(self):
    arithmetic_terms.append(self)
    return original_arithmetic_result(self)
runtime.AntihydraArithmeticTerm.result = traced_arithmetic_result
captured = StringIO()
with redirect_stdout(captured):
    assert main(['antihydra', '--nth', '64', '--no-value', '--info', 'hensel', '--info', 'mahler', '--info', 'metrics', '--format', 'json']) == 0
arithmetic = json.loads(captured.getvalue())
assert arithmetic['value'] is None
for name in ('hensel', 'mahler'):
    packet = arithmetic['info'][name]
    assert packet['guarded_physical_status'] == 'not_requested'
mahler_action = arithmetic['info']['mahler']['value']['associated_action']
assert mahler_action['first_failure'] == 2
root_shell = mahler_action['root_shell']
assert root_shell['coordinate'] == 'r_squared=theta=2*fractional_offset'
assert root_shell['guard_squared']['empty']
assert root_shell['radicand_offset']['numerator'] < 0
assert not mahler_action['all_time_claim']
assert arithmetic_terms and all(term is arithmetic_terms[0] for term in arithmetic_terms)
mahler_work = arithmetic_terms[0].ledger.counters
assert mahler_work.get('physical_roof_construction_requests', 0) == 0
assert mahler_work['mahler_source_composed_image_reads'] == 1
assert mahler_work.get('mahler_source_cylinder_compositions', 0) == 0
mahler_metrics = arithmetic['info']['metrics']['execution_metrics']
assert mahler_metrics['schema_version'] == 8
assert mahler_metrics['construction']['source_image_adapter_registrations'] == 1
assert mahler_metrics['construction']['arithmetic_result_publications'] == 1
assert mahler_metrics['projection']['publications'] >= 2
assert mahler_metrics['observations']['physical_roof_evaluations'] is None
assert mahler_metrics['observations']['mahler_source_composed_image_reads'] == 1
assert mahler_metrics['observations']['mahler_associated_action_demands'] == 1
assert mahler_metrics['observations']['mahler_root_shell_projections'] == 1
assert mahler_metrics['observations']['mahler_root_shell_operand_bits'] > 0
from number_compiler.sequences.collatz.source_publisher import CollatzSourcePublisher
original_publish = CollatzSourcePublisher.publish
published_sources = []
def traced_publish(self):
    published = original_publish(self)
    published_sources.append((self, published))
    return published
CollatzSourcePublisher.publish = traced_publish
try:
    captured = StringIO()
    with redirect_stdout(captured):
        assert main(['collatz', '--events', '5', '--seed', '27', '--info', 'safety', '--format', 'json']) == 0
    safety = json.loads(captured.getvalue())['info']['safety']
    assert safety['value']['events'] == 5
    assert not safety['value']['descended_below_source']
    assert not safety['value']['all_time_claim']
    assert len(published_sources) == 1
    publisher, published = published_sources[0]
    assert published.discovered_events == 5
    assert publisher.ledger.counters['collatz_source_discovery_events'] == 5
    assert publisher.ledger.counters['collatz_saturated_event_reads'] == 5
finally:
    CollatzSourcePublisher.publish = original_publish
from number_compiler.hashlife.execution.dyadic_return_images import DyadicReturnImageWorkspace as Images
original_summary = Images.saturated_summary
reuse_calls = []
def traced_summary(self):
    summary = original_summary(self)
    reuse_calls.append(dict(self.ledger.counters))
    return summary
Images.saturated_summary = traced_summary
try:
    captured = StringIO()
    with redirect_stdout(captured):
        assert main(['collatz', '--nth', '1024', '--seed', str(1 << 4096)]) == 0
    assert captured.getvalue().strip() == str(1 << 3072)
    assert reuse_calls
    reuse = reuse_calls[-1]
    assert reuse['collatz_physical_balanced_effect_memo_hits'] > 0
    assert reuse['collatz_physical_reused_temporal_extent'] >= 960
    assert reuse['collatz_physical_transient_leaf_steps'] <= 64
    assert reuse.get('source_image_primitive_applications', 0) == 0
finally:
    Images.saturated_summary = original_summary
from number_compiler.api.number_api import PoweredCollatzTermPayload
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
limb_seed = (1 << 512) + 27
limb_expected = limb_seed
for _ in range(129):
    limb_expected = 3 * limb_expected + 1 if limb_expected & 1 else limb_expected // 2
limb_term = PoweredCollatzTerm(limb_seed, 129)
limb_payload = PoweredCollatzTermPayload(limb_term, 1 << 63)
original_point = PoweredCollatzTerm._point_symbol
def forbidden_binary_point(*args, **kwargs):
    raise AssertionError('installed limb expanded into binary point queries')
PoweredCollatzTerm._point_symbol = forbidden_binary_point
try:
    assert limb_payload.digit(0) == limb_expected % (1 << 63)
    assert limb_payload.digit(0) == limb_expected % (1 << 63)
    assert limb_term._ledger.counters['collatz_image_radix_demands'] == 1
finally:
    PoweredCollatzTerm._point_symbol = original_point
print(json.dumps({'public_exports': len(api.__all__), 'kernel_left_states': kernel.left_count, 'kernel_right_states': kernel.right_count, 'installed_path': api.__file__, 'arithmetic_cli_roof_poison': 'passed', 'complete_effect_cli_reuses': reuse['collatz_physical_balanced_effect_memo_hits'], 'mahler_composed_image': 'passed'}))
""",
            ],
            cwd=work,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        )
        cli = subprocess.run(
            [
                str(python),
                "-I",
                "-m",
                "number_compiler",
                "prime",
                "--nth",
                "0",
                "--format",
                "json",
            ],
            cwd=work,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        )
        result: object = json.loads(cli.stdout)
        if not isinstance(result, dict) or result.get("value") != "2":
            raise ValueError("installed CLI returned another prime result")
        factor_cli = subprocess.run(
            [
                str(python),
                "-I",
                "-m",
                "number_compiler",
                "mersenne",
                "--nth",
                "11",
                "--no-value",
                "--info",
                "primality",
                "--info",
                "factor",
                "--format",
                "json",
            ],
            cwd=work,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        )
        factor: object = json.loads(factor_cli.stdout)
        info = factor.get("info") if isinstance(factor, dict) else None
        primality = info.get("primality") if isinstance(info, dict) else None
        witness = info.get("factor") if isinstance(info, dict) else None
        if (
            not isinstance(primality, dict)
            or primality.get("status") != "composite"
            or not isinstance(witness, dict)
            or witness.get("factor_witness") != 23
        ):
            raise ValueError("installed CLI did not print the checked M11 factor")
        commands = [
            (["prime", "--nth", "10", "--info", "metrics"], 0, "31"),
            (["prime", "--nth", "10", "--max-prime-states", "1"], 2, ""),
            (["196", "--nth", "0"], 0, "196"),
            (["196", "--nth", "2"], 0, "1675"),
            (["reverse-add", "--nth", "0", "--seed", "0"], 0, "0"),
            (["a367620", "--nth", "1"], 0, "20"),
            (["a367620", "--nth", "412987860"], 0, "19999999999"),
            (["a367620", "--nth", "412987861"], 3, ""),
            (["collatz", "--nth", "4", "--seed", "27"], 0, "62"),
            (["collatz", "--events", "5", "--seed", "27", "--info", "safety"], 0, ""),
            (["collatz", "--nth", "1000000", "--seed", "27"], 0, "4"),
            (
                [
                    "collatz",
                    "--nth",
                    "999999",
                    "--seed",
                    "27",
                    "--max-output-bits",
                    "1",
                ],
                0,
                "1",
            ),
            (
                [
                    "collatz",
                    "--nth",
                    "1000000",
                    "--seed",
                    "27",
                    "--max-output-bits",
                    "2",
                ],
                2,
                "",
            ),
            (["fermat", "--nth", "0"], 0, "3"),
            (["mersenne", "--nth", "1"], 0, "1"),
            (
                [
                    "antihydra",
                    "--nth",
                    "10",
                    "--info",
                    "ledger",
                    "--info",
                    "clock",
                    "--info",
                    "hensel",
                    "--info",
                    "mahler",
                    "--info",
                    "metrics",
                ],
                0,
                "454",
            ),
            (["fermat", "--nth", "4", "--no-value", "--info", "primality"], 3, ""),
            (["nth", "prime", "0"], 2, ""),
        ]
        cold_processes: list[dict[str, object]] = []
        for arguments, status, value in commands:
            started = perf_counter()
            observed = subprocess.run(
                [str(python), "-I", "-m", "number_compiler", *arguments],
                cwd=work,
                env=environment,
                capture_output=True,
                text=True,
                check=False,
            )
            cold_processes.append(
                {
                    "arguments": arguments,
                    "seconds": perf_counter() - started,
                    "exit_code": observed.returncode,
                    "stdout_bytes": len(observed.stdout.encode()),
                    "stderr_bytes": len(observed.stderr.encode()),
                }
            )
            if observed.returncode != status or observed.stdout.strip() != value:
                raise ValueError(
                    f"installed CLI contract failed: {arguments}: {observed}"
                )
            if arguments[0] == "prime" and "--info" in arguments:
                metrics = json.loads(observed.stderr)["metrics"]
                if (
                    metrics["prime_dag_states"] <= 0
                    or metrics["prime_discovery_queries"] <= 0
                    or metrics["prime_parent_gap_positions_materialized"] != 0
                ):
                    raise ValueError(
                        "installed prime CLI bypassed the descriptor owner"
                    )
            if arguments[0] == "antihydra":
                details = json.loads(observed.stderr)
                if details["ledger"]["value"]["ledger"] != 11:
                    raise ValueError(
                        "installed Antihydra ledger differs from arithmetic source"
                    )
                mahler = details["mahler"]["value"]
                hensel = details["hensel"]["value"]
                execution = details["metrics"]["execution_metrics"]
                construction = execution["construction"]
                observations = execution["observations"]
                if (
                    "associated_action" in hensel
                    or mahler["associated_action"]["extent"] != 10
                    or mahler["associated_action"]["first_failure"] != 2
                    or construction["source_image_adapter_registrations"] != 1
                    or construction["arithmetic_result_publications"] != 1
                    or observations["mahler_source_composed_image_reads"] != 1
                    or observations["mahler_associated_action_demands"] != 1
                    or execution["projection"]["publications"] < 2
                ):
                    raise ValueError(
                        "installed Mahler consumer bypassed the shared scheduler"
                    )
            if arguments[0] == "collatz" and "safety" in arguments:
                safety = json.loads(observed.stderr)["safety"]
                if (
                    safety["value"]["events"] != 5
                    or safety["value"]["descended_below_source"]
                    or safety["value"]["all_time_claim"]
                ):
                    raise ValueError(
                        "installed safety consumer lost its admitted prefix"
                    )
            if (
                arguments[0] == "nth"
                and "old command form removed" not in observed.stderr
            ):
                raise ValueError("removed command did not supply a migration hint")
        return {
            "wheel": wheel.name,
            "kernel_resources": resources,
            "smoke": json.loads(smoke.stdout),
            "cli_value": "2",
            "cli_m11_factor": 23,
            "family_first_contract_cases": len(commands),
            "cold_process_samples": cold_processes,
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wheel", type=Path)
    args = parser.parse_args()
    print(json.dumps(verify_wheel(args.wheel), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
