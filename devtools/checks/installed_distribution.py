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

from devtools.checks.package_contracts import DEVELOPER_ROOTS


def _report_stage(stage: str) -> None:
    """Keep the active wheel-verification phase visible to the run guard."""
    print(f"package-stage: {stage}", file=sys.stderr, flush=True)


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
        if any(name.split("/")[0] in DEVELOPER_ROOTS for name in members):
            raise ValueError("developer or formal-proof files leaked into the wheel")
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

    _report_stage("wheel-content-validation:start")
    members = validate_wheel_contents(wheel, repository_root() / "src")
    _report_stage("wheel-content-validation:complete")
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
        _report_stage("venv-create:start")
        subprocess.run(
            [sys.executable, "-m", "venv", str(venv)],
            check=True,
            env=environment,
            capture_output=True,
            text=True,
        )
        _report_stage("venv-create:complete")
        python = venv / ("Scripts/python.exe" if os.name == "nt" else "bin/python")
        _report_stage("wheel-install:start")
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
        _report_stage("wheel-install:complete")
        _report_stage("installed-smoke:start")
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
from number_compiler.sequences.collatz.physical_kernel import PhysicalCollatzFourBlockEffect
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
    'sequences.reverse_add.cocycle_temporal',
    'sequences.reverse_add.threshold_cocycle',
    'sequences.reverse_add.domain',
    'sequences.reverse_add.local_interface',
    'sequences.reverse_add.frobenius_sectors',
    'sequences.reverse_add.tile_sector_observation',
    'resources.cocycle_temporal_payload_audit',
):
    assert find_spec('number_compiler.' + removed) is None
assert not any(name == 'devtools' or name.startswith('devtools.') for name in sys.modules)
from number_compiler.api.cli import main
from number_compiler.sequences.comma.power import CommaTerm
assert CommaTerm(20000).materialize() == 1039404
from unittest.mock import patch
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveTemporalCutover,
)
from number_compiler.sequences.reverse_add.recursive_adapters import _ReverseRecursiveFieldAdapter
leaf_compile = _ReverseRecursiveFieldAdapter._compile
def require_completed_children(self, action, source):
    assert self.sources.resolve(source).level == 0, 'parent recompiled original source'
    return leaf_compile(self, action, source)
with patch.object(_ReverseRecursiveFieldAdapter, '_compile', require_completed_children):
    with patch.object(ReverseRecursiveTemporalCutover, 'digit_image', side_effect=AssertionError('terminal image rebuilt')):
        reverse = api.ReverseAddPoweredTerm(196, 20)
        assert ''.join(map(str, reversed(reverse.digits()))) == '70446464506'
assert not any(name == 'devtools' or name.startswith('devtools.') for name in sys.modules)
captured = StringIO()
with patch('number_compiler.sequences.comma.certificates._verify', side_effect=AssertionError('report replayed admission')):
    with redirect_stdout(captured):
        assert main(['a367620', '--nth', '20000', '--no-value', '--info', 'certificate', '--format', 'json']) == 0
comma_status = json.loads(captured.getvalue())
captured_compact = StringIO()
with redirect_stdout(captured_compact):
    assert main(['a367620', '--nth-power10', '0', '--no-value', '--info', 'certificate', '--format', 'json']) == 0
compact_status = json.loads(captured_compact.getvalue())
assert compact_status['index'] == {'encoding': 'power10', 'exponent': 0}
assert compact_status['value'] is None

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
    assert reuse['collatz_physical_temporal_run_actions'] == 1
    assert reuse['collatz_physical_temporal_zero_run_symbols'] == 1024
    assert reuse['collatz_physical_run_contraction_publications'] == 1
    assert reuse.get('collatz_physical_transient_leaf_steps', 0) == 0
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
api.NumberCompiler.clear_shared_cache()
for high in (1, 3):
    germ_seed = (high << 200) + 931386509544713451
    germ_expected = germ_seed
    for _ in range(1000):
        germ_expected = 3 * germ_expected + 1 if germ_expected & 1 else germ_expected // 2
    captured = StringIO()
    with redirect_stdout(captured):
        assert main(['collatz', '--seed', str(germ_seed), '--nth', '1000', '--info', 'metrics', '--format', 'json']) == 0
    packet = json.loads(captured.getvalue())
    assert packet['value'] == str(germ_expected)
    macro = packet['info']['metrics']['execution_metrics']['macrocells'][0]
    assert macro['index_unit'] == 'normalized_symbol'
assert macro['occurrence']['transported_hits'] >= 1
api.NumberCompiler.clear_shared_cache()
from number_compiler.sequences.antihydra.arithmetic_images import AntihydraArithmeticImageWorkspace
cold_cli = StringIO()
arguments = ['antihydra', '--nth', '1024', '--info', 'metrics', '--format', 'json']
with redirect_stdout(cold_cli):
    assert main(arguments) == 0
expected_cli = json.loads(cold_cli.getvalue())['value']
original_candidate = AntihydraArithmeticImageWorkspace.complete_composite_candidate
original_run = AntihydraArithmeticImageWorkspace._run_candidate
AntihydraArithmeticImageWorkspace.complete_composite_candidate = forbidden_binary_point
AntihydraArithmeticImageWorkspace._run_candidate = forbidden_binary_point
try:
    warm_cli = StringIO()
    with redirect_stdout(warm_cli):
        assert main(arguments) == 0
    warm_packet = json.loads(warm_cli.getvalue())
    assert warm_packet['value'] == expected_cli
    warm_row = next(row for row in warm_packet['info']['metrics']['execution_metrics']['macrocells'] if row['family'] == 'antihydra')
    assert warm_row['source_action']['applied_parent_hits'] == 1
finally:
    AntihydraArithmeticImageWorkspace.complete_composite_candidate = original_candidate
    AntihydraArithmeticImageWorkspace._run_candidate = original_run
api.NumberCompiler.clear_shared_cache()
print(json.dumps({'public_exports': len(api.__all__), 'kernel_left_states': kernel.left_count, 'kernel_right_states': kernel.right_count, 'installed_path': api.__file__, 'arithmetic_cli_roof_poison': 'passed', 'homogeneous_run_cli_actions': reuse['collatz_physical_temporal_run_actions'], 'mahler_composed_image': 'passed', 'cross_seed_macrocells': 'passed', 'antihydra_digit_parent_reuse': 'passed'}))
""",
            ],
            cwd=work,
            env=environment,
            check=False,
            capture_output=True,
            text=True,
        )
        if smoke.returncode:
            print(smoke.stdout, end="")
            print(smoke.stderr, end="", file=sys.stderr)
            smoke.check_returncode()
        _report_stage("installed-smoke:complete")
        _report_stage("installed-cli-contracts:start prime")
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
        _report_stage("installed-cli-contracts:mersenne-factor")
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
        _report_stage("installed-cli-contracts:complete")
        commands = [
            (["prime", "--nth-power10", "0"], 0, "3"),
            (["196", "--nth-power10", "0"], 0, "887"),
            (["reverse-add", "--nth-power10", "0", "--seed", "1"], 0, "2"),
            (["collatz", "--nth-power10", "6", "--seed", "27"], 0, "4"),
            (["antihydra", "--nth-power10", "0"], 0, "12"),
            (["fermat", "--nth-power10", "0"], 0, "5"),
            (["mersenne", "--nth-power10", "0"], 0, "1"),
            (["a367620", "--nth-power10", "0"], 0, "20"),
            (
                ["collatz", "--nth-power10", "1000000000", "--max-index-bits", "20"],
                2,
                "",
            ),
            (["prime", "--nth", "10", "--info", "metrics"], 0, "31"),
            (["prime", "--nth", "10", "--max-prime-states", "1"], 2, ""),
            (["196", "--nth", "0"], 0, "196"),
            (["196", "--nth", "2"], 0, "1675"),
            (["196", "--nth", "20"], 0, "70446464506"),
            (
                ["196", "--nth", "128"],
                0,
                "4431637520621652749397876519890256677940462572161148460244",
            ),
            (["196", "--seed", "1", "--nth", "4"], 0, "16"),
            (
                ["196", "--nth", "129"],
                0,
                "8852285932234405389895643040879413465879935133421405821588",
            ),
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
        _report_stage(f"cold-cli:start cases={len(commands)}")
        for index, (arguments, status, value) in enumerate(commands, start=1):
            _report_stage(
                f"cold-cli:case={index}/{len(commands)} command={arguments!r}"
            )
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
            if arguments[0] == "antihydra" and "ledger" in arguments:
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
        _report_stage("cold-cli:complete")
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
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
