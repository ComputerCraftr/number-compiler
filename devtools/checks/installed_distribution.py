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
from number_compiler.api.family_registry import family_spec
from number_compiler.arithmetic.contracts.family_identity import family_id
from number_compiler.arithmetic.contracts.input_validation import string_keyed_mapping


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


def verify_wheel(
    wheel: Path, *, python_executable: Path | None = None
) -> dict[str, object]:
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
    required_future_asset = "number_compiler/kernels/comma_semantic_future_v2.json"
    if required_future_asset not in members:
        raise ValueError("installed distribution lacks the admitted comma future")
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
            [str(python_executable or sys.executable), "-m", "venv", str(venv)],
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
from hashlib import sha256
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
assert find_spec('number_compiler.sequences.comma.forest_verifier') is None
assert not files('number_compiler').joinpath('kernels/comma_prefix_v1.jsonl.gz').is_file()
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
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma import future_provider
global_digest = future_provider.registered_global_release_artifact_sha256()
assert global_digest is not None
future_asset = files('number_compiler').joinpath('kernels/comma_semantic_future_v2.json')
future_record = json.loads(future_asset.read_text())
provider_store = future_provider.SemanticFutureProviderStore(ResourceLedger())
future_instance = provider_store.load_record(
    future_record, charge_work=lambda _amount: None
)
assert future_instance.global_release_admitted
assert future_instance.artifact_sha256 == global_digest
assert sha256(future_asset.read_bytes()).hexdigest() == global_digest
from number_compiler.api.cli import main
from number_compiler.sequences.comma.power import CommaTerm
from unittest.mock import patch
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveTemporalCutover,
)
from number_compiler.sequences.reverse_add.recursive_adapters import ReverseRecursiveFieldAdapter
leaf_compile = ReverseRecursiveFieldAdapter.compile_completed
def require_completed_children(self, action, source):
    assert self.sources.resolve(source).level == 0, 'parent recompiled original source'
    return leaf_compile(self, action, source)
with patch.object(ReverseRecursiveFieldAdapter, 'compile_completed', require_completed_children):
    with patch.object(ReverseRecursiveTemporalCutover, 'digit_image', side_effect=AssertionError('terminal image rebuilt')):
        reverse = api.ReverseAddPoweredTerm(196, 20)
        assert ''.join(map(str, reversed(reverse.digits()))) == '70446464506'
assert not any(name == 'devtools' or name.startswith('devtools.') for name in sys.modules)
captured = StringIO()
with patch.object(CommaTerm, '_stage_global_future_provider_artifact_locked', side_effect=AssertionError('metadata request loaded the artifact')):
    with redirect_stdout(captured):
        assert main(['a367620', '--nth', '20000', '--no-value', '--info', 'safety.certificate', '--format', 'json']) == 0
comma_status = json.loads(captured.getvalue())
captured_compact = StringIO()
with redirect_stdout(captured_compact):
    assert main(['a367620', '--nth-power10', '0', '--no-value', '--info', 'safety.certificate', '--format', 'json']) == 0
compact_status = json.loads(captured_compact.getvalue())
assert compact_status['index'] == {'encoding': 'power10', 'exponent': 0}
assert compact_status['value'] is None

assert comma_status['index_unit'] == 'oeis_index'
assert comma_status['value'] is None
assert comma_status['info']['safety.certificate']['runtime_verified'] is False
assert comma_status['info']['safety.certificate']['isabelle_instance_checked'] is True
assert comma_status['info']['safety.certificate']['certificate_sha256'] == global_digest
assert comma_status['info']['safety.certificate']['coverage'] == 'all_positive_indices'
for index, expected in ((1, '20'), (20000, '1039404'), (412987859, '19999999918'), (412987860, '19999999999')):
    output = StringIO()
    with redirect_stdout(output):
        assert main(['a367620', '--nth', str(index)]) == 0
    assert output.getvalue().strip() == expected
from number_compiler.sequences.comma.arithmetic import comma_children
assert comma_children(19999999918) == (19999999999, 20000000000)
from importlib.resources import as_file
from number_compiler.sequences.comma.boundary_quotient import BoundaryState, construct_macro
from number_compiler.sequences.comma.occurrence import BoundaryOccurrence, OccurrencePrefixReturn
from number_compiler.sequences.comma.semantic_branch import select_global_semantic_macro_child
with as_file(future_asset) as provider_path:
    provider = provider_store.load_file(
        provider_path, charge_work=lambda _amount: None
    )
source = BoundaryOccurrence(BoundaryState('N', 2, 10), 10)
expected_fork_sources = (BoundaryState('N', 2, 10), BoundaryState('N', 7, 12))
expected_fork_children = (
    (6999999999999, 7000000000000),
    (19999999999999, 20000000000000),
)
# Authored rank rows fix N(2,10) to slot 0 and N(7,12) to slot 1.
expected_fork_slots = (0, 1)
expected_selected_literals = (6999999999999, 20000000000000)
transition_counts = []
for expected_state, expected_children, expected_slot, expected_literal in zip(
    expected_fork_sources, expected_fork_children, expected_fork_slots,
    expected_selected_literals, strict=True
):
    assert source.state == expected_state
    prefix = OccurrencePrefixReturn(source, construct_macro(source.state))
    assert prefix.outcome == 'fork'
    assert comma_children(prefix.terminal_value) == expected_children
    ordered = prefix.ordered_literal_children()
    _, literals = ordered.validated_parts()
    selected = select_global_semantic_macro_child(
        source,
        prefix,
        fork_value=prefix.terminal_value,
        ordered_literal_children=(literals[0], literals[1]),
        provider=provider,
        charge_work=lambda _amount: None,
    )
    assert selected.selection.selected_slot == expected_slot
    assert expected_children[expected_slot] == expected_literal
    assert selected.literal_value == expected_literal
    transition_counts.append(selected.total_transition_count)
    source = selected.target
later_index = 412987860 + sum(transition_counts)
expected_later_output = 20000000000000
assert source.value() == expected_later_output
observed_fork_sources = []
original_select = SemanticFutureProvider.select_unique_unranked_child
def traced_select(self, state, *, charge_work):
    observed_fork_sources.append(state)
    return original_select(self, state, charge_work=charge_work)
later_output = StringIO()
with patch.object(SemanticFutureProvider, 'select_unique_unranked_child', traced_select):
    with redirect_stdout(later_output):
        assert main(['a367620', '--nth', str(later_index), '--format', 'json']) == 0
later_packet = json.loads(later_output.getvalue())
assert later_packet['index'] == later_index
assert later_packet['value'] == str(expected_later_output)
assert expected_fork_sources[0] in observed_fork_sources
assert expected_fork_sources[1] in observed_fork_sources
provider_store.close()
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
    assert main(['antihydra', '--nth', '64', '--no-value', '--info', 'arithmetic.hensel', '--info', 'arithmetic.mahler', '--info', 'metrics', '--format', 'json']) == 0
arithmetic = json.loads(captured.getvalue())
assert arithmetic['value'] is None
for name in ('arithmetic.hensel', 'arithmetic.mahler'):
    packet = arithmetic['info'][name]
    assert packet['guarded_physical_status'] == 'not_requested'
mahler_action = arithmetic['info']['arithmetic.mahler']['value']['associated_action']
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
        assert main(['collatz', '--events', '5', '--seed', '27', '--info', 'safety.execution', '--format', 'json']) == 0
    safety = json.loads(captured.getvalue())['info']['safety.execution']
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
print(json.dumps({'python_version': list(sys.version_info[:3]), 'public_exports': len(api.__all__), 'kernel_left_states': kernel.left_count, 'kernel_right_states': kernel.right_count, 'installed_path': api.__file__, 'arithmetic_cli_roof_poison': 'passed', 'homogeneous_run_cli_actions': reuse['collatz_physical_temporal_run_actions'], 'mahler_composed_image': 'passed', 'cross_seed_macrocells': 'passed', 'antihydra_digit_parent_reuse': 'passed'}))
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
        result = string_keyed_mapping(json.loads(cli.stdout))
        if result is None or result.get("value") != "2":
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
                "number-theory.primality",
                "--info",
                "number-theory.factor",
                "--format",
                "json",
            ],
            cwd=work,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        )
        factor = string_keyed_mapping(json.loads(factor_cli.stdout))
        info = string_keyed_mapping(factor.get("info")) if factor is not None else None
        primality = (
            string_keyed_mapping(info.get("number-theory.primality"))
            if info is not None
            else None
        )
        witness = (
            string_keyed_mapping(info.get("number-theory.factor"))
            if info is not None
            else None
        )
        if (
            primality is None
            or primality.get("status") != "composite"
            or witness is None
            or witness.get("factor_witness") != 23
        ):
            raise ValueError("installed CLI did not print the checked M11 factor")
        _report_stage("installed-cli-contracts:complete")
        commands = [
            (["prime", "--nth-power10", "0"], 0, "3"),
            (["reverse-add", "--seed", "196", "--nth-power10", "0"], 0, "887"),
            (["2rev10", "--seed", "10", "--nth", "0"], 0, "10"),
            (["2rev10", "--seed", "10", "--nth-power10", "0"], 0, "2"),
            (
                [
                    "2rev10",
                    "--seed",
                    "196",
                    "--nth",
                    "64",
                    "--no-value",
                    "--info",
                    "spatial.stencil",
                    "--info",
                    "temporal.bank",
                    "--info",
                    "temporal.closed-form",
                    "--info",
                    "spatial.pair-bank",
                ],
                0,
                "",
            ),
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
            (["reverse-add", "--seed", "196", "--nth", "0"], 0, "196"),
            (["reverse-add", "--seed", "196", "--nth", "2"], 0, "1675"),
            (["reverse-add", "--seed", "196", "--nth", "20"], 0, "70446464506"),
            (
                ["reverse-add", "--seed", "196", "--nth", "128"],
                0,
                "4431637520621652749397876519890256677940462572161148460244",
            ),
            (["reverse-add", "--seed", "1", "--nth", "4"], 0, "16"),
            (
                ["reverse-add", "--seed", "196", "--nth", "129"],
                0,
                "8852285932234405389895643040879413465879935133421405821588",
            ),
            (["reverse-add", "--nth", "0", "--seed", "0"], 0, "0"),
            (["a367620", "--nth", "1"], 0, "20"),
            (["a367620", "--nth", "20000"], 0, "1039404"),
            (["a367620", "--nth", "412987859"], 0, "19999999918"),
            (["a367620", "--nth", "412987860"], 0, "19999999999"),
            (["a367620", "--nth", "412987861"], 0, "20000000091"),
            (["collatz", "--nth", "4", "--seed", "27"], 0, "62"),
            (
                [
                    "collatz",
                    "--events",
                    "5",
                    "--seed",
                    "27",
                    "--info",
                    "safety.execution",
                ],
                0,
                "",
            ),
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
                    "safety.ledger",
                    "--info",
                    "temporal.clock",
                    "--info",
                    "arithmetic.hensel",
                    "--info",
                    "arithmetic.mahler",
                    "--info",
                    "metrics",
                ],
                0,
                "454",
            ),
            (
                [
                    "fermat",
                    "--nth",
                    "4",
                    "--no-value",
                    "--info",
                    "number-theory.primality",
                ],
                3,
                "",
            ),
            (["not-a-family", "--nth", "0"], 2, ""),
        ]
        for family, index, steps, source_options in (
            ("reverse-add", 79, 2, ("--seed", "196")),
            ("2rev10", 32, 10, ("--seed", "196")),
            ("collatz", 2, 2, ("--seed", "11")),
            ("antihydra", 16, 4, ()),
            ("fermat", 2, 3, ()),
            ("mersenne", 31, 16, ()),
        ):
            commands.append(
                (
                    [
                        family,
                        *source_options,
                        "--nth",
                        str(index),
                        "--no-value",
                        "--info",
                        "temporal.matrix",
                        "--temporal-matrix-steps",
                        str(steps),
                    ],
                    0,
                    "",
                )
            )
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
            if "temporal.matrix" in arguments:
                matrix = json.loads(observed.stderr)["temporal.matrix"]
                ticks = int(arguments[arguments.index("--temporal-matrix-steps") + 1])
                capability = family_spec(family_id(arguments[0])).matrix
                assert capability is not None
                if (
                    matrix["status"] != "available"
                    or matrix["matrix_kind"] != "source-transfer"
                    or matrix["horizon"]
                    != {"ticks": ticks, "unit": capability.clock.value}
                    or matrix["execution_authority"] is not False
                ):
                    raise ValueError(
                        "installed matrix consumer lost its request contract"
                    )
            if arguments[0] == "2rev10" and "spatial.stencil" in arguments:
                details = json.loads(observed.stderr)
                rows = {
                    row["observer"]: row
                    for row in details["temporal.bank"]["envelopes"]
                }
                if (
                    details["spatial.stencil"]["digit"] != 8
                    or rows["growth"]["exact_sum"] != 24
                    or details["temporal.closed-form"]["prefix_steps"] != 16
                    or details["temporal.closed-form"]["entry_value"] != 173488
                    or details["temporal.closed-form"]["suffix_steps"] != 48
                    or details["spatial.pair-bank"]["position_unit"]
                    != "final_outer_to_inner_pair"
                ):
                    raise ValueError(
                        "installed 2rev10 cylinder observations are inexact"
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
            if arguments[0] == "antihydra" and "safety.ledger" in arguments:
                details = json.loads(observed.stderr)
                if details["safety.ledger"]["value"]["ledger"] != 11:
                    raise ValueError(
                        "installed Antihydra ledger differs from arithmetic source"
                    )
                mahler = details["arithmetic.mahler"]["value"]
                hensel = details["arithmetic.hensel"]["value"]
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
            if arguments[0] == "collatz" and "safety.execution" in arguments:
                safety = json.loads(observed.stderr)["safety.execution"]
                if (
                    safety["value"]["events"] != 5
                    or safety["value"]["descended_below_source"]
                    or safety["value"]["all_time_claim"]
                ):
                    raise ValueError(
                        "installed safety consumer lost its admitted prefix"
                    )
            if (
                arguments[0] == "not-a-family"
                and "invalid choice" not in observed.stderr
            ):
                raise ValueError(
                    "unknown family did not produce an ordinary parser error"
                )
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
    parser.add_argument("--python-executable", type=Path)
    args = parser.parse_args()
    print(
        json.dumps(
            verify_wheel(args.wheel, python_executable=args.python_executable),
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
