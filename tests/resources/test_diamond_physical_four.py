"""The fixed C^4 interface is kernel data, with an exhaustive offline proof."""

import hashlib
from dataclasses import FrozenInstanceError
from itertools import product
from typing import Literal, Never

import pytest

from devtools.experiments.collatz.generate_physical_collatz_four_kernel import (
    build as proof_kernel,
)
from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
    _HEADER,
    _RAW_SHA256,
    PhysicalCollatzFourBlockEffect,
    compile_physical_diamond,
)
from number_compiler.arithmetic.contracts.temporal_family import _issue_certificate
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.observation.diamond_query import DiamondApplication
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.assertions import assert_rejected_atomically
from tests.support.diamond_runtime import build, oracle


def test_complete_fixed_kernel_matches_all_old_bimachine_states_transitions_and_outputs() -> (
    None
):
    expected = proof_kernel()
    effect = PhysicalCollatzFourBlockEffect()
    actual = (
        _HEADER + effect.left_transitions + effect.right_transitions + effect.outputs
    )
    assert actual == expected
    assert hashlib.sha256(actual).hexdigest() == _RAW_SHA256
    with pytest.raises(FrozenInstanceError):
        effect.__setattr__("base", 3)


def test_fixed_kernel_metadata_and_tables_cannot_forge_family_issuance() -> None:
    for attribute, value in (("base", 3), ("exponent", 8), ("outputs", b"\0" * 13500)):
        effect = PhysicalCollatzFourBlockEffect()
        object.__setattr__(effect, attribute, value)
        with pytest.raises(ValueError):
            _issue_certificate(effect, "collatz", effect.exponent)


def test_fixed_kernel_generic_projection_keeps_its_full_halo() -> None:
    effect = PhysicalCollatzFourBlockEffect()
    for bits in product((0, 1), repeat=4):
        source = (*bits, 1)
        application = HashLifeBlockIndex(effect, source, logical_length=16)
        expected = oracle(CollatzPhysicalBlockEffect(), source, 16, 4)
        assert [application.direct_powered_point(i) for i in range(8)] == expected[:8]


def test_fixed_kernel_projection_lowers_before_tile_execution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = PhysicalCollatzFourBlockEffect()
    source = (1, 0, 1, 1, 1)
    expected = oracle(CollatzPhysicalBlockEffect(), source, 16, 4)
    application = HashLifeBlockIndex(effect, source, logical_length=16)
    from number_compiler.hashlife.observation.tile_projection import LazyProjection

    assert type(application._lazy_application) is LazyProjection
    adapter = application._lazy_application.scheduler.adapter
    assert isinstance(adapter, PrimitiveTileKernelAdapter)
    assert all(
        type(kernel.effect) is CollatzPhysicalBlockEffect
        for kernel in adapter.kernels._kernels
    )

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("tile execution reentered the proof C4 machine")

    monkeypatch.setattr(PhysicalCollatzFourBlockEffect, "advance", forbidden)
    monkeypatch.setattr(PhysicalCollatzFourBlockEffect, "emit", forbidden)
    assert [application.direct_powered_point(i) for i in range(8)] == expected[:8]
    report = collect_ledger_metrics(application._ledger)
    assert report.proof_machine_applications == 0


def test_forged_fixed_kernel_rejects_before_index_ledger_mutation() -> None:
    effect = PhysicalCollatzFourBlockEffect()
    object.__setattr__(effect, "right_count", 90.0)
    ledger = ResourceLedger()
    assert_rejected_atomically(
        ledger,
        lambda: HashLifeBlockIndex(effect, (1,), logical_length=4, ledger=ledger),
        ValueError,
        match="certificate",
    )


def test_macro_physical_compiler_consumes_binary_dag_and_certifies_halo_and_cycle() -> (
    None
):
    runtime, _ = build(CollatzPhysicalBlockEffect(), (1,), 16, 1)
    root = compile_physical_diamond(
        runtime.actions.compiler, runtime.actions, 10**12 + 2
    )
    assert runtime.actions.node(root).exponent == 10**12 + 2
    assert runtime.halos.right(root) == 10**12 + 2
    application = DiamondApplication(runtime, root)
    assert application.active_width() == 1
    assert application.point(0) == 1
    report = collect_ledger_metrics(runtime.ledger)
    assert report.representation_boundary_complete == 1
    assert report.finite_cycle_certificate_nodes == 1
    assert report.sequential_generation_advances == 0


@pytest.mark.parametrize(
    ("attribute", "value"),
    [
        ("exponent", 4.0),
        ("right_count", 90.0),
        ("stable_blank_output", 1),
        ("eager_boundary_quotient", False),
        ("supports_predecessor_trace", 0),
        ("storage_bytes", 866.0),
        ("uncompressed_bytes", True),
        ("kernel_name", "forged"),
    ],
)
def test_equal_but_wrong_type_metadata_is_rejected_before_warm_compiler_admission(
    attribute: Literal[
        "eager_boundary_quotient",
        "exponent",
        "kernel_name",
        "right_count",
        "stable_blank_output",
        "storage_bytes",
        "supports_predecessor_trace",
        "uncompressed_bytes",
    ],
    value: Literal["forged"] | bool | float,
) -> None:
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler

    compiler = LazyCompiler(ResourceLedger())
    effect = PhysicalCollatzFourBlockEffect()
    compiler.atom(effect)
    object.__setattr__(effect, attribute, value)
    before = compiler.ledger.snapshot()
    with pytest.raises(ValueError):
        compiler.atom(effect)
    with pytest.raises(ValueError):
        _issue_certificate(effect, "collatz", 4)
    assert compiler.ledger.snapshot() == before
