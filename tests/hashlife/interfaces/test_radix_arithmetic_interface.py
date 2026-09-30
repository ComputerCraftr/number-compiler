"""Closed numeric division must stay exact without a carry-domain truth table."""

from dataclasses import replace
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FunctionSignature,
)
from number_compiler.arithmetic.radix_division import SymbolicBinaryDivisionEffect
from number_compiler.arithmetic.radix_port_functions import DivisionCarry
from number_compiler.arithmetic.radix_transfer import RadixRemainderTransfer
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.observation.tile_projection import build_tile_projection
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.assertions import assert_rejected_atomically
from tests.support.diamond_quotient import division_interface


@pytest.mark.parametrize("radix", (257, (1 << 63) - 25))
def test_numeric_parent_hit_does_not_expand_boolean_ports(
    radix: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((1, 0, 1, 1), 2, blank=2, extent=4, alphabet_size=2)
    with build_tile_projection(
        CollatzPhysicalBlockEffect(), SourceGeometry(ledger, source)
    ) as projection:
        adapter = projection.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        action = adapter.admit(
            SymbolicBinaryDivisionEffect(radix), cocycle=TemporalCocycle()
        )
        app = projection.scheduler.application(
            action,
            projection._application.source,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("numeric division entered Boolean parent substitution")

        monkeypatch.setattr(type(adapter), "_parent_components", forbidden)
        monkeypatch.setattr(type(adapter), "_leaf_components", forbidden)
        interface = app.interface()
        assert interface.outgoing_ports == (0, 26)
        before = ledger.snapshot()
        monkeypatch.setattr(type(adapter), "primitive_law", forbidden)
        monkeypatch.setattr(type(adapter), "_compile_interface", forbidden)
        assert app.interface() == interface
        after = ledger.snapshot()
        assert (before.entries, before.nodes) == (after.entries, after.nodes)
        assert ledger.counters.get("tile_radix_arithmetic_parent_interfaces", 0) > 0
        app.close()


def test_numeric_components_cannot_silently_narrow_admissibility() -> None:
    ledger = ResourceLedger()
    source = ExactSource((1, 0), 2, blank=2, extent=2, alphabet_size=2)
    with build_tile_projection(
        CollatzPhysicalBlockEffect(), SourceGeometry(ledger, source)
    ) as projection:
        _unused_adapter_binding, _unused_action_binding, interface_id, arena = (
            division_interface(projection)
        )
        record = arena.resolve(interface_id)
        interface = arena.interface(record.signature)
        before = ledger.snapshot()
        swapped = replace(record.components, activity=record.components.termination)
        with pytest.raises(ValueError, match="activity summary"):
            arena.intern(record.signature, swapped)
        assert ledger.snapshot() == before
        false = arena.functions.atom(FunctionSignature(interface.inputs, BOOL), 0)
        restricted = arena.intern_interface(replace(interface, admissible=false))
        before = ledger.snapshot()
        with pytest.raises(ValueError, match="admissibility"):
            arena.intern(restricted, record.components)
        after = ledger.snapshot()
        assert (before.entries, before.nodes) == (after.entries, after.nodes)


def test_unreachable_threshold_cannot_authorize_affine_substitution() -> None:
    with pytest.raises(ValueError, match="uncertified activation threshold"):
        DivisionCarry(RadixRemainderTransfer(7, 2, 1), 6)
    carry = DivisionCarry.leaf(7, 1)
    ledger = ResourceLedger()
    assert_rejected_atomically(
        ledger, lambda: carry.preimage(True, ledger), ValueError, match="finite domain"
    )
