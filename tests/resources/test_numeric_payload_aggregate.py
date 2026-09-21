"""A bounded limb is not permission to retain a width-growing numeric word."""

from __future__ import annotations

from collections.abc import Generator
from dataclasses import dataclass
from inspect import isgenerator
from typing import cast

import pytest

from devtools.proofs.lazy_collatz import (
    CarryRangeSummary,
    CarryRangeTransfer,
    Mul3Carry,
    _Mul3Port,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
    TransferSummaryID,
    WordLimb,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_port_action import (
    FinitePortActionArena,
    FoldedPortCut,
    PortComponent,
    PortVariable,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.numeric_payload import numeric_aggregate_audit
from number_compiler.resources.stores import LedgerList


@dataclass(frozen=True)
class RenamedLink:
    first: object
    next: object = None


def limbs() -> tuple[WordLimb, ...]:
    # This is a test oracle. Production may neither build it nor retain its
    # four numeric pieces merely because each individual piece fits a limb.
    tail = (1 << 254) + (0x91A0B76CDE0557 << 128) + (0xABCDA99B << 64) + 19
    values = tuple(
        WordLimb((tail >> (64 * i)) & ((1 << 64) - 1), 63 if i == 3 else 64)
        for i in range(4)
    )
    assert sum(piece.value << (64 * i) for i, piece in enumerate(values)) == tail
    return values


@pytest.mark.parametrize("shape", ("list", "nested", "dag", "mapping", "identity"))
def test_four_bounded_limbs_cannot_masquerade_as_an_aggregate_summary(
    shape: str,
) -> None:
    pieces = limbs()
    payload: object
    if shape == "list":
        payload = list(pieces)
    elif shape == "nested":
        payload = ((pieces[0], (pieces[1],)), ((pieces[2],), pieces[3]))
    elif shape == "dag":
        payload = None
        for piece in reversed(pieces):
            payload = RenamedLink(piece, payload)
    elif shape == "mapping":
        payload = {i: piece for i, piece in enumerate(pieces)}
    else:
        payload = SemanticIdentity(
            "claimed-kernel", tuple(piece.value for piece in pieces)
        )
    ledger = ResourceLedger()
    owner = ledger.register("observer", "transfer_summary")
    storage: LedgerList[object]
    storage = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    storage.append(payload)
    for piece in pieces:
        ledger.observe_arithmetic(piece.value)
    report = collect_ledger_metrics(ledger)
    assert report.maximum_arithmetic_bits <= 64
    assert report.forbidden_future_payloads > 0
    assert report.resource_accounting_mismatch == 0


def test_payload_callbacks_cannot_erase_the_aggregate_relationship() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("observer", "transfer_summary")
    storage: LedgerList[object]
    storage = ledger.make_list(owner)
    ledger.reserve(owner, entries=4, nodes=4)
    storage.extend(limbs())
    # Each callback result is individually valid. Actual container traversal
    # must still see all four pieces as one retained numeric sequence.
    ledger.register_container(
        owner, storage, node_count=lambda: 4, payloads=lambda: iter(storage)
    )
    assert collect_ledger_metrics(ledger).forbidden_future_payloads > 0


def test_an_arbitrary_symbolic_anchor_cannot_hide_nested_numeric_limbs() -> None:
    token = ArenaToken("symbol")
    anchor = ActionProgramID(token, "program", 0)
    payload = [(anchor, piece) for piece in limbs()]
    audit = numeric_aggregate_audit(
        payload, semantic=lambda value: isinstance(value, ActionProgramID)
    )
    assert audit.forbidden_objects
    assert audit.maximum_untyped_bits == 255


def test_numeric_pieces_are_rejected_as_joint_port_components() -> None:
    arena = FinitePortActionArena()
    ports = tuple(PortVariable(i, 0, "carry", 0) for i in range(4))
    for port, piece in zip(ports, limbs()):
        with pytest.raises(ValueError, match="transfer handles"):
            PortComponent(port, cast("TransferSummaryID", piece))
    with pytest.raises(ValueError, match="symbolic port"):
        FoldedPortCut(cast("tuple[PortComponent, ...]", limbs()))
    valid = arena.cut({port: arena.variable(port) for port in ports})
    audit = numeric_aggregate_audit(
        valid, semantic=lambda value: type(value) in (FoldedPortCut, PortComponent)
    )
    assert not audit.forbidden_objects


def test_collatz_carry_records_enforce_the_actual_three_state_machine() -> None:
    program = ActionProgramID(ArenaToken("mul3"), "program", 0)
    for incoming in Mul3Carry:
        for bit in (0, 1):
            port = _Mul3Port(program, incoming)
            total = 3 * bit + int(incoming)
            assert port.advance(bit, ResourceLedger()) == total & 1
            assert port.state == Mul3Carry(total >> 1)
    with pytest.raises(ValueError, match="finite carry"):
        _Mul3Port(program, cast("Mul3Carry", limbs()[0]))
    with pytest.raises(ValueError, match="finite carry"):
        CarryRangeSummary(20, cast("int", limbs()[0]), 0, 19)
    with pytest.raises(ValueError, match="exactly three"):
        CarryRangeTransfer(tuple(CarryRangeSummary(20, 0, 0, 19) for _ in range(4)))


def test_a_suspended_generator_cannot_hold_an_untyped_four_limb_tail() -> None:
    def hidden(
        pieces: tuple[WordLimb, ...],
    ) -> Generator[None | dict[int, WordLimb], None, None]:
        renamed = {i: piece for i, piece in enumerate(pieces)}
        yield None
        yield renamed

    continuation = hidden(limbs())
    next(continuation)
    audit = numeric_aggregate_audit([continuation], semantic=lambda value: False)
    assert audit.forbidden_objects
    assert audit.maximum_untyped_bits >= 255
    continuation.close()


def test_transient_collatz_cut_contains_valid_machine_ports_not_numeric_words() -> None:
    from devtools.proofs.lazy_collatz import (
        CollatzLazyView,
        LazyCollatzApplication,
        _ShiftPort,
    )

    source = (1 << 253) + 127
    app = LazyCollatzApplication(
        2, 0, tuple((source >> i) & 1 for i in range(source.bit_length()))
    )
    result = app.advance_events(20)
    stream = app._stream(result.view)
    next(stream)
    assert isgenerator(stream) and stream.gi_frame is not None
    ports = stream.gi_frame.f_locals["ports"]
    assert len(ports) > 4
    for port in ports:
        assert type(port) in (_Mul3Port, _ShiftPort)
        assert isinstance(port.program, ActionProgramID)
        port.program.validate(app.token, "program")
        if isinstance(port, _Mul3Port):
            assert type(port.state) is Mul3Carry
    semantic_types = (
        LazyCollatzApplication,
        CollatzLazyView,
        ActionProgramID,
        _Mul3Port,
        _ShiftPort,
    )
    audit = numeric_aggregate_audit(
        stream, semantic=lambda value: type(value) in semantic_types
    )
    assert not audit.forbidden_objects
    assert numeric_aggregate_audit(
        (stream, limbs()), semantic=lambda value: type(value) in semantic_types
    ).forbidden_objects
    stream.close()


def test_exact_microblocks_cannot_accept_numeric_limb_wrappers_or_wide_payloads() -> (
    None
):
    from number_compiler.projection.microblock_cache import ExactMicroblock

    with pytest.raises(ValueError, match="at most 64"):
        ExactMicroblock(cast("int", limbs()[0]), 1)
    with pytest.raises(ValueError, match="at most 64"):
        ExactMicroblock(1 << 64, 64)


def test_numeric_aggregate_classifies_each_object_once() -> None:
    root = ("semantic", 7)
    calls: dict[int, int] = {}

    def semantic(value: object) -> bool:
        identity = id(value)
        calls[identity] = calls.get(identity, 0) + 1
        return value is root

    audit = numeric_aggregate_audit((root, root), semantic=semantic)
    assert not audit.forbidden_objects
    assert calls[id(root)] == 1
