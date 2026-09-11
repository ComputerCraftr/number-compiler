"""Scoped production transfer carrier for the complete primitive equations."""

from __future__ import annotations

from array import array
from dataclasses import replace
from itertools import product
from typing import TYPE_CHECKING, Never, TypedDict, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BlockEffect,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken, ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID,
    FieldGeometry,
    FieldGeometryArena,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.field_images import SourceCellArena
from number_compiler.hashlife.execution.field_transfer import FieldTransferExecutor
from number_compiler.hashlife.execution.field_transfers import (
    FieldTransferArena,
    FieldTransferRequestKey,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondQuotientArena,
)
from number_compiler.hashlife.interfaces.semantic_interfaces import (
    PrimitiveSemanticTransferAdapter,
    SemanticBoundaryArena,
    SemanticLocalInterfaceCompiler,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.execution.field_images import (
        SourceCellArena,
        SourceCellID,
    )
    from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
    )
    from number_compiler.hashlife.interfaces.semantic_interfaces import (
        SemanticLocalInterfaceCompiler,
    )
    from number_compiler.resources.ledger import ResourceLedger


def _primitive(mode: str = "normal") -> FiniteBlockEffect:
    left = [
        q if mode == "forget-source" else (q + symbol) % 2
        for q in range(2)
        for symbol in range(4)
    ]
    right = [
        q if mode == "forget-source" else q ^ (symbol == 1)
        for q in range(2)
        for symbol in range(4)
    ]
    outputs = [
        ((a + r) % 2 if mode == "forget-source" else (a + symbol + 2 * r) % 4)
        for a in range(2)
        for symbol in range(4)
        for r in range(2)
    ]
    return FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=2,
        right_count=2,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", left),
        right_transitions=array("I", right),
        outputs=bytes(outputs),
        kernel_name="semantic-field-test",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=False,
    )


def _setup(
    word: tuple[int, ...], effect: FiniteBlockEffect | None = None
) -> tuple[
    ResourceLedger,
    SourceCellArena,
    SourceCellID,
    DiamondKernelArena,
    ActionProgramID,
    DiamondQuotientArena,
    SemanticLocalInterfaceCompiler,
]:
    effect = _primitive() if effect is None else effect
    ledger = ResourceLedger()
    geometry = SourceGeometry(
        ledger,
        ExactSource(
            word,
            2,
            blank=effect.blank,
            extent=len(word),
            alphabet_size=effect.blank + 1,
        ),
    )
    geometry.span(word, effect.blank, len(word))
    sources = SourceCellArena(geometry)
    root = sources.intern(0, len(word).bit_length() - 1)
    kernels = DiamondKernelArena(ledger)
    kernel = kernels.intern(effect)
    quotients = DiamondQuotientArena(SemanticFunctionArena(ledger))
    compiler = SemanticLocalInterfaceCompiler(kernels, quotients, sources)
    return ledger, sources, root, kernels, kernel, quotients, compiler


def _oracle(
    effect: BlockEffect,
    word: tuple[int, ...],
    left: int,
    right: int,
    coordinate: int,
) -> dict[str, object]:
    ls: list[object] = [left]
    rs: list[object] = [right]
    for symbol in word:
        ls.append(effect.advance(BoundarySide.LEFT, ls[-1], symbol))
    for symbol in reversed(word):
        rs.append(effect.advance(BoundarySide.RIGHT, rs[-1], symbol))
    rs.reverse()
    output = [effect.emit(ls[i], symbol, rs[i + 1]) for i, symbol in enumerate(word)]
    active = [i for i, symbol in enumerate(output) if symbol != effect.blank]
    source = [i for i, symbol in enumerate(word) if symbol != effect.blank]
    width = len(word)
    extent = active[-1] + 1 if active else 0
    return dict(
        zip(
            COMPONENT_ROLES,
            (
                ls[-1],
                rs[0],
                output[coordinate],
                int(bool(active)),
                active[0] if active else width,
                active[-1] if active else width,
                extent,
                output[0],
                output[-1],
                width + extent - (source[-1] + 1 if source else 0),
                int(not active),
                output[coordinate],
                coordinate,
            ),
            strict=True,
        )
    )


@pytest.mark.parametrize("word", [(0,), (3,), (0, 1), (3, 3), (0, 1, 3, 0)])
def test_complete_interface_matches_every_port_and_coordinate(
    word: tuple[int, int, int, int] | tuple[int, int] | tuple[int],
) -> None:
    _, _, root, _, kernel, quotients, compiler = _setup(word)
    signature = compiler.signature(kernel, len(word).bit_length() - 1)
    interface = compiler.compile(kernel, root, signature)
    effect = compiler.kernels.kernel(kernel).effect
    for left, right, coordinate in product(range(2), range(2), range(len(word))):
        expected = _oracle(effect, word, left, right, coordinate)
        assert {
            role: compiler.observe(interface, role, left, right, coordinate)
            for role in COMPONENT_ROLES
        } == expected
    record = quotients.resolve(interface)
    assert len(record.components.functions()) == 13


def test_semantically_equal_source_bindings_alias_before_transfer_publication() -> None:
    effect = _primitive("forget-source")
    _, sources, root, _, kernel, _, compiler = _setup((0, 1), effect)
    left, right = sources.children(root)
    signature = compiler.signature(kernel, 0)
    assert compiler.compile(kernel, left, signature) == compiler.compile(
        kernel, right, signature
    )


def test_source_interface_cache_is_scoped_by_complete_kernel_handle() -> None:
    word = (0, 1)
    ledger, sources, root, kernels, first, quotients, compiler = _setup(word)
    second = kernels.intern(_primitive("forget-source"))
    first_signature = compiler.signature(first, 1)
    second_signature = compiler.signature(second, 1)
    first_interface = compiler.compile(first, root, first_signature)
    second_interface = compiler.compile(second, root, second_signature)
    assert first_interface != second_interface
    assert compiler.compile(first, root, first_signature) == first_interface
    assert compiler.compile(second, root, second_signature) == second_interface

    from number_compiler.resources.ownership import audit_execution_ownership

    ownership = audit_execution_ownership(ledger)
    assert ownership.violations == ()


def test_huge_spatial_level_does_not_create_coordinate_port_or_cartesian_summary() -> (
    None
):
    _, _, _, _, kernel, quotients, compiler = _setup((0,))
    signature = compiler.signature(kernel, 10**9)
    contract = quotients.interface(signature)
    assert tuple(port.variable.role for port in contract.inputs) == (
        "macro-left",
        "macro-right",
    )
    assert all(port.cardinality <= 2 for port in contract.inputs)
    assert all("coordinate" not in repr(port.variable) for port in contract.inputs)
    assert not hasattr(compiler, "_summary_all_ports")


def test_parent_transfer_warm_hit_needs_no_compiler_or_source_leaf(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, sources, root, kernels, kernel, quotients, compiler = _setup((0, 1, 3, 0))
    action_owner = ArenaToken("semantic-test-actions")
    action = FieldCellActionID(action_owner, "field-cell-action", 0)
    boundaries = SemanticBoundaryArena(ledger)
    incoming = boundaries.intern(0, 0)
    adapter = PrimitiveSemanticTransferAdapter(
        compiler,
        boundaries,
        lambda value: value.validate(action_owner, "field-cell-action", size=1),
        lambda _value: kernel,
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(2))
    signature = compiler.signature(kernel, 2)
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=action_owner,
        output_owner=compiler.outputs.owner,
        action_validate=lambda value: value.validate(
            action_owner, "field-cell-action", size=1
        ),
        output_validate=compiler.outputs.validate,
    )
    adapter.attach_transfers(transfers)
    executor = FieldTransferExecutor(transfers, adapter)
    first = executor.transfer(action, root, geometry, signature)
    expected = executor.point(first, root, incoming, 2)
    leaf_visits = ledger.counters.get("source_leaf_visits", 0)

    def poison(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("warm parent descended into semantic construction")

    monkeypatch.setattr(compiler, "compile", poison)
    monkeypatch.setattr(compiler.outputs, "intern", poison)
    assert executor.transfer(action, root, geometry, signature) == first
    assert executor.point(first, root, incoming, 2) == expected
    assert ledger.counters.get("source_leaf_visits", 0) == leaf_visits

    application = executor.application(action, root, geometry, signature, incoming)

    def no_transfer(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("invalid scalar reached a warm transfer lookup")

    monkeypatch.setattr(executor, "transfer", no_transfer)
    for invalid in (True, False, 0.0, 2.0, "2"):
        with pytest.raises(TypeError, match="exact integer"):
            application.point(invalid)  # type: ignore[arg-type]


def test_transfer_request_rejects_scoped_aliases_before_warm_lookup_or_mutation() -> (
    None
):
    ledger, sources, root, kernels, kernel, quotients, compiler = _setup((0, 1))
    action_owner = ArenaToken("semantic-test-actions")
    action = FieldCellActionID(action_owner, "field-cell-action", 0)
    boundaries = SemanticBoundaryArena(ledger)
    adapter = PrimitiveSemanticTransferAdapter(
        compiler,
        boundaries,
        lambda value: value.validate(action_owner, "field-cell-action", size=1),
        lambda _value: kernel,
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(1))
    signature = compiler.signature(kernel, 1)
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=action_owner,
        output_owner=compiler.outputs.owner,
        action_validate=lambda value: value.validate(
            action_owner, "field-cell-action", size=1
        ),
        output_validate=compiler.outputs.validate,
    )
    adapter.attach_transfers(transfers)
    executor = FieldTransferExecutor(transfers, adapter)
    expected = executor.transfer(action, root, geometry, signature)
    key = FieldTransferRequestKey(action, root, geometry, signature)
    assert transfers.probe(key) == expected

    invalid = (
        replace(
            key,
            action=FieldCellActionID(
                ArenaToken("semantic-test-actions"), action.kind, 0
            ),
        ),
        replace(key, action=FieldCellActionID(action.owner, "wrong-kind", 0)),
        replace(key, action=FieldCellActionID(action.owner, action.kind, 1)),
        replace(
            key, source=type(root)(ArenaToken("source-cells"), root.kind, root.local_id)
        ),
        replace(key, source=cast("SourceCellID", root.local_id)),
        replace(key, geometry=type(geometry)(geometry.owner, geometry.kind, 99)),
        replace(
            key,
            signature=type(signature)(
                signature.owner, "wrong-kind", signature.local_id
            ),
        ),
        replace(key, action=cast("FieldCellActionID", True)),
        replace(key, geometry=cast("FieldGeometryID", 0.0)),
    )
    for forged in invalid:
        before = ledger.snapshot()
        with pytest.raises((TypeError, ValueError)):
            transfers.probe(forged)
        assert ledger.snapshot() == before


def test_transfer_semantic_key_excludes_occurrence_and_observation_coordinates() -> (
    None
):
    ledger, sources, root, _, kernel, quotients, compiler = _setup((0, 1))
    action_owner = ArenaToken("semantic-test-actions")
    action = FieldCellActionID(action_owner, "field-cell-action", 0)
    boundaries = SemanticBoundaryArena(ledger)
    adapter = PrimitiveSemanticTransferAdapter(
        compiler,
        boundaries,
        lambda value: value.validate(action_owner, "field-cell-action", size=1),
        lambda _value: kernel,
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(1))
    signature = compiler.signature(kernel, 1)
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=action_owner,
        output_owner=compiler.outputs.owner,
        action_validate=lambda value: value.validate(
            action_owner, "field-cell-action", size=1
        ),
        output_validate=compiler.outputs.validate,
    )
    adapter.attach_transfers(transfers)
    FieldTransferExecutor(transfers, adapter).transfer(
        action,
        root,
        geometry,
        signature,
    )
    semantic = next(iter(transfers._keys))
    assert set(semantic.__dataclass_fields__) == {
        "level",
        "interface",
        "output",
        "geometry",
    }
    assert not any(
        token in name
        for name in semantic.__dataclass_fields__
        for token in ("source", "generation", "coordinate", "position", "trajectory")
    )


@pytest.mark.parametrize(
    ("field", "value", "error"),
    (
        ("action_owner", True, TypeError),
        ("output_owner", 0, TypeError),
        ("action_kind", True, ValueError),
        ("action_kind", "", ValueError),
        ("output_kind", 1.0, ValueError),
        ("output_kind", "", ValueError),
    ),
)
def test_transfer_arena_rejects_owner_and_sort_aliases_atomically(
    field: str,
    value: object,
    error: type[Exception],
) -> None:
    ledger, sources, _, _, _, quotients, compiler = _setup((0, 1))
    geometries = FieldGeometryArena(ledger)
    action_owner = ArenaToken("semantic-test-actions")
    arguments = {
        "action_owner": action_owner,
        "output_owner": compiler.outputs.owner,
        "action_kind": "field-cell-action",
        "output_kind": "coordinate-output-morphism",
    }
    arguments[field] = value
    before = ledger.snapshot()
    with pytest.raises(error):
        FieldTransferArena(
            ledger,
            sources,
            geometries,
            quotients,
            action_validate=lambda _value: None,
            output_validate=lambda _value: None,
            **cast("TransferDomains", arguments),
        )
    assert ledger.snapshot() == before


def test_binding_eviction_preserves_canonical_transfer_id_and_accounting() -> None:
    ledger, sources, root, _, kernel, quotients, compiler = _setup((0, 1))
    action_owner = ArenaToken("semantic-test-actions")
    action = FieldCellActionID(action_owner, "field-cell-action", 0)
    boundaries = SemanticBoundaryArena(ledger)
    adapter = PrimitiveSemanticTransferAdapter(
        compiler,
        boundaries,
        lambda value: value.validate(action_owner, "field-cell-action", size=1),
        lambda _value: kernel,
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(1))
    signature = compiler.signature(kernel, 1)
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=action_owner,
        output_owner=compiler.outputs.owner,
        action_validate=lambda value: value.validate(
            action_owner,
            "field-cell-action",
            size=1,
        ),
        output_validate=compiler.outputs.validate,
    )
    adapter.attach_transfers(transfers)
    executor = FieldTransferExecutor(transfers, adapter)
    first = executor.transfer(action, root, geometry, signature)
    record = transfers.resolve(first)
    before_nodes = transfers.retained_transfers
    transfers.clear()
    assert transfers.resolve(first) == record
    assert transfers.retained_transfers == before_nodes
    assert transfers.retained_bindings == 0
    second = executor.transfer(action, root, geometry, signature)
    assert second == first
    assert transfers.resolve(first) == record


def test_global_query_eviction_cannot_stale_semantic_transfer_ids() -> None:
    ledger, sources, root, _, kernel, quotients, compiler = _setup((0, 1))
    action_owner = ArenaToken("semantic-test-actions")
    action = FieldCellActionID(action_owner, "field-cell-action", 0)
    adapter = PrimitiveSemanticTransferAdapter(
        compiler,
        SemanticBoundaryArena(ledger),
        lambda value: value.validate(action_owner, "field-cell-action", size=1),
        lambda _value: kernel,
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(1))
    signature = compiler.signature(kernel, 1)
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=action_owner,
        output_owner=compiler.outputs.owner,
        action_validate=lambda value: value.validate(
            action_owner, "field-cell-action", size=1
        ),
        output_validate=compiler.outputs.validate,
    )
    adapter.attach_transfers(transfers)
    executor = FieldTransferExecutor(transfers, adapter)
    first = executor.transfer(action, root, geometry, signature)
    record = transfers.resolve(first)
    before_inventory = {row.owner: row for row in ledger.inventory()}
    node_entries = before_inventory[transfers._node_owner].entries
    key_entries = before_inventory[transfers._key_owner].entries
    ledger.evict_query_memos()
    assert transfers.resolve(first) == record
    assert transfers.retained_transfers == 1
    assert transfers.retained_bindings == 0
    after_inventory = {row.owner: row for row in ledger.inventory()}
    assert after_inventory[transfers._node_owner].entries == node_entries
    assert after_inventory[transfers._key_owner].entries == key_entries
    assert executor.transfer(action, root, geometry, signature) == first


def test_semantic_alias_with_inconsistent_occurrence_bound_rejects_atomically() -> None:
    effect = _primitive("forget-source")
    ledger, sources, root, _, kernel, quotients, compiler = _setup((0, 1), effect)
    left, right = sources.children(root)
    action_owner = ArenaToken("semantic-test-actions")
    action = FieldCellActionID(action_owner, "field-cell-action", 0)
    boundaries = SemanticBoundaryArena(ledger)
    adapter = PrimitiveSemanticTransferAdapter(
        compiler,
        boundaries,
        lambda value: value.validate(action_owner, "field-cell-action", size=1),
        lambda _value: kernel,
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(0))
    signature = compiler.signature(kernel, 0)
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=action_owner,
        output_owner=compiler.outputs.owner,
        action_validate=lambda value: value.validate(
            action_owner,
            "field-cell-action",
            size=1,
        ),
        output_validate=compiler.outputs.validate,
    )
    adapter.attach_transfers(transfers)
    executor = FieldTransferExecutor(transfers, adapter)
    first = executor.transfer(action, left, geometry, signature)
    record = transfers.resolve(first)
    transfers.clear_bindings()
    ledger_before = ledger.snapshot()
    before = (
        len(transfers._nodes),
        len(transfers._keys),
        len(transfers._bindings),
        ledger.counters.get("field_transfer_binding_publications", 0),
    )
    with pytest.raises(ValueError, match="inconsistent admission bounds"):
        transfers.publish(
            FieldTransferRequestKey(action, right, geometry, signature),
            replace(record, extent_bound=record.extent_bound + 1),
        )
    assert (
        len(transfers._nodes),
        len(transfers._keys),
        len(transfers._bindings),
        ledger.counters.get("field_transfer_binding_publications", 0),
    ) == before
    assert ledger.snapshot() == ledger_before


def test_transfer_observation_rejects_an_unpublished_source_alias() -> None:
    effect = _primitive("forget-source")
    ledger, sources, root, kernels, kernel, quotients, compiler = _setup(
        (0, 1),
        effect,
    )
    left, right = sources.children(root)
    action_owner = ArenaToken("semantic-test-actions")
    action = FieldCellActionID(action_owner, "field-cell-action", 0)
    boundaries = SemanticBoundaryArena(ledger)
    incoming = boundaries.intern(0, 0)
    adapter = PrimitiveSemanticTransferAdapter(
        compiler,
        boundaries,
        lambda value: value.validate(action_owner, "field-cell-action", size=1),
        lambda _value: kernel,
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(0))
    signature = compiler.signature(kernel, 0)
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=action_owner,
        output_owner=compiler.outputs.owner,
        action_validate=lambda value: value.validate(
            action_owner,
            "field-cell-action",
            size=1,
        ),
        output_validate=compiler.outputs.validate,
    )
    adapter.attach_transfers(transfers)
    executor = FieldTransferExecutor(transfers, adapter)
    first = executor.transfer(action, left, geometry, signature)
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="not published for this source"):
        executor.point(first, right, incoming, 0)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)

    # Once the equal occurrence is explicitly bound it can reuse the same
    # semantic transfer and be observed through its own source authority.
    second = executor.transfer(action, right, geometry, signature)
    assert second == first
    assert executor.point(second, right, incoming, 0) in range(effect.blank + 1)


def test_rejected_transfer_binding_is_atomic() -> None:
    ledger, sources, root, _, kernel, quotients, compiler = _setup((0, 1))
    action_owner = ArenaToken("semantic-test-actions")
    action = FieldCellActionID(action_owner, "field-cell-action", 0)
    boundaries = SemanticBoundaryArena(ledger)
    adapter = PrimitiveSemanticTransferAdapter(
        compiler,
        boundaries,
        lambda value: value.validate(action_owner, "field-cell-action", size=1),
        lambda _value: kernel,
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(1))
    signature = compiler.signature(kernel, 1)
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=action_owner,
        output_owner=compiler.outputs.owner,
        action_validate=lambda value: value.validate(
            action_owner, "field-cell-action", size=1
        ),
        output_validate=compiler.outputs.validate,
    )
    adapter.attach_transfers(transfers)
    executor = FieldTransferExecutor(transfers, adapter)
    executor.transfer(action, root, geometry, signature)
    transfers.clear_bindings()
    before = ledger.snapshot()
    ledger.max_cache_entries = ledger.entries
    with pytest.raises(BlockContextBudgetExceeded):
        executor.transfer(action, root, geometry, signature)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert transfers.retained_bindings == 0


def test_transfer_publication_rejects_interface_from_another_signature() -> None:
    from number_compiler.hashlife.execution.field_transfers import (
        FieldTransferRequestKey,
    )

    ledger, sources, root, _, kernel, quotients, compiler = _setup((0, 1))
    action_owner = ArenaToken("semantic-test-actions")
    action = FieldCellActionID(action_owner, "field-cell-action", 0)
    boundaries = SemanticBoundaryArena(ledger)
    adapter = PrimitiveSemanticTransferAdapter(
        compiler,
        boundaries,
        lambda value: value.validate(action_owner, "field-cell-action", size=1),
        lambda _value: kernel,
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(1))
    signature = compiler.signature(kernel, 1)
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=action_owner,
        output_owner=compiler.outputs.owner,
        action_validate=lambda value: value.validate(
            action_owner,
            "field-cell-action",
            size=1,
        ),
        output_validate=compiler.outputs.validate,
    )
    adapter.attach_transfers(transfers)
    executor = FieldTransferExecutor(transfers, adapter)
    transfer = executor.transfer(action, root, geometry, signature)
    record = transfers.resolve(transfer)
    other_signature = compiler.signature(kernel, 0)
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="another port signature"):
        transfers.publish(
            FieldTransferRequestKey(action, root, geometry, other_signature),
            record,
        )
    with pytest.raises(ValueError, match="level differs"):
        transfers.publish(
            FieldTransferRequestKey(action, root, geometry, signature),
            replace(record, level=0),
        )
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_transfer_observation_authority_is_in_independent_payload_audit() -> None:
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    ledger, sources, root, _, kernel, quotients, compiler = _setup((0, 1))
    action_owner = ArenaToken("semantic-test-actions")
    action = FieldCellActionID(action_owner, "field-cell-action", 0)
    boundaries = SemanticBoundaryArena(ledger)
    adapter = PrimitiveSemanticTransferAdapter(
        compiler,
        boundaries,
        lambda value: value.validate(action_owner, "field-cell-action", size=1),
        lambda _value: kernel,
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(1))
    signature = compiler.signature(kernel, 1)
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=action_owner,
        output_owner=compiler.outputs.owner,
        action_validate=lambda value: value.validate(
            action_owner,
            "field-cell-action",
            size=1,
        ),
        output_validate=compiler.outputs.validate,
    )
    adapter.attach_transfers(transfers)
    FieldTransferExecutor(transfers, adapter).transfer(
        action,
        root,
        geometry,
        signature,
    )
    report = collect_ledger_metrics(ledger)
    assert report.resource_accounting_mismatch == 0
    assert audit_field_image_payloads(ledger).invalid == frozenset()
    bindings = [
        row for row in report.resource_inventory if row.role == "field_transfer_binding"
    ]
    observations = [
        row for row in report.resource_inventory if row.role == "observation_memo"
    ]
    assert len(bindings) == len(observations) == 1
    assert bindings[0].entries == bindings[0].observed_entries == 1
    assert observations[0].entries == observations[0].observed_entries == 1


class TransferDomains(TypedDict):
    action_owner: ArenaToken
    output_owner: ArenaToken
    action_kind: str
    output_kind: str
