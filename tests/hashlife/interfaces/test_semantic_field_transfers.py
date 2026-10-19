"""Scoped production transfer carrier for the complete primitive equations."""

from __future__ import annotations

from array import array
from dataclasses import replace
from functools import partial
from itertools import product
from typing import TYPE_CHECKING, NamedTuple, Never, TypedDict, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
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
    FieldTransferID,
    FieldTransferRecord,
    FieldTransferRequestKey,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import (
    DiamondQuotientArena,
)
from number_compiler.hashlife.interfaces.semantic_interfaces import (
    PrimitiveSemanticTransferAdapter,
    SemanticBoundaryArena,
    SemanticLocalInterfaceCompiler,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    COMPONENT_ROLES,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.assertions import assert_rejected_atomically
from tests.support.semantic_oracles import macro_oracle as _oracle

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.execution.field_images import (
        SourceCellID,
    )


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


def _transfer_setup(
    ledger: ResourceLedger,
    sources: SourceCellArena,
    kernel: ActionProgramID,
    quotients: DiamondQuotientArena,
    compiler: SemanticLocalInterfaceCompiler,
    level: int,
) -> tuple[
    FieldCellActionID,
    SemanticBoundaryArena,
    FieldGeometryID,
    PortSignatureID,
    FieldTransferArena,
    FieldTransferExecutor,
]:
    """Construct one consistently scoped transfer fixture for authority tests."""
    owner = ArenaToken("semantic-test-actions")
    action = FieldCellActionID(owner, "field-cell-action", 0)
    boundaries = SemanticBoundaryArena(ledger)

    def validate(value: FieldCellActionID) -> None:
        value.validate(owner, "field-cell-action", size=1)

    adapter = PrimitiveSemanticTransferAdapter(
        compiler, boundaries, validate, lambda _value: kernel
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(level))
    signature = compiler.signature(kernel, level)
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=owner,
        output_owner=compiler.outputs.owner,
        action_validate=validate,
        output_validate=compiler.outputs.validate,
    )
    adapter.attach_transfers(transfers)
    return (
        action,
        boundaries,
        geometry,
        signature,
        transfers,
        FieldTransferExecutor(transfers, adapter),
    )


class _TransferFixture(NamedTuple):
    ledger: ResourceLedger
    sources: SourceCellArena
    root: SourceCellID
    compiler: SemanticLocalInterfaceCompiler
    kernel: ActionProgramID
    action: FieldCellActionID
    boundaries: SemanticBoundaryArena
    geometry: FieldGeometryID
    signature: PortSignatureID
    transfers: FieldTransferArena
    executor: FieldTransferExecutor


def _transfer_fixture(
    word: tuple[int, ...], level: int, effect: FiniteBlockEffect | None = None
) -> _TransferFixture:
    ledger, sources, root, _kernels, kernel, quotients, compiler = _setup(word, effect)
    action, boundaries, geometry, signature, transfers, executor = _transfer_setup(
        ledger, sources, kernel, quotients, compiler, level
    )
    return _TransferFixture(
        ledger,
        sources,
        root,
        compiler,
        kernel,
        action,
        boundaries,
        geometry,
        signature,
        transfers,
        executor,
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
    ledger, _sources, root, kernels, first, _quotients, compiler = _setup(word)
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
    fixture = _transfer_fixture((0, 1, 3, 0), 2)
    incoming = fixture.boundaries.intern(0, 0)
    first = fixture.executor.transfer(
        fixture.action, fixture.root, fixture.geometry, fixture.signature
    )
    expected = fixture.executor.point(first, fixture.root, incoming, 2)
    leaf_visits = fixture.ledger.counters.get("source_leaf_visits", 0)

    def poison(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("warm parent descended into semantic construction")

    monkeypatch.setattr(fixture.compiler, "compile", poison)
    monkeypatch.setattr(fixture.compiler.outputs, "intern", poison)
    assert (
        fixture.executor.transfer(
            fixture.action, fixture.root, fixture.geometry, fixture.signature
        )
        == first
    )
    assert fixture.executor.point(first, fixture.root, incoming, 2) == expected
    assert fixture.ledger.counters.get("source_leaf_visits", 0) == leaf_visits

    application = fixture.executor.application(
        fixture.action, fixture.root, fixture.geometry, fixture.signature, incoming
    )

    def no_transfer(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("invalid scalar reached a warm transfer lookup")

    monkeypatch.setattr(fixture.executor, "transfer", no_transfer)
    for invalid in (True, False, 0.0, 2.0, "2"):
        with pytest.raises(TypeError, match="exact integer"):
            application.point(cast(int, invalid))


def test_transfer_request_rejects_scoped_aliases_before_warm_lookup_or_mutation() -> (
    None
):
    fixture = _transfer_fixture((0, 1), 1)
    expected = fixture.executor.transfer(
        fixture.action, fixture.root, fixture.geometry, fixture.signature
    )
    key = FieldTransferRequestKey(
        fixture.action, fixture.root, fixture.geometry, fixture.signature
    )
    assert fixture.transfers.probe(key) == expected

    invalid = (
        replace(
            key,
            action=FieldCellActionID(
                ArenaToken("semantic-test-actions"), fixture.action.kind, 0
            ),
        ),
        replace(key, action=FieldCellActionID(fixture.action.owner, "wrong-kind", 0)),
        replace(
            key, action=FieldCellActionID(fixture.action.owner, fixture.action.kind, 1)
        ),
        replace(
            key,
            source=type(fixture.root)(
                ArenaToken("source-cells"), fixture.root.kind, fixture.root.local_id
            ),
        ),
        replace(key, source=cast("SourceCellID", fixture.root.local_id)),
        replace(
            key,
            geometry=type(fixture.geometry)(
                fixture.geometry.owner, fixture.geometry.kind, 99
            ),
        ),
        replace(
            key,
            signature=type(fixture.signature)(
                fixture.signature.owner, "wrong-kind", fixture.signature.local_id
            ),
        ),
        replace(key, action=cast("FieldCellActionID", True)),
        replace(key, geometry=cast("FieldGeometryID", 0.0)),
    )
    for forged in invalid:
        assert_rejected_atomically(
            fixture.ledger,
            partial(fixture.transfers.probe, forged),
            (TypeError, ValueError),
        )


def test_transfer_semantic_key_excludes_occurrence_and_observation_coordinates() -> (
    None
):
    fixture = _transfer_fixture((0, 1), 1)
    fixture.executor.transfer(
        fixture.action,
        fixture.root,
        fixture.geometry,
        fixture.signature,
    )
    semantic = next(iter(fixture.transfers._keys))
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
    assert_rejected_atomically(
        ledger,
        lambda: FieldTransferArena(
            ledger,
            sources,
            geometries,
            quotients,
            action_validate=lambda _value: None,
            output_validate=lambda _value: None,
            **cast("TransferDomains", arguments),
        ),
        error,
    )


def _published_transfer_fixture() -> tuple[
    _TransferFixture, FieldTransferID, FieldTransferRecord
]:
    fixture = _transfer_fixture((0, 1), 1)
    transfer = fixture.executor.transfer(
        fixture.action, fixture.root, fixture.geometry, fixture.signature
    )
    return fixture, transfer, fixture.transfers.resolve(transfer)


def _alias_transfer_fixture() -> tuple[
    FiniteBlockEffect, _TransferFixture, SourceCellID, SourceCellID
]:
    effect = _primitive("forget-source")
    fixture = _transfer_fixture((0, 1), 0, effect)
    left, right = fixture.sources.children(fixture.root)
    return effect, fixture, left, right


def test_binding_eviction_preserves_canonical_transfer_id_and_accounting() -> None:
    fixture, first, record = _published_transfer_fixture()
    before_nodes = fixture.transfers.retained_transfers
    fixture.transfers.clear()
    assert fixture.transfers.resolve(first) == record
    assert fixture.transfers.retained_transfers == before_nodes
    assert fixture.transfers.retained_bindings == 0
    second = fixture.executor.transfer(
        fixture.action, fixture.root, fixture.geometry, fixture.signature
    )
    assert second == first
    assert fixture.transfers.resolve(first) == record


def test_global_query_eviction_cannot_stale_semantic_transfer_ids() -> None:
    fixture, first, record = _published_transfer_fixture()
    before_inventory = {row.owner: row for row in fixture.ledger.inventory()}
    node_entries = before_inventory[fixture.transfers._node_owner].entries
    key_entries = before_inventory[fixture.transfers._key_owner].entries
    fixture.ledger.evict_query_memos()
    assert fixture.transfers.resolve(first) == record
    assert fixture.transfers.retained_transfers == 1
    assert fixture.transfers.retained_bindings == 0
    after_inventory = {row.owner: row for row in fixture.ledger.inventory()}
    assert after_inventory[fixture.transfers._node_owner].entries == node_entries
    assert after_inventory[fixture.transfers._key_owner].entries == key_entries
    assert (
        fixture.executor.transfer(
            fixture.action, fixture.root, fixture.geometry, fixture.signature
        )
        == first
    )


def test_semantic_alias_with_inconsistent_occurrence_bound_rejects_atomically() -> None:
    _unused_effect_binding, fixture, left, right = _alias_transfer_fixture()
    first = fixture.executor.transfer(
        fixture.action, left, fixture.geometry, fixture.signature
    )
    record = fixture.transfers.resolve(first)
    fixture.transfers.clear_bindings()
    ledger_before = fixture.ledger.snapshot()
    before = (
        len(fixture.transfers._nodes),
        len(fixture.transfers._keys),
        len(fixture.transfers._bindings),
        fixture.ledger.counters.get("field_transfer_binding_publications", 0),
    )
    with pytest.raises(ValueError, match="inconsistent admission bounds"):
        fixture.transfers.publish(
            FieldTransferRequestKey(
                fixture.action, right, fixture.geometry, fixture.signature
            ),
            replace(record, extent_bound=record.extent_bound + 1),
        )
    assert (
        len(fixture.transfers._nodes),
        len(fixture.transfers._keys),
        len(fixture.transfers._bindings),
        fixture.ledger.counters.get("field_transfer_binding_publications", 0),
    ) == before
    assert fixture.ledger.snapshot() == ledger_before


def test_transfer_observation_rejects_an_unpublished_source_alias() -> None:
    effect, fixture, left, right = _alias_transfer_fixture()
    incoming = fixture.boundaries.intern(0, 0)
    first = fixture.executor.transfer(
        fixture.action, left, fixture.geometry, fixture.signature
    )
    before = fixture.ledger.snapshot()
    with pytest.raises(ValueError, match="not published for this source"):
        fixture.executor.point(first, right, incoming, 0)
    after = fixture.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)

    # Once the equal occurrence is explicitly bound it can reuse the same
    # semantic transfer and be observed through its own source authority.
    second = fixture.executor.transfer(
        fixture.action, right, fixture.geometry, fixture.signature
    )
    assert second == first
    assert fixture.executor.point(second, right, incoming, 0) in range(effect.blank + 1)


def test_rejected_transfer_binding_is_atomic() -> None:
    fixture = _transfer_fixture((0, 1), 1)
    fixture.executor.transfer(
        fixture.action, fixture.root, fixture.geometry, fixture.signature
    )
    fixture.transfers.clear_bindings()
    before = fixture.ledger.snapshot()
    fixture.ledger.max_cache_entries = fixture.ledger.entries
    with pytest.raises(BlockContextBudgetExceeded):
        fixture.executor.transfer(
            fixture.action, fixture.root, fixture.geometry, fixture.signature
        )
    after = fixture.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert fixture.transfers.retained_bindings == 0


def test_transfer_publication_rejects_interface_from_another_signature() -> None:
    from number_compiler.hashlife.execution.field_transfers import (
        FieldTransferRequestKey,
    )

    fixture, _unused_transfer_binding, record = _published_transfer_fixture()
    other_signature = fixture.compiler.signature(fixture.kernel, 0)
    before = fixture.ledger.snapshot()
    with pytest.raises(ValueError, match="another port signature"):
        fixture.transfers.publish(
            FieldTransferRequestKey(
                fixture.action, fixture.root, fixture.geometry, other_signature
            ),
            record,
        )
    with pytest.raises(ValueError, match="level differs"):
        fixture.transfers.publish(
            FieldTransferRequestKey(
                fixture.action, fixture.root, fixture.geometry, fixture.signature
            ),
            replace(record, level=0),
        )
    after = fixture.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_transfer_observation_authority_is_in_independent_payload_audit() -> None:
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    fixture = _transfer_fixture((0, 1), 1)
    fixture.executor.transfer(
        fixture.action,
        fixture.root,
        fixture.geometry,
        fixture.signature,
    )
    report = collect_ledger_metrics(fixture.ledger)
    assert report.resource_accounting_mismatch == 0
    assert audit_field_image_payloads(fixture.ledger).invalid == frozenset()
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
