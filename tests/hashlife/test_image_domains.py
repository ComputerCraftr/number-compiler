"""Recursive field images separate source occurrences from semantic macrocells."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass, fields, is_dataclass, replace

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaHandle,
    ArenaToken,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
    FieldGeometry,
    FieldGeometryArena,
)
from number_compiler.hashlife.execution.field_capabilities import (
    validate_field_image_application,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageRecord,
    FieldImageSummary,
    ImageRequestKey,
    RecursiveFieldImageArena,
)
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.resources.ledger import ResourceLedger
from tests.support.assertions import assert_rejected_atomically
from tests.support.recursive_field_images import (
    _application_setup,
    _SecondDomainArena,
    _setup,
)


def test_image_arena_rejects_callable_only_domain_before_registration() -> None:
    ledger, _, _signature, _, _, images, adapter, _ = _setup()
    assert_rejected_atomically(
        ledger,
        lambda: RecursiveFieldImageArena(
            ledger,
            images.sources,
            images.geometries,
            images.interfaces,
            signature_owner=images.interfaces.owner,
            action_owner=ArenaToken("callable-only-actions"),
            output_owner=ArenaToken("callable-only-outputs"),
            action_validate=adapter.validate_action,
            output_validate=adapter.validate_output,
            signature_for=adapter.signature,
        ),
        ValueError,
        match="supplied together",
    )


def test_image_domain_audit_rejects_missing_authority_metadata() -> None:
    from number_compiler.hashlife.execution.field_image_domains import _FieldImageDomain
    from number_compiler.resources.payload_audit import audit_registered_payloads

    ledger, _, _, _, _, images, _, _ = _setup()
    domain_key, domain = next(
        (key, value)
        for key, value in images._domains.items()
        if type(value) is _FieldImageDomain
    )
    images._domains[domain_key] = replace(domain, action_authority=None)

    audit = audit_registered_payloads(ledger, fresh=True)
    assert audit.forbidden_future_payloads > 0


def test_shared_image_arena_admits_exact_second_semantic_domain() -> None:
    ledger, source, signature, geometry, _, images, adapter, _ = _setup((0,))
    action_owner = ArenaToken("second-actions")
    output_owner = ArenaToken("second-outputs")
    action = FieldCellActionID(action_owner, "second-field-action", 0)
    output = CoordinateOutputMorphismID(output_owner, "second-output", 0)
    authority = _SecondDomainArena(
        ledger,
        action_owner,
        output_owner,
        signature,
    )
    images.admit_domain(
        images.interfaces,
        action_owner=action_owner,
        action_kind="second-field-action",
        action_validate=authority.validate_action,
        output_owner=output_owner,
        output_kind="second-output",
        output_validate=authority.validate_output,
        signature_kind=images.interfaces.signature_kind,
        signature_for=authority.signature,
        action_authority=authority,
        output_authority=authority,
        signature_authority=authority,
    )
    from number_compiler.hashlife.execution.field_images import FieldImageSummary

    request = ImageRequestKey(action, source, geometry, signature)
    record = FieldImageRecord(
        0,
        None,
        None,
        adapter.interface,
        output,
        geometry,
        FieldImageSummary(True, 0, 0, 1),
    )
    image = images.publish(request, record)
    images.validate_binding(request, image)
    assert images.resolve(image) == record

    before = ledger.snapshot()
    wrong = replace(record, output=adapter.output)
    with pytest.raises(ValueError, match="another semantic domain"):
        images.publish(request, wrong)
    assert ledger.snapshot() == before


def test_image_domains_are_charged_and_shared_output_authority_is_reused() -> None:
    ledger, source, signature, geometry, _, images, adapter, _ = _setup((0,))
    initial_entries = len(images._domains)
    output_owner = ArenaToken("shared-output-arena")
    first_action_owner = ArenaToken("shared-output-first-actions")
    first = _SecondDomainArena(
        ledger,
        first_action_owner,
        output_owner,
        signature,
        "shared-output-first-action",
        "shared-output",
    )
    before_entries = ledger.entries
    images.admit_domain(
        images.interfaces,
        action_owner=first_action_owner,
        action_kind=first.action_kind,
        action_validate=first.validate_action,
        output_owner=output_owner,
        output_kind=first.output_kind,
        output_validate=first.validate_output,
        signature_kind=images.interfaces.signature_kind,
        signature_for=first.signature,
        action_authority=first,
        output_authority=first,
        signature_authority=first,
    )
    assert len(images._domains) == initial_entries + 2
    assert ledger.entries == before_entries + 2

    second_action_owner = ArenaToken("shared-output-second-actions")
    second = _SecondDomainArena(
        ledger,
        second_action_owner,
        output_owner,
        signature,
        "shared-output-second-action",
        "shared-output",
    )
    action = FieldCellActionID(second_action_owner, second.action_kind, 0)
    output = CoordinateOutputMorphismID(output_owner, second.output_kind, 0)
    before_entries = ledger.entries
    images.admit_domain(
        images.interfaces,
        action_owner=second_action_owner,
        action_kind=second.action_kind,
        action_validate=second.validate_action,
        output_owner=output_owner,
        output_kind=second.output_kind,
        output_validate=first.validate_output,
        signature_kind=images.interfaces.signature_kind,
        signature_for=second.signature,
        action_authority=second,
        output_authority=first,
        signature_authority=second,
    )
    assert len(images._domains) == initial_entries + 3
    assert ledger.entries == before_entries + 1
    record = FieldImageRecord(
        0,
        None,
        None,
        adapter.interface,
        output,
        geometry,
        FieldImageSummary(True, 0, 0, 1),
    )
    request = ImageRequestKey(action, source, geometry, signature)
    images.validate_binding(request, images.publish(request, record))


def test_duplicate_or_unowned_image_domain_rejects_before_reservation() -> None:
    ledger, _, signature, _, _, images, adapter, _ = _setup((0,))
    before = assert_rejected_atomically(
        ledger,
        lambda: images.admit_domain(
            images.interfaces,
            action_owner=adapter.action.owner,
            action_kind=adapter.action.kind,
            action_validate=adapter.validate_action,
            output_owner=adapter.output.owner,
            output_kind=adapter.output.kind,
            output_validate=adapter.validate_output,
            signature_kind=images.interfaces.signature_kind,
            signature_for=adapter.signature,
            action_authority=adapter,
            output_authority=adapter,
            signature_authority=adapter,
        ),
        ValueError,
        match="already registered",
    )

    fake_owner = ArenaToken("unowned-actions")
    with pytest.raises(ValueError, match="not an index arena"):
        images.admit_domain(
            images.interfaces,
            action_owner=fake_owner,
            action_kind="unowned-action",
            action_validate=lambda _value: None,
            output_owner=adapter.output.owner,
            output_kind=adapter.output.kind,
            output_validate=adapter.validate_output,
            signature_kind=images.interfaces.signature_kind,
            signature_for=lambda _action, _geometry: signature,
            action_authority=object(),
            output_authority=adapter,
            signature_authority=object(),
        )
    assert ledger.snapshot() == before


@pytest.mark.parametrize("method", ("point", "active_width"))
def test_same_arena_wrong_signature_cannot_reach_parent_observer(
    monkeypatch: pytest.MonkeyPatch, method: str
) -> None:
    (
        ledger,
        source,
        signature,
        geometry,
        action,
        images,
        adapter,
        executor,
        incoming,
        application,
    ) = _application_setup()
    assert isinstance(images.interfaces, DiamondQuotientArena)
    other = images.interfaces.intern_interface(
        replace(
            images.interfaces.interface(signature),
            kernel=SemanticIdentity("different-interface-v1", ("different-kernel",)),
        )
    )

    def forbidden(*args: object) -> None:
        pytest.fail("wrong interface reached a parent observer")

    monkeypatch.setattr(adapter, "observe_parent_point", forbidden, raising=False)
    monkeypatch.setattr(adapter, "observe_parent_width", forbidden, raising=False)
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="normalized signature"):
        executor.application(action, source, geometry, other, incoming)
    application.signature = other
    assert not validate_field_image_application(application, ledger)
    with pytest.raises(ValueError, match="normalized signature"):
        application.point(0) if method == "point" else application.active_width()
    assert ledger.snapshot() == before


def test_image_phase_domain_matches_admitted_port_before_lookup() -> None:
    from number_compiler.hashlife.execution.field_images import ImageRequestKey

    ledger, source, signature, geometry, action, images, _, executor = _setup()
    executor.image(action, source, geometry, signature)
    wrong_geometry = images.geometries.intern(FieldGeometry(1, phase=1, phase_count=2))
    assert_rejected_atomically(
        ledger,
        lambda: images.probe(
            ImageRequestKey(action, source, wrong_geometry, signature)
        ),
        ValueError,
        match="phase domain",
    )


def test_image_publication_rejects_interface_from_another_signature() -> None:
    from number_compiler.hashlife.execution.field_images import ImageRequestKey

    ledger, source, signature, geometry, action, images, _adapter, executor = _setup()
    image = executor.image(action, source, geometry, signature)
    record = images.resolve(image)
    assert isinstance(images.interfaces, DiamondQuotientArena)
    declared = images.interfaces.interface(signature)
    other_signature = images.interfaces.intern_interface(
        replace(
            declared,
            kernel=SemanticIdentity(
                "recursive-image-other-signature-v1",
                ("other-kernel",),
            ),
        )
    )
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="another port signature"):
        images.publish(
            ImageRequestKey(action, source, geometry, other_signature),
            record,
        )
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_field_geometry_has_no_absolute_occurrence_or_width_identity() -> None:
    names = {field.name for field in fields(FieldGeometry)}
    assert names == {
        "spatial_level",
        "orientation",
        "phase",
        "phase_count",
        "halo_left",
        "halo_right",
    }
    assert names.isdisjoint(
        {
            "start",
            "origin",
            "generation",
            "source",
            "source_id",
            "extent",
            "width",
            "frame_shift",
            "occurrence",
        }
    )


def test_geometry_payload_audit_rejects_semantic_key_poisoning() -> None:
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )

    ledger = ResourceLedger()
    arena = FieldGeometryArena(ledger)
    arena.intern(FieldGeometry(2))
    original, local_id = next(iter(arena._keys.items()))
    poisoned = FieldGeometry(2, phase=1, phase_count=2)
    del arena._keys[original]
    arena._keys[poisoned] = local_id
    assert (arena._key_owner, id(poisoned)) in audit_field_image_payloads(
        ledger
    ).invalid


def test_signature_subclass_cannot_alias_the_configured_handle_sort() -> None:
    ledger, source, signature, geometry, action, images, _, executor = _setup()

    @dataclass(frozen=True, slots=True)
    class ForgedSignature(PortSignatureID):
        pass

    forged = ForgedSignature(signature.owner, signature.kind, signature.local_id)
    assert_rejected_atomically(
        ledger, lambda: executor.image(action, source, geometry, forged), TypeError
    )
    assert images.retained_bindings == 0


@dataclass(frozen=True, slots=True)
class _PortID(ArenaHandle):
    pass


def test_non_source_image_graph_owns_no_exact_digit_geometry() -> None:
    from number_compiler.arithmetic.fields.dyadic_tile import DyadicSpan, DyadicTile

    ledger, source, signature, geometry, action, _, _, executor = _setup()
    executor.image(action, source, geometry, signature)
    roles = {item.owner: item.role for item in ledger.inventory()}
    allowed = {"source_cell", "source_cell_interner", "exact_source"}
    pending = [
        (owner, payload)
        for owner, payload in ledger.iter_payloads()
        if roles[owner] not in allowed
    ]
    seen: set[int] = set()
    while pending:
        owner, value = pending.pop()
        if id(value) in seen:
            continue
        seen.add(id(value))
        assert not isinstance(value, (DyadicSpan, DyadicTile))
        if isinstance(value, Mapping):
            pending.extend((owner, item) for pair in value.items() for item in pair)
        elif isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
            pending.extend((owner, item) for item in value)
        elif is_dataclass(value) and not isinstance(value, type):
            pending.extend(
                (owner, getattr(value, field.name)) for field in fields(value)
            )


def test_geometry_rejects_boolean_integer_aliases() -> None:
    ledger = ResourceLedger()
    arena = FieldGeometryArena(ledger)
    assert_rejected_atomically(
        ledger,
        lambda: arena.intern(FieldGeometry(True)),
        TypeError,
        match="exact integer",
    )


def test_geometry_nodes_and_interner_are_independently_inventoried() -> None:
    ledger = ResourceLedger()
    arena = FieldGeometryArena(ledger)
    arena.intern(FieldGeometry(2))
    inventory = {
        item.role: item
        for item in ledger.inventory()
        if item.role in ("field_geometry", "field_geometry_interner")
    }
    assert inventory["field_geometry"].observed_entries == 1
    assert inventory["field_geometry"].observed_nodes == 1
    assert inventory["field_geometry_interner"].observed_entries == 1
