from __future__ import annotations

from typing import cast

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.owned_memo import OwnedMemo
from number_compiler.resources.reverse_source_payload_audit import (
    ReverseSourcePayloadAudit,
    audit_reverse_source_payloads,
)
from number_compiler.sequences.reverse_add.q19_occurrence import (
    ReversePairOutputOccurrence,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveOccurrence,
)
from number_compiler.sequences.reverse_add.source_images import (
    MAX_COMPLETED_CHILD_FALLBACK_STEPS,
    ReverseSourceImageWorkspace,
)


def _audit(workspace: ReverseSourceImageWorkspace) -> ReverseSourcePayloadAudit:
    ledger = workspace.ledger
    return audit_reverse_source_payloads(
        ledger,
        tuple(ledger.iter_execution_roots()),
        dict(ledger.iter_containers()),
    )


def test_recursive_occurrence_audit_checks_exact_same_arena_action_binding() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3, base=3)
    tuple(workspace.iter_digits())
    adapter = workspace.adapter
    adapter_snapshot = adapter.audit_snapshot()
    cutover = adapter_snapshot.recursive
    assert cutover is not None
    original_value = adapter_snapshot.recursive_occurrences.payload_view[3]
    if type(original_value) is not ReverseRecursiveOccurrence:
        raise TypeError("recursive occurrence has another record type")
    original = original_value
    assert id(workspace) in _audit(workspace).approved

    # This is a genuine completed occurrence in the same action and image
    # arenas. Replacing the step-three publication with it must fail the exact
    # memo key, action, and image/source occurrence checks.
    foreign_steps = cutover.pair_image(2)
    assert foreign_steps.action != original.action
    assert foreign_steps.image.owner is original.image.owner
    occurrences = cast(
        OwnedMemo[int, ReverseRecursiveOccurrence],
        object.__getattribute__(adapter, "_recursive_occurrences"),
    )
    occurrences[3] = foreign_steps

    audit = _audit(workspace)
    assert (
        adapter_snapshot.recursive_occurrences.owner,
        id(foreign_steps),
    ) in audit.invalid
    assert id(workspace) not in audit.approved


def test_disposal_keeps_canonical_arena_accounting_explicit() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3, base=3)
    tuple(workspace.iter_digits())
    ledger = workspace.ledger
    cutover = workspace.adapter.audit_snapshot().recursive
    assert cutover is not None
    workspace.dispose()

    inventory = ledger.inventory()
    assert sum(item.accounting_delta or 0 for item in inventory) == 0
    assert any(
        item.role == "field_image"
        and item.entries > 0
        and item.observed_entries == item.entries
        for item in inventory
    )
    occurrence_owner = next(
        item
        for item in inventory
        if item.role == "reverse_recursive_occurrence_binding"
    )
    assert occurrence_owner.disposed
    assert occurrence_owner.entries == occurrence_owner.observed_entries == 0


def test_repeated_d64_metrics_keep_the_complete_payload_audit() -> None:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, 64)
    term.digit(0)
    term.width()

    first = collect_ledger_metrics(term.resource_ledger)
    assert first.resource_audit_complete == 1
    assert first.forbidden_future_payloads == 0
    assert term.metrics().forbidden_future_payloads == 0
    assert term.metrics().resource_audit_complete == 1


def test_explicit_metrics_audit_rechecks_nested_issued_border_certificate() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    certificate = None
    original_growth: tuple[int, ...] | None = None
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=5, window_digits=1
        )
        clean = collect_ledger_metrics(ledger, audit_payloads=True)
        assert clean.forbidden_future_payloads == 0
        assert (
            collect_ledger_metrics(ledger, audit_payloads=False).resource_audit_complete
            == 1
        )

        # The retained OwnedMemo value and its live-root signature are
        # unchanged, so only a fresh explicit audit can see this nested edit.
        growth_word = certificate.growth_word
        original_growth = growth_word
        object.__setattr__(
            certificate,
            "growth_word",
            (1 - growth_word[0],) + growth_word[1:],
        )
        poisoned = collect_ledger_metrics(ledger, audit_payloads=True)
        assert poisoned.forbidden_future_payloads > 0
    finally:
        if certificate is not None and original_growth is not None:
            object.__setattr__(certificate, "growth_word", original_growth)
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_completed_width_image_cannot_be_rebound_to_foreign_owner() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 16)
    assert workspace.width() == 9
    image = workspace.audit_snapshot().image
    assert image is not None
    assert id(workspace) in _audit(workspace).approved
    foreign = ReverseSourceImageWorkspace(ResourceLedger(), 196, 16)
    assert foreign.width() == 9
    foreign_image = foreign.audit_snapshot().image
    assert foreign_image is not None
    object.__setattr__(workspace, "_image", foreign_image)
    assert id(workspace) not in _audit(workspace).approved
    object.__setattr__(workspace, "_image", image)
    assert id(workspace) in _audit(workspace).approved
    foreign.dispose()
    workspace.dispose()


def test_signature_memo_rejects_wrong_action_and_unregistered_level() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 64, base=3)
    tuple(workspace.iter_digits())
    assert id(workspace) in _audit(workspace).approved

    cutover = workspace.adapter.audit_snapshot().recursive
    assert cutover is not None
    adapter = cutover.adapter
    adapter_state = adapter.audit_snapshot()
    signatures = cast(
        OwnedMemo[tuple[FieldCellActionID, int], PortSignatureID],
        object.__getattribute__(adapter, "_signatures"),
    )
    signature_view = adapter_state.signatures.payload_view
    level_zero_keys = [key for key in signature_view if key[1] == 0]
    key = level_zero_keys[0]
    foreign_key = next(
        candidate for candidate in level_zero_keys if candidate[0] != key[0]
    )
    original_signature = signatures[key]
    signatures[key] = signatures[foreign_key]

    audit = _audit(workspace)
    assert (signatures.owner, id(key)) in audit.invalid
    assert id(workspace) not in audit.approved

    signatures[key] = original_signature
    assert id(workspace) in _audit(workspace).approved

    geometry_snapshot = adapter_state.geometries
    assert geometry_snapshot is not None
    max_level = max(geometry.spatial_level for geometry in geometry_snapshot.nodes)
    signature = signatures[key]
    del signatures[key]
    invalid_key = (key[0], max_level + 1)
    signatures[invalid_key] = signature

    audit = _audit(workspace)
    assert (signatures.owner, id(invalid_key)) in audit.invalid
    assert id(workspace) not in audit.approved


def test_recursive_construction_audit_rejects_wrong_geometry_and_horizon() -> None:
    for mutation in ("extent", "alphabet", "horizon"):
        workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3, base=3)
        adapter = workspace.adapter
        adapter_state = adapter.audit_snapshot()
        construction = adapter_state.recursive_construction
        assert construction is not None
        source = construction.validate_source()

        if mutation == "extent":
            assert source.extent is not None
            object.__setattr__(
                construction,
                "source",
                ExactSource(
                    source.digits,
                    source.base,
                    source.orbit,
                    source.blank,
                    source.extent * 2,
                    source.alphabet_size,
                ),
            )
        elif mutation == "alphabet":
            object.__setattr__(
                construction,
                "source",
                ExactSource(
                    source.digits,
                    source.base,
                    source.orbit,
                    source.blank,
                    source.extent,
                    2 * source.base + 1,
                ),
            )
        else:
            object.__setattr__(
                adapter,
                "_recursive_maximum_steps",
                MAX_COMPLETED_CHILD_FALLBACK_STEPS + 1,
            )

        audit = _audit(workspace)
        assert id(workspace) not in audit.approved


def test_q19_audit_rejects_foreign_occurrence_and_source_rebinding() -> None:
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 196, 3)
    foreign = ReverseSourceImageWorkspace(ledger, 196, 3)
    tuple(workspace.iter_digits())
    tuple(foreign.iter_digits())
    owner = workspace.adapter.audit_snapshot().q19_owner
    foreign_owner = foreign.adapter.audit_snapshot().q19_owner
    assert owner is not None and foreign_owner is not None
    occurrence = owner.initial
    foreign_occurrence = foreign_owner.initial
    assert occurrence != foreign_occurrence

    clean = _audit(workspace)
    assert clean.valid(workspace)
    assert clean.valid(owner)
    assert clean.valid(occurrence)

    key = (occurrence.root, occurrence.temporal_steps)
    issued = cast(
        OwnedMemo[tuple[int, int], ReversePairOutputOccurrence],
        object.__getattribute__(owner, "_issued"),
    )
    issued[key] = foreign_occurrence
    forged = _audit(workspace)
    assert not forged.valid(workspace)
    assert not forged.valid(owner)
    assert any(root_id == id(owner) for _, root_id in forged.invalid)

    issued[key] = occurrence
    original_digits = owner.audit_snapshot().digits
    rebound_digits = tuple(digit for digit in original_digits)
    object.__setattr__(owner, "_digits", rebound_digits)
    assert rebound_digits == original_digits and rebound_digits is not original_digits
    rebound = _audit(workspace)
    assert not rebound.valid(workspace)
    assert not rebound.valid(owner)

    object.__setattr__(owner, "_digits", original_digits)
    assert _audit(workspace).valid(workspace)
    workspace.dispose()
    foreign.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_source_image_rejects_same_owner_q19_occurrence_with_wrong_duration() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3)
    tuple(workspace.iter_digits())
    owner = workspace.adapter.audit_snapshot().q19_owner
    image = workspace.audit_snapshot().image
    assert owner is not None and image is not None
    from number_compiler.sequences.reverse_add.source_images import (
        ReverseImagePayload,
    )

    core = workspace.scheduler.source_image_core()
    payload = cast(ReverseImagePayload, core.view(image).payload)
    assert type(payload) is ReverseImagePayload
    original = payload.pair_output
    assert original is not None and original.temporal_steps == workspace.steps
    wrong_duration = owner.initial
    assert wrong_duration.temporal_steps != workspace.steps
    assert wrong_duration.owner is original.owner

    object.__setattr__(payload, "pair_output", wrong_duration)
    audit = _audit(workspace)
    assert id(workspace) not in audit.approved
    object.__setattr__(payload, "pair_output", original)
    assert id(workspace) in _audit(workspace).approved

    original_width = original.pair_width
    object.__setattr__(original, "pair_width", original_width + 1)
    assert id(workspace) not in _audit(workspace).approved
    object.__setattr__(original, "pair_width", original_width)
    assert id(workspace) in _audit(workspace).approved
    workspace.dispose()


def test_q19_disposal_releases_the_audited_output_grammar() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3)
    tuple(workspace.iter_digits())
    ledger = workspace.ledger
    owner = workspace.adapter.audit_snapshot().q19_owner
    assert owner is not None
    assert _audit(workspace).valid(workspace)
    before = tuple(
        item for item in ledger.inventory() if item.role.startswith("reverse_pair_")
    )
    assert {item.role for item in before} >= {
        "reverse_pair_output_grammar",
        "reverse_pair_q19_summary",
        "reverse_pair_output_occurrence",
    }
    assert any(item.entries > 0 for item in before)

    workspace.dispose()
    after = tuple(
        item for item in ledger.inventory() if item.role.startswith("reverse_pair_")
    )
    assert after
    assert all(
        item.entries == item.nodes == item.observed_entries == 0
        and item.accounting_delta == 0
        for item in after
        if item.role != "reverse_pair_output_workspace"
    )
    scratch = next(
        item for item in after if item.role == "reverse_pair_output_workspace"
    )
    assert scratch.entries == scratch.nodes == 0
    assert all(
        item.disposed for item in after if item.role != "reverse_pair_output_workspace"
    )
    assert ledger.entries == ledger.nodes == 0
