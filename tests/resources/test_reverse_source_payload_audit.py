from __future__ import annotations

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.reverse_source_payload_audit import (
    ReverseSourcePayloadAudit,
    audit_reverse_source_payloads,
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
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3)
    tuple(workspace.iter_digits())
    adapter = workspace.adapter
    cutover = adapter._recursive
    assert cutover is not None
    original = adapter._recursive_occurrences[3]
    assert id(workspace) in _audit(workspace).approved

    # This is a genuine completed occurrence in the same action and image
    # arenas. Replacing the step-three publication with it must fail the exact
    # memo key, action, and image/source occurrence checks.
    foreign_steps = cutover.pair_image(2)
    assert foreign_steps.action != original.action
    assert foreign_steps.image.owner is original.image.owner
    adapter._recursive_occurrences[3] = foreign_steps

    audit = _audit(workspace)
    assert (adapter._recursive_occurrences.owner, id(foreign_steps)) in audit.invalid
    assert id(workspace) not in audit.approved


def test_disposal_keeps_canonical_arena_accounting_explicit() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3)
    tuple(workspace.iter_digits())
    ledger = workspace.ledger
    cutover = workspace.adapter._recursive
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

    first = collect_ledger_metrics(term._ledger)
    assert first.resource_audit_complete == 1
    assert first.forbidden_future_payloads == 0
    assert term.metrics().forbidden_future_payloads == 0
    assert term.metrics().resource_audit_complete == 1


def test_signature_memo_rejects_wrong_action_and_unregistered_level() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 64)
    tuple(workspace.iter_digits())
    assert id(workspace) in _audit(workspace).approved

    cutover = workspace.adapter._recursive
    assert cutover is not None
    adapter = cutover.adapter
    signatures = adapter._signatures
    level_zero_keys = [key for key in signatures if key[1] == 0]
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

    max_level = max(geometry.spatial_level for geometry in adapter._geometries._nodes)
    signature = signatures[key]
    del signatures[key]
    invalid_key = (key[0], max_level + 1)
    signatures[invalid_key] = signature

    audit = _audit(workspace)
    assert (signatures.owner, id(invalid_key)) in audit.invalid
    assert id(workspace) not in audit.approved


def test_recursive_construction_audit_rejects_wrong_geometry_and_horizon() -> None:
    for mutation in ("extent", "alphabet", "horizon"):
        workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3)
        adapter = workspace.adapter
        construction = adapter._recursive_construction
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
            adapter._recursive_maximum_steps = MAX_COMPLETED_CHILD_FALLBACK_STEPS + 1

        audit = _audit(workspace)
        assert id(workspace) not in audit.approved
