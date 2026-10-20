"""Owner-local validation of retained Antihydra projection payloads."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import fields
from typing import TYPE_CHECKING

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)
from number_compiler.sequences.antihydra.payload_audit import (
    approve_payload,
    owned_row_matches,
    reject_payload,
)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


def _fragment_source_bindings(
    cache: object,
    terms: Mapping[int, AntihydraArithmeticTerm],
    ledger: ResourceLedger,
) -> set[int]:
    """Verify fragment phase keys against authenticated chronological support."""
    from number_compiler.sequences.antihydra.blocks import (
        ArithmeticCylinder,
        physical_roof,
    )
    from number_compiler.sequences.antihydra.projection_fragments import (
        ProjectionFragmentCache,
        ProjectionFragmentKey,
    )
    from number_compiler.sequences.antihydra.runtime import (
        AntihydraArithmeticTerm,
        ArithmeticSegment,
    )

    if type(cache) is not ProjectionFragmentCache:
        return set()
    demanded: dict[int, dict[int, list[ProjectionFragmentKey]]] = {}
    for key in cache.fragments:
        if type(key) is not ProjectionFragmentKey:
            continue
        if any(
            type(getattr(key, name)) is not int
            for name in (
                "source_owner",
                "requested",
                "start",
                "spatial_width",
                "temporal_width",
                "spatial_sign",
                "temporal_sign",
                "modulus",
                "head_phase",
                "time_phase",
            )
        ):
            continue
        term = terms.get(key.source_owner)
        if type(term) is not AntihydraArithmeticTerm:
            continue
        term_snapshot = term.audit_snapshot()
        if (
            term.ledger is not ledger
            or term.engine.projection_fragments is not cache
            or key.requested != term.requested
            or not 0 <= key.start < term.requested
            or term.published_physical_run is None
            or term.published_physical_run.halted
            or not 1 <= key.spatial_width <= 64
            or not 1 <= key.temporal_width <= 64
            or key.spatial_sign not in (-1, 1)
            or key.temporal_sign not in (-1, 1)
            or key.modulus < 2
            or type(key.cylinder) is not tuple
            or len(key.cylinder) != 6
            or any(type(part) is not int for part in key.cylinder)
        ):
            continue
        demanded.setdefault(key.source_owner, {}).setdefault(key.start, []).append(key)

    bound: set[int] = set()
    for owner, starts in demanded.items():
        term = terms[owner]
        term_snapshot = term.audit_snapshot()
        last = max(starts)
        h, balance, head, time, start = 8, 0, 1, 11, 0
        if not term_snapshot.segments_ready:
            continue
        for segment in term_snapshot.segments:
            if (
                type(segment) is not ArithmeticSegment
                or type(segment.start) is not int
                or segment.start != start
                or type(segment.cylinder) is not ArithmeticCylinder
            ):
                break
            block = segment.cylinder
            if (
                type(block.width) is not int
                or not 1 <= block.width <= 64
                or any(
                    type(getattr(block, item.name)) is not int
                    or abs(getattr(block, item.name)).bit_length()
                    > 2 * block.width + 10
                    for item in fields(block)
                )
                or block.residue != h % (1 << block.width)
                or balance + block.minimum < 0
            ):
                break
            signature = (
                block.width,
                block.residue,
                block.output,
                block.delta,
                block.minimum,
                block.parity_word,
            )
            for key in starts.get(start, ()):
                spatial = key.spatial_width * (2 if key.spatial_sign == -1 else 1)
                temporal = key.temporal_width * (2 if key.temporal_sign == -1 else 1)
                if (
                    key.cylinder == signature
                    and key.head_phase == head % spatial
                    and key.time_phase == time % temporal
                ):
                    bound.add(id(key))
            if start >= last:
                break
            ledger.bump(
                _antihydra_keys.ANTIHYDRA_PAYLOAD_AUDIT_PROJECTION_FRAGMENT_STEPS,
                block.width,
            )
            ledger.bump(
                _antihydra_keys.ANTIHYDRA_PAYLOAD_AUDIT_PROJECTION_FRAGMENT_OPERAND_BITS,
                h.bit_length()
                + balance.bit_length()
                + head.bit_length()
                + time.bit_length(),
            )
            h, balance, left, right = physical_roof(block).apply(h, balance)
            head += right - left
            time += right + left
            start += block.width
    return bound


def audit_antihydra_fragment_cache(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Check seals and original source coordinates for one fragment cache."""
    from number_compiler.sequences.antihydra.projection_fragments import (
        ProjectionFragment,
        ProjectionFragmentCache,
        ProjectionFragmentKey,
    )
    from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm

    if type(ledger) is not ResourceLedger or type(root) is not ProjectionFragmentCache:
        raise TypeError("Antihydra fragment audit requires its exact cache root")
    cache = root
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    terms = {
        candidate.segment_owner: candidate
        for candidate in ledger.iter_execution_roots()
        if type(candidate) is AntihydraArithmeticTerm
    }
    source_bindings = _fragment_source_bindings(cache, terms, ledger)
    structurally_valid = (
        set(vars(cache)) == {"ledger", "owner", "seal_owner", "fragments", "seals"}
        and cache.ledger is ledger
        and owned_row_matches(
            ledger,
            cache.owner,
            cache.fragments,
            "demanded_projection",
            entries=len(cache.fragments),
        )
        and owned_row_matches(
            ledger,
            cache.seal_owner,
            cache.seals,
            "projection_binding",
            entries=len(cache.seals),
        )
        and len(cache.fragments) == len(cache.seals) <= 32
    )
    if not structurally_valid:
        reject_payload(invalid, cache.owner, cache)
        return PayloadAuditContribution((), tuple(invalid))

    seal_entries = {key: (key, seal) for key, seal in cache.seals.items()}
    if set(cache.fragments) != set(seal_entries):
        structurally_valid = False
    for key, fragment in cache.fragments.items():
        seal_key, seal = seal_entries.get(key, (None, None))
        valid = (
            id(key) in source_bindings
            and type(key) is ProjectionFragmentKey
            and type(fragment) is ProjectionFragment
            and cache.matches_seal(key, fragment)
            and fragment.key == key
            and seal_key is key
        )
        if valid:
            try:
                fragment.validate()
            except (TypeError, ValueError, AttributeError):
                valid = False
        if valid:
            approve_payload(approved, cache.owner, key)
            approve_payload(approved, cache.owner, fragment)
            approve_payload(approved, cache.seal_owner, seal_key)
            approve_payload(approved, cache.seal_owner, seal)
        else:
            structurally_valid = False
            reject_payload(invalid, cache.owner, key)
            reject_payload(invalid, cache.owner, fragment)
            if seal is not None:
                reject_payload(invalid, cache.seal_owner, key)
                reject_payload(invalid, cache.seal_owner, seal)
    if not structurally_valid:
        reject_payload(invalid, cache.owner, cache)
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


def audit_antihydra_cursor(ledger: object, root: object) -> PayloadAuditContribution:
    """Require the reusable occurrence cursor to be idle and empty."""
    from number_compiler.sequences.antihydra.projection_occurrences import (
        ProjectionOccurrenceCursor,
    )

    if (
        type(ledger) is not ResourceLedger
        or type(root) is not ProjectionOccurrenceCursor
    ):
        raise TypeError("Antihydra cursor audit requires its exact cursor root")
    cursor = root
    invalid: list[PayloadAuditEntry] = []
    cursor_snapshot = cursor.audit_snapshot()
    stores = cursor_snapshot.stores
    valid = (
        set(vars(cursor))
        == {
            "ledger",
            "_state_owner",
            "_state_seal_owner",
            "_occurrence_owner",
            "_occurrence_seal_owner",
            "_states",
            "_state_seals",
            "_occurrences",
            "_occurrence_seals",
            "_token",
            "_active",
        }
        and cursor.ledger is ledger
        and cursor_snapshot.active is False
        and cursor_snapshot.token_is_valid
        and all(
            not store
            and owned_row_matches(ledger, owner, store, role, entries=0, nodes=0)
            for owner, _attribute, role, store in stores
        )
    )
    if not valid:
        reject_payload(invalid, cursor_snapshot.stores[0].owner, cursor)
    return PayloadAuditContribution((), tuple(invalid))


def audit_antihydra_fragment_adapter(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Require the reusable source-image adapter to have released query state."""
    from number_compiler.sequences.antihydra.projection_core import (
        AntihydraFragmentAdapter,
    )

    if type(ledger) is not ResourceLedger or type(root) is not AntihydraFragmentAdapter:
        raise TypeError("Antihydra adapter audit requires its exact adapter root")
    adapter = root
    invalid: list[PayloadAuditEntry] = []
    valid = (
        set(vars(adapter))
        == {
            "ledger",
            "projection",
            "key",
            "block",
            "_cursor",
            "_occurrence",
            "_section_capacity",
            "_source_h",
            "_source_balance",
            "_source_token",
            "_source_kind",
            "_token",
            "_kind",
            "_owner",
            "_records",
            "_seal_owner",
            "_seals",
            "_source_seal_owner",
            "_source_seals",
        }
        and adapter.ledger is ledger
        and adapter.audit_snapshot().token_is_valid
        and adapter.audit_snapshot().idle
        and all(
            owned_row_matches(
                ledger, row.owner, row.store, row.role, entries=0, nodes=0
            )
            for row in adapter.audit_snapshot().stores
        )
    )
    if not valid:
        reject_payload(invalid, adapter.audit_snapshot().stores[0].owner, adapter)
    return PayloadAuditContribution((), tuple(invalid))


def audit_antihydra_section_workspace(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Require the reusable bounded section workspace to be empty between calls."""
    from number_compiler.sequences.antihydra.projection_workspace import (
        SectionImageWorkspace,
    )

    if type(ledger) is not ResourceLedger or type(root) is not SectionImageWorkspace:
        raise TypeError("Antihydra section audit requires its exact workspace root")
    workspace = root
    invalid: list[PayloadAuditEntry] = []
    valid = (
        set(vars(workspace)) == {"ledger", "owner", "images", "area", "active"}
        and workspace.ledger is ledger
        and not workspace.active
        and not workspace.images
        and workspace.area == 0
        and owned_row_matches(
            ledger,
            workspace.owner,
            workspace.images,
            "demanded_projection",
            entries=0,
            nodes=0,
        )
    )
    if not valid:
        reject_payload(invalid, workspace.owner, workspace)
    return PayloadAuditContribution((), tuple(invalid))
