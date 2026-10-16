"""Common sealing order for source-bound Q19 certificate records."""

from __future__ import annotations

from collections.abc import Mapping
from typing import TYPE_CHECKING, Protocol, TypeVar

from number_compiler.resources.ledger import OwnedMemo, ResourceLedger

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.diagonal_growth_bank import (
        CertifiedDiagonalComparison,
    )
    from number_compiler.sequences.reverse_add.q19_border_control import (
        CertifiedBorderGrowth,
    )
    from number_compiler.sequences.reverse_add.q19_controlled_gt_bank import (
        SourceGuardedGTBankAction,
    )
    from number_compiler.sequences.reverse_add.q19_occurrence import (
        ReversePairOutputOccurrence,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.q19_spatial_bank_morphism import (
        ReverseAddSpatialBankMorphism,
    )
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        ReverseAddTemporalRingBank,
    )


class _SnapshotRecord(Protocol):
    def _snapshot(self) -> tuple[object, ...]: ...


_Record = TypeVar("_Record", bound=_SnapshotRecord)


def _border_certificate_key(
    source: ReversePairOutputOccurrence, steps: int, window_digits: int
) -> tuple[int, int, int, int]:
    return source.root, source.temporal_steps, steps, window_digits


def _snapshot_matches(
    trusted: tuple[object, ...],
    current: tuple[object, ...],
    *,
    identity_positions: tuple[int, ...],
) -> bool:
    if len(trusted) != len(current):
        return False
    identities = frozenset(identity_positions)
    return all(
        original is value if index in identities else original == value
        for index, (original, value) in enumerate(zip(trusted, current, strict=True))
    )


class Q19IssuanceRegistry:
    """Request-local owner registry for source-authorized Q19 records."""

    def __init__(
        self,
        owner: ReversePairQ19OutputOwner,
        ledger: ResourceLedger,
        prefix: str,
    ) -> None:
        self.owner = owner
        border_owner = ledger.register(
            prefix + "-border-certificates", "reverse_pair_q19_border_certificate"
        )
        self.border_certificates: OwnedMemo[
            tuple[int, int, int, int],
            tuple[CertifiedBorderGrowth, tuple[object, ...]],
        ] = OwnedMemo(ledger, border_owner, node_cost=self._border_record_cost)
        diagonal_owner = ledger.register(
            prefix + "-directed-diagonal-comparisons",
            "reverse_pair_q19_directed_diagonal_comparison",
        )
        self.diagonal_comparisons: OwnedMemo[
            int, tuple[CertifiedDiagonalComparison, tuple[object, ...]]
        ] = OwnedMemo(ledger, diagonal_owner, node_cost=self._diagonal_comparison_cost)
        self.diagonal_comparison_next = 0
        bank_owner = ledger.register(
            prefix + "-controlled-gt-banks",
            "reverse_pair_q19_conditional_gt_bank",
        )
        self.controlled_gt_banks: OwnedMemo[
            int, tuple[SourceGuardedGTBankAction, tuple[object, ...]]
        ] = OwnedMemo(ledger, bank_owner, node_cost=self._bank_record_cost)
        self.controlled_gt_bank_next = 0
        spatial_owner = ledger.register(
            prefix + "-spatial-bank-windows", "reverse_pair_q19_spatial_bank_window"
        )
        self.spatial_bank_windows: OwnedMemo[
            int,
            tuple[ReverseAddSpatialBankMorphism, tuple[object, ...]],
        ] = OwnedMemo(
            ledger,
            spatial_owner,
            node_cost=self._spatial_bank_window_cost,
        )
        self.spatial_bank_window_next = 0
        ring_owner = ledger.register(
            prefix + "-temporal-ring-banks", "reverse_pair_q19_temporal_ring_bank"
        )
        self.temporal_ring_banks: OwnedMemo[
            int, tuple[ReverseAddTemporalRingBank, tuple[object, ...]]
        ] = OwnedMemo(ledger, ring_owner, node_cost=self._temporal_ring_bank_cost)
        self.temporal_ring_bank_next = 0

    def _check_open(self) -> None:
        self.owner._check_open()
        if (
            self.owner._issuance_registry is not self
            or self.owner._border_certificates is not self.border_certificates
            or self.owner._controlled_gt_banks is not self.controlled_gt_banks
            or self.owner._spatial_bank_windows is not self.spatial_bank_windows
            or self.owner._temporal_ring_banks is not self.temporal_ring_banks
            or self.owner._diagonal_comparisons is not self.diagonal_comparisons
            or self.diagonal_comparison_next != len(self.diagonal_comparisons)
        ):
            raise ValueError("Q19 issuance registry binding changed")

    @staticmethod
    def _border_record_cost(
        _key: tuple[int, int, int, int],
        issued: tuple[CertifiedBorderGrowth, tuple[object, ...]],
    ) -> int:
        record, binding = issued
        return (
            len(record.growth_word)
            + len(record.outer_pairs)
            + len(record.window_tiles)
            + len(binding)
            + 1
        )

    @staticmethod
    def _diagonal_comparison_cost(
        _key: int,
        issued: tuple[CertifiedDiagonalComparison, tuple[object, ...]],
    ) -> int:
        record, _snapshot = issued
        inlet_count = len(record.first_inlets) + len(record.second_inlets)
        port_count = middle_count = 0
        for inlets in (record.first_inlets, record.second_inlets):
            for inlet in inlets:
                port = inlet.bilateral_port
                if port is not None:
                    port_count += 1
                    middle_count += len(port.admitted_middle)
        # Count the nested immutable snapshot tuples (including their slots),
        # the retained comparison/inlet/port objects, and the registry pair.
        # The fixed snapshot shape costs 56 nodes; each inlet costs 12 plus its
        # optional bilateral port (42 + its admitted maps).
        snapshot_nodes = 56 + 12 * inlet_count + 42 * port_count + middle_count
        retained_objects = (
            22
            + 5 * inlet_count
            + 15 * port_count
            + middle_count
            + 3  # (record, snapshot) registry pair
        )
        return snapshot_nodes + retained_objects

    @staticmethod
    def _bank_record_cost(
        _key: int, issued: tuple[SourceGuardedGTBankAction, tuple[object, ...]]
    ) -> int:
        record, binding = issued
        action = record.action
        return (
            len(action.arena.nodes)
            + 2 * action.orbit_states * len(record.period)
            + action.moore_states
            + len(record.growth_control)
            + len(record.period)
            + len(binding)
            + 1
        )

    @staticmethod
    def _spatial_bank_window_cost(
        _key: int,
        issued: tuple[ReverseAddSpatialBankMorphism, tuple[object, ...]],
    ) -> int:
        _record, binding = issued
        return len(binding) + 1

    @staticmethod
    def _temporal_ring_bank_cost(
        _key: int,
        issued: tuple[ReverseAddTemporalRingBank, tuple[object, ...]],
    ) -> int:
        record, binding = issued
        orbit_fields = (
            "pair_f5",
            "low_carries",
            "reflected_carries",
            "reflected_xor",
            "raw_innovation_borrow",
            "carry_borrow_xor",
            "low_birth",
            "low_death",
            "reflected_birth",
            "reflected_death",
            "selected_bands",
        )
        return (
            len(record.positions)
            + len(record.widths)
            + sum(
                1 + len(domain)
                for position_domains in record.phase_pair_domains
                for domain in position_domains
            )
            + sum(
                len(values) + sum(len(row) for row in values)
                for orbit in record.output_orbits
                for values in (getattr(orbit, name) for name in orbit_fields)
            )
            + sum(len(word.lanes) + 1 for word in record.bank_words)
            + len(record.finite_moore_classes)
            + len(binding)
            + 1
        )

    def allocate_diagonal_comparison_key(self) -> int:
        self._check_open()
        if type(
            self.diagonal_comparison_next
        ) is not int or self.diagonal_comparison_next != len(self.diagonal_comparisons):
            raise ValueError("directed diagonal issuer registry was altered")
        return self.diagonal_comparison_next

    def retain_diagonal_comparison(
        self, key: int, record: CertifiedDiagonalComparison
    ) -> None:
        self._check_open()
        if (
            type(key) is not int
            or key != self.diagonal_comparison_next
            or record.certificate.owner is not self.owner
            or record._registry_key != key
        ):
            raise ValueError("invalid directed diagonal comparison registration")
        self.diagonal_comparisons[key] = (record, record._snapshot())
        self.diagonal_comparison_next += 1

    def validate_diagonal_comparison(self, record: CertifiedDiagonalComparison) -> None:
        self._check_open()
        key = record._registry_key
        if type(key) is not int or not 0 <= key < self.diagonal_comparison_next:
            raise ValueError(
                "directed diagonal comparison is not retained by this Q19 owner"
            )
        issued = self.diagonal_comparisons.get(key)
        if issued is None or issued[0] is not record:
            raise ValueError(
                "directed diagonal comparison was not retained by this Q19 owner"
            )
        if not _snapshot_matches(
            issued[1], record._snapshot(), identity_positions=(0,)
        ):
            raise ValueError("retained directed diagonal comparison was altered")
        if record.certificate.owner is not self.owner:
            raise ValueError("directed diagonal comparison has a foreign certificate")
        self.validate_border(record.certificate)

    def discard_diagonal_comparison(
        self, key: int, record: CertifiedDiagonalComparison
    ) -> None:
        """Roll back only the latest record after failed publication."""
        if self.owner._disposed:
            return
        self._check_open()
        if key != self.diagonal_comparison_next - 1:
            return
        issued = self.diagonal_comparisons.get(key)
        if issued is not None and issued[0] is record:
            del self.diagonal_comparisons[key]
            self.diagonal_comparison_next = key

    def _lookup_border_issuance(
        self,
        source: ReversePairOutputOccurrence,
        steps: int,
        window_digits: int,
    ) -> tuple[
        tuple[int, int, int, int],
        tuple[CertifiedBorderGrowth, tuple[object, ...]] | None,
    ]:
        self._check_open()
        self.owner._validate_occurrence_handle(source)
        key = _border_certificate_key(source, steps, window_digits)
        return key, self.border_certificates.get(key)

    def lookup_border(
        self,
        source: ReversePairOutputOccurrence,
        steps: int,
        window_digits: int,
    ) -> CertifiedBorderGrowth | None:
        _key, issued = self._lookup_border_issuance(source, steps, window_digits)
        if issued is None:
            return None
        record, binding = issued
        if not _snapshot_matches(
            binding, record._snapshot(), identity_positions=(0, 1)
        ):
            raise ValueError("retained border certificate was altered")
        return record

    def retain_border(
        self, certificate: CertifiedBorderGrowth
    ) -> CertifiedBorderGrowth:
        key, existing = self._lookup_border_issuance(
            certificate.source,
            len(certificate.growth_word),
            certificate.window_digits,
        )
        if existing is not None:
            retained, binding = existing
            if not _snapshot_matches(
                binding, retained._snapshot(), identity_positions=(0, 1)
            ):
                raise ValueError("retained border certificate was altered")
            if retained.growth_word != certificate.growth_word:
                raise ValueError(
                    "conflicting border certificates for one source horizon"
                )
            return retained
        self.border_certificates[key] = (certificate, certificate._snapshot())
        return certificate

    def validate_border(self, certificate: CertifiedBorderGrowth) -> None:
        _key, issued = self._lookup_border_issuance(
            certificate.source,
            len(certificate.growth_word),
            certificate.window_digits,
        )
        if (
            issued is None
            or issued[0] is not certificate
            or not _snapshot_matches(
                issued[1], certificate._snapshot(), identity_positions=(0, 1)
            )
        ):
            raise ValueError("border certificate was not retained by this Q19 owner")

    def discard_border(self, certificate: CertifiedBorderGrowth) -> None:
        """Roll back only the exact last record after failed publication."""
        if self.owner._disposed:
            return
        self._check_open()
        key = _border_certificate_key(
            certificate.source,
            len(certificate.growth_word),
            certificate.window_digits,
        )
        issued = self.border_certificates.get(key)
        if issued is not None and issued[0] is certificate:
            del self.border_certificates[key]

    def allocate_bank_key(self) -> int:
        self._check_open()
        if type(
            self.controlled_gt_bank_next
        ) is not int or self.controlled_gt_bank_next != len(self.controlled_gt_banks):
            raise ValueError("controlled bank issuer registry was altered")
        return self.controlled_gt_bank_next

    def retain_bank(self, key: int, action: SourceGuardedGTBankAction) -> None:
        self._check_open()
        if (
            type(key) is not int
            or key != self.controlled_gt_bank_next
            or action.owner is not self.owner
            or action._registry_key != key
        ):
            raise ValueError("invalid controlled bank issuer registration")
        self.controlled_gt_banks[key] = (action, action._snapshot())
        self.controlled_gt_bank_next += 1

    def validate_bank(self, action: SourceGuardedGTBankAction) -> None:
        self._check_open()
        key = action._registry_key
        if type(key) is not int or not 0 <= key < self.controlled_gt_bank_next:
            raise ValueError(
                "controlled bank action was not retained by this Q19 owner"
            )
        issued = self.controlled_gt_banks.get(key)
        if (
            issued is None
            or issued[0] is not action
            or not _snapshot_matches(
                issued[1],
                action._snapshot(),
                identity_positions=(0, 1, 7, 8, 10, 15, 16, 21),
            )
        ):
            raise ValueError(
                "controlled bank action was not retained by this Q19 owner"
            )

    def discard_bank(self, key: int, action: SourceGuardedGTBankAction) -> None:
        """Roll back a failed final validation without consuming its key."""
        if self.owner._disposed:
            return
        self._check_open()
        if key != self.controlled_gt_bank_next - 1:
            return
        issued = self.controlled_gt_banks.get(key)
        if issued is not None and issued[0] is action:
            del self.controlled_gt_banks[key]
            self.controlled_gt_bank_next = key

    def allocate_spatial_bank_window_key(self) -> int:
        self._check_open()
        if type(
            self.spatial_bank_window_next
        ) is not int or self.spatial_bank_window_next != len(self.spatial_bank_windows):
            raise ValueError("spatial bank window issuer registry was altered")
        return self.spatial_bank_window_next

    def retain_spatial_bank_window(
        self, key: int, window: ReverseAddSpatialBankMorphism
    ) -> None:
        self._check_open()
        if (
            type(key) is not int
            or key != self.spatial_bank_window_next
            or window.action.owner is not self.owner
            or window._registry_key != key
        ):
            raise ValueError("invalid spatial bank window registration")
        self.spatial_bank_windows[key] = (window, window._snapshot())
        self.spatial_bank_window_next += 1

    def validate_spatial_bank_window(
        self, window: ReverseAddSpatialBankMorphism
    ) -> None:
        self._check_open()
        key = window._registry_key
        if type(key) is not int or not 0 <= key < self.spatial_bank_window_next:
            raise ValueError("spatial bank window is not retained by this Q19 owner")
        issued = self.spatial_bank_windows.get(key)
        if (
            issued is None
            or issued[0] is not window
            or not _snapshot_matches(
                issued[1],
                window._snapshot(),
                identity_positions=(0, 1),
            )
        ):
            raise ValueError("spatial bank window was not retained by this Q19 owner")

    def discard_spatial_bank_window(
        self, key: int, window: ReverseAddSpatialBankMorphism
    ) -> None:
        """Roll back only the latest spatial window after failed publication."""
        if self.owner._disposed:
            return
        self._check_open()
        if key != self.spatial_bank_window_next - 1:
            return
        issued = self.spatial_bank_windows.get(key)
        if issued is not None and issued[0] is window:
            del self.spatial_bank_windows[key]
            self.spatial_bank_window_next = key

    def allocate_temporal_ring_bank_key(self) -> int:
        self._check_open()
        if type(
            self.temporal_ring_bank_next
        ) is not int or self.temporal_ring_bank_next != len(self.temporal_ring_banks):
            raise ValueError("temporal ring bank issuer registry was altered")
        return self.temporal_ring_bank_next

    def retain_temporal_ring_bank(
        self, key: int, bank: ReverseAddTemporalRingBank
    ) -> None:
        self._check_open()
        if (
            type(key) is not int
            or key != self.temporal_ring_bank_next
            or bank.certificate.owner is not self.owner
            or bank._registry_key != key
        ):
            raise ValueError("invalid temporal ring bank registration")
        self.temporal_ring_banks[key] = (bank, bank._snapshot())
        self.temporal_ring_bank_next += 1

    def validate_temporal_ring_bank(self, bank: ReverseAddTemporalRingBank) -> None:
        self._check_open()
        key = bank._registry_key
        if type(key) is not int or not 0 <= key < self.temporal_ring_bank_next:
            raise ValueError("temporal ring bank is not retained by this Q19 owner")
        issued = self.temporal_ring_banks.get(key)
        if (
            issued is None
            or issued[0] is not bank
            or not _snapshot_matches(
                issued[1],
                bank._snapshot(),
                identity_positions=(0, 1, 2, 3, 12, 16),
            )
        ):
            raise ValueError("temporal ring bank was not retained by this Q19 owner")

    def discard_temporal_ring_bank(
        self, key: int, bank: ReverseAddTemporalRingBank
    ) -> None:
        """Roll back the latest ring only after failed publication."""
        if self.owner._disposed:
            return
        self._check_open()
        if key != self.temporal_ring_bank_next - 1:
            return
        issued = self.temporal_ring_banks.get(key)
        if issued is not None and issued[0] is bank:
            del self.temporal_ring_banks[key]
            self.temporal_ring_bank_next = key


def issue_q19_record(
    record: _Record, values: Mapping[str, object], issuer: object
) -> _Record:
    """Assign a certificate payload before binding its snapshot and issuer."""
    for name, value in values.items():
        object.__setattr__(record, name, value)
    object.__setattr__(record, "_seal", issuer)
    object.__setattr__(record, "_binding", record._snapshot())
    return record
