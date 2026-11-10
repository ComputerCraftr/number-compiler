"""Ledger-owned decimal pair output grammar and Q19 summaries.

This owner contains spatial pair-step work only.  Temporal powers are still
driven by ``TileScheduler`` through source-image primitive and composition
callbacks; a published occurrence is the completed SLP root plus its exact
Q19/width metadata.
"""

from __future__ import annotations

from collections.abc import Callable, Generator, Iterator
from contextlib import ExitStack, closing, contextmanager
from typing import TYPE_CHECKING

from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.q19_border_control import (
        CertifiedBorderGrowth,
    )
    from number_compiler.sequences.reverse_add.q19_controlled_gt_bank import (
        SourceGuardedGTBankAction,
    )
    from number_compiler.sequences.reverse_add.q19_periodic_cone import (
        CertifiedUniformizingCone,
    )
    from number_compiler.sequences.reverse_add.q19_spatial_bank_morphism import (
        ReverseAddSpatialBankMorphism,
    )
    from number_compiler.sequences.reverse_add.q19_uniform_cone import (
        CertifiedUniformCone,
    )
    from number_compiler.sequences.reverse_add.radix19_cochain import (
        Radix19CarryBlock,
    )
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        ReverseAddTemporalRingBank,
    )
    from number_compiler.sequences.reverse_add.temporal_seed_morphism import (
        Q19WordFiber,
    )

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import (
    BimachineSLPProjector,
)
from number_compiler.arithmetic.automata.slp_walks import iter_symbols
from number_compiler.arithmetic.contracts.input_validation import is_runtime_instance
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.construction_scope import RuntimeConstruction
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.reverse_add._q19_issuance import (
    Q19IssuanceRegistry,
)
from number_compiler.sequences.reverse_add.q19_occurrence import (
    ReversePairOutputOccurrence as ReversePairOutputOccurrence,
)
from number_compiler.sequences.reverse_add.q19_output_contracts import (
    ReversePairQ19OutputAuditSnapshot,
)
from number_compiler.sequences.reverse_add.q19_output_publication import (
    Q19OutputPublicationMixin,
)
from number_compiler.sequences.reverse_add.q19_punctured_producer import (
    PuncturedPairProducer,
)
from number_compiler.sequences.reverse_add.q19_word_summary import (
    Q19_LOWER,
    Q19_UPPER,
    Q19Summary,
    WordSummary,
    pair_step_law,
)


class ReversePairQ19OutputOwner(Q19OutputPublicationMixin):
    """One exact decimal pair transducer owned by a source-image adapter."""

    def __init__(
        self,
        ledger: ResourceLedger,
        digits_lsd: tuple[int, ...],
        *,
        base: int,
    ) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("Q19 output owner requires a resource ledger")
        if type(digits_lsd) is not tuple or not digits_lsd:
            raise ValueError("Q19 output owner requires original source digits")
        if type(base) is not int or base != 10:
            raise ValueError("the Q19 pair transducer is decimal-only")
        if any(type(value) is not int or not 0 <= value < base for value in digits_lsd):
            raise ValueError("Q19 source contains a digit outside its radix")
        self.ledger = ledger
        self.base = base
        self._digits = digits_lsd
        # One source-scoped key hint only; authenticated output handles remain
        # exclusively in the issued-occurrence memo.
        self._broadword_last: tuple[int, int] | None = None
        self._authority = ArenaToken("reverse-pair-q19-output")
        prefix = f"reverse-pair-q19-{ledger.owner_count}"

        # A construction scope records each ledger owner and weak root as it is
        # registered, so failure in any intermediate account/store constructor
        # retires exactly the resources created by this unpublished owner.
        with RuntimeConstruction(ledger):
            self.arena = LedgerSLPArena(
                ledger, prefix, owner_kind="reverse_pair_output"
            )
            self.machine = pair_step_law()
            self.projector = BimachineSLPProjector(self.machine, self.arena)

            forward_owner = ledger.register(
                prefix + "-projector-forward", "reverse_pair_projector_memo"
            )
            forward: OwnedMemo[tuple[int, int], int | None] = OwnedMemo(
                ledger, forward_owner, nodes_per_entry=1
            )
            reverse_owner = ledger.register(
                prefix + "-projector-reverse", "reverse_pair_projector_memo"
            )
            backward: OwnedMemo[tuple[int, int], int | None] = OwnedMemo(
                ledger, reverse_owner, nodes_per_entry=1
            )
            block_owner = ledger.register(
                prefix + "-projector-block", "reverse_pair_projector_memo"
            )
            block: OwnedMemo[tuple[int, int, int], int] = OwnedMemo(
                ledger, block_owner, nodes_per_entry=1
            )
            forward_power_owner = ledger.register(
                prefix + "-projector-forward-power",
                "reverse_pair_projector_memo",
            )
            forward_power: OwnedMemo[tuple[int, int, int], int | None] = OwnedMemo(
                ledger, forward_power_owner, nodes_per_entry=1
            )
            backward_power_owner = ledger.register(
                prefix + "-projector-reverse-power",
                "reverse_pair_projector_memo",
            )
            backward_power: OwnedMemo[tuple[int, int, int], int | None] = OwnedMemo(
                ledger, backward_power_owner, nodes_per_entry=1
            )
            self._projector_owners = (
                forward_owner,
                reverse_owner,
                block_owner,
                forward_power_owner,
                backward_power_owner,
            )
            self._projector_memos = (
                forward,
                backward,
                block,
                forward_power,
                backward_power,
            )
            self.projector.bind_cache_stores(
                forward=forward,
                reverse=backward,
                block=block,
                forward_power=forward_power,
                reverse_power=backward_power,
            )
            self._summary_owner = ledger.register(
                prefix + "-q19-summaries", "reverse_pair_q19_summary"
            )
            self._summaries = OwnedMemo[int, WordSummary](
                ledger, self._summary_owner, nodes_per_entry=1
            )
            self._issued_owner = ledger.register(
                prefix + "-issued-occurrences", "reverse_pair_output_occurrence"
            )
            self._issued = OwnedMemo[tuple[int, int], ReversePairOutputOccurrence](
                ledger, self._issued_owner, nodes_per_entry=1
            )
            self.word_fiber_cache_owner = ledger.register(
                prefix + "-word-fibers", "observation_memo"
            )
            self.word_fiber_cache: OwnedMemo[
                tuple[int, int, int], tuple[Q19WordFiber, tuple[object, ...]]
            ] = OwnedMemo(
                ledger, self.word_fiber_cache_owner, nodes_per_entry=32, evictable=True
            )
            self._issuance_registry = Q19IssuanceRegistry(self, ledger, prefix)
            self._border_certificates_owner = (
                self._issuance_registry.border_certificates.owner
            )
            self._border_certificates = self._issuance_registry.border_certificates
            self._controlled_gt_banks_owner = (
                self._issuance_registry.controlled_gt_banks.owner
            )
            self._controlled_gt_banks = self._issuance_registry.controlled_gt_banks
            self._spatial_bank_windows_owner = (
                self._issuance_registry.spatial_bank_windows.owner
            )
            self._spatial_bank_windows = self._issuance_registry.spatial_bank_windows
            self._temporal_ring_banks_owner = (
                self._issuance_registry.temporal_ring_banks.owner
            )
            self._temporal_ring_banks = self._issuance_registry.temporal_ring_banks
            self._diagonal_comparisons_owner = (
                self._issuance_registry.diagonal_comparisons.owner
            )
            self._diagonal_comparisons = self._issuance_registry.diagonal_comparisons
            self._scratch_owner = ledger.register(
                prefix + "-workspace", "reverse_pair_output_workspace"
            )
            self._active_symbol_walks = 0
            self._disposed = False
            self._cleanup_complete = False
            self._dispose_resources_complete = False
            self._binding = (
                ledger,
                digits_lsd,
                base,
                self._authority,
                self.arena,
                self.projector,
                self.machine,
                self._border_certificates,
                self._controlled_gt_banks,
                self._issuance_registry,
                self._spatial_bank_windows,
                self._temporal_ring_banks,
                self._diagonal_comparisons,
                self.word_fiber_cache,
            )
        with ExitStack() as rollback:
            rollback.enter_context(cleanup_on_error(self.dispose))
            ledger.register_execution_root(self)
            self._capture_audit_bindings()
            self.initial = self._make_initial()
            self._register_payload_audit_contract()

    def _capture_audit_bindings(self) -> None:
        """Retain exact store identities before fallible initial issuance."""
        self._audit_nodes = self.arena.nodes
        (
            self._audit_terms,
            self._audit_concats,
            self._audit_repeats,
        ) = self.arena.audit_interner_stores
        self._audit_summaries = self._summaries.audit_container
        self._audit_issued = self._issued.audit_container
        self._audit_word_fibers = self.word_fiber_cache.audit_container
        self._audit_border_certificates = self._border_certificates.audit_container
        self._audit_controlled_gt_banks = self._controlled_gt_banks.audit_container
        self._audit_spatial_bank_windows = self._spatial_bank_windows.audit_container
        self._audit_temporal_ring_banks = self._temporal_ring_banks.audit_container
        self._audit_diagonal_comparisons = self._diagonal_comparisons.audit_container
        (
            self._audit_projector_forward,
            self._audit_projector_reverse,
            self._audit_projector_block,
            self._audit_projector_forward_power,
            self._audit_projector_reverse_power,
        ) = tuple(memo.audit_container for memo in self._projector_memos)

    def _register_payload_audit_contract(self) -> None:
        from .q19_payload_audit_registration import (
            register_reverse_pair_output_contract,
        )

        register_reverse_pair_output_contract(
            self.ledger,
            self,
            arena_owners=self.arena.owners,
            summary_owner=self._summary_owner,
            issued_owner=self._issued_owner,
            word_fibers_owner=self.word_fiber_cache_owner,
            border_owner=self._border_certificates_owner,
            controlled_gt_owner=self._controlled_gt_banks_owner,
            spatial_owner=self._spatial_bank_windows_owner,
            ring_owner=self._temporal_ring_banks_owner,
            diagonal_owner=self._diagonal_comparisons_owner,
            projector_owners=self._projector_owners,
        )

    def audit_snapshot(self) -> ReversePairQ19OutputAuditSnapshot:
        """Expose exact backing identities to independent, read-only audits."""
        try:
            initial: ReversePairOutputOccurrence | None = self.initial
        except AttributeError:
            # Construction rollback may request an audit after the initial
            # occurrence builder failed, before the assignment completed.
            initial = None
        (
            projector_forward,
            projector_reverse,
            projector_block,
            projector_forward_power,
            projector_reverse_power,
        ) = self._projector_memos
        return ReversePairQ19OutputAuditSnapshot(
            ledger=self.ledger,
            digits=self._digits,
            base=self.base,
            authority=self._authority,
            disposed=self._disposed,
            cleanup_complete=self._cleanup_complete,
            dispose_resources_complete=self._dispose_resources_complete,
            active_symbol_walks=self._active_symbol_walks,
            binding=self._binding,
            arena=self.arena,
            projector=self.projector,
            machine=self.machine,
            issuance_registry=self._issuance_registry,
            initial=initial,
            summary_owner=self._summary_owner,
            summaries=self._summaries.audit_snapshot(),
            issued_owner=self._issued_owner,
            issued=self._issued.audit_snapshot(),
            word_fibers_owner=self.word_fiber_cache_owner,
            word_fibers=self.word_fiber_cache.audit_snapshot(),
            word_fibers_binding=self.word_fiber_cache,
            border_certificates_owner=self._border_certificates_owner,
            border_certificates=self._border_certificates.audit_snapshot(),
            border_certificates_binding=self._border_certificates,
            controlled_gt_banks_owner=self._controlled_gt_banks_owner,
            controlled_gt_banks=self._controlled_gt_banks.audit_snapshot(),
            controlled_gt_banks_binding=self._controlled_gt_banks,
            spatial_bank_windows_owner=self._spatial_bank_windows_owner,
            spatial_bank_windows=self._spatial_bank_windows.audit_snapshot(),
            spatial_bank_windows_binding=self._spatial_bank_windows,
            temporal_ring_banks_owner=self._temporal_ring_banks_owner,
            temporal_ring_banks=self._temporal_ring_banks.audit_snapshot(),
            temporal_ring_banks_binding=self._temporal_ring_banks,
            diagonal_comparisons_owner=self._diagonal_comparisons_owner,
            diagonal_comparisons=self._diagonal_comparisons.audit_snapshot(),
            diagonal_comparisons_binding=self._diagonal_comparisons,
            projector_owners=self._projector_owners,
            projector_forward=projector_forward.audit_snapshot(),
            projector_reverse=projector_reverse.audit_snapshot(),
            projector_block=projector_block.audit_snapshot(),
            projector_forward_power=projector_forward_power.audit_snapshot(),
            projector_reverse_power=projector_reverse_power.audit_snapshot(),
            projector_cache_stores=self.projector.audit_cache_stores,
            audit_bindings=(
                self._audit_nodes,
                self._audit_terms,
                self._audit_concats,
                self._audit_repeats,
                self._audit_summaries,
                self._audit_issued,
                self._audit_word_fibers,
                self._audit_border_certificates,
                self._audit_controlled_gt_banks,
                self._audit_spatial_bank_windows,
                self._audit_temporal_ring_banks,
                self._audit_diagonal_comparisons,
                self._audit_projector_forward,
                self._audit_projector_reverse,
                self._audit_projector_block,
                self._audit_projector_forward_power,
                self._audit_projector_reverse_power,
            ),
        )

    def validate_open(self) -> None:
        if self._disposed:
            raise ValueError("disposed Q19 pair output owner")
        if self.base != 10 or type(self._digits) is not tuple or not self._digits:
            raise ValueError("Q19 pair output source binding changed")
        current = (
            self.ledger,
            self._digits,
            self.base,
            self._authority,
            self.arena,
            self.projector,
            self.machine,
            self._border_certificates,
            self._controlled_gt_banks,
            self._issuance_registry,
            self._spatial_bank_windows,
            self._temporal_ring_banks,
            self._diagonal_comparisons,
            self.word_fiber_cache,
        )
        if len(self._binding) != len(current) or any(
            original is not bound
            for original, bound in zip(self._binding, current, strict=True)
        ):
            raise ValueError("Q19 output owner or finite law binding changed")
        self._issuance_registry.validate_stores(
            border_certificates=self._border_certificates,
            controlled_gt_banks=self._controlled_gt_banks,
            spatial_bank_windows=self._spatial_bank_windows,
            temporal_ring_banks=self._temporal_ring_banks,
            diagonal_comparisons=self._diagonal_comparisons,
        )

    @property
    def is_disposed(self) -> bool:
        """Expose the owner's lifecycle state to its issuance registry."""
        return self._disposed

    @property
    def initial_digits(self) -> tuple[int, ...]:
        return self._digits

    @property
    def issuance_registry(self) -> Q19IssuanceRegistry:
        return self._issuance_registry

    def validate_issuance_registry(self, registry: Q19IssuanceRegistry) -> None:
        """Authenticate the exact registry and its retained mirrors."""
        self.validate_open()
        if self._issuance_registry is not registry:
            raise ValueError("Q19 issuance registry binding changed")

    @property
    def scratch_owner(self) -> int:
        return self._scratch_owner

    def published_word_summary(self, root: int) -> WordSummary:
        summary = self._summaries.audit_snapshot().payload_view[root]
        if not is_runtime_instance(summary, WordSummary):
            raise TypeError("published Q19 summary has another record type")
        return summary

    def issued_carry_phi6_packet(
        self, occurrence: ReversePairOutputOccurrence
    ) -> dict[str, object]:
        """Demand the source's spatial five-band and forward carry responses.

        Both Phi6 roots retain both incoming physical carry cases. The packet
        belongs to this issued Q19 occurrence and licenses no temporal return.
        """
        from number_compiler.arithmetic.fields.decimal_pair_partition import (
            DECIMAL_PAIR_BANDS,
            decimal_pair_partition,
        )
        from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
            crt_mod70_from_residues,
        )

        from .temporal_matrix7_port import Mod7CarryPortAction

        self.validate_occurrence(occurrence)
        if self._summaries.get(occurrence.root) is None:
            raise ValueError("issued Q19 source lost its cached base summary")
        base_summary = self._validated_full_summary(occurrence)
        phi6 = self._demanded_carry_phi6_summary(occurrence)
        if phi6.length != base_summary.length or (
            phi6.carry_exit(0),
            phi6.carry_exit(1),
        ) != (
            int(base_summary.domain == Q19_UPPER),
            int(base_summary.domain != Q19_LOWER),
        ):
            raise ValueError("Phi6 carry projection disagrees with issued Q19 extent")
        source_summary = self._summaries.get(occurrence.root)
        if not is_runtime_instance(source_summary, WordSummary):
            raise TypeError("source-issued Q19 word changed summary type")
        if source_summary.first_symbol is None:
            raise ValueError("source-issued Q19 word lost its first pair")
        first = self.symbol_at(occurrence.root, 1)
        if not 0 <= first <= 18 or first != source_summary.first_symbol:
            raise ValueError("source-issued Q19 first pair metadata changed")
        first_bands = decimal_pair_partition(first).masks
        mirror_factor = pow(5, (phi6.length - 1) % 6, 7)

        def symmetric_phi6(at3: int) -> tuple[int, int]:
            # Raw pair coefficients are palindromic; physical carry is not.
            return phi6.phi6(at3, mirror_factor * at3 % 7)

        gt3 = (phi6.bands3[3] + phi6.bands3[4]) % 7
        eq3 = phi6.bands3[2]
        growth = phi6.carry_exit(0)
        difference = phi6.aligned_difference_mod7()
        port = Mod7CarryPortAction.from_port(difference_mod7=difference, growth=growth)
        return {
            "source_pair_width": phi6.length,
            "occurrence_temporal_steps": occurrence.temporal_steps,
            "spatial_orientation": "lsd_to_msd",
            "scope": "whole symmetric Q19 occurrence; spatial carry only",
            "spatial_phase_mod6": phi6.length % 6,
            "raw_gt_mask_mod70": crt_mod70_from_residues(gt3, int(first > 9)),
            "raw_eq_mask_mod70": crt_mod70_from_residues(eq3, int(first == 9)),
            "propagated_carry_mod70": crt_mod70_from_residues(
                phi6.carry3[0], int(first > 9)
            ),
            "raw_gt_phi6_mod7": symmetric_phi6(gt3),
            "raw_eq_phi6_mod7": symmetric_phi6(eq3),
            "five_band_mod70": {
                band.value: crt_mod70_from_residues(residue, first_bands[index])
                for index, (band, residue) in enumerate(
                    zip(DECIMAL_PAIR_BANDS, phi6.bands3, strict=True)
                )
            },
            "five_band_phi6_mod7": {
                band.value: symmetric_phi6(residue)
                for band, residue in zip(DECIMAL_PAIR_BANDS, phi6.bands3, strict=True)
            },
            "forward_carry_at3": phi6.carry3,
            "forward_carry_at5": phi6.carry5,
            "propagated_carry_phi6_mod7": phi6.carry_phi6(),
            "growth_carry": growth,
            "aligned_difference_mod7": difference,
            "source_mod7_affine_action": (port.multiplier, port.correction),
            "mod7_affine_source_step": occurrence.temporal_steps,
            "mod7_affine_target_step": occurrence.temporal_steps + 1,
            "mod7_affine_coordinate": "normalized decimal term residue",
            "complete_temporal_successor_certified": False,
        }

    def discard_published_word_summary(self, root: int) -> None:
        if root in self._summaries:
            del self._summaries[root]

    def pair_value_at(self, occurrence: ReversePairOutputOccurrence, index: int) -> int:
        from .q19_source_authority import pair_value_at

        return pair_value_at(self, occurrence, index)

    def apply_punctured_pair_block(
        self, occurrence: ReversePairOutputOccurrence, *, steps: int
    ) -> ReversePairOutputOccurrence:
        """Apply a checked finite group-ring/carry macro on one issued field."""
        return PuncturedPairProducer(self).apply(occurrence, steps=steps)

    def radix19_cochain(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        z: int = 2,
        modulus: int = 5,
    ) -> Radix19CarryBlock:
        """Project an issued Q19 source through decimal normalization."""
        from .q19_source_authority import radix19_cochain

        return radix19_cochain(self, occurrence, z=z, modulus=modulus)

    def radix19_walsh64_mod5(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        channel: str,
        start: int = 0,
    ) -> tuple[int, ...]:
        """Read 64 source-bound pair ports and transform them over F5."""
        from .q19_source_authority import radix19_walsh64_mod5

        return radix19_walsh64_mod5(self, occurrence, channel=channel, start=start)

    def authorize_radix19_gt_bank(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        coordinate: int,
        period_sizes: tuple[int, ...] = (1, 2, 3, 4, 5, 6, 7, 8),
        window_digits: int = 6,
        max_states: int = 8192,
    ) -> SourceGuardedGTBankAction:
        """Join exact border growth with a source-guarded conditional bank."""
        from .q19_source_authority import authorize_radix19_gt_bank

        return authorize_radix19_gt_bank(
            self,
            occurrence,
            steps=steps,
            coordinate=coordinate,
            period_sizes=period_sizes,
            window_digits=window_digits,
            max_states=max_states,
        )

    def authorize_temporal_cell(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        coordinate: int,
    ) -> CertifiedUniformCone:
        """Authorize one protected interior coefficient from its source."""
        from .q19_source_authority import authorize_temporal_cell

        return authorize_temporal_cell(
            self, occurrence, steps=steps, coordinate=coordinate
        )

    def authorize_mixed_temporal_cell(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        coordinate: int,
        period_size: int = 2,
    ) -> CertifiedUniformizingCone:
        """Authorize a mixed periodic source core that closes to uniform."""
        from .q19_source_authority import authorize_mixed_temporal_cell

        return authorize_mixed_temporal_cell(
            self,
            occurrence,
            steps=steps,
            coordinate=coordinate,
            period_size=period_size,
        )

    def certify_border_growth(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        window_digits: int = 2,
        max_states: int = 8192,
    ) -> CertifiedBorderGrowth:
        """Certify a finite growth tape from the exact source root."""
        from .q19_source_authority import certify_border_growth

        return certify_border_growth(
            self,
            occurrence,
            steps=steps,
            window_digits=window_digits,
            max_states=max_states,
        )

    def authorize_controlled_gt_bank(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        coordinate: int,
        growth_control: tuple[int, ...] | CertifiedBorderGrowth,
        period_size: int = 2,
        max_states: int = 10000,
    ) -> SourceGuardedGTBankAction:
        """Authorize a conditional source-protected GT/F5 bank."""
        from .q19_source_authority import authorize_controlled_gt_bank

        return authorize_controlled_gt_bank(
            self,
            occurrence,
            steps=steps,
            coordinate=coordinate,
            growth_control=growth_control,
            period_size=period_size,
            max_states=max_states,
        )

    def authorize_spatial_bank_morphism(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        start: int,
        count: int,
        growth_control: tuple[int, ...] | CertifiedBorderGrowth,
        period_size: int = 2,
        max_states: int = 10000,
    ) -> ReverseAddSpatialBankMorphism:
        """Issue a protected multi-cell GT/EQ/LT output morphism."""
        from .q19_spatial_bank_morphism import authorize_spatial_bank_morphism

        return authorize_spatial_bank_morphism(
            self,
            occurrence,
            steps=steps,
            start=start,
            count=count,
            growth_control=growth_control,
            period_size=period_size,
            max_states=max_states,
        )

    def authorize_temporal_ring_bank(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        start: int = 0,
        duration: int | None = None,
        positions: tuple[int, ...] = (0,),
        source_pair_prefix: int = 0,
        window_digits: int = 3,
        max_states: int = 8192,
        max_cells: int = 16384,
        include_source_digits: bool = False,
    ) -> ReverseAddTemporalRingBank:
        """Build a *finite*, source-certified reverse/add macro ring bank.

        No 2rev10 periods are imported and no full-root REPEAT is authorized.
        """
        cert = self.certify_border_growth(
            occurrence,
            steps=steps,
            window_digits=window_digits,
            max_states=max_states,
        )
        return self.authorize_certified_temporal_ring_bank(
            cert,
            start=start,
            duration=duration,
            positions=positions,
            source_pair_prefix=source_pair_prefix,
            max_cells=max_cells,
            include_source_digits=include_source_digits,
        )

    def authorize_certified_temporal_ring_bank(
        self,
        certificate: CertifiedBorderGrowth,
        *,
        start: int = 0,
        duration: int | None = None,
        positions: tuple[int, ...] = (0,),
        source_pair_prefix: int = 0,
        include_source_digits: bool = False,
        max_cells: int = 16384,
        bank_action: SourceGuardedGTBankAction | None = None,
    ) -> ReverseAddTemporalRingBank:
        """Build and issue only from an authenticated Q19 certificate."""
        self.validate_open()
        from .q19_border_control import CertifiedBorderGrowth

        if type(certificate) is not CertifiedBorderGrowth:
            raise TypeError("temporal ring requires an exact border certificate")
        if certificate.owner is not self:
            raise ValueError("temporal ring certificate belongs to another Q19 owner")
        certificate.validate(self, certificate.source)
        from .temporal_ring_harmonics import issue_temporal_ring_bank_from_source

        return issue_temporal_ring_bank_from_source(
            certificate,
            self._issuance_registry,
            start=start,
            duration=duration,
            positions=positions,
            source_pair_prefix=source_pair_prefix,
            include_source_digits=include_source_digits,
            max_cells=max_cells,
            bank_action=bank_action,
        )

    def compose_temporal_ring_banks(
        self,
        first: ReverseAddTemporalRingBank,
        later: ReverseAddTemporalRingBank,
    ) -> ReverseAddTemporalRingBank:
        """Join adjacent issued children and publish through this Q19 owner."""
        self.validate_open()
        from .temporal_ring_harmonics import compose_issued_temporal_ring_banks

        return compose_issued_temporal_ring_banks(first, later, self._issuance_registry)

    def validate_temporal_ring_bank(self, bank: ReverseAddTemporalRingBank) -> None:
        """Validate a retained ring through its owning Q19 registry."""
        self.validate_open()
        if bank.certificate.owner is not self:
            raise ValueError("temporal ring belongs to another Q19 owner")
        self._issuance_registry.validate_temporal_ring_bank(bank)

    def range_summary(
        self, root: int, begin: int, end: int, *, reverse: bool = False
    ) -> Q19Summary:
        from .q19_source_authority import range_summary

        return range_summary(self, root, begin, end, reverse=reverse)

    def digit(self, occurrence: ReversePairOutputOccurrence, position: int) -> int:
        from .q19_source_authority import digit

        return digit(self, occurrence, position)

    def _iter_symbols(
        self, root: int, *, reverse: bool = False
    ) -> Generator[int, None, None]:
        def record_visit(is_node: bool) -> None:
            if is_node:
                self.ledger.bump(_shared_keys.RECURSIVE_OUTPUT_STREAM_NODE_VISITS)

        def walk() -> Generator[int, None, None]:
            with self._active_scratch_use():
                yield from iter_symbols(
                    self.arena,
                    root,
                    reverse=reverse,
                    on_task=record_visit,
                    reserve_task=lambda: self.ledger.reserve(
                        self._scratch_owner, nodes=1
                    ),
                    release_tasks=lambda count: self.ledger.release(
                        self._scratch_owner, nodes=count
                    ),
                    check_open=self.validate_open,
                )

        return walk()

    @contextmanager
    def _active_scratch_use(self) -> Generator[None, None, None]:
        """Keep the existing scratch owner alive through a charged demand."""
        self.validate_open()
        # This audit-visible count also covers non-stream demands that reserve
        # the same scratch owner. Its disposal finalizer has one owner.
        self._active_symbol_walks += 1
        try:
            yield
        finally:
            self._active_symbol_walks -= 1
            if self._disposed and self._active_symbol_walks == 0:
                self._mark_scratch_disposed()
                if self._dispose_resources_complete:
                    self._cleanup_complete = True

    def iter_pair_values(
        self, occurrence: ReversePairOutputOccurrence
    ) -> Generator[int, None, None]:
        self.validate(occurrence)
        yield from self._stream_pair_values(occurrence)

    def iter_encoded_symbols(
        self, occurrence: ReversePairOutputOccurrence
    ) -> Generator[int, None, None]:
        """Stream one issued encoded half, with the owner's charged worklist."""
        self.validate_issued_occurrence(occurrence)
        return self._iter_symbols(occurrence.root)

    def _stream_pair_values(
        self, occurrence: ReversePairOutputOccurrence
    ) -> Generator[int, None, None]:
        # Public entrypoints authenticate before entering this private stream.
        encoded_length = self.arena.nodes[occurrence.root].length
        parity = self.symbol_at(occurrence.root, 0) - (2 * self.base - 1)
        if parity not in (0, 1):
            raise ValueError("pair output grammar has an invalid parity tag")
        emitted = 0
        with closing(self._iter_symbols(occurrence.root)) as forward:
            for index, symbol in enumerate(forward):
                if 0 < index < encoded_length - 1:
                    emitted += 1
                    yield symbol
        reverse_seen = 0
        with closing(self._iter_symbols(occurrence.root, reverse=True)) as backward:
            for index, symbol in enumerate(backward):
                if not 0 < index < encoded_length - 1:
                    continue
                if parity and reverse_seen == 0:
                    reverse_seen += 1
                    continue
                reverse_seen += 1
                emitted += 1
                yield symbol
        if emitted != occurrence.pair_width:
            raise AssertionError("Q19 output grammar stream changed its pair width")

    def iter_digits(self, occurrence: ReversePairOutputOccurrence) -> Iterator[int]:
        self.validate(occurrence)
        carry = 0
        emitted = 0
        with closing(self._stream_pair_values(occurrence)) as pairs:
            for pair in pairs:
                total = pair + carry
                carry, digit = divmod(total, self.base)
                emitted += 1
                self.ledger.bump(_shared_keys.RECURSIVE_OUTPUT_STREAM_EMITTED_DIGITS)
                yield digit
        if carry:
            emitted += 1
            self.ledger.bump(_shared_keys.RECURSIVE_OUTPUT_STREAM_EMITTED_DIGITS)
            yield carry
        if emitted != occurrence.output_width:
            raise AssertionError("Q19 output stream disagrees with exact width")

    def dispose(self) -> None:
        if self._cleanup_complete:
            return
        self._disposed = True
        if not self._dispose_resources_complete:
            cleanup: list[Callable[[], object]] = [
                self._unregister_payload_audit_contract,
                self.word_fiber_cache.dispose,
                self._issued.dispose,
                self._diagonal_comparisons.dispose,
                self._temporal_ring_banks.dispose,
                self._spatial_bank_windows.dispose,
                self._controlled_gt_banks.dispose,
                self._border_certificates.dispose,
                self._summaries.dispose,
                *(memo.dispose for memo in self._projector_memos),
            ]

            def dispose_arena() -> None:
                nodes = self.arena.nodes
                if type(nodes) is not LedgerList:
                    raise TypeError("pair grammar lost its ledger node store")
                self.arena.dispose()

            def dispose_scratch() -> None:
                if self._active_symbol_walks == 0:
                    self._mark_scratch_disposed()

            cleanup.append(dispose_arena)
            cleanup.append(dispose_scratch)
            cleanup_all(cleanup)
            self._dispose_resources_complete = True
        if self._active_symbol_walks == 0:
            self._mark_scratch_disposed()
            self._cleanup_complete = True

    def _mark_scratch_disposed(self) -> None:
        self.ledger.mark_disposed(self._scratch_owner)

    def _unregister_payload_audit_contract(self) -> None:
        self.ledger.remove_payload_audit_contract(self, "reverse_add")


__all__ = ["ReversePairOutputOccurrence", "ReversePairQ19OutputOwner"]
