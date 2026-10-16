"""Demand lifecycle for scheduler-owned reverse/add source images."""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import ExitStack
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageDemand,
    SourceImageID,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.sequences.reverse_add.source_actions import (
    ReverseActionArena,
    ReverseSource,
)

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.q19_controlled_gt_bank import (
        SourceGuardedGTBankAction,
    )
    from number_compiler.sequences.reverse_add.q19_spatial_bank_morphism import (
        ReverseAddSpatialBankMorphism,
    )
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        ReverseAddTemporalRingBank,
    )


class ReverseSourceImageWorkspace:
    """Demanded reverse/add image bound to one original source and one action."""

    def __init__(
        self,
        ledger: ResourceLedger,
        seed: int,
        steps: int,
        *,
        base: int = 10,
        source_construction: OriginalSourceConstruction | None = None,
    ) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("reverse source workspace requires a resource ledger")
        seed = require_integer(seed, "seed", 0)
        steps = require_integer(steps, "reverse/add steps", 0)
        base = require_integer(base, "base", 2)
        if base == 10 and source_construction is not None:
            raise ValueError(
                "decimal source images do not consume recursive source authority"
            )
        self.ledger = ledger
        ledger.bump(_shared_keys.TEMPORAL_POINT_REQUESTS, 0)
        ledger.bump(_shared_keys.TEMPORAL_LENGTH_REQUESTS, 0)
        rollback = ExitStack()
        with cleanup_on_error(rollback.close):
            from number_compiler.sequences.reverse_add.source_images import (
                MAX_COMPLETED_CHILD_FALLBACK_STEPS,
                _ReverseSourceImageAdapter,
            )

            actions = ReverseActionArena(ledger)
            rollback.callback(actions.dispose)
            source = actions.admit_source(seed, base)
            root_action = actions.action(steps)
            scheduler = TileScheduler.source_only(ledger)
            rollback.callback(scheduler.dispose_source_images)
            adapter = _ReverseSourceImageAdapter(actions)
            rollback.callback(adapter.dispose)
            pointed_owner = ledger.register(
                f"reverse-source-pointed-bank-{ledger.owner_count}",
                "reverse_source_pointed_gt_bank",
            )
            pointed_gt_banks: OwnedMemo[
                tuple[ReverseSource, int, int], SourceGuardedGTBankAction
            ] = OwnedMemo(
                ledger,
                pointed_owner,
                nodes_per_entry=1,
            )
            rollback.callback(pointed_gt_banks.dispose)
            if base != 10 and 3 <= steps <= MAX_COMPLETED_CHILD_FALLBACK_STEPS:
                adapter.prepare_recursive_authority(
                    actions.source(source), steps, source_construction
                )
            scheduler.register_source_image_adapter(adapter)
            self.actions = actions
            self.source = source
            self.root_action = root_action
            self.scheduler = scheduler
            self.adapter = adapter
            self._pointed_gt_banks = pointed_gt_banks
            self.steps = steps
            self.base = base
            self._request_binding = (seed, steps, base)
            self._image: SourceImageID | None = None
            self._image_cache_owner: ArenaToken = scheduler._source_image_core().owner
            self._disposed = False
            self._cleanup_complete = False
            self._authority = (
                ledger,
                actions,
                source,
                root_action,
                scheduler,
                adapter,
                steps,
                base,
                source_construction,
                self._request_binding,
                pointed_gt_banks,
            )
            ledger.register_execution_root(self)
            self._audit_action_nodes = actions._nodes._data
            self._audit_action_normal = actions._normal._data
            self._audit_sources = actions._sources._data
            self._audit_action_workspace = actions._workspace
            self._audit_recursive_occurrences = adapter._recursive_occurrences._data
            self._audit_pointed_gt_banks = pointed_gt_banks._data
            self._audit_source_contract_key: (
                tuple[tuple[tuple[int, str, str], ...], tuple[int, ...]] | None
            ) = None
            rollback.callback(self._remove_source_payload_audit_contract)
            self._register_source_payload_audit_contract()
            rollback.pop_all()

    def _remove_source_payload_audit_contract(self) -> None:
        # The ledger may publish the contract before registration raises, so
        # the local cache key is not authoritative for cleanup. Ledger removal
        # is idempotent for an absent family contract.
        self.ledger.remove_payload_audit_contract(self, "reverse_add")
        self._audit_source_contract_key = None

    def _register_source_payload_audit_contract(self) -> None:
        from number_compiler.resources.payload_contracts import (
            PayloadAuditStoreBinding,
        )
        from number_compiler.sequences.reverse_add.source_audit_bindings import (
            bind_nested_source_stores,
        )
        from number_compiler.sequences.reverse_add.source_payload_audit import (
            audit_reverse_source_owner,
        )

        bindings = (
            PayloadAuditStoreBinding(
                self.actions._nodes.owner,
                "_audit_action_nodes",
                "reverse_source_action",
            ),
            PayloadAuditStoreBinding(
                self.actions._normal.owner,
                "_audit_action_normal",
                "reverse_source_action_normal_form",
            ),
            PayloadAuditStoreBinding(
                self.actions._sources.owner,
                "_audit_sources",
                "reverse_original_source",
            ),
            PayloadAuditStoreBinding(
                self.actions._workspace_owner,
                "_audit_action_workspace",
                "reverse_source_action_workspace",
            ),
            PayloadAuditStoreBinding(
                self.adapter._recursive_occurrences.owner,
                "_audit_recursive_occurrences",
                "reverse_recursive_occurrence_binding",
            ),
            PayloadAuditStoreBinding(
                self._pointed_gt_banks.owner,
                "_audit_pointed_gt_banks",
                "reverse_source_pointed_gt_bank",
            ),
            *bind_nested_source_stores(self),
        )
        binding_key = tuple(
            (binding.owner, binding.attribute, binding.role) for binding in bindings
        )
        q19_owner = self.adapter._q19_owner
        dependencies = () if q19_owner is None else (q19_owner,)
        dependency_key = tuple(id(dependency) for dependency in dependencies)
        contract_key = (binding_key, dependency_key)
        if contract_key == self._audit_source_contract_key:
            return
        if self._audit_source_contract_key is not None:
            self.ledger.remove_payload_audit_contract(self, "reverse_add")
        self.ledger.register_payload_audit_contract(
            self,
            "reverse_add",
            bindings,
            audit_reverse_source_owner,
            dependencies=dependencies,
        )
        self._audit_source_contract_key = contract_key

    def _check_open(self, *, check_image: bool = True) -> None:
        if self._disposed:
            raise ValueError("disposed reverse source workspace")
        (
            ledger,
            actions,
            source,
            root_action,
            scheduler,
            adapter,
            steps,
            base,
            source_construction,
            request_binding,
            pointed_gt_banks,
        ) = self._authority
        if (
            self.ledger is not ledger
            or self.actions is not actions
            or self.source != source
            or self.root_action != root_action
            or self.scheduler is not scheduler
            or self.adapter is not adapter
            or self._pointed_gt_banks is not pointed_gt_banks
            or self.steps != steps
            or self.base != base
            or self._request_binding is not request_binding
            or request_binding[1:] != (steps, base)
            or (
                source_construction is not None
                and adapter._recursive_construction is not source_construction
            )
            or adapter.actions is not actions
            or adapter.ledger is not ledger
            or scheduler.ledger is not ledger
        ):
            raise ValueError("reverse source workspace binding was altered")
        actions.source(source)
        actions.node(root_action)
        if actions.node(root_action).steps != steps:
            raise ValueError("reverse source workspace action was altered")
        cache_owner = scheduler._source_image_core().owner
        if cache_owner is not self._image_cache_owner:
            self._image = None
            pointed_gt_banks.clear()
            adapter.clear_query_output()
            self._image_cache_owner = cache_owner
            self._register_source_payload_audit_contract()
        image = self._image
        if image is not None and check_image:
            view = scheduler._source_image_core().view(image)
            if view.binding.source != source or view.binding.action != root_action:
                raise ValueError("reverse source workspace image binding was altered")

    def check_request(self, seed: int, steps: int, base: int) -> None:
        """Authenticate a consumer against this workspace's original request."""
        require_integer(seed, "seed", 0)
        require_integer(steps, "reverse/add steps", 0)
        require_integer(base, "base", 2)
        self._check_open()
        if (seed, steps, base) != self._request_binding:
            raise ValueError("reverse source workspace belongs to another request")

    def boundary_source_ports(self) -> SourceCarryPorts:
        """Share admitted source carries without constructing a target image."""
        self._check_open()
        if self.base != 10:
            raise ValueError("boundary source ports require a decimal source")
        source = self.actions.source(self.source)
        ports = self.adapter.ports(source)
        self._register_source_payload_audit_contract()
        return ports

    def completed_width_if_cached(self) -> int | None:
        """Return only a still-owned width projection; never demand one here."""
        self._check_open()
        image = self._image
        if image is not None:
            retained = self.scheduler.cached_source_projection(
                self.adapter, image, SourceImageDemand("width")
            )
            if retained is not None:
                if type(retained.value) is not int:
                    raise TypeError(
                        "reverse source width projection must be an integer"
                    )
                return retained.value
        return None

    def _demanded_image(self, demand: SourceImageDemand) -> SourceImageID:
        self._check_open()
        found = self._image
        if found is None:
            found = self.scheduler.source_image_demanded(
                self.adapter, self.source, self.root_action, demand
            )
            self._image = found
        self._register_source_payload_audit_contract()
        return found

    @property
    def operator_nodes(self) -> int:
        return self.actions.operator_nodes

    @property
    def compose_operations(self) -> int:
        return self.actions.compose_operations

    @property
    def syntax_depth_bound(self) -> int:
        return self.actions.node(self.root_action).depth

    def certified_temporal_ring_bank(
        self, start: int, count: int
    ) -> ReverseAddTemporalRingBank:
        """NC16 finite open ring over the actual decimal reverse/add source.

        This is source/carry/modular guarded, not a copied 2rev10 clock or a
        whole-root output action.  The explicit observer cannot replay a
        future border phase that its first source cannot certify.
        """
        self._check_open()
        if self.base != 10:
            raise ValueError("finite decimal ring requires 1..128 steps")
        if (
            type(start) is not int
            or type(count) is not int
            or start < 0
            or not 1 <= count <= 64
        ):
            raise ValueError("invalid ring positions")
        from .temporal_ring_harmonics import ReverseTemporalRingRefused

        if not 1 <= self.steps <= 128:
            self.ledger.bump(_reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_FAILURES)
            raise ReverseTemporalRingRefused(
                "finite reverse/add ring supports horizons of 1..128 steps"
            )
        source = self.actions.source(self.source)
        if start + count > (len(source.digits) + 1) // 2:
            self.ledger.bump(_reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_FAILURES)
            raise ReverseTemporalRingRefused(
                "ring crosses the active source pair center"
            )
        owner = self.adapter._q19_output_owner(source)
        self._register_source_payload_audit_contract()
        return owner.authorize_temporal_ring_bank(
            owner.initial,
            steps=self.steps,
            start=0,
            duration=self.steps,
            positions=tuple(range(start, start + count)),
            source_pair_prefix=min(start + count + 2, (len(source.digits) + 1) // 2),
            window_digits=3 if len(source.digits) >= 7 else 1,
            max_states=512,
            max_cells=8192,
        )

    def certified_spatial_bank_morphism(
        self, start: int, count: int, *, period: int = 2
    ) -> ReverseAddSpatialBankMorphism:
        """Publish a finite protected spatial output from the live source root."""
        self._check_open()
        if self.base != 10 or not 1 <= self.steps <= 128:
            raise ValueError("only finite source-certified decimal bank horizons")
        if (
            type(start) is not int
            or type(count) is not int
            or type(period) is not int
            or start < 0
            or count < 1
            or not 1 <= period <= 32
        ):
            raise ValueError("invalid spatial bank coordinates or period")
        from .mixed_periodic_bank import required_protected_halo
        from .q19_uniform_cone import UniformConeNotAuthorized

        source = self.actions.source(self.source)
        halo = required_protected_halo(period, self.steps) + 2
        if start - halo < 0 or start + count + halo > len(source.digits) // 2:
            raise UniformConeNotAuthorized(
                "unprotected source border/center in spatial bank window"
            )
        owner = self.adapter._q19_output_owner(source)
        self._register_source_payload_audit_contract()
        cert = owner.certify_border_growth(
            owner.initial, steps=self.steps, window_digits=6, max_states=2048
        )
        return owner.authorize_spatial_bank_morphism(
            owner.initial,
            steps=self.steps,
            start=start,
            count=count,
            period_size=period,
            growth_control=cert,
            max_states=128,
        )

    def _certified_gt_bank_digit(self, position: int) -> int | None:
        """Try the bounded original-source GT bank for one low-side digit.

        The bank is a pointed consumer only.  It returns no complete image or
        width claim, and every refusal remains the scheduler's normal descent
        case.  The finite border tape comes only from the live owner's exact
        original source relation; conditional CLI growth words never enter
        this physical demand path.
        """
        if self.base != 10 or not 2 <= self.steps <= 128:
            return None
        source = self.actions.source(self.source)
        # Q19's initial pair field is the exact input to the first reverse/add
        # transition; each bank frame emits one output generation.
        depth = self.steps
        if position >= len(source.digits) // 2:
            return None

        from number_compiler.sequences.reverse_add.mixed_periodic_bank import (
            IncompleteMixedBorder,
            required_protected_halo,
        )

        min_halo = required_protected_halo(1, depth) + 2
        if position < min_halo or position + min_halo >= len(source.digits):
            self.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_POINTED_GT_BANK_HALO_REFUSALS
            )
            return None

        from number_compiler.sequences.reverse_add.q19_border_control import (
            BoundaryControlNotAuthorized,
        )
        from number_compiler.sequences.reverse_add.q19_uniform_cone import (
            UniformConeNotAuthorized,
        )

        owner = self.adapter._q19_output_owner(source)
        self._register_source_payload_audit_contract()
        cache_key = (self.source, depth, position)
        cached = self._pointed_gt_banks.get(cache_key)
        if cached is not None:
            self.ledger.bump(_reverse_add_keys.REVERSE_Q19_POINTED_GT_BANK_CACHE_HITS)
            frame = cached.frame(depth - 1)
            return frame.digits_low[position % len(cached.period)]
        try:
            control = owner.certify_border_growth(
                owner.initial, steps=depth, window_digits=6, max_states=8192
            )
        except (BoundaryControlNotAuthorized, BlockContextBudgetExceeded):
            self.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_POINTED_GT_BANK_BORDER_REFUSALS
            )
            return None

        # Independently check the first physical width bit through the exact
        # source SLP cochain before consuming a controlled bank certificate.
        # This projection does not issue another temporal Q19 step.
        if (
            owner.radix19_cochain(owner.initial, z=2, modulus=5).exits[0]
            != (control.growth_word[0])
        ):
            raise AssertionError("radix-19 carry and border growth disagree")

        # Periods are tried in increasing order and accepted only after the
        # source SLP proves the entire depth-dependent protected halo. The
        # controlled-bank constructor reserves its orbit and output growth
        # incrementally at the allocation boundary.
        max_states = 512
        max_period = min(8, len(source.digits))
        for period_size in range(1, max_period + 1):
            self.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_POINTED_GT_BANK_CANDIDATE_ATTEMPTS
            )
            try:
                action = owner.authorize_controlled_gt_bank(
                    owner.initial,
                    steps=depth,
                    coordinate=position,
                    period_size=period_size,
                    growth_control=control,
                    max_states=max_states,
                )
                frame = action.frame(depth - 1)
                value = frame.digits_low[position % period_size]
                self._pointed_gt_banks[cache_key] = action
            except (
                BlockContextBudgetExceeded,
                IncompleteMixedBorder,
                UniformConeNotAuthorized,
            ):
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_Q19_POINTED_GT_BANK_CANDIDATE_REFUSALS
                )
                continue
            self.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_POINTED_GT_BANK_APPLIED_ACTIONS
            )
            self.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_POINTED_GT_BANK_APPLIED_MOORE_STATES,
                action.moore_states,
            )
            return value
        return None

    def digit(self, position: int) -> int:
        position = require_integer(position, "digit coordinate")
        self._check_open()
        if position < 0:
            raise IndexError(position)
        self.ledger.bump(_shared_keys.TEMPORAL_POINT_REQUESTS)
        if (
            self.base == 10
            and self.steps >= 3
            and self.actions.source(self.source).digits == (0,)
        ):
            if position != 0:
                raise IndexError(position)
            return 0
        # A previously published complete image is the existing authority and
        # keeps its established cache/projection precedence.  The bounded bank
        # is only an initial point-demand constructor on a cold workspace.
        if self._image is None:
            pointed = self._certified_gt_bank_digit(position)
            if pointed is not None:
                return pointed
        demand = SourceImageDemand("digit", (position,))
        image = self._demanded_image(demand)
        return cast(
            int, self.scheduler.source_projection(self.adapter, image, demand).value
        )

    def _certified_border_width(self) -> int | None:
        """Use the full finite edge theorem for WIDTH only, never for digits.

        This source-owned option uses a short proven edge itinerary. Inputs
        too narrow for an independent edge tile, an unresolved carry branch
        or a long horizon return to the exact source scheduler; no unproved
        periodic growth word enters production.
        """
        if self.base != 10 or not 2 <= self.steps <= 128:
            return None
        source = self.actions.source(self.source)
        if len(source.digits) < 256:
            return None
        from number_compiler.sequences.reverse_add.q19_border_control import (
            BoundaryControlNotAuthorized,
        )

        owner = self.adapter._q19_output_owner(source)
        self._register_source_payload_audit_contract()
        for window in (6, 8, 10, 12):
            if len(source.digits) < 2 * window + 1:
                continue
            try:
                certificate = owner.certify_border_growth(
                    owner.initial,
                    steps=self.steps,
                    window_digits=window,
                    max_states=2048,
                )
            except (BoundaryControlNotAuthorized, BlockContextBudgetExceeded):
                self.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_REFUSALS)
                continue
            self.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_PUBLICATIONS)
            return certificate.final_width
        return None

    def width(self) -> int:
        self.ledger.bump(_shared_keys.TEMPORAL_LENGTH_REQUESTS)
        self._check_open()
        if self._image is None:
            certified_width = self._certified_border_width()
            if certified_width is not None:
                return certified_width
        if self.base == 10 and self.steps >= 3:
            self._check_open()
            if self.actions.source(self.source).digits == (0,):
                return 1
        demand = SourceImageDemand("width")
        image = self._demanded_image(demand)
        projection = self.scheduler.source_projection(self.adapter, image, demand)
        if type(projection.value) is not int:
            raise TypeError("reverse source width projection must be an integer")
        return projection.value

    def iter_digits(self) -> Iterator[int]:
        from number_compiler.sequences.reverse_add.source_images import (
            ReverseImagePayload,
        )

        self._check_open()
        if (
            self.base == 10
            and self.steps >= 3
            and self.actions.source(self.source).digits == (0,)
        ):
            yield 0
            return
        image = self._demanded_image(SourceImageDemand("width"))
        view = self.scheduler._source_image_core().view(image)
        payload = cast(ReverseImagePayload, view.payload)
        if payload.pair_output is not None:
            owner = self.adapter._q19_owner
            if owner is None:
                raise ValueError("decimal pair output owner was disposed")
            yield from owner.iter_digits(payload.pair_output)
            return
        if self.steps == 0:
            yield from self.actions.source(self.source).digits
            return
        if self.steps == 2:
            yield from self.adapter.iter_second_digits(self.actions.source(self.source))
            return
        if self.steps >= 3:
            recursive = self.adapter._recursive_for_steps(self.steps)
            if recursive is not None:
                cutover, occurrence = recursive
                yield from cutover.iter_digits(occurrence)
                return
            yield from self.adapter.iter_same_carry_digits(
                self.actions.source(self.source), self.steps
            )
            return
        yield from self.adapter.iter_primitive_digits(self.actions.source(self.source))

    def dispose(self) -> None:
        if self._cleanup_complete:
            return
        # Invalidate every public query immediately, but retain the cleanup
        # state so failed owners can be retried by a later dispose call.
        self._disposed = True
        self._image = None
        scheduler = self._authority[4]
        actions = self._authority[1]
        adapter = self._authority[5]
        cleanup_all(
            (
                self._pointed_gt_banks.dispose,
                scheduler.dispose_source_images,
                adapter.dispose,
                actions.dispose,
            )
        )
        self._remove_source_payload_audit_contract()
        self._cleanup_complete = True


__all__ = ["ReverseSourceImageWorkspace"]
