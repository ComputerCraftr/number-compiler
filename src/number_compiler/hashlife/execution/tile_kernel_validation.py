"""Pure input and fused-capability checks for the primitive tile adapter."""

from __future__ import annotations

from typing import TYPE_CHECKING, Protocol

from number_compiler.resources.tile_alphabet_contract import (
    CANONICAL_TILE_ALPHABET_VERSION,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_execution_adapter import (
        FamilyTileHooks,
    )
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.resources.causal_workspace import CausalActionAdmission

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, _effect_key
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    DECIMAL_REVERSE_GROWTH_CERTIFICATE,
    FrobeniusSectorSourceBound,
    ReverseFrobeniusPlan,
    validate_decimal_growth_certificate,
)
from number_compiler.arithmetic.radix_division import (
    SymbolicBinaryDivisionEffect,
    certified_binary_division_radix,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.actions.tile_action_algebra import (
    PrimitiveTileAction,
    blank_context_metadata,
)
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    PrimitiveKernel,
)
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tiles import TileArena, TileID


class _ActionView(Protocol):
    @property
    def kernel(self) -> ActionProgramID: ...
    @property
    def signature(self) -> PortSignatureID: ...
    @property
    def children(self) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...
    @property
    def cocycle(self) -> TemporalCocycle: ...
    @property
    def repetitions(self) -> int: ...
    @property
    def homogeneous(self) -> bool: ...
    @property
    def spatial_events_add(self) -> bool: ...
    @property
    def reverse_frobenius(self) -> ReverseFrobeniusPlan | None: ...


class _Host(Protocol):
    tiles: TileArena
    kernels: DiamondKernelArena

    def action_record(self, action: FieldCellActionID) -> _ActionView: ...
    def validate_action(self, action: FieldCellActionID) -> None: ...
    def fused_primitive_pair(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...


def validate_input(
    self: _Host,
    action: FieldCellActionID,
    source: TileID,
    *,
    output: bool = False,
) -> None:
    """Validate immutable tile interpretation without interning anything."""
    if type(output) is not bool:
        raise TypeError("tile alphabet direction requires a boolean")
    # Admission permits composition only when base, blank and cell width agree.
    # The action's validated kernel is therefore an alphabet witness for both
    # endpoints. Walking a temporal spine here repeats O(log N) work at every
    # spatial memo hit without obtaining any additional alphabet information.
    current = self.action_record(action)
    kernel = self.kernels.kernel(current.kernel)
    validate_kernel_alphabet(self.tiles, source, kernel)


def validate_fused_action(self: _Host, action: FieldCellActionID) -> None:
    """Validate a binary edge admitted by finite or causal tile absorption."""
    # `action_record` performs the complete warm validation. Calling
    # `validate_action` first repeats the same immutable-record audit.
    if self.action_record(action).children is None:
        raise UnsupportedInterfaceError(
            "primitive temporal action has no bounded fused primitive-pair or causal edge"
        )


def validate_fused_wiring(
    self: _Host,
    action: FieldCellActionID,
    producer: ResultWiring,
    result: ResultWiring,
) -> None:
    pair = self.action_record(action).children
    if pair is None:
        raise UnsupportedInterfaceError("fused wiring requires a temporal edge")
    expected = self.action_record(pair[0]).signature
    if (
        producer.signature != expected
        or result.signature != self.action_record(pair[1]).signature
    ):
        raise ValueError("fused producer or result has another port signature")
    if any((producer.orientation, producer.phase, result.orientation, result.phase)):
        raise ValueError("primitive fused wiring has no certified automorphism")


def admit_family_effect(
    effect: BlockEffect,
    hooks: FamilyTileHooks | None,
) -> BlockEffect:
    """Admit a family primitive or reject its compatibility form precisely."""
    if hooks is None:
        raise ValueError(
            "unsupported weighted runtime kernel: no certified family hook"
        )
    if hooks.owns_effect(effect):
        return hooks.clone(effect)
    if hooks.owns_compatibility(effect):
        message = hooks.compatibility_tile_error(effect)
        if message is not None:
            raise ValueError(message)
    raise ValueError("unsupported weighted runtime kernel: no certified family hook")


__all__ = [
    "admit_family_effect",
    "admitted_action_record",
    "validate_action_record",
    "validate_fused_action",
    "validate_fused_wiring",
    "validate_input",
]


def admitted_action_record(
    self: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
    admission: CausalActionAdmission,
) -> PrimitiveTileAction:
    """Read an action row using its live admission without deep replay."""
    from number_compiler.resources.causal_workspace import (
        CausalActionAdmission,
        action_admission_matches,
        action_admission_snapshot,
    )

    if type(admission) is not CausalActionAdmission:
        raise TypeError("causal metadata read requires its admitted-run lease")
    expected = admission.admitted_snapshot_for(self, action)
    record = self.checked_action_record(action)
    if not action_admission_matches(
        expected, action_admission_snapshot(action, record)
    ):
        raise ValueError("causal action metadata changed after admission")
    return record


def validate_action_record(
    self: PrimitiveTileKernelAdapter, action: FieldCellActionID
) -> tuple[PrimitiveTileAction, PrimitiveKernel]:
    """Authenticate retained action structure without rebuilding deep semantics."""
    record = self.checked_action_record(action)
    kernel = self.kernels.kernel(record.kernel)
    self.quotients.interface(record.signature)
    if type(record.repetitions) is not int or record.repetitions < 1:
        raise ValueError("tile action has an invalid repetition count")
    if type(record.cocycle) is not TemporalCocycle:
        raise TypeError("tile action has another cocycle sort")
    if type(record.homogeneous) is not bool:
        raise TypeError("tile action has another algebra-kind flag")
    if type(record.spatial_events_add) is not bool:
        raise TypeError("tile action has another spatial weight law")
    expected_reverse = (
        record.homogeneous
        and type(kernel.effect) is BaseBlockEffect
        and kernel.base == 10
    )
    plan = record.reverse_frobenius
    if expected_reverse:
        if type(plan) is not ReverseFrobeniusPlan:
            raise TypeError("decimal reverse action requires its Frobenius plan")
        if (
            type(plan.maximum_classes) is not int
            or type(plan.bits) is not int
            or type(plan.steps) is not int
        ):
            raise TypeError("reverse Frobenius plans require exact integers")
        if (
            plan.maximum_classes != 8
            or plan.bits != 5
            or plan.steps != record.repetitions
            or plan.growth_certificate is not DECIMAL_REVERSE_GROWTH_CERTIFICATE
            or type(plan.sectors) is not tuple
            or len(plan.sectors) != 4
        ):
            raise ValueError("reverse Frobenius plan differs from its temporal action")
    elif plan is not None:
        raise ValueError("another action family cannot carry a reverse Frobenius plan")
    blank_metadata = blank_context_metadata(record)
    if record.children is None:
        semantic_key = ("power", record.kernel, 1, record.cocycle)
        if (
            record.repetitions != 1
            or not record.homogeneous
            or not self.action_key_matches(semantic_key, action.local_id)
            or record.spatial_events_add != self.spatial_events_add(kernel.effect)
            or blank_metadata
            != (
                kernel.effect.blank_left_tail,
                kernel.effect.blank_right_tail,
                kernel.effect.stable_blank_output,
            )
        ):
            raise ValueError(
                "primitive tile action has inconsistent metadata or signature"
            )
        return record, kernel
    if type(record.children) is not tuple or len(record.children) != 2:
        raise TypeError("tile action requires an immutable binary composition")
    before, after = record.children
    if action in record.children:
        raise ValueError("tile action cannot contain itself")
    for child in (before, after):
        if type(child) is not FieldCellActionID:
            raise TypeError("tile action child has another scoped sort")
        child.validate(self.owner, "field-cell-action", size=self.next_action_identity)
        if child.local_id >= action.local_id:
            raise ValueError("tile action children must precede their parent")
        if not self.action_is_published(child.local_id):
            raise ValueError("tile action contains a stale child")
    first = self.checked_action_record(before)
    second = self.checked_action_record(after)
    homogeneous = (
        first.homogeneous
        and second.homogeneous
        and first.kernel == second.kernel
        and first.signature == second.signature
    )
    if (
        record.homogeneous != homogeneous
        or record.spatial_events_add
        != (first.spatial_events_add or second.spatial_events_add)
        or (
            homogeneous
            and (record.kernel != first.kernel or record.signature != first.signature)
        )
        or (
            not homogeneous
            and (
                record.kernel != second.kernel
                or record.signature != second.signature
                or not self.kernels_compatible(first.kernel, second.kernel)
            )
        )
        or first.repetitions + second.repetitions != record.repetitions
        or record.cocycle.physical_ticks
        != first.cocycle.physical_ticks + second.cocycle.physical_ticks
        or record.cocycle.event_weight
        != first.cocycle.event_weight + second.cocycle.event_weight
        or record.cocycle.frame_shift
        != first.cocycle.frame_shift + second.cocycle.frame_shift
        or blank_metadata != blank_context_metadata(first, second)
    ):
        raise ValueError("tile action composition witness is inconsistent")
    return record, kernel


def validate_action(
    self: PrimitiveTileKernelAdapter, action: FieldCellActionID
) -> None:
    from number_compiler.hashlife.execution.tile_kernel_contract import (
        TILE_KERNEL_CONTRACT,
    )

    record, kernel = validate_action_record(self, action)
    signature = self.quotients.interface(record.signature)
    division_radix = certified_binary_division_radix(kernel.effect)
    expected_kernel = (
        SymbolicBinaryDivisionEffect(division_radix).canonical_key()
        if division_radix is not None
        else _effect_key(kernel.effect)
    )
    if signature.kernel.behavior != (TILE_KERNEL_CONTRACT, expected_kernel):
        raise ValueError("tile action signature differs from its kernel semantics")
    expected_reverse = (
        record.homogeneous
        and type(kernel.effect) is BaseBlockEffect
        and kernel.base == 10
    )
    plan = record.reverse_frobenius
    if expected_reverse:
        assert type(plan) is ReverseFrobeniusPlan
        validate_decimal_growth_certificate(plan.growth_certificate)
        classes = 1
        uniform_bound = record.repetitions // 4
        for sector in plan.sectors:
            if type(sector) is not FrobeniusSectorSourceBound:
                raise TypeError("reverse Frobenius plan has another sector sort")
            if (
                type(sector.classes) is not int
                or type(sector.bits) is not int
                or type(sector.steps) is not int
                or type(sector.uniform_no_growth_lower_bound) is not int
                or type(sector.valuation_lower_bound) is not int
            ):
                raise TypeError("reverse Frobenius sector requires exact integers")
            if (
                sector.classes != classes
                or sector.bits != 5
                or sector.steps != record.repetitions
                or sector.uniform_no_growth_lower_bound != uniform_bound
                or sector.valuation_lower_bound
                != min(5, max(record.repetitions // classes, uniform_bound))
            ):
                raise ValueError(
                    "reverse Frobenius plan differs from its temporal action"
                )
            classes <<= 1


def validate_kernel_alphabet(
    tiles: TileArena, source: TileID, kernel: PrimitiveKernel
) -> None:
    """Validate the fixed cell interpretation after independent action admission."""
    node = tiles.resolve(source)
    alphabet = tiles.alphabet(node.alphabet)
    if (
        alphabet.symbol_count != kernel.blank + 1
        or alphabet.blank != kernel.blank
        or alphabet.radix != kernel.base
        or alphabet.cell_bits != max(1, kernel.blank.bit_length())
        or alphabet.interpretation != "unsigned-radix-cell-with-explicit-blank"
        or alphabet.version != CANONICAL_TILE_ALPHABET_VERSION
    ):
        raise ValueError("tile alphabet differs from primitive kernel")
