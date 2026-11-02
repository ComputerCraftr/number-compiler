"""Source-issued weighted carry actions for centered Antihydra arithmetic.

The physical recurrence is ``H' = floor(3 H / 2)``.  With ``D = H - 1``
the same step is ``D' = (3 D + (D mod 2)) / 2`` and an admitted extent
``n`` therefore has the exact source action

``2**n D_n = 3**n D_0 + J_n``.

This module owns that weighted carry.  It does not issue scheduler successor
authority: every public result remains bound to an already authenticated
Antihydra source image and revalidates that binding before use.  The bounded
eight-tick atoms and their balanced postorder composition are owned by the
shared dyadic scheduler; all additional temporary storage is reserved by the
caller's :class:`RunArithmeticWorkspace`.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING, Final

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnActionID,
    DyadicReturnImageID,
    DyadicReturnSourceID,
)
from number_compiler.hashlife.execution.dyadic_return_transport import (
    balanced_residue_effect,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageBinding,
    SourceImageID,
    SourceImageView,
)
from number_compiler.resources.metric_keys import antihydra as _keys
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MAX_MAHLER_SOURCE_EXTENT,
)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.arithmetic_images import (
        AntihydraArithmeticImageWorkspace,
    )
    from number_compiler.sequences.antihydra.mahler_x15_source_morphism import (
        X15CarryMorphism,
    )


MAX_WEIGHTED_CARRY_EXTENT: Final[int] = MAX_MAHLER_SOURCE_EXTENT
_WEIGHTED_CARRY_ISSUANCE_SEAL: Final[object] = object()

_METRICS: Final[tuple[str, ...]] = (
    _keys.ANTIHYDRA_WEIGHTED_CARRY_REQUESTS,
    _keys.ANTIHYDRA_WEIGHTED_CARRY_BLOCK_REQUESTS,
    _keys.ANTIHYDRA_WEIGHTED_CARRY_BLOCK_HITS,
    _keys.ANTIHYDRA_WEIGHTED_CARRY_BLOCK_MISSES,
    _keys.ANTIHYDRA_WEIGHTED_CARRY_LEAF_STEPS,
    _keys.ANTIHYDRA_WEIGHTED_CARRY_COMPOSITIONS,
    _keys.ANTIHYDRA_WEIGHTED_CARRY_OPERAND_BITS,
    _keys.ANTIHYDRA_WEIGHTED_CARRY_TROPICAL_COMPOSITIONS,
    _keys.ANTIHYDRA_WEIGHTED_CARRY_PROJECTION_REQUESTS,
    _keys.ANTIHYDRA_WEIGHTED_CARRY_PROJECTION_OPERAND_BITS,
)


@dataclass(frozen=True, slots=True)
class _CarryIssuanceCertificate:
    issuer: object
    payload: tuple[object, ...]


@dataclass(frozen=True, slots=True, init=False)
class IssuedWeightedCarry:
    """An exact weighted carry still owned by its source-image occurrence."""

    width: int
    residue: int
    innovation: int
    delta: int
    minimum: int
    odd_h_steps: int
    gain: int
    denominator: int
    skew: SkewTransfer[int]
    cap_hat: int | None
    forced_mod4: bool | None
    first_centered_bit: int | None
    last_centered_bit: int | None
    _workspace: AntihydraArithmeticImageWorkspace
    _source_image: SourceImageID
    _source: DyadicReturnSourceID
    _action: DyadicReturnActionID
    _binding: SourceImageBinding
    _centered_source: int
    _projection_payload: DyadicReturnImageID | None
    _issuer: object
    _certificate: _CarryIssuanceCertificate
    _snapshot: tuple[object, ...]

    @property
    def centered_source(self) -> int:
        self.require_issued()
        return self._centered_source

    @property
    def physical_transfer(self) -> SkewTransfer[int]:
        """The exact H transfer consumed by the production image publisher."""
        self.require_issued()
        return SkewTransfer(
            self.gain,
            self.innovation + self.denominator - self.gain,
            self.denominator,
        )

    def charge_projection_metric(self, name: str, amount: int = 1) -> None:
        """Charge a demanded child projection to this source owner."""
        self.charge_projection_metrics(((name, amount),))

    def charge_projection_metrics(self, entries: tuple[tuple[str, int], ...]) -> None:
        """Validate once, then charge a bounded projection work batch."""
        self.require_issued()
        if type(entries) is not tuple:
            raise TypeError("projection metrics must be an immutable batch")
        for name, amount in entries:
            if (
                type(name) is not str
                or not name
                or type(amount) is not int
                or amount < 0
            ):
                raise ValueError("projection metric batch has an invalid entry")
            self._workspace.ledger.bump(name, amount)

    def has_same_resource_owner(self, other: IssuedWeightedCarry) -> bool:
        self.require_issued()
        if type(other) is not IssuedWeightedCarry:
            return False
        other.require_issued()
        return self._workspace.ledger is other._workspace.ledger

    def require_issued(self) -> None:
        """Reject stale, foreign, or mutated carry/source publications."""
        from number_compiler.sequences.antihydra.arithmetic_images import (
            ANTIHYDRA_ARITHMETIC_LAW,
            AntihydraArithmeticImageWorkspace,
        )

        workspace = self._workspace
        certificate = getattr(self, "_certificate", None)
        if (
            getattr(self, "_issuer", None) is not _WEIGHTED_CARRY_ISSUANCE_SEAL
            or type(certificate) is not _CarryIssuanceCertificate
            or certificate.issuer is not _WEIGHTED_CARRY_ISSUANCE_SEAL
            or certificate.payload != self.publication_payload()
        ):
            raise ValueError("weighted carry was not issued by its source owner")
        if type(workspace) is not AntihydraArithmeticImageWorkspace:
            raise TypeError("weighted carry has another workspace type")
        workspace.validate_law()
        if workspace.law != ANTIHYDRA_ARITHMETIC_LAW:
            raise ValueError("weighted carry has another arithmetic law")
        workspace.validate_source(self._source)
        workspace.validate_action(self._action)
        view = workspace.scheduler.source_image_view(workspace, self._source_image)
        admitted = workspace.source_node(self._source)
        expected_binding_action = (
            self._action if self._projection_payload is not None else workspace.identity
        )
        source_h = self._centered_source + 1
        if (
            view.binding != self._binding
            or view.binding.source != self._source
            or view.binding.action != expected_binding_action
            or view.failure_prefix is not None
            or not admitted.exact
            or admitted.precision != self.width
            or workspace.action_node(self._action).width != self.width
            or admitted.residue != _low_bits(source_h, admitted.precision)
            or admitted.lift != source_h >> admitted.precision
            or self._centered_source < 0
            or self.residue != _low_bits(self._centered_source, self.width)
        ):
            raise ValueError("weighted carry lost its exact source/action binding")
        projection = self._projection_payload
        if projection is not None:
            workspace.validate_payload(projection)
            image = workspace.image_node(projection)
            if (
                view.payload != projection
                or image.source != self._source
                or image.action != self._action
                or image.summary.width != self.width
                or image.summary.transfer.upper != self.gain
                or image.summary.transfer.lower != self.denominator
                or image.summary.transfer.offset
                != self.innovation + self.denominator - self.gain
                or image.summary.delta != self.delta
                or image.summary.minimum != self.minimum
                or image.summary.odd_steps != self.odd_h_steps
            ):
                raise ValueError("weighted carry projection lost its root image")
            if (
                self.cap_hat is not None
                or self.forced_mod4 is not None
                or self.first_centered_bit is not None
                or self.last_centered_bit is not None
            ):
                raise ValueError("weighted carry projection forged unknown metadata")
        elif (
            self.cap_hat is not None
            or self.forced_mod4 is not None
            or self.first_centered_bit is not None
            or self.last_centered_bit is not None
        ):
            raise ValueError("weighted carry producer forged unissued metadata")
        if self.publication_payload() != self._snapshot:
            raise ValueError("weighted carry publication was altered")

    def endpoint(self, centered_source: int) -> int:
        """Apply this carry only to a source in its admitted dyadic inlet."""
        self.require_issued()
        if type(centered_source) is not int or centered_source < 0:
            raise ValueError("centered source must be nonnegative")
        if _low_bits(centered_source, self.width) != self.residue:
            raise ValueError("weighted carry has another dyadic source guard")
        numerator = self.gain * centered_source + self.innovation
        if numerator & (self.denominator - 1):
            raise ArithmeticError("weighted carry lost exact integrality")
        return numerator >> self.width

    def x15_morphism(self, *, reserve_bits: Callable[[int], None]) -> X15CarryMorphism:
        """Demand the multiplicative source morphism without another replay."""
        self.require_issued()
        from number_compiler.sequences.antihydra.mahler_x15_source_morphism import (
            X15CarryMorphism,
        )

        return X15CarryMorphism.from_carry(self, reserve_bits=reserve_bits)

    def publication_payload(self) -> tuple[object, ...]:
        """Return the immutable semantic value authenticated at publication."""
        return (
            self.width,
            self.residue,
            self.innovation,
            self.delta,
            self.minimum,
            self.odd_h_steps,
            self.gain,
            self.denominator,
            self.skew,
            self.cap_hat,
            self.forced_mod4,
            self.first_centered_bit,
            self.last_centered_bit,
            self._source_image,
            self._source,
            self._action,
            self._binding,
            self._centered_source,
            self._projection_payload,
            self._issuer,
        )


@dataclass(frozen=True, slots=True)
class _CarryEffect:
    skew: SkewTransfer[int]
    delta: int
    minimum: int
    odd_h_steps: int
    cap_hat: int | None
    forced_mod4: bool | None
    first_centered_bit: int | None
    last_centered_bit: int | None


def issued_weighted_carry(
    workspace: AntihydraArithmeticImageWorkspace,
    source: SourceImageView,
    action: DyadicReturnActionID,
    *,
    reserve_bits: Callable[[int], None],
) -> IssuedWeightedCarry:
    """Construct the cold exact carry before the root image is published."""
    from number_compiler.sequences.antihydra.arithmetic_images import (
        ANTIHYDRA_ARITHMETIC_LAW,
        AntihydraArithmeticImageWorkspace,
    )

    if type(workspace) is not AntihydraArithmeticImageWorkspace:
        raise TypeError("weighted carry requires an Antihydra workspace")
    if type(source) is not SourceImageView:
        raise TypeError("weighted carry requires an authenticated source view")
    if type(action) is not DyadicReturnActionID:
        raise TypeError("weighted carry requires a dyadic action")
    if not callable(reserve_bits):
        raise TypeError("weighted carry requires a scratch reservation hook")
    _declare_metrics(workspace)
    workspace.ledger.bump(_keys.ANTIHYDRA_WEIGHTED_CARRY_REQUESTS)
    workspace.validate_action(action)
    workspace.validate_payload(source.payload)
    if workspace.scheduler.source_image_view(workspace, source.identity) != source:
        raise ValueError("weighted carry source view was not issued by this scheduler")
    if workspace.law != ANTIHYDRA_ARITHMETIC_LAW:
        raise ValueError("weighted carry has another arithmetic law")
    source_id = source.binding.source
    if type(source_id) is not DyadicReturnSourceID:
        raise TypeError("weighted carry source has another sort")
    admitted = workspace.source_node(source_id)
    width = workspace.action_node(action).width
    if (
        source.binding.action != workspace.identity
        or source.failure_prefix is not None
        or not admitted.exact
        or admitted.precision != width
        or width <= 0
    ):
        raise ValueError("weighted carry requires an exact identity source")
    if width > MAX_WEIGHTED_CARRY_EXTENT:
        raise BlockContextBudgetExceeded("weighted carry extent exceeds hard limit")
    # Reserve for any explicit non-root source lift, balanced worklist fields,
    # and result before materializing wide arithmetic.
    source_bound = max(1, admitted.residue.bit_length(), admitted.lift.bit_length())
    reserve_bits(16_384 + 16 * (width + source_bound + 64))
    source_h = _issued_physical_source(workspace, source_id, action, admitted)
    if source_h <= 0:
        raise ValueError("weighted carry requires a positive physical source")
    centered_source = source_h - 1
    effect = _power(
        workspace,
        centered_source,
        width,
        reserve_bits=reserve_bits,
    )
    return _issue(
        workspace,
        source,
        source_id,
        action,
        centered_source,
        effect,
        projection_payload=None,
    )


def project_weighted_carry(
    workspace: AntihydraArithmeticImageWorkspace,
    *,
    reserve_bits: Callable[[int], None],
) -> IssuedWeightedCarry:
    """Project ``J`` from the authenticated root transfer without parity replay."""
    from number_compiler.sequences.antihydra.arithmetic_images import (
        AntihydraArithmeticImageWorkspace,
    )

    if type(workspace) is not AntihydraArithmeticImageWorkspace:
        raise TypeError("weighted carry projection requires Antihydra")
    if not callable(reserve_bits):
        raise TypeError("weighted carry projection requires scratch reservation")
    _declare_metrics(workspace)
    workspace.ledger.bump(_keys.ANTIHYDRA_WEIGHTED_CARRY_PROJECTION_REQUESTS)
    workspace.validate()
    source = workspace.source_node(workspace.root_source)
    summary = workspace.summary()
    width = summary.width
    if width > MAX_WEIGHTED_CARRY_EXTENT:
        raise BlockContextBudgetExceeded("weighted carry extent exceeds hard limit")
    bits = 8 * (
        width
        + max(1, source.residue.bit_length(), source.lift.bit_length())
        + max(1, abs(summary.transfer.offset).bit_length())
        + 64
    )
    reserve_bits(bits)
    workspace.ledger.bump(_keys.ANTIHYDRA_WEIGHTED_CARRY_PROJECTION_OPERAND_BITS, bits)
    centered_source = workspace.seed - 1
    gain = summary.transfer.upper
    denominator = summary.transfer.lower
    innovation = summary.transfer.offset + gain - denominator
    skew = SkewTransfer(gain, innovation, denominator)
    centered_bit_sum = width - summary.odd_steps
    if summary.delta != 3 * centered_bit_sum - width:
        raise ValueError("root ledger is inconsistent with its weighted carry")
    effect = _CarryEffect(
        skew,
        summary.delta,
        summary.minimum,
        summary.odd_steps,
        None,
        None,
        None,
        None,
    )
    view = workspace.scheduler.source_image_view(workspace, workspace.root_image)
    carry = _issue(
        workspace,
        view,
        workspace.root_source,
        workspace.root_action,
        centered_source,
        effect,
        projection_payload=workspace.root_payload,
    )
    if carry.endpoint(centered_source) != workspace.endpoint() - 1:
        raise ArithmeticError("root weighted carry disagrees with physical endpoint")
    return carry


def _issue(
    workspace: AntihydraArithmeticImageWorkspace,
    source: SourceImageView,
    source_id: DyadicReturnSourceID,
    action: DyadicReturnActionID,
    centered_source: int,
    effect: _CarryEffect,
    *,
    projection_payload: DyadicReturnImageID | None,
) -> IssuedWeightedCarry:
    value = object.__new__(IssuedWeightedCarry)
    fields: tuple[tuple[str, object], ...] = (
        ("width", workspace.action_node(action).width),
        ("residue", _low_bits(centered_source, workspace.action_node(action).width)),
        ("innovation", effect.skew.offset),
        ("delta", effect.delta),
        ("minimum", effect.minimum),
        ("odd_h_steps", effect.odd_h_steps),
        ("gain", effect.skew.upper),
        ("denominator", effect.skew.lower),
        ("skew", effect.skew),
        ("cap_hat", effect.cap_hat),
        ("forced_mod4", effect.forced_mod4),
        ("first_centered_bit", effect.first_centered_bit),
        ("last_centered_bit", effect.last_centered_bit),
        ("_workspace", workspace),
        ("_source_image", source.identity),
        ("_source", source_id),
        ("_action", action),
        ("_binding", source.binding),
        ("_centered_source", centered_source),
        ("_projection_payload", projection_payload),
        ("_issuer", _WEIGHTED_CARRY_ISSUANCE_SEAL),
    )
    for name, item in fields:
        object.__setattr__(value, name, item)
    snapshot = value.publication_payload()
    object.__setattr__(
        value,
        "_certificate",
        _CarryIssuanceCertificate(_WEIGHTED_CARRY_ISSUANCE_SEAL, snapshot),
    )
    object.__setattr__(value, "_snapshot", snapshot)
    value.require_issued()
    return value


def _power(
    workspace: AntihydraArithmeticImageWorkspace,
    centered_source: int,
    width: int,
    *,
    reserve_bits: Callable[[int], None],
) -> _CarryEffect:
    source_h = centered_source + 1
    source_residue = _low_bits(source_h, width)
    reserve_bits(
        16_384 + 16 * (width + source_h.bit_length() + source_residue.bit_length() + 64)
    )
    counters = workspace.ledger.counters
    prefix = workspace.counter_prefix

    def count(suffix: str) -> int:
        return counters.get(f"{prefix}_{suffix}", 0)

    before_lookups = count("finite_block_lookups")
    before_hits = count("finite_block_hits")
    before_misses = count("finite_block_misses")
    before_steps = count("transient_leaf_steps")
    before_finite_compositions = count("finite_block_compositions")
    before_balanced_compositions = count("balanced_effect_compositions")
    try:
        physical = balanced_residue_effect(
            workspace,
            width,
            source_residue,
            retain_cache=False,
        )
    finally:
        workspace.ledger.bump(
            _keys.ANTIHYDRA_WEIGHTED_CARRY_BLOCK_REQUESTS,
            count("finite_block_lookups") - before_lookups,
        )
        workspace.ledger.bump(
            _keys.ANTIHYDRA_WEIGHTED_CARRY_BLOCK_HITS,
            count("finite_block_hits") - before_hits,
        )
        workspace.ledger.bump(
            _keys.ANTIHYDRA_WEIGHTED_CARRY_BLOCK_MISSES,
            count("finite_block_misses") - before_misses,
        )
        workspace.ledger.bump(
            _keys.ANTIHYDRA_WEIGHTED_CARRY_LEAF_STEPS,
            count("transient_leaf_steps") - before_steps,
        )
        workspace.ledger.bump(
            _keys.ANTIHYDRA_WEIGHTED_CARRY_COMPOSITIONS,
            count("finite_block_compositions")
            - before_finite_compositions
            + count("balanced_effect_compositions")
            - before_balanced_compositions,
        )
    transfer = physical.transfer
    centered = SkewTransfer(
        transfer.upper,
        transfer.offset + transfer.upper - transfer.lower,
        transfer.lower,
    )
    workspace.ledger.bump(
        _keys.ANTIHYDRA_WEIGHTED_CARRY_OPERAND_BITS,
        sum(
            max(1, abs(value).bit_length())
            for value in (
                source_h,
                source_residue,
                transfer.upper,
                transfer.offset,
                transfer.lower,
                centered.offset,
                physical.delta,
                physical.minimum,
                physical.odd_steps,
            )
        )
        + width.bit_length(),
    )
    return _CarryEffect(
        centered,
        physical.delta,
        physical.minimum,
        physical.odd_steps,
        None,
        None,
        None,
        None,
    )


def _declare_metrics(workspace: AntihydraArithmeticImageWorkspace) -> None:
    for name in _METRICS:
        workspace.ledger.bump(name, 0)


def _low_bits(value: int, width: int) -> int:
    if width == 0 or value == 0:
        return 0
    if value.bit_length() <= width:
        return value
    return value & ((1 << width) - 1)


def _issued_physical_source(
    workspace: AntihydraArithmeticImageWorkspace,
    source_id: DyadicReturnSourceID,
    action: DyadicReturnActionID,
    admitted: object,
) -> int:
    """Read the authenticated root seed without rebuilding an intermediate."""
    from number_compiler.hashlife.execution.dyadic_return_records import (
        DyadicReturnSourceRecord,
    )

    if type(admitted) is not DyadicReturnSourceRecord:
        raise TypeError("weighted carry source has another record type")
    if source_id == workspace.root_source and action == workspace.root_action:
        source_h = workspace.seed
        if (
            admitted.residue != _low_bits(source_h, admitted.precision)
            or admitted.lift != source_h >> admitted.precision
        ):
            raise ValueError("weighted carry root disagrees with its issued seed")
        return source_h
    # Explicit non-root research sources have no independent endpoint owner;
    # their exact, authenticated source record is the authority.
    if admitted.lift == 0:
        return admitted.residue
    return admitted.residue + (admitted.lift << admitted.precision)


__all__ = [
    "IssuedWeightedCarry",
    "MAX_WEIGHTED_CARRY_EXTENT",
    "issued_weighted_carry",
    "project_weighted_carry",
]
