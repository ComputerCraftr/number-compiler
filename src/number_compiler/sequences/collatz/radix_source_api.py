"""Radix observations and applications for one admitted Collatz source."""

from __future__ import annotations

from collections.abc import Callable, MutableMapping
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.projection.microblock_cache import (
    ExactMicroblock,
    MicroblockCache,
    MicroblockKey,
)
from number_compiler.resources.ledger import ResourceLedger, ResourceScope
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.projection.lazy_radix import RadixProjection
    from number_compiler.sequences.collatz.physical_images import (
        CollatzPhysicalImageWorkspace,
    )


class ExteriorRadixCoordinate(IndexError):
    """Exact affine threshold says a scalar coordinate is outside the value."""


def admitted_radix_digit(
    radix: int,
    position: int,
    seed: int,
    ledger: ResourceLedger,
    source_image: Callable[[], CollatzPhysicalImageWorkspace],
) -> int:
    """Extract an active digit without constructing the affine numerator."""
    if radix == 2:
        from number_compiler.hashlife.execution.dyadic_return_observers import (
            binary_cell,
        )

        symbol = binary_cell(source_image(), position)
        if symbol == 2:
            raise ExteriorRadixCoordinate(position)
        return symbol
    transfer = source_image().saturated_summary().transfer
    numerator_bits = (
        max(
            transfer.upper.bit_length() + seed.bit_length(),
            abs(transfer.offset).bit_length(),
        )
        + 1
    )
    scaled_place_bits = (
        transfer.lower.bit_length() - 1 + position * (radix.bit_length() - 1)
    )
    if scaled_place_bits >= numerator_bits:
        ledger.bump(_collatz_keys.COLLATZ_RADIX_EXTERIOR_SHORTCUTS)
        if position == 0:
            return 0
        raise ExteriorRadixCoordinate(position)
    place = int(radix**position)
    threshold = transfer.lower * place
    # For N=u*seed+o, N<T iff o<T and
    # (u=0 or seed <= floor((T-o-1)/u)).
    exterior = transfer.offset < threshold and (
        transfer.upper == 0
        or seed <= (threshold - transfer.offset - 1) // transfer.upper
    )
    if exterior:
        ledger.bump(_collatz_keys.COLLATZ_RADIX_EXTERIOR_SHORTCUTS)
        if position == 0:
            return 0
        raise ExteriorRadixCoordinate(position)
    modulus = threshold * radix
    residue = (
        (transfer.upper % modulus) * (seed % modulus) + transfer.offset % modulus
    ) % modulus
    ledger.bump(
        _collatz_keys.COLLATZ_IMAGE_PROJECTION_OPERAND_BITS, modulus.bit_length()
    )
    return residue // threshold


def observe_radix_symbol(
    radix: int,
    position: int,
    steps: int,
    seed_digits: tuple[int, ...],
    ledger: ResourceLedger,
    microblocks: MicroblockCache,
    maximum_width: Callable[[], int],
    source_image: Callable[[], CollatzPhysicalImageWorkspace],
    source_image_program: Callable[[], ActionProgramID],
    admitted_digit: Callable[[int, int], int],
) -> int:
    """Observe one source-bound radix limb through the shared microblock cache."""
    radix = require_integer(radix, "binary limb radix", 2, 1 << 63)
    if radix & (radix - 1):
        raise ValueError("binary limb radix must be a power of two")
    position = require_integer(position, "digit coordinate")
    limb_bits = radix.bit_length() - 1
    start = position * limb_bits
    if position < 0 or start >= maximum_width():
        raise IndexError(position)
    if steps == 0:
        if start >= len(seed_digits):
            return radix
        value = 0
        for offset in range(min(limb_bits, len(seed_digits) - start)):
            value = ledger.observe_arithmetic(
                value | (seed_digits[start + offset] << offset)
            )
            ledger.bump(_collatz_keys.COLLATZ_ORIGINAL_LIMB_SOURCE_READS)
        return value

    ledger.bump(_collatz_keys.DIRECT_POWERED_POINT_QUERIES)
    workspace = source_image()
    key = MicroblockKey(
        source_image_program(),
        radix,
        0,
        position,
        "output",
        source_scope=workspace.owner,
    )
    cached = microblocks.get(key)
    if cached is not None:
        # Source/action/image authority was checked before the cache lookup.
        if not 0 <= cached.encoded <= radix:
            raise ValueError("cached Collatz point belongs to another alphabet")
        return cached.encoded
    try:
        symbol = admitted_digit(radix, position)
    except ExteriorRadixCoordinate:
        symbol = radix
    else:
        ledger.bump(_shared_keys.COLLATZ_IMAGE_RADIX_DEMANDS)
        if not 0 <= symbol < radix:
            raise AssertionError("source image produced an invalid limb")
    microblocks.put(key, ExactMicroblock(symbol, limb_bits + 1))
    return symbol


def source_radix_application(
    radix: int,
    width: int,
    ledger: ResourceLedger,
    projections: MutableMapping[int, RadixProjection],
    microblocks: MicroblockCache,
) -> RadixProjection:
    """Get or create an accounted radix application for the admitted source."""
    from number_compiler.projection.lazy_radix import RadixProjection

    radix = require_integer(radix, "radix", 2, 1 << 63)
    width = require_integer(width, "radix width", 1)
    projection: object | None = projections.get(radix)
    if projection is not None:
        if (
            type(projection) is not RadixProjection
            or projection.radix != radix
            or projection.width != width
            or projection.ledger is not ledger
        ):
            raise ValueError("radix application belongs to another source")
        return projection
    owner = ledger.register(
        "radix-applications", "application_index", ResourceScope.INDEX_OWNED
    )
    ledger.reserve(owner, entries=1)
    from number_compiler.resources.construction_scope import RuntimeConstruction

    try:
        with RuntimeConstruction(ledger):
            projection = RadixProjection(
                radix,
                width,
                ledger,
                microblocks,
                width_is_upper_bound=True,
            )
            projections[radix] = projection
    except BaseException:
        ledger.release(owner, entries=1)
        raise
    return projection
