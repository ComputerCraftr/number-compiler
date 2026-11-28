"""Read a projected width, digit or residue from an authenticated reverse/add image."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.execution.field_images import FieldImageID
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageDemand,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

from .q19_output import ReversePairOutputOccurrence
from .small_radix import SmallRadixImage
from .source_actions import ReverseActionID, ReverseSource
from .source_chamber import same_carry_digit

if TYPE_CHECKING:
    from .source_images import ReverseSourceImageAdapter


@dataclass(frozen=True, slots=True)
class ReverseImagePayload:
    """Chronological action and one authenticated completed-output form."""

    action: ReverseActionID
    occurrence: FieldImageID | None = None
    pair_output: ReversePairOutputOccurrence | None = None
    radix_output: SmallRadixImage | None = None

    def __post_init__(self) -> None:
        if (
            sum(
                x is not None
                for x in (self.occurrence, self.pair_output, self.radix_output)
            )
            > 1
        ):
            raise ValueError("reverse image cannot carry two completed outputs")


def project(
    self: ReverseSourceImageAdapter, image: SourceImageView, demand: SourceImageDemand
) -> SourceImageProjection:
    payload = self.validate_view(image)
    source = self.actions.source(cast(ReverseSource, image.binding.source))
    source_width = len(source.digits)
    steps = self.actions.node(payload.action).steps
    if payload.radix_output is not None:
        output = payload.radix_output
        if demand == SourceImageDemand("width"):
            return SourceImageProjection(output.width)
        if len(demand.parameters) != 1 or type(demand.parameters[0]) is not int:
            raise ValueError("invalid small radix output demand")
        parameter = demand.parameters[0]
        if demand.name == "digit":
            return SourceImageProjection(output.digit(parameter))
        if demand.name == "modulus":
            return SourceImageProjection(output.residue(parameter))
        raise ValueError("unsupported small radix output demand")
    if payload.pair_output is not None:
        owner = self.q19_output_owner(source)
        if demand == SourceImageDemand("width"):
            return SourceImageProjection(payload.pair_output.output_width)
        if demand.name != "digit" or len(demand.parameters) != 1:
            raise ValueError("unsupported decimal pair output demand")
        position = demand.parameters[0]
        if type(position) is not int:
            raise TypeError("decimal digit coordinate must be an integer")
        return SourceImageProjection(owner.digit(payload.pair_output, position))
    if demand == SourceImageDemand("width"):
        if steps == 0:
            return SourceImageProjection(source_width)
        if steps == 2:
            self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_TWO_STEP_WIDTH_DEMANDS)
            return SourceImageProjection(self.ports(source).second_width())
        if steps >= 3:
            recursive = self.recursive_for_steps(steps)
            if recursive is not None:
                cutover, occurrence = recursive
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_RECURSIVE_WIDTH_DEMANDS
                )
                return SourceImageProjection(cutover.width(occurrence))
            self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_SAME_CARRY_WIDTH_DEMANDS)
            return SourceImageProjection(source_width)
        return SourceImageProjection(self.primitive_width(source))
    if demand.name != "digit" or len(demand.parameters) != 1:
        raise ValueError("unsupported reverse/add source image demand")
    position = demand.parameters[0]
    if type(position) is not int:
        raise TypeError("reverse/add digit coordinate must be an integer")
    if position < 0:
        raise IndexError(position)
    if steps >= 3:
        recursive = self.recursive_for_steps(steps)
        if recursive is not None:
            cutover, occurrence = recursive
            self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_RECURSIVE_DIGIT_DEMANDS)
            return SourceImageProjection(cutover.digit(occurrence, position))
        if position >= source_width:
            raise IndexError(position)
        self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_SAME_CARRY_DIGIT_DEMANDS)
        return SourceImageProjection(
            same_carry_digit(self.ports(source), steps, position)
        )
    if steps == 2:
        self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_TWO_STEP_DIGIT_DEMANDS)
        return SourceImageProjection(self.second_digit(source, position))
    if steps == 0:
        if position >= source_width:
            raise IndexError(position)
        self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_DIGIT_READS)
        return SourceImageProjection(source.digits[position])
    if position > source_width:
        raise IndexError(position)
    ports = self.ports(source)
    if position == source_width:
        if not ports.terminal:
            raise IndexError(position)
        digit = 1
    else:
        _, digit = self.normalize_pair(
            ports.pair(position), ports.carry(position), source.base
        )
        self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_CARRY_COORDINATES)
    return SourceImageProjection(digit)
