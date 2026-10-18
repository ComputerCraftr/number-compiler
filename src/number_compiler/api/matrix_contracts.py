"""Lazy declarations and admitted requests for temporal matrix observations."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from enum import StrEnum

from number_compiler.api.observation_types import ObservationId, OptionSpec
from number_compiler.arithmetic.contracts.input_validation import require_integer


class MatrixKind(StrEnum):
    SOURCE_TRANSFER = "source-transfer"
    INNOVATION = "innovation"


class MatrixCoordinate(StrEnum):
    PAIR_DEPTH = "pair-depth"
    DIGIT_POSITION = "digit-position"
    CENTER_SPLIT = "center-split"
    LOW_BORDER = "low-border"


class MatrixLaw(StrEnum):
    GUARDED_PAIR_RELATION = "guarded-pair-relation"
    PARITY_WEIGHTED_CARRY = "parity-weighted-carry"
    AFFINE_PREFIX_SAFETY = "affine-prefix-safety"
    ORDERED_TRIPLING_CARRY = "ordered-tripling-carry"
    INNOVATION_MOMENT = "innovation-moment"


@dataclass(frozen=True, slots=True)
class SourceTransferRequest:
    steps: int
    coordinate_kind: MatrixCoordinate
    coordinate: int | None

    def __post_init__(self) -> None:
        require_integer(self.steps, "--temporal-matrix-steps", 1)
        if type(self.coordinate_kind) is not MatrixCoordinate:
            raise TypeError("matrix coordinate requires a declared coordinate kind")
        if self.coordinate is None:
            if self.coordinate_kind not in {
                MatrixCoordinate.CENTER_SPLIT,
                MatrixCoordinate.LOW_BORDER,
            }:
                raise ValueError("this matrix requires an explicit coordinate")
        else:
            require_integer(self.coordinate, "matrix coordinate", 0)


@dataclass(frozen=True, slots=True)
class InnovationMatrixRequest:
    modulus: int | None = None

    def __post_init__(self) -> None:
        if self.modulus is not None:
            require_integer(self.modulus, "--temporal-matrix-modulus", 2)
            if self.modulus.bit_length() > 4096:
                raise ValueError("temporal matrix modulus exceeds bit budget")


MatrixRequest = SourceTransferRequest | InnovationMatrixRequest


@dataclass(frozen=True, slots=True)
class MatrixCapability:
    """Parser and lazy adapter contract; contains no arithmetic implementation."""

    module: str
    attribute: str
    coordinate: MatrixCoordinate
    max_steps: int
    max_coordinate: int
    default_coordinate: int | None = 1
    step_multiple: int = 1
    innovation: bool = False
    minimum_coordinate: int = 0
    max_source_index: int | None = None
    law: MatrixLaw = MatrixLaw.GUARDED_PAIR_RELATION

    @property
    def coordinate_option(self) -> str:
        return "temporal_matrix_" + self.coordinate.value.replace("-", "_")

    def options(self) -> tuple[tuple[str, OptionSpec], ...]:
        info = (ObservationId.TEMPORAL_MATRIX,)
        kinds = (
            tuple(kind.value for kind in MatrixKind)
            if self.innovation
            else (MatrixKind.SOURCE_TRANSFER.value,)
        )
        common: tuple[tuple[str, OptionSpec], ...] = (
            (
                "temporal_matrix_kind",
                OptionSpec(
                    MatrixKind.SOURCE_TRANSFER.value,
                    info,
                    value_kind="choice",
                    choices=kinds,
                    help="source-guarded transfer or diagnostic innovation",
                ),
            ),
            (
                "temporal_matrix_steps",
                OptionSpec(
                    None,
                    info,
                    help="positive physical recurrence ticks from the selected term",
                ),
            ),
        )
        if self.default_coordinate is not None:
            common += (
                (
                    self.coordinate_option,
                    OptionSpec(
                        self.default_coordinate,
                        info,
                        help=self.coordinate.value,
                    ),
                ),
            )
        if not self.innovation:
            return common
        return common + (("temporal_matrix_modulus", OptionSpec(None, info)),)

    def build(self, values: Mapping[str, object]) -> MatrixRequest:
        kind = values["temporal_matrix_kind"]
        if kind == MatrixKind.INNOVATION:
            if not self.innovation:
                raise ValueError("innovation matrix is unavailable for this family")
            if values.get("temporal_matrix_steps") is not None:
                raise ValueError(
                    "innovation matrix describes the selected term, not a future horizon"
                )
            specified = values.get("_specified", {})
            if isinstance(specified, Mapping) and self.coordinate_option in specified:
                raise ValueError("innovation matrix has no source-transfer coordinate")
            modulus = values.get("temporal_matrix_modulus")
            if modulus is not None:
                modulus = require_integer(modulus, "--temporal-matrix-modulus", 2)
            return InnovationMatrixRequest(modulus)
        if kind != MatrixKind.SOURCE_TRANSFER:
            raise ValueError("unsupported temporal matrix kind")
        if values.get("temporal_matrix_modulus") is not None:
            raise ValueError("--temporal-matrix-modulus requires innovation kind")
        steps = values.get("temporal_matrix_steps")
        if steps is None:
            raise ValueError("source-transfer requires --temporal-matrix-steps")
        request = SourceTransferRequest(
            require_integer(steps, "--temporal-matrix-steps", 1),
            self.coordinate,
            None
            if self.default_coordinate is None
            else require_integer(
                values[self.coordinate_option], "matrix coordinate", 0
            ),
        )
        self.validate(request)
        return request

    def validate(self, request: MatrixRequest) -> None:
        if type(request) is InnovationMatrixRequest:
            if not self.innovation:
                raise ValueError("innovation matrix is unavailable for this family")
            request.__post_init__()
            return
        if type(request) is not SourceTransferRequest:
            raise TypeError("matrix request must be an admitted matrix record")
        request.__post_init__()
        if request.coordinate_kind is not self.coordinate:
            raise ValueError("matrix coordinate belongs to a different transfer law")
        if request.steps > self.max_steps or request.steps % self.step_multiple:
            raise ValueError(
                f"matrix requires at most {self.max_steps} physical ticks "
                f"in multiples of {self.step_multiple}"
            )
        if request.coordinate is None:
            if self.default_coordinate is not None:
                raise ValueError("matrix coordinate is required")
        elif (
            self.default_coordinate is None
            or not self.minimum_coordinate <= request.coordinate <= self.max_coordinate
        ):
            raise ValueError("matrix coordinate exceeds admitted extent")
