"""Future-aware Moore quotient of the exact ``2rev10`` two-step stencil."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Literal

StencilOutput = Literal["digit", "ltgt", "f5", "joint"]


def _stencil_kernel(left_high: int, digit: int, right_f5: int) -> int:
    """Trusted arithmetic core for validated decimal ports."""
    return (
        4 * digit + 2 * left_high + int(right_f5 >= 3 or (right_f5 == 2 and digit >= 5))
    ) % 10


def stencil_from_ports(left_high: int, digit: int, right_f5: int) -> int:
    """Apply F from the left threshold, center digit, and right F5 port."""
    if (
        type(left_high) is not int
        or left_high not in (0, 1)
        or type(digit) is not int
        or not 0 <= digit <= 9
        or type(right_f5) is not int
        or not 0 <= right_f5 < 5
    ):
        raise ValueError("invalid 2rev10 Moore stencil port")
    return _stencil_kernel(left_high, digit, right_f5)


def stencil_cell(left: int, digit: int, right: int) -> int:
    """Exact local action without assuming a border cycle."""
    if any(
        type(value) is not int or not 0 <= value <= 9 for value in (left, digit, right)
    ):
        raise ValueError("stencil requires three decimal digits")
    return _stencil_kernel(int(left >= 5), digit, right % 5)


def _label(digit: int, observer: StencilOutput) -> tuple[int, ...]:
    if observer == "digit":
        return (digit,)
    if observer == "ltgt":
        return (int(digit >= 5),)
    if observer == "f5":
        return (digit % 5,)
    if observer == "joint":
        return (int(digit >= 5), digit % 5)
    raise ValueError("unsupported Moore stencil output contract")


def _canonical_classes(rows: list[object]) -> tuple[int, ...]:
    identifiers: dict[object, int] = {}
    return tuple(identifiers.setdefault(row, len(identifiers)) for row in rows)


@dataclass(frozen=True, slots=True)
class DigitStencilMoore:
    """Coarsest all-context future congruence for one requested output."""

    observer: StencilOutput
    initial_classes: int
    classes: tuple[int, ...]
    refinement_rounds: int

    @property
    def state_count(self) -> int:
        return len(set(self.classes))

    def project(self, digit: int) -> tuple[int, ...]:
        if type(digit) is not int or not 0 <= digit <= 9:
            raise ValueError("invalid decimal digit")
        return _label(digit, self.observer)

    def transition(self, digit: int, left_high: int, right_f5: int) -> int:
        return self.classes[stencil_from_ports(left_high, digit, right_f5)]

    def separating_port(self, a: int, b: int) -> tuple[int, int] | None:
        if self.project(a) != self.project(b):
            return None
        for left_high in (0, 1):
            for right_f5 in range(5):
                left_output = self.project(stencil_from_ports(left_high, a, right_f5))
                right_output = self.project(stencil_from_ports(left_high, b, right_f5))
                if left_output != right_output:
                    return left_high, right_f5
        return None


def minimize_digit_stencil(observer: StencilOutput) -> DigitStencilMoore:
    """Refine present outputs against all ten conditional neighbor ports."""
    if observer not in ("digit", "ltgt", "f5", "joint"):
        raise ValueError("unsupported Moore stencil output contract")
    classes = _canonical_classes([_label(digit, observer) for digit in range(10)])
    initial_count = len(set(classes))
    rounds = 0
    while True:
        refined = _canonical_classes(
            [
                (
                    classes[digit],
                    tuple(
                        classes[stencil_from_ports(left, digit, right)]
                        for left in (0, 1)
                        for right in range(5)
                    ),
                )
                for digit in range(10)
            ]
        )
        if refined == classes:
            return DigitStencilMoore(observer, initial_count, classes, rounds)
        if any(
            classes[left] != classes[right] and refined[left] == refined[right]
            for left in range(10)
            for right in range(10)
        ):
            raise AssertionError("Moore partition coarsened during refinement")
        classes = refined
        rounds += 1
        if rounds >= 10:
            raise AssertionError("finite digit Moore partition did not stabilize")


_IDENTITY_CLASSES = tuple(range(10))
DIGIT_STENCIL_MOORE: Mapping[StencilOutput, DigitStencilMoore] = MappingProxyType(
    {
        "digit": DigitStencilMoore("digit", 10, _IDENTITY_CLASSES, 0),
        "ltgt": DigitStencilMoore("ltgt", 2, _IDENTITY_CLASSES, 1),
        "f5": DigitStencilMoore("f5", 5, _IDENTITY_CLASSES, 1),
        "joint": DigitStencilMoore("joint", 10, _IDENTITY_CLASSES, 0),
    }
)
