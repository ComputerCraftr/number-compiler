"""Bounded references for projections of a reverse/add cylinder effect.

Uniform and edge/core words describe emitted pair fields, not the state of a
successor-closed cylinder grammar. These formulas are deliberately outside the
installed package. Neither their shape labels nor their source-realizability
predicate confer source authority or authorize temporal composition.

``instantiate`` renders a diagnostic word; it is forbidden in production
construction. The full cylinder arrow must own innovation, charts, source
predicates and output before these projections can be requested.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import CarryFn


class UniformPumpUnavailable(ValueError):
    """The next grammar family has no constructor-owned production yet."""


@dataclass(frozen=True, slots=True)
class AffineCount:
    """A run count ``coefficient*m + offset``."""

    coefficient: int
    offset: int = 0

    def __post_init__(self) -> None:
        if type(self.coefficient) is not int or type(self.offset) is not int:
            raise TypeError("grammar run counts require exact affine coefficients")

    def evaluate(self, width: int) -> int:
        if type(width) is not int:
            raise TypeError("grammar width requires an exact integer")
        return self.coefficient * width + self.offset


@dataclass(frozen=True, slots=True)
class ProjectionRun:
    symbol: int
    count: AffineCount

    def __post_init__(self) -> None:
        if type(self.symbol) is not int or not 0 <= self.symbol <= 18:
            raise ValueError("pair grammar symbol lies outside the decimal alphabet")
        if type(self.count) is not AffineCount:
            raise TypeError("pair grammar run requires an affine count")


@dataclass(frozen=True, slots=True)
class ProjectionClause:
    """One exact pair-field production over symbolic width parameter ``m``.

    ``terminal_carry`` is the spatial carry transform of the source pair
    field.  It is not a temporally composed carry certificate.
    """

    source_shape: str
    target_shape: str
    minimum_width: int
    maximum_width: int | None
    events: int
    growth: int
    terminal_carry: CarryFn
    extent: AffineCount
    runs: tuple[ProjectionRun, ...]

    def __post_init__(self) -> None:
        if self.source_shape not in ("uniform", "edge-core"):
            raise ValueError("unknown pumped source grammar class")
        if self.target_shape not in ("uniform", "edge-core", "boundary-core"):
            raise ValueError("unknown pumped target grammar class")
        if (
            type(self.minimum_width) is not int
            or self.minimum_width < 1
            or self.maximum_width is not None
            and (
                type(self.maximum_width) is not int
                or self.maximum_width < self.minimum_width
            )
            or type(self.events) is not int
            or self.events < 1
            or type(self.growth) is not int
            or not 0 <= self.growth <= self.events
            or type(self.terminal_carry) is not CarryFn
            or type(self.extent) is not AffineCount
            or type(self.runs) is not tuple
            or not self.runs
        ):
            raise ValueError("invalid pumped grammar clause")

    def admits(self, width: int) -> bool:
        return (
            type(width) is int
            and width >= self.minimum_width
            and (self.maximum_width is None or width <= self.maximum_width)
        )

    def instantiate(self, width: int) -> tuple[int, ...]:
        """Bounded diagnostic rendering; temporal construction never calls it."""
        if not self.admits(width):
            raise ValueError("symbolic width lies outside the production guard")
        values: list[int] = []
        for run in self.runs:
            count = run.count.evaluate(width)
            if count < 0:
                raise ValueError("pumped production has a negative run count")
            values.extend((run.symbol,) * count)
        if len(values) != self.extent.evaluate(width):
            raise ValueError("pumped production extent disagrees with its runs")
        return tuple(values)


def _run(symbol: int, coefficient: int, offset: int = 0) -> ProjectionRun:
    return ProjectionRun(symbol, AffineCount(coefficient, offset))


def uniform_source_admitted(symbol: int, width: int) -> bool:
    """Whether ``U_s(width)`` is the pair field of a canonical natural word.

    A pair field has an even center at odd width.  Zero has only the canonical
    one-digit representation; leading-zero padded occurrences are excluded.
    This predicate is deliberately separate from the algebraic production,
    which remains valid for every positive symbolic width.
    """
    if (
        type(symbol) is not int
        or not 0 <= symbol <= 18
        or type(width) is not int
        or width < 1
    ):
        return False
    if symbol == 0:
        return width == 1
    return width % 2 == 0 or symbol % 2 == 0


def uniform_successor(symbol: int) -> ProjectionClause:
    """Return the exact primitive production for ``U_s(m) = s**m``."""
    if type(symbol) is not int or not 0 <= symbol <= 18:
        raise ValueError("uniform pair symbol lies outside the decimal alphabet")
    if symbol <= 9:
        return ProjectionClause(
            "uniform",
            "uniform",
            1,
            None,
            1,
            0,
            CarryFn.CONST0 if symbol < 9 else CarryFn.ID,
            AffineCount(1),
            (_run(2 * symbol, 1),),
        )
    edge, core = symbol - 9, 2 * symbol - 18
    return ProjectionClause(
        "uniform",
        "edge-core",
        1,
        None,
        1,
        1,
        CarryFn.CONST1,
        AffineCount(1, 1),
        (_run(edge, 0, 1), _run(core, 1, -1), _run(edge, 0, 1)),
    )


def uniform_no_growth_power(symbol: int, events: int) -> ProjectionClause:
    """Power a uniform production while every source class stays no-growth."""
    if type(symbol) is not int or not 0 <= symbol <= 9:
        raise ValueError("uniform no-growth pumping requires a symbol through nine")
    if type(events) is not int or events < 1:
        raise ValueError("uniform pumping requires a positive event count")
    if symbol == 0:
        output = 0
    else:
        maximum = (9 // symbol).bit_length()
        if events > maximum:
            raise UniformPumpUnavailable(
                "uniform power exits the repeated no-growth grammar chamber"
            )
        output = symbol << events
    return ProjectionClause(
        "uniform",
        "uniform",
        1,
        None,
        events,
        0,
        CarryFn.CONST0 if symbol < 9 else CarryFn.ID,
        AffineCount(1),
        (_run(output, 1),),
    )


def edge_core_successors(edge: int, core: int) -> tuple[ProjectionClause, ...]:
    """Normalize ``edge, core**(m-1), edge`` for the first generated family.

    Only ``core == 2*edge`` with ``1 <= edge <= 8`` is constructor-owned here.
    At width parameters two and three, the high-core result is a generalized
    edge/core field outside ``core == 2*edge``.  At parameter four and above it
    introduces another boundary layer.  Both successors are intentionally
    unsupported here.
    """
    if (
        type(edge) is not int
        or type(core) is not int
        or not 1 <= edge <= 8
        or core != 2 * edge
    ):
        raise UniformPumpUnavailable(
            "edge/core grammar is outside the generated uniform successor family"
        )
    if edge <= 4:
        return (
            ProjectionClause(
                "edge-core",
                "edge-core",
                1,
                None,
                1,
                0,
                CarryFn.CONST0,
                AffineCount(1, 1),
                (
                    _run(2 * edge, 0, 1),
                    _run(4 * edge, 1, -1),
                    _run(2 * edge, 0, 1),
                ),
            ),
        )
    return (
        ProjectionClause(
            "edge-core",
            "uniform",
            1,
            1,
            1,
            0,
            CarryFn.CONST0,
            AffineCount(0, 2),
            (_run(2 * edge, 0, 2),),
        ),
        ProjectionClause(
            "edge-core",
            "edge-core",
            2,
            2,
            1,
            0,
            CarryFn.CONST0,
            AffineCount(1, 1),
            (
                _run(2 * edge + 1, 0, 1),
                _run(4 * edge - 20, 0, 1),
                _run(2 * edge + 1, 0, 1),
            ),
        ),
        ProjectionClause(
            "edge-core",
            "edge-core",
            3,
            3,
            1,
            0,
            CarryFn.CONST0,
            AffineCount(1, 1),
            (
                _run(2 * edge + 1, 0, 1),
                _run(4 * edge - 19, 0, 2),
                _run(2 * edge + 1, 0, 1),
            ),
        ),
        ProjectionClause(
            "edge-core",
            "boundary-core",
            4,
            None,
            1,
            0,
            CarryFn.CONST0,
            AffineCount(1, 1),
            (
                _run(2 * edge + 1, 0, 1),
                _run(4 * edge - 19, 0, 1),
                _run(4 * edge - 18, 1, -3),
                _run(4 * edge - 19, 0, 1),
                _run(2 * edge + 1, 0, 1),
            ),
        ),
    )


def select_clause(
    clauses: tuple[ProjectionClause, ...], width: int
) -> ProjectionClause:
    matches = tuple(clause for clause in clauses if clause.admits(width))
    if len(matches) != 1:
        raise ValueError("pumped grammar guards are not a total disjoint partition")
    return matches[0]


__all__ = [
    "AffineCount",
    "ProjectionClause",
    "ProjectionRun",
    "UniformPumpUnavailable",
    "edge_core_successors",
    "select_clause",
    "uniform_no_growth_power",
    "uniform_source_admitted",
    "uniform_successor",
]
