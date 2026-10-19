"""Decimal growth's output-facing carry coboundary, with no source decoder.

Symbols 0..9 mean (q, 0), 10 means (0, -1), and 11 means (9, 1).
Only geometry-admitted growth contexts give the reconstruction law. Local
tables are total outside that context so circuits remain ordinary functions;
their arbitrary extensions are not additional admitted source states.
"""

from dataclasses import dataclass

GROWTH_SYMBOLS = tuple((q, 0) for q in range(10)) + ((0, -1), (9, 1))


def growth_symbol_value(residue: int, outgoing: int, reflected: int) -> int:
    """Consume already-derived ports, forgetting their source geometry label."""
    if residue == 9 and outgoing != reflected:
        return 10 if outgoing else 11
    return (residue + outgoing) % 10


def growth_pair_value(previous: int, current: int) -> int:
    """Integer radius-one law; an unrelated pair of symbols need not be legal."""
    q0, d0 = GROWTH_SYMBOLS[previous]
    q1, d1 = GROWTH_SYMBOLS[current]
    return q1 + q0 + d1 - 10 * d0


@dataclass(frozen=True, slots=True)
class GrowthCoboundaryHalf:
    """Output-facing occurrence: width and symbols, never source Gamma/value."""

    width: int
    symbols: tuple[int, ...]

    def __post_init__(self) -> None:
        if (
            type(self.width) is not int
            or self.width < 1
            or type(self.symbols) is not tuple
            or len(self.symbols) != (self.width + 1) // 2
            or any(type(v) is not int or not 0 <= v < 12 for v in self.symbols)
        ):
            raise ValueError("invalid growth coboundary half")

    def output_half(self) -> tuple[int, ...]:
        q, delta = GROWTH_SYMBOLS[self.symbols[0]]
        result = [q + delta]
        result.extend(
            growth_pair_value(a, b)
            for a, b in zip(self.symbols, self.symbols[1:], strict=False)
        )
        if self.width % 2 == 0:
            q, delta = GROWTH_SYMBOLS[self.symbols[-1]]
            if delta:
                raise ValueError(
                    "even growth center requires zero reflected carry difference"
                )
            result.append(2 * q)
        if any(not 0 <= v <= 18 for v in result):
            raise ValueError("symbols do not describe an admitted growth occurrence")
        return tuple(result)
