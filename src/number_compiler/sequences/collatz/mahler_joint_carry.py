"""Joint issued-source Mahler carry/innovation return for normalized Collatz.

An explicitly requested carry view exposes a window's already issued endpoint
as a decimal return seam; the cold executor does not construct or consume it.
Full chronological Laurent polynomials are reconstructed *on demand* by one
finite source pass with no retained per-generation carry/cochain history. The
source is authenticated by the same issued affine word that owns the endpoint.

Neither a cyclotomic port period nor a reconstructed carry polynomial can
issue a previously unknown future parity word: that remains the owner's guard.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.morphism_core import binary_power

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.diagonal_source_window import (
        CollatzDiagonalWindow,
    )
    from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
        DyadicTerminalEndpointAction,
        DyadicTerminalFieldAction,
    )
    from number_compiler.sequences.collatz.joint_harmonic_band import (
        TwoOddHarmonicPoint,
    )


@dataclass(frozen=True, slots=True, init=False)
class MahlerFutureCarryPort:
    """Typed view of a source window's authenticated future carry.

    The window remains the sole issuer. The view reports the exact first 6305
    numerator and tail but cannot authorize another transition.
    """

    _window: CollatzDiagonalWindow

    def __init__(self, *_args: object, **_kwargs: object) -> None:
        raise TypeError("Mahler carry views must come from an issued source window")

    @classmethod
    def from_issued_window(
        cls,
        window: CollatzDiagonalWindow,
    ) -> MahlerFutureCarryPort:
        from number_compiler.sequences.collatz.diagonal_source_window import (
            CollatzDiagonalWindow,
        )

        if type(window) is not CollatzDiagonalWindow:
            raise TypeError("future carry view requires an issued source window")
        window.require_issued()
        result = object.__new__(cls)
        object.__setattr__(result, "_window", window)
        return result

    @property
    def producer_issued(self) -> bool:
        return type(self) is MahlerFutureCarryPort and self._window.producer_issued

    @property
    def target(self) -> int:
        self._require_window()
        return self._window.normalized_endpoint

    @property
    def parity(self) -> int:
        return self.target & 1

    @property
    def border_upper(self) -> int | None:
        target = self.target
        if target % 10 != 3:
            return None
        upper = 3 * ((target - 3) // 10) + 1
        if 3 * target + 1 != 10 * upper:
            raise AssertionError("6305 outgoing carry is not source authentic")
        return upper

    @property
    def border_zero_tail(self) -> int | None:
        upper = self.border_upper
        if upper is None:
            return None
        return (upper & -upper).bit_length() - 1

    def first_6305_carry(self, source: int) -> tuple[int, int] | None:
        """Return the first upper numerator and zero tail at this exact seam."""
        self.require_target(source)
        if source % 10 != 3:
            return None
        upper = 3 * ((source - 3) // 10) + 1
        if 3 * source + 1 != 10 * upper:
            raise AssertionError("6305 outgoing carry is not source authentic")
        return upper, (upper & -upper).bit_length() - 1

    def pointed_harmonic_band(self, source: int) -> TwoOddHarmonicPoint | None:
        """Read the same sealed endpoint through the two-odd harmonic ports."""
        self.require_target(source)
        if source & 3 != 3:
            return None
        from number_compiler.sequences.collatz.joint_harmonic_band import (
            TWO_ODD_HARMONIC_BAND,
        )

        return TWO_ODD_HARMONIC_BAND.point(source)

    def _require_window(self) -> None:
        if type(self) is not MahlerFutureCarryPort:
            raise TypeError("foreign future Mahler carry view")
        try:
            self._window.require_issued()
        except (AttributeError, TypeError, ValueError) as exc:
            raise ValueError("future carry source window is no longer issued") from exc

    def require_target(self, source: int) -> None:
        self._require_window()
        if type(source) is not int or source != self._window.normalized_endpoint:
            raise ValueError("future carry port does not belong to this source seam")

    def nested_band(self, source: int, places: int) -> tuple[int, int, int]:
        """Return lower decimal band, upper binary carry-in and parity."""
        self.require_target(source)
        if type(places) is not int or not 1 <= places <= 4096:
            raise ValueError("nested band width must be in 1..4096")
        width = 10**places
        return source % width, (source // width) & 1, self.parity


@dataclass(frozen=True, slots=True)
class MahlerRecoveredCocycle:
    """Full finite Laurent certificate at one explicitly requested source.

    Polynomial coefficients are low-degree first.  With d=steps, they obey
       z^d P_endpoint - 15^d P_source
         = innovation(z) + (z-10)*chronological_carries(z).
    No per-step carry tape is retained, and the ordinary cold executor never
    materializes these coefficients.
    """

    source: int
    endpoint: int
    steps: int
    innovation: tuple[int, ...]
    chronological_carries: tuple[int, ...]
    total_defect: tuple[int, ...]


def _decimal_digits(value: int, column_limit: int) -> list[int]:
    result: list[int] = []
    while value:
        value, digit = divmod(value, 10)
        result.append(digit)
        if len(result) > column_limit:
            raise ValueError("chronological Mahler carry exceeds column budget")
    return result


def _trim(values: list[int]) -> tuple[int, ...]:
    while values and values[-1] == 0:
        values.pop()
    return tuple(values)


def recover_chronological_cocycle(
    action: DyadicTerminalEndpointAction | DyadicTerminalFieldAction,
    source: int,
    *,
    max_steps: int = 2048,
    max_columns: int = 4096,
    reserve_bits: Callable[[int], None] | None = None,
) -> MahlerRecoveredCocycle:
    """Recover BOTH weighted Laurent outputs in a single finite source pass.

    The parity innovations are streamed with I_(n+1)=15*I_n+z^n*E_n,
    where E_n=5 for an odd step and E_n=-10*P_(x_n) for an even step.
    Dividing the *exact endpoint defect minus I* by z-10 recovers all
    chronological carries.  No carried digit vector or chronological source
    history is stored; no independent word-selector/revalidation is called.
    """
    from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
        DyadicTerminalEndpointAction,
        DyadicTerminalFieldAction,
    )

    if type(action) not in (DyadicTerminalEndpointAction, DyadicTerminalFieldAction):
        raise TypeError("chronological carry requires an issued action")
    if type(max_steps) is not int or not 0 <= max_steps <= 65536:
        raise ValueError("invalid Mahler step budget")
    if type(max_columns) is not int or not 1 <= max_columns <= 65536:
        raise ValueError("invalid Mahler column budget")
    if action.steps > max_steps:
        raise ValueError("chronological Mahler carry exceeds step budget")
    if reserve_bits is not None and not callable(reserve_bits):
        raise TypeError("Mahler chronological scratch preflight must be callable")
    source = require_integer(source, "Mahler source", 1)
    if reserve_bits is not None:
        # Three output coefficient arrays, scratch digits, and Python bigint
        # object overhead. Charge an upper bound, not merely live digits.
        coefficient_bits = source.bit_length() + 5 * action.steps + 384
        # The normalized Collatz map grows by less than a factor of two per
        # step.  This bounds every intermediate decimal width without
        # computing any intermediate value or creating a digit history.
        source_width_bound = (source.bit_length() + action.steps + 5) // 3 + 3
        active_columns = min(max_columns, action.steps + source_width_bound + 3)
        reserve_bits(16 * (active_columns + 4) * coefficient_bits)

    # The issuer owns the entire parity word; keep this exact source guard
    # after scratch preflight so a rejected request does not first construct
    # its potentially large affine endpoint.
    endpoint = action.endpoint(source)
    if action.steps + max(1, endpoint.bit_length() // 3) > 4 * max_columns:
        # A cheap necessary budget preflight before any history traversal.
        raise ValueError("chronological Mahler carry exceeds column budget")

    initial_digits = _decimal_digits(source, max_columns)
    innovation: list[int] = []
    # For a source-certified all-odd program the complete innovation has
    # the closed form 5*(15**d-z**d)/(15-z).  In particular there is no
    # need to inspect the 2-adic trajectory to recover the carry cocycle.
    # The exact polynomial output still requires O(d) coefficients.
    if action.gain == pow(3, action.steps):
        if action.steps > max_columns:
            raise ValueError("chronological Mahler carry exceeds column budget")
        coefficient = 5 * pow(15, max(0, action.steps - 1))
        for _ in range(action.steps):
            innovation.append(coefficient)
            coefficient //= 15
    else:
        cursor = source
        for step in range(action.steps):
            # Keep only one cumulative innovation polynomial (not a cochain
            # list). Its new injection is at moving-cut exponent 'step'.
            for j in range(len(innovation)):
                innovation[j] *= 15
            if cursor & 1:
                if len(innovation) <= step:
                    innovation.extend([0] * (step + 1 - len(innovation)))
                innovation[step] += 5
                cursor = (3 * cursor + 1) >> 1
            else:
                digits = _decimal_digits(cursor, max_columns)
                needed = step + len(digits)
                if needed > max_columns:
                    raise ValueError("chronological Mahler carry exceeds column budget")
                if len(innovation) < needed:
                    innovation.extend([0] * (needed - len(innovation)))
                for j, digit in enumerate(digits):
                    innovation[step + j] -= 10 * digit
                cursor >>= 1
        if cursor != endpoint:
            raise AssertionError("issued Mahler source action does not match its word")

    end_digits = _decimal_digits(endpoint, max_columns)
    length = max(
        1, action.steps + len(end_digits), len(initial_digits), len(innovation)
    )
    if length > max_columns:
        raise ValueError("chronological Mahler carry exceeds column budget")
    total = [0] * length
    remainder = [0] * length
    for j, digit in enumerate(end_digits):
        total[action.steps + j] += digit
    ma = pow(15, action.steps)
    for j, digit in enumerate(initial_digits):
        total[j] -= ma * digit
    for j, coefficient in enumerate(total):
        remainder[j] = coefficient - (innovation[j] if j < len(innovation) else 0)

    # Exact low-to-high synthetic division by z-10. This is the only carry
    # reconstruction; no per-step carry vector gets materialized or replayed.
    carries: list[int] = []
    previous = 0
    for coefficient in remainder:
        quotient, rem = divmod(previous - coefficient, 10)
        if rem:
            raise AssertionError("Mahler innovation does not factor through z-10")
        carries.append(quotient)
        previous = quotient
    if previous:
        raise AssertionError("Mahler carried polynomial escaped the declared seam")
    return MahlerRecoveredCocycle(
        source, endpoint, action.steps, _trim(innovation), _trim(carries), _trim(total)
    )


@dataclass(frozen=True, slots=True)
class MahlerCarryProgram:
    """Source-free binary-powerable word/defect composition DAG.

    The action and its source cylinder remain the *one* arithmetic authority.
    `power` builds O(log q) nodes and never expands the repeated program.
    Full chronological polynomial materialization is separately budgeted and
    may still take work proportional to its requested physical extent.
    """

    action: DyadicTerminalFieldAction
    left: MahlerCarryProgram | None = None
    right: MahlerCarryProgram | None = None

    @classmethod
    def issued(cls, action: DyadicTerminalFieldAction) -> MahlerCarryProgram:
        from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
            DyadicTerminalFieldAction,
        )

        if type(action) is not DyadicTerminalFieldAction or not action.producer_issued:
            raise ValueError("Mahler program requires a producer-issued parity action")
        return cls(action)

    def then(self, other: MahlerCarryProgram) -> MahlerCarryProgram:
        if type(other) is not MahlerCarryProgram:
            raise TypeError(
                "Mahler program composition requires another issued program"
            )
        if not self.action.steps:
            return other
        if not other.action.steps:
            return self
        return MahlerCarryProgram(self.action.then(other.action), self, other)

    def power(self, count: int) -> MahlerCarryProgram:
        if type(count) is not int or count < 0:
            raise ValueError("Mahler program power must be nonnegative")
        return binary_power(
            self,
            count,
            identity=MahlerCarryProgram.issued(self.action.identity()),
            compose=MahlerCarryProgram.then,
        ).value

    def endpoint(self, source: int) -> int:
        return self.action.endpoint(source)

    def chronological_cocycle(
        self,
        source: int,
        *,
        max_steps: int = 2048,
        max_columns: int = 4096,
        reserve_bits: Callable[[int], None] | None = None,
    ) -> MahlerRecoveredCocycle:
        # The issued action recovers the word in one bounded source pass.
        # The DAG remains compressed rather than storing a carry history.
        return recover_chronological_cocycle(
            self.action,
            source,
            max_steps=max_steps,
            max_columns=max_columns,
            reserve_bits=reserve_bits,
        )


__all__ = [
    "MahlerCarryProgram",
    "MahlerFutureCarryPort",
    "MahlerRecoveredCocycle",
    "recover_chronological_cocycle",
]
