"""Finite mixed 2/11 forcing programs read from issued Q19 occurrences."""

from __future__ import annotations

from dataclasses import InitVar, dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    MatrixEntries,
    OrderedMatrixProgram,
)
from number_compiler.resources.ledger_records import ResourceScope
from number_compiler.resources.lifecycle import cleanup_all

if TYPE_CHECKING:
    from .power import ReverseAddPoweredTerm
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner


_CHECKED_FORCING_SEAL = object()


@dataclass(frozen=True, slots=True)
class _ForcingLetter:
    incoming_birth: int
    outgoing_birth: int
    action: Matrix2


@dataclass(frozen=True, slots=True)
class CheckedFiniteForcing:
    """Output of a checked finite observation. Grants no issuance authority."""

    source_generation: int
    initial_residue: int
    final_residue: int
    decimal_places: int
    period: int
    verified_repeats: int
    period_action: Matrix2
    _issue_token: InitVar[object]
    _binding: tuple[int, int, int, int, int, int, MatrixEntries, int | None] = field(
        init=False,
        repr=False,
        compare=False,
    )

    def __post_init__(self, _issue_token: object) -> None:
        if _issue_token is not _CHECKED_FORCING_SEAL:
            raise TypeError("finite forcing requires source verification")
        object.__setattr__(self, "_binding", self._coordinates())

    def _coordinates(
        self,
    ) -> tuple[int, int, int, int, int, int, MatrixEntries, int | None]:
        return (
            self.source_generation,
            self.initial_residue,
            self.final_residue,
            self.decimal_places,
            self.period,
            self.verified_repeats,
            self.period_action.entries,
            self.period_action.modulus,
        )

    def _require_binding(self) -> None:
        if type(self.period_action) is not Matrix2 or any(
            type(entry) is not int for entry in self.period_action.entries
        ):
            raise ValueError("verified forcing matrix was altered")
        actual = self._coordinates()
        if any(
            type(current) is not type(issued) or current != issued
            for current, issued in zip(actual, self._binding, strict=True)
        ):
            raise ValueError("verified forcing coordinates were altered")

    def consume(self, repeats: int) -> int:
        self._require_binding()
        require_integer(
            repeats, "source-verified repetition count", 0, self.verified_repeats
        )
        return self.period_action.power(repeats).apply(self.initial_residue, 1)[0]

    def project_precision(self, precision: int) -> CheckedFiniteForcing:
        """Reduce an already checked program to a lower decimal precision."""
        self._require_binding()
        precision = require_integer(
            precision, "forcing decimal places", 1, self.decimal_places
        )
        modulus: int = 10**precision
        return type(self)(
            self.source_generation,
            self.initial_residue % modulus,
            self.final_residue % modulus,
            precision,
            self.period,
            self.verified_repeats,
            Matrix2(self.period_action.entries, modulus),
            _CHECKED_FORCING_SEAL,
        )


def _border_residues(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    places: int,
    *,
    include_reflected: bool,
) -> tuple[int, int | None]:
    """Read both bounded borders with one authenticated Q19 prefix walk."""
    from .q19_source_authority import digits_at

    count = min(places, source.output_width)
    low_positions = tuple(range(count))
    reflected_positions = (
        tuple(source.output_width - 1 - position for position in range(count))
        if include_reflected
        else ()
    )
    values = digits_at(owner, source, low_positions + reflected_positions)
    low = 0
    for digit in reversed(values[:count]):
        low = 10 * low + digit
    if not include_reflected:
        return low, None
    reflected = 0
    for digit in reversed(values[count:]):
        reflected = 10 * reflected + digit
    return low, reflected


def certify_finite_period(
    term: ReverseAddPoweredTerm, *, period: int, repeats: int, precision: int
) -> CheckedFiniteForcing:
    """Check both birth guards and the complete modular forcing letter per tick."""
    term.validate_source_binding()
    if term.base != 10 or term.generation < 1:
        raise ValueError("mixed forcing requires a positive-generation decimal source")
    require_integer(period, "forcing period", 1, 128)
    require_integer(repeats, "forcing repetitions", 1, 128 // period)
    require_integer(precision, "forcing decimal places", 1, 128)
    ledger = term.resource_ledger
    scratch = ledger.register(
        f"reverse-mixed-forcing-{ledger.owner_count}",
        "temporary_work",
        scope=ResourceScope.INDEX_OWNED,
    )
    try:
        with ledger.reservation(scratch, nodes=32 + (period + 4) * (16 + precision)):
            result = _check_window(term, period, repeats, precision)
        ledger.mark_disposed(scratch)
        return result
    except BaseException as error:

        def release_remaining() -> None:
            entries, nodes = ledger.account_usage(scratch)
            if entries or nodes:
                ledger.release(scratch, entries=entries, nodes=nodes)

        try:
            cleanup_all((release_remaining, lambda: ledger.mark_disposed(scratch)))
        except BaseException as cleanup_error:
            raise error from cleanup_error
        raise


def _check_window(
    term: ReverseAddPoweredTerm, period: int, repeats: int, precision: int
) -> CheckedFiniteForcing:
    owner, current, _, _ = term.completed_q19_occurrence()
    owner.validate_issued_occurrence(current)
    generation = term.generation
    if current.temporal_steps != generation:
        raise ValueError("mixed forcing source does not match the selected generation")
    modulus = 10**precision
    initial, reflected = _border_residues(
        owner, current, precision, include_reflected=True
    )
    residue = initial
    word: list[_ForcingLetter] = []
    total_ticks = period * repeats
    for tick in range(total_ticks):
        if reflected is None:
            raise AssertionError("mixed forcing lost its reflected source border")
        child = owner.apply_pair_step(current)
        owner.validate_issued_occurrence(child)
        if (
            child.temporal_steps != generation + tick + 1
            or child.pair_width != current.output_width
        ):
            raise ValueError(
                "mixed forcing children do not share the issued source seam"
            )
        incoming = current.output_width - current.pair_width
        outgoing = child.output_width - child.pair_width
        if incoming not in (0, 1) or outgoing not in (0, 1):
            raise ValueError("mixed forcing requires a one-bit width birth")
        multiplier = 2 + 9 * incoming
        forcing = reflected - (1 + 9 * incoming) * residue
        action = Matrix2((multiplier, forcing, 0, 1), modulus)
        target, next_reflected = _border_residues(
            owner, child, precision, include_reflected=tick + 1 < total_ticks
        )
        if action.apply(residue, 1)[0] != target:
            raise ValueError(
                "mixed forcing does not reproduce the issued child residue"
            )
        letter = _ForcingLetter(incoming, outgoing, action)
        if tick < period:
            word.append(letter)
        elif letter != word[tick % period]:
            raise ValueError(
                "complete guarded forcing does not repeat on the source window"
            )
        current, residue, reflected = child, target, next_reflected
    if repeats > 1 and word[0].incoming_birth != word[-1].outgoing_birth:
        raise ValueError("mixed forcing cannot repeat across an open birth seam")
    product = OrderedMatrixProgram(tuple(letter.action for letter in word)).product(
        0, period
    )
    result = CheckedFiniteForcing(
        generation,
        initial,
        residue,
        precision,
        period,
        repeats,
        product,
        _CHECKED_FORCING_SEAL,
    )
    if result.consume(repeats) != residue:
        raise AssertionError("powered forcing differs from the checked finite endpoint")
    return result
