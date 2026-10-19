"""Validated execution queries for the public number projection API.

Presentation and optional observer configuration live in the CLI request
layer.  These records contain only the parameters that identify and execute a
mathematical family request.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import ClassVar, TypeAlias, TypeGuard

from number_compiler.api.observation_types import SelectorId
from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.arithmetic.contracts.input_validation import require_integer


class QueryOptionError(ValueError):
    """One typed query field failed admission at its public boundary."""

    def __init__(self, field: str, message: str) -> None:
        self.field = field
        super().__init__(message)


def require_query_integer(
    value: object,
    field: str,
    minimum: int | None = None,
    maximum: int | None = None,
    *,
    name: str | None = None,
) -> int:
    """Validate an integer while retaining the canonical parser field name."""
    try:
        return require_integer(
            value, field.replace("_", " ") if name is None else name, minimum, maximum
        )
    except (TypeError, ValueError) as exc:
        raise QueryOptionError(field, str(exc)) from exc


@dataclass(frozen=True, slots=True)
class ReverseAddTermQuery:
    index: int
    seed: int = field(kw_only=True)
    base: int = 10

    family: ClassVar[FamilyId] = FamilyId.REVERSE_ADD
    selector: ClassVar[SelectorId] = SelectorId.NTH

    def __post_init__(self) -> None:
        require_query_integer(self.index, "index", 0, name="term index")
        require_query_integer(self.seed, "seed", 0, name="reverse-add seed")
        require_query_integer(self.base, "base", 2, name="reverse-add base")


@dataclass(frozen=True, slots=True)
class DoubleReverseTermQuery:
    index: int
    seed: int = field(kw_only=True)
    max_steps: int = 4096
    max_state_bits: int = 4096

    family: ClassVar[FamilyId] = FamilyId.DOUBLE_REVERSE
    selector: ClassVar[SelectorId] = SelectorId.NTH

    def __post_init__(self) -> None:
        require_query_integer(self.index, "index", 0, name="term index")
        require_query_integer(self.seed, "seed", 0, name="2rev10 seed")
        require_query_integer(
            self.max_steps, "max_steps", 0, name="maximum 2rev10 steps"
        )
        require_query_integer(
            self.max_state_bits,
            "max_state_bits",
            1,
            name="maximum 2rev10 state bits",
        )


@dataclass(frozen=True, slots=True)
class CollatzTermQuery:
    index: int
    seed: int = field(kw_only=True)
    radix: int = 2

    family: ClassVar[FamilyId] = FamilyId.COLLATZ
    selector: ClassVar[SelectorId] = SelectorId.NTH

    def __post_init__(self) -> None:
        require_query_integer(self.index, "index", 0, name="term index")
        require_query_integer(self.seed, "seed", 1, name="Collatz seed")
        radix = require_query_integer(self.radix, "radix", 2, name="Collatz radix")
        if radix not in (2, 3) and radix % 6 != 0:
            raise QueryOptionError(
                "radix", "Collatz radix must be 2, 3, or divisible by 6"
            )


@dataclass(frozen=True, slots=True)
class AntihydraTermQuery:
    index: int
    max_steps: int = 4096
    max_state_bits: int = 4096

    family: ClassVar[FamilyId] = FamilyId.ANTIHYDRA
    selector: ClassVar[SelectorId] = SelectorId.NTH

    def __post_init__(self) -> None:
        require_query_integer(self.index, "index", 0, name="term index")
        require_query_integer(
            self.max_steps, "max_steps", 0, name="maximum Antihydra steps"
        )
        require_query_integer(
            self.max_state_bits,
            "max_state_bits",
            4,
            name="maximum Antihydra state bits",
        )


@dataclass(frozen=True, slots=True)
class CommaTermQuery:
    index: int
    max_comma_states: int = 131_072
    max_comma_work: int = 1_000_000

    family: ClassVar[FamilyId] = FamilyId.A367620
    selector: ClassVar[SelectorId] = SelectorId.NTH

    def __post_init__(self) -> None:
        require_query_integer(self.index, "index", 1, name="A367620 index")
        require_query_integer(
            self.max_comma_states, "max_comma_states", 1, name="comma state budget"
        )
        require_query_integer(
            self.max_comma_work, "max_comma_work", 1, name="comma work budget"
        )


@dataclass(frozen=True, slots=True)
class PrimeTermQuery:
    index: int
    start: int = 2
    max_prime_states: int = 131_072
    max_prime_work: int = 1_000_000
    max_prime_stages: int = 4096

    family: ClassVar[FamilyId] = FamilyId.PRIME
    selector: ClassVar[SelectorId] = SelectorId.NTH

    def __post_init__(self) -> None:
        require_query_integer(self.index, "index", 0, name="prime index")
        require_query_integer(self.start, "start", 0, name="prime start")
        require_query_integer(
            self.max_prime_states, "max_prime_states", 1, name="prime state budget"
        )
        require_query_integer(
            self.max_prime_work, "max_prime_work", 1, name="prime work budget"
        )
        require_query_integer(
            self.max_prime_stages, "max_prime_stages", 1, name="prime stage budget"
        )


@dataclass(frozen=True, slots=True)
class FermatTermQuery:
    index: int

    family: ClassVar[FamilyId] = FamilyId.FERMAT
    selector: ClassVar[SelectorId] = SelectorId.NTH

    def __post_init__(self) -> None:
        require_query_integer(self.index, "index", 0, name="Fermat index")


@dataclass(frozen=True, slots=True)
class MersenneTermQuery:
    index: int

    family: ClassVar[FamilyId] = FamilyId.MERSENNE
    selector: ClassVar[SelectorId] = SelectorId.NTH

    def __post_init__(self) -> None:
        require_query_integer(self.index, "index", 1, name="Mersenne exponent/index")


TermQuery: TypeAlias = (
    ReverseAddTermQuery
    | DoubleReverseTermQuery
    | CollatzTermQuery
    | AntihydraTermQuery
    | CommaTermQuery
    | PrimeTermQuery
    | FermatTermQuery
    | MersenneTermQuery
)


@dataclass(frozen=True, slots=True)
class CollatzEventQuery:
    events: int
    seed: int = field(kw_only=True)
    max_events: int = 4096
    max_digits: int = 4096

    family: ClassVar[FamilyId] = FamilyId.COLLATZ
    selector: ClassVar[SelectorId] = SelectorId.EVENTS

    @property
    def index(self) -> int:
        """Expose the event coordinate under the CLI envelope's common name."""
        return self.events

    def __post_init__(self) -> None:
        require_query_integer(self.events, "events", 0, name="event count")
        require_query_integer(self.seed, "seed", 1, name="Collatz event seed")
        if self.seed % 2 == 0:
            raise QueryOptionError(
                "seed", "accelerated event observations require an odd seed"
            )
        require_query_integer(self.max_events, "max_events", 0, name="maximum events")
        require_query_integer(self.max_digits, "max_digits", 1, name="maximum digits")
        if self.events > self.max_events:
            raise QueryOptionError("max_events", "source observation budget exceeded")


@dataclass(frozen=True, slots=True)
class AntihydraVerifyQuery:
    certificate: str

    family: ClassVar[FamilyId] = FamilyId.ANTIHYDRA
    selector: ClassVar[SelectorId] = SelectorId.VERIFY

    @property
    def index(self) -> int:
        """Verification addresses a certificate rather than a term index."""
        return 0

    def __post_init__(self) -> None:
        if type(self.certificate) is not str or not self.certificate:
            raise QueryOptionError(
                "certificate", "certificate path must be a nonempty string"
            )


ExecutionQuery: TypeAlias = TermQuery | CollatzEventQuery | AntihydraVerifyQuery

_TERM_QUERY_TYPES = (
    ReverseAddTermQuery,
    DoubleReverseTermQuery,
    CollatzTermQuery,
    AntihydraTermQuery,
    CommaTermQuery,
    PrimeTermQuery,
    FermatTermQuery,
    MersenneTermQuery,
)


def is_term_query(query: ExecutionQuery) -> TypeGuard[TermQuery]:
    """Narrow an execution request to a concrete ordinary-term query."""
    return type(query) in _TERM_QUERY_TYPES


__all__ = [
    "AntihydraTermQuery",
    "AntihydraVerifyQuery",
    "CollatzEventQuery",
    "CollatzTermQuery",
    "CommaTermQuery",
    "DoubleReverseTermQuery",
    "ExecutionQuery",
    "FermatTermQuery",
    "MersenneTermQuery",
    "PrimeTermQuery",
    "QueryOptionError",
    "ReverseAddTermQuery",
    "TermQuery",
    "is_term_query",
    "require_query_integer",
]
