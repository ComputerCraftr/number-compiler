"""Certified public demands over the finite comma-cylinder arithmetic owner."""

from __future__ import annotations

from collections.abc import Generator
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.output_stream_metrics import closing_output_stream

if TYPE_CHECKING:
    from number_compiler.sequences.comma.future_provider import (
        SemanticFutureProviderLease,
    )
    from number_compiler.sequences.comma.power import CommaTerm


@dataclass(frozen=True, slots=True)
class CommaTermPayload:
    term: CommaTerm

    def __post_init__(self) -> None:
        from number_compiler.sequences.comma.power import CommaTerm

        if type(self.term) is not CommaTerm:
            raise TypeError("comma payload requires its exact source owner")

    def require_certified(self) -> None:
        self.term.require_certified_public_prefix()

    @property
    def certificate_provider(self) -> SemanticFutureProviderLease | None:
        """Observe an already retained global lease without charging a hit."""
        return self.term.retained_global_future_provider

    @property
    def estimated_bit_length(self) -> int:
        # Each legal edge adds between one and 99, independently of branch choice.
        return (20 + 99 * (self.term.index - 1)).bit_length()

    def materialize(self, *, max_bits: int) -> int:
        require_integer(max_bits, "output bit cap", 0)
        self.require_certified()
        return self.term.materialize(max_bits=max_bits)

    def digit(self, index: int) -> int:
        index = require_integer(index, "digit coordinate", 0)
        self.require_certified()
        return self.term.digit(index)

    def iter_digits(self) -> Generator[int, None, None]:
        from number_compiler.resources.process_cache import get_process_cache

        # Admission is deferred with the stream, so reset before the first pull
        # cannot leave a pre-admitted but unevaluated iterator behind.
        self.require_certified()
        cache = get_process_cache() if self.term.shared_cache else None
        generation = cache.generation if cache is not None else None
        with closing_output_stream(self.term.iter_digits()) as stream:
            while True:
                self.term.arena.charge()
                if cache is not None and cache.generation != generation:
                    raise ValueError("stale comma stream admission after cache reset")
                try:
                    digit = next(stream)
                except StopIteration:
                    return
                yield digit

    def digits(self) -> tuple[int, ...]:
        return tuple(self.iter_digits())
