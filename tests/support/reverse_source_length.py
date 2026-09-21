"""Independent length references for spatially composed source carry actions.

These test-only helpers own temporary projections. Production shares one
``SourceCarryPorts`` instance through its source-image workspace. Keeping the
reference here prevents a second production width API from surviving the
source-only scheduler cutover.
"""

from collections.abc import Iterator

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts


def source_width(source: ExactSource) -> int:
    """Return the authenticated original digit extent."""
    if type(source) is not ExactSource:
        raise TypeError("source width requires an exact source")
    return len(source.digits)


def source_growth(source: ExactSource, ledger: ResourceLedger) -> int:
    """Read the composed root carry without normalizing digits."""
    ports = SourceCarryPorts(source, ledger)
    try:
        ledger.bump("reverse_source_length_growth_queries")
        return ports.terminal
    finally:
        ports.dispose()


def one_step_width(source: ExactSource, ledger: ResourceLedger) -> int:
    return source_width(source) + source_growth(source, ledger)


def iter_second_pairs(source: ExactSource, ledger: ResourceLedger) -> Iterator[int]:
    """Bounded reference/output projection; this iterator never owns width."""
    ports = SourceCarryPorts(source, ledger)
    try:
        for position in range(ports.width + ports.terminal):
            yield ports.second_pair(position)
    finally:
        ports.dispose()


def fused_two_step_width(source: ExactSource, ledger: ResourceLedger) -> int:
    ports = SourceCarryPorts(source, ledger)
    try:
        ledger.bump("reverse_source_length_fused_queries")
        return ports.second_width()
    finally:
        ports.dispose()


__all__ = [
    "fused_two_step_width",
    "iter_second_pairs",
    "one_step_width",
    "source_growth",
    "source_width",
]
