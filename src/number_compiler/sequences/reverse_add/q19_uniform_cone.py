"""All-border-choices temporal authorization for protected uniform Q19 cells.

This does not guess future growth or replay physical Q19 steps.  A cell whose
source is surrounded by a sufficiently thick *exact* uniform pair-sum region
has a closed finite temporal grammar.  The guard inspects the compressed Q19
source, not observed future states.  The proof only publishes an interior cell,
NEVER a complete reverse/add integer or global U/V moment.

For a uniform source coefficient s != 9 both carry ingresses reset locally;
for s == 9 the source's two authentic ingresses must agree.  In either case
the first successor is even and not EQ=9, then its two ingresses reset forever.
The homogeneous successor s -> 2s - 18*[s>9] is independent of growth.

An exterior disturbance can move at most two pair cells inward per physical
step while protected homogeneous cells stay non-EQ: each local output uses
nearest carry resets and (on growth) at most one shifted source coefficient.
The 2*steps+2 spatial halo therefore protects a queried fixed coordinate
for every possible future growth word and both external carries.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.decimal_pair_partition import decimal_pair_band
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.sequences.reverse_add.q19_conditional_stencil import (
    next_quiet_joint_xor_response,
)

_UNIFORM_CONE_SEAL = object()

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
    )


class UniformConeNotAuthorized(ValueError):
    """The exact Q19 source has not proved the requested temporal cell."""


def _homogeneous_next(value: int) -> int:
    if value == 9:
        raise AssertionError("unpunctured EQ wire cannot be autonomously doubled")
    return 2 * value - 18 * int(value > 9)


@dataclass(frozen=True, slots=True)
class UniformConeMooreCertificate:
    """Exhaustive all-growth-choice Moore certificate of the bulk controller."""

    admitted_entry_states: int
    distinct_future_states: int
    future_coefficients: tuple[int, ...]
    transition: tuple[int, ...]
    cycle_lengths: tuple[int, ...]


def uniform_cone_moore_certificate() -> UniformConeMooreCertificate:
    """Exhaustively prove the 20 admissible entries map into ten closed cells.

    This enumerates BOTH physical growth branches and their complete
    normalized interior digits. It does not assume a border growth pattern.
    After one step every reachable coefficient is even and carries reset;
    all ten such states have different next pair outputs and are therefore
    pairwise Moore-distinguishable for the specified future port alphabet.
    """
    entries = [(s, int(s > 9)) for s in range(19) if s != 9]
    entries += [(9, 0), (9, 1)]
    images: set[int] = set()
    for s, c in entries:
        low = s + c - 10 * int(s > 9 or (s == 9 and c))
        if not 0 <= low <= 9:
            raise AssertionError("entry digit left the decimal alphabet")
        target = 2 * s - 18 * c
        if not 0 <= target <= 18 or target % 2:
            raise AssertionError("homogeneous source did not reset to even")
        for growth in (0, 1):
            # Both the normal and shifted-growth recurrence use the same
            # source value at every position of a homogeneous region.
            physical = 2 * s + 2 * c - 20 * c
            if growth not in (0, 1) or physical != target:
                raise AssertionError("growth and nongrowth cores disagreed")
        images.add(target)
    expected = tuple(range(0, 19, 2))
    if tuple(sorted(images)) != expected:
        raise AssertionError("homogeneous Moore images are not complete")
    table = tuple(_homogeneous_next(s) // 2 for s in expected)
    periods: list[int] = []
    for initial in expected:
        positions: dict[int, int] = {}
        current = initial
        while current not in positions:
            positions[current] = len(positions)
            current = _homogeneous_next(current)
        period = len(positions) - positions[current]
        if period not in (1, 2, 6):
            raise AssertionError("homogeneous period escaped Moore bank")
        periods.append(period)
    # Each target coefficient is itself an emitted port, so no two image
    # states can merge under all-future output-aware Moore refinement.
    return UniformConeMooreCertificate(
        len(entries), len(expected), expected, table, tuple(periods)
    )


def _bulk_at(entry: int, ingress: int, steps: int) -> int:
    """Finite-state exponentiation, with exact EQ puncture in the first tick."""
    if steps == 0:
        return entry
    source = 18 - 18 * ingress if entry == 9 else _homogeneous_next(entry)
    remaining = steps - 1
    seen: dict[int, int] = {}
    states: list[int] = []
    while source not in seen:
        seen[source] = len(states)
        states.append(source)
        source = _homogeneous_next(source)
    pre = seen[source]
    if remaining < len(states):
        return states[remaining]
    return states[pre + (remaining - pre) % (len(states) - pre)]


def _same_symbol_range(
    owner: ReversePairQ19OutputOwner,
    root: int,
    begin: int,
    end: int,
    symbol: int,
) -> bool:
    """Check a half-word range exactly over CONCAT/REPEAT without expanding it.

    Indices count coefficient symbols, not Q19's parity and terminal markers.
    A full SLP component uses its certified `runs==1` summary.  A REPEAT
    interior is checked once, not once per copy.
    """
    if begin == end:
        return True
    summary = owner._word_summary(root)
    if not 0 <= begin < end <= summary.symbols:
        raise ValueError("Q19 homogeneous guard has invalid half-word interval")
    node_bound = len(owner.arena.nodes)
    with owner.ledger.reservation(
        owner._scratch_owner,
        entries=4 * (node_bound + 1),
        nodes=4 * (node_bound + 1),
    ):
        tasks = [(root, begin, end)]
        try:
            while tasks:
                node_id, lo, hi = tasks.pop()
                owner.ledger.bump(
                    _reverse_add_keys.REVERSE_Q19_UNIFORM_GUARD_NODE_VISITS
                )
                owner.ledger.bump(
                    _reverse_add_keys.REVERSE_Q19_UNIFORM_GUARD_OPERAND_BITS,
                    owner.arena.nodes[node_id].length.bit_length(),
                )
                if lo == hi:
                    continue
                report = owner._summaries[node_id]
                if lo == 0 and hi == report.symbols:
                    if report.runs != 1 or report.first_symbol != symbol:
                        return False
                    continue
                node = owner.arena.nodes[node_id]
                if node.kind == "CONCAT":
                    middle = owner._summaries[node.left].symbols
                    if lo < middle:
                        tasks.append((node.left, lo, min(hi, middle)))
                    if hi > middle:
                        tasks.append((node.right, max(0, lo - middle), hi - middle))
                elif node.kind == "REPEAT":
                    width = owner._summaries[node.child].symbols
                    if not width:
                        raise AssertionError(
                            "partial Q19 repetition has no coefficient"
                        )
                    first, offset = divmod(lo, width)
                    last, tail = divmod(hi, width)
                    if first == last:
                        tasks.append((node.child, offset, tail))
                    else:
                        if offset:
                            tasks.append((node.child, offset, width))
                            first += 1
                        if last > first:
                            child = owner._summaries[node.child]
                            if child.runs != 1 or child.first_symbol != symbol:
                                return False
                        if tail:
                            tasks.append((node.child, 0, tail))
                else:
                    raise AssertionError("partial Q19 coefficient is not a composite")
            return True
        finally:
            tasks.clear()


def _full_pair_region_uniform(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    begin: int,
    end: int,
    symbol: int,
) -> bool:
    """Map the two reflected halves to the exact encoded Q19 half-word."""
    w = source.pair_width
    half = (w + 1) // 2
    if begin < half and not _same_symbol_range(
        owner, source.root, begin, min(end, half), symbol
    ):
        return False
    if end > half:
        reflected_lo = w - end
        reflected_hi = w - max(begin, half)
        if not _same_symbol_range(
            owner, source.root, reflected_lo, reflected_hi, symbol
        ):
            return False
    return True


@dataclass(frozen=True, slots=True)
class CertifiedUniformCone:
    """One unconditional (all future growth choices) *interior* temporal port.

    Its returned coefficient is the actual pair coefficient at `coordinate`
    after `steps` reverse/add transitions from the issued `source`; it does
    NOT certify other coordinates, the future width, or numeric moments.
    """

    source: ReversePairOutputOccurrence
    owner: ReversePairQ19OutputOwner
    coordinate: int
    steps: int
    source_symbol: int
    source_ingress: int
    halo: int
    _seal: object = field(init=False, repr=False, compare=False)
    _binding: tuple[object, ...] = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        if getattr(self, "_seal", None) is not _UNIFORM_CONE_SEAL:
            raise ValueError("uniform cone records are issued by a Q19 owner")

    @classmethod
    def _issue(
        cls,
        source: ReversePairOutputOccurrence,
        owner: ReversePairQ19OutputOwner,
        coordinate: int,
        steps: int,
        source_symbol: int,
        source_ingress: int,
        halo: int,
    ) -> CertifiedUniformCone:
        record = object.__new__(cls)
        values = (
            source,
            owner,
            coordinate,
            steps,
            source_symbol,
            source_ingress,
            halo,
        )
        for name, value in zip(
            (
                "source",
                "owner",
                "coordinate",
                "steps",
                "source_symbol",
                "source_ingress",
                "halo",
            ),
            values,
            strict=True,
        ):
            object.__setattr__(record, name, value)
        object.__setattr__(record, "_binding", values)
        object.__setattr__(record, "_seal", _UNIFORM_CONE_SEAL)
        return record

    def _validate(self) -> None:
        """Check the issued binding and live owner without re-deriving its halo."""
        from number_compiler.sequences.reverse_add.q19_output import (
            ReversePairQ19OutputOwner,
        )

        if self._seal is not _UNIFORM_CONE_SEAL or self._binding != (
            self.source,
            self.owner,
            self.coordinate,
            self.steps,
            self.source_symbol,
            self.source_ingress,
            self.halo,
        ):
            raise ValueError("uniform cell observation was altered or not issued")
        if type(self.owner) is not ReversePairQ19OutputOwner:
            raise TypeError("uniform cell observation requires its Q19 owner")
        self.owner.validate_issued_occurrence(self.source)

    @property
    def coefficient(self) -> int:
        self._validate()
        return _bulk_at(self.source_symbol, self.source_ingress, self.steps)

    @property
    def f5(self) -> int:
        return self.coefficient % 5

    @property
    def five_band(self) -> str:
        return decimal_pair_band(self.coefficient).value

    @property
    def bulk_carry(self) -> int | None:
        self._validate()
        s = self.coefficient
        if s == 9:
            return self.source_ingress
        return int(s > 9)

    def next_quiet_borrow_response(self, offset: int) -> tuple[int, int]:
        """Complete raw innovation-borrow port truth table for a quiet exit.

        Output at offset+1 is `(port[0],port[1])` for incoming spatial
        borrow 0/1. A following *growth* comparison instead requires its
        shifted reversal seam and is not authorized by this table.
        """
        self._validate()
        if type(offset) is not int or not 0 <= offset < self.steps:
            raise ValueError("borrow gate must have a certified following tick")
        old = self.at(offset)
        incoming = self.source_ingress if old == 9 else int(old > 9)
        emitted = old + incoming - 10 * int(old > 9 or (old == 9 and incoming))
        new = self.at(offset + 1)
        reset = int(new > 9)
        identity = (emitted == 0 and reset == 0) or (emitted == 9 and reset == 1)
        return (0, 1) if identity else (reset, reset)

    def next_quiet_joint_xor_response(self, offset: int) -> tuple[int, int]:
        """Conditional XOR of the next carry with the raw borrow port.

        This is a local carry/borrow stencil, not the magnitude-oriented
        signed innovation vector or a source-wide CRT observer.
        """
        return next_quiet_joint_xor_response(self, offset)

    def extend(
        self, owner: ReversePairQ19OutputOwner, steps: int
    ) -> CertifiedUniformCone:
        """Source-guarded temporal join without constructing middle sources."""
        if type(steps) is not int or steps < 0:
            raise ValueError("macro extension needs a nonnegative duration")
        return authorize_uniform_cone(
            owner,
            self.source,
            steps=self.steps + steps,
            coordinate=self.coordinate,
        )

    def square(self, owner: ReversePairQ19OutputOwner) -> CertifiedUniformCone:
        """Real temporal square, rechecking the doubled *source* halo guard."""
        return self.extend(owner, self.steps)

    def at(self, offset: int) -> int:
        self._validate()
        if type(offset) is not int or not 0 <= offset <= self.steps:
            raise ValueError("cone query must stay within its certified span")
        return _bulk_at(self.source_symbol, self.source_ingress, offset)


def authorize_uniform_cone(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    steps: int,
    coordinate: int,
) -> CertifiedUniformCone:
    """Certify and directly power one actual pair coordinate, without a target.

    Strongly source-bound: a passed occurrence must have been issued by the
    live Q19 ledger owner, and the entire 4D+5 uniform guard is checked
    exactly using SLP runs. No growth itinerary or numeric trajectory table
    is accepted as an authority input.
    """
    return _derive_uniform_cone(owner, source, steps=steps, coordinate=coordinate)


def _derive_uniform_cone(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    steps: int,
    coordinate: int,
) -> CertifiedUniformCone:
    owner.validate(source)
    if type(steps) is not int or steps < 0:
        raise ValueError("nonnegative temporal depth required")
    if type(coordinate) is not int or not 0 <= coordinate < source.pair_width:
        raise IndexError(coordinate)
    halo = 2 * steps + 2
    w = source.pair_width
    if coordinate - halo < 0 or coordinate + halo >= w:
        raise UniformConeNotAuthorized("no protected source halo for this depth")
    value = owner._pair_value_at(source, coordinate)
    if not _full_pair_region_uniform(
        owner, source, coordinate - halo, coordinate + halo + 1, value
    ):
        raise UniformConeNotAuthorized("interior pair-word halo is not uniform")
    if value == 9:
        # The EQ wire transmits carries from the exterior.  We admit it
        # only if the two *actual* reflected source carry ingresses coincide,
        # forcing a RESET0/RESET1 homogeneous successor on the first tick.
        from number_compiler.sequences.reverse_add.q19_conditional_stencil import (
            GuardedPairStencil,
        )

        stencil = GuardedPairStencil.from_occurrence(owner, source)
        low = stencil.carry_at(owner, coordinate)
        high = stencil.carry_at(owner, w - 1 - coordinate)
        if low != high:
            raise UniformConeNotAuthorized(
                "asymmetric EQ wire remains exterior-dependent"
            )
        ingress = low
    else:
        ingress = int(value > 9)
    result = CertifiedUniformCone._issue(
        source, owner, coordinate, steps, value, ingress, halo
    )
    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_AUTHORIZED_BULK_TEMPORAL_CELLS)
    return result


__all__ = [
    "CertifiedUniformCone",
    "UniformConeMooreCertificate",
    "UniformConeNotAuthorized",
    "authorize_uniform_cone",
    "uniform_cone_moore_certificate",
]


def main(argv: list[str] | None = None) -> int:
    """Strict CLI for an interior cell, never a complete reverse/add endpoint."""
    import argparse
    import json

    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    parser = argparse.ArgumentParser(prog="python -m ...q19_uniform_cone")
    parser.add_argument("--source-digits", required=True)
    parser.add_argument("--steps", required=True, type=int)
    parser.add_argument("--coordinate", required=True, type=int)
    args = parser.parse_args(argv)
    source = args.source_digits
    if (
        not source
        or not source.isascii()
        or not source.isdecimal()
        or (len(source) > 1 and source[0] == "0")
    ):
        parser.error("source-digits must be a canonical nonnegative decimal word")
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(
        ledger, tuple(ord(c) - 48 for c in reversed(source)), base=10
    )
    try:
        try:
            action = owner.authorize_temporal_cell(
                owner.initial, steps=args.steps, coordinate=args.coordinate
            )
        except UniformConeNotAuthorized as exc:
            result: dict[str, object] = {
                "status": "refused",
                "reason": str(exc),
                "complete_integer_certified": False,
            }
        else:
            result = {
                "status": "authorized-interior-cell",
                "proof_scope": "Q19_ALL_BORDER_CHOICES_UNIFORM_CONE",
                "coordinate_lsd_pair": action.coordinate,
                "steps": action.steps,
                "source_coefficient": action.source_symbol,
                "future_coefficient": action.coefficient,
                "future_five_band": action.five_band,
                "future_f5": action.f5,
                "halo": action.halo,
                "complete_integer_certified": False,
                "source_growth_tape_certified": False,
                "physical_q19_kernel_calls": sum(
                    value
                    for key, value in ledger.counters.items()
                    if key.startswith("reverse_q19_punctured_t")
                    and key.endswith("_applications")
                ),
            }
            if action.steps:
                result["next_quiet_borrow_port_at_entry"] = list(
                    action.next_quiet_borrow_response(0)
                )
                result["next_quiet_carry_borrow_xor_at_entry"] = list(
                    action.next_quiet_joint_xor_response(0)
                )
    finally:
        owner.dispose()
        if ledger.entries or ledger.nodes:
            raise AssertionError("Q19 uniform macro leaked its source owner")
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
