"""Finite 100-state Q19 transfers over an exact issued carry-phase word.

The matrix consumes retained border-bank phases and their correlated
first-reset/map witnesses.  Projected coefficient domains make the relation
an overapproximation of source-root-admissible paths; it does not issue Q19
roots or certify future repetition.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING
from weakref import ReferenceType, ref

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.fields.boolean_transfer import (
    BooleanMatrix,
    BooleanStateSpace,
)

from ._q19_issuance import issue_q19_record

if TYPE_CHECKING:
    from .temporal_carry_phase import CertifiedCarryPhase, CertifiedCarryWord

PAIR_COUNT = 100
ALL_PAIRS: tuple[tuple[int, int], ...] = tuple(
    (left, right) for left in range(10) for right in range(10)
)
# Ordered pair states follow the inward coordinates used by the Q19 border
# rows: the LSD side first, then the mirrored MSD side.
PAIR_COORDINATE_ORDER = ("lower_lsd_inward", "upper_msd_inward")
_PAIR_STATE_SPACE: BooleanStateSpace[tuple[int, int]] = BooleanStateSpace(
    "reverse_add.decimal-pair", ALL_PAIRS
)
_ISSUER = object()


def pair_index(pair: tuple[int, int]) -> int:
    if (
        type(pair) is not tuple
        or len(pair) != 2
        or any(type(digit) is not int or not 0 <= digit <= 9 for digit in pair)
    ):
        raise ValueError("ordered pair must contain two exact decimal digits")
    return 10 * pair[0] + pair[1]


@dataclass(frozen=True, slots=True, init=False)
class BooleanPairMatrix:
    """Boolean relation owned by the reverse-add ordered-pair state space."""

    _relation: BooleanMatrix[tuple[int, int]]

    def __init__(self, rows: tuple[int, ...]) -> None:
        object.__setattr__(self, "_relation", BooleanMatrix(_PAIR_STATE_SPACE, rows))

    @classmethod
    def _from_relation(
        cls, relation: BooleanMatrix[tuple[int, int]]
    ) -> BooleanPairMatrix:
        if (
            type(relation) is not BooleanMatrix
            or relation.state_space is not _PAIR_STATE_SPACE
        ):
            raise TypeError("reverse-add matrix needs its ordered-pair state space")
        result = object.__new__(cls)
        object.__setattr__(result, "_relation", relation)
        return result

    @property
    def rows(self) -> tuple[int, ...]:
        return self._relation.rows

    @property
    def state_space(self) -> BooleanStateSpace[tuple[int, int]]:
        return self._relation.state_space

    @classmethod
    def identity(cls) -> BooleanPairMatrix:
        relation: BooleanMatrix[tuple[int, int]] = BooleanMatrix(
            _PAIR_STATE_SPACE,
            tuple(1 << state for state in range(_PAIR_STATE_SPACE.size)),
        )
        return cls._from_relation(relation)

    def then(self, later: BooleanPairMatrix) -> BooleanPairMatrix:
        if type(later) is not BooleanPairMatrix:
            raise TypeError("Boolean composition needs another pair matrix")
        return self._from_relation(self._relation.then(later._relation))

    def image(self, source_states: int) -> int:
        return self._relation.image(source_states)

    def endpoints(self, source: tuple[int, int]) -> tuple[tuple[int, int], ...]:
        image = self.image(1 << pair_index(source))
        return tuple(
            ALL_PAIRS[index] for index in range(PAIR_COUNT) if image >> index & 1
        )

    @property
    def edge_count(self) -> int:
        return sum(row.bit_count() for row in self.rows)

    @property
    def maximum_successors(self) -> int:
        return max((row.bit_count() for row in self.rows), default=0)


def _offset_mask_product(left: int, right: int, multiplier: int) -> int:
    result = 0
    for first in range(5):
        if left & (1 << first):
            for later in range(5):
                if right & (1 << later):
                    result |= 1 << ((multiplier * first + later) % 5)
    return result


@dataclass(frozen=True, slots=True)
class Q19AffinePairMatrix:
    """Finite ordered-pair relation with path-correlated F5 offsets.

    This is a projection of the same candidate edges as ``BooleanPairMatrix``.
    It composes only across the requested source-word phases and provides no
    powering or physical-repeat authority.
    """

    steps: int
    rows: tuple[tuple[tuple[int, int], ...], ...]

    def __post_init__(self) -> None:
        if (
            type(self.steps) is not int
            or self.steps < 0
            or type(self.rows) is not tuple
            or len(self.rows) != PAIR_COUNT
        ):
            raise ValueError("invalid Q19 affine-pair matrix dimensions")
        multiplier = pow(2, self.steps, 5)
        for source, row in enumerate(self.rows):
            if type(row) is not tuple:
                raise ValueError("affine-pair rows must be immutable")
            previous = -1
            source_sum = sum(ALL_PAIRS[source])
            for target, offsets in row:
                if (
                    type(target) is not int
                    or not previous < target < PAIR_COUNT
                    or type(offsets) is not int
                    or not 0 < offsets < 32
                ):
                    raise ValueError("invalid affine-pair destination or offset set")
                previous = target
                target_sum = sum(ALL_PAIRS[target])
                if any(
                    (multiplier * source_sum + offset) % 5 != target_sum % 5
                    for offset in range(5)
                    if offsets & (1 << offset)
                ):
                    raise ValueError("affine offset disagrees with pair endpoints")

    @classmethod
    def identity(cls) -> Q19AffinePairMatrix:
        return cls(0, tuple(((index, 1),) for index in range(PAIR_COUNT)))

    @classmethod
    def from_boolean(cls, matrix: BooleanPairMatrix) -> Q19AffinePairMatrix:
        if type(matrix) is not BooleanPairMatrix:
            raise TypeError("affine projection requires a Boolean pair matrix")
        rows: list[tuple[tuple[int, int], ...]] = []
        for source, row_bits in enumerate(matrix.rows):
            source_sum = sum(ALL_PAIRS[source])
            row: list[tuple[int, int]] = []
            while row_bits:
                bit = row_bits & -row_bits
                target = bit.bit_length() - 1
                target_sum = sum(ALL_PAIRS[target])
                offset = (target_sum - 2 * source_sum) % 5
                row.append((target, 1 << offset))
                row_bits ^= bit
            rows.append(tuple(row))
        return cls(1, tuple(rows))

    def then(self, later: Q19AffinePairMatrix) -> Q19AffinePairMatrix:
        if type(later) is not Q19AffinePairMatrix:
            raise TypeError("affine-pair composition requires a compatible matrix")
        multiplier = pow(2, later.steps, 5)
        rows: list[tuple[tuple[int, int], ...]] = []
        for first_row in self.rows:
            combined: dict[int, int] = {}
            for via, first_offsets in first_row:
                for target, later_offsets in later.rows[via]:
                    product = _offset_mask_product(
                        first_offsets, later_offsets, multiplier
                    )
                    combined[target] = combined.get(target, 0) | product
            rows.append(tuple(sorted(combined.items())))
        return Q19AffinePairMatrix(self.steps + later.steps, tuple(rows))

    @property
    def boolean(self) -> BooleanPairMatrix:
        return BooleanPairMatrix(
            tuple(sum(1 << target for target, _mask in row) for row in self.rows)
        )

    def endpoints(
        self, source: tuple[int, int]
    ) -> tuple[tuple[tuple[int, int], tuple[int, ...]], ...]:
        return tuple(
            (
                ALL_PAIRS[target],
                tuple(offset for offset in range(5) if mask & (1 << offset)),
            )
            for target, mask in self.rows[pair_index(source)]
        )


def _scalar_snapshot(value: object) -> tuple[object, object]:
    return type(value), value


def _integer_tuple_snapshot(value: object) -> tuple[object, ...]:
    if not is_exact_object_tuple(value):
        return (type(value), value)
    return (tuple, tuple(_scalar_snapshot(item) for item in value))


def _domain_rows_snapshot(value: object) -> tuple[object, ...]:
    if not is_exact_object_tuple(value):
        return (type(value), value)
    return (tuple, tuple(_integer_tuple_snapshot(row) for row in value))


def _matrix_snapshot(value: object) -> tuple[object, ...]:
    if type(value) is not BooleanPairMatrix:
        return (type(value), value)
    return (BooleanPairMatrix, _integer_tuple_snapshot(value.rows))


def _matrix_rows_snapshot(value: object) -> tuple[object, ...]:
    if not is_exact_object_tuple(value):
        return (type(value), value)
    return (tuple, tuple(_matrix_snapshot(matrix) for matrix in value))


def _affine_matrix_snapshot(value: object) -> tuple[object, ...]:
    if type(value) is not Q19AffinePairMatrix:
        return type(value), id(value)
    rows = tuple(
        tuple(
            (_scalar_snapshot(target), _scalar_snapshot(mask)) for target, mask in row
        )
        for row in value.rows
    )
    return Q19AffinePairMatrix, _scalar_snapshot(value.steps), rows


def _carry(pair_sum: int, incoming: int) -> int:
    return int(pair_sum + incoming >= 10)


def _apply_carry(function: CarryFn, incoming: int) -> int:
    if function is CarryFn.CONST0:
        return 0
    if function is CarryFn.CONST1:
        return 1
    return incoming


def _outer_border_data(
    tile: object,
) -> tuple[tuple[int, ...], tuple[tuple[int, int], ...]]:
    from .border_carry_safety import BorderTile

    if type(tile) is not BorderTile:
        raise TypeError("Q19 depth matrix requires issued border tiles")
    size = tile.k
    high = tuple(map(int, str(tile.high).zfill(size)))
    lower_lsd = tuple(tile.low // (10**index) % 10 for index in range(size))
    return (
        tuple(high[index] + lower_lsd[index] for index in range(size)),
        tuple((lower_lsd[index], high[index]) for index in range(size)),
    )


def _candidate_pairs(
    phase: CertifiedCarryPhase,
    source_domain: tuple[int, ...],
    target_domain: tuple[int, ...],
    source_pair: tuple[int, int],
    *,
    exact_target: tuple[int, int] | None = None,
) -> tuple[tuple[int, int], ...]:
    """Evaluate every correlated reset witness against the same border seam."""
    position = phase.port.source.k
    if source_pair[0] + source_pair[1] not in source_domain:
        return ()
    pair_sum = sum(source_pair)
    pair_sums, _source_outer = _outer_border_data(phase.port.source)
    _target_sums, target_outer = _outer_border_data(phase.port.target)
    low = phase.low_carry
    folded = 0
    for outer_sum in pair_sums:
        folded = _carry(outer_sum, folded)
    if folded != low:
        raise ValueError("issued low carry disagrees with its exact Q19 border")

    lower_source: list[int] = []
    carry = 0
    for outer_sum in pair_sums:
        lower_source.append((outer_sum + carry) % 10)
        carry = _carry(outer_sum, carry)

    outputs: set[tuple[int, int]] = set()
    for reset_position, transfer in phase.first_reset_witnesses:
        if transfer not in phase.middle_transfers:
            raise ValueError("first-reset witness lost its correlated carry map")
        # The retained transfer spans the candidate pair as well as the
        # deeper seam. Its value is the carry leaving that pair, not the
        # reflected carry entering it. Reconstruct the latter from the
        # deeper map and the carry entering the pair.
        if reset_position == position:
            expected_reset = (
                CarryFn.CONST0
                if pair_sum < 9
                else CarryFn.CONST1
                if pair_sum > 9
                else None
            )
            if expected_reset is None or transfer is not expected_reset:
                continue
        elif reset_position == -1 or reset_position > position:
            if pair_sum != 9:
                continue
        else:
            raise ValueError("first-reset witness precedes the retained pair")

        for deeper in (CarryFn.CONST0, CarryFn.ID, CarryFn.CONST1):
            # The whole middle map is K_q o F o K_q. Check both possible
            # inputs before using F to recover the reflected carry.
            if any(
                _carry(pair_sum, _apply_carry(deeper, _carry(pair_sum, bit)))
                != _apply_carry(transfer, bit)
                for bit in (0, 1)
            ):
                continue
            right_in = _apply_carry(deeper, _carry(pair_sum, low))
            high_out = _carry(pair_sum, right_in)
            upper_source = [0] * position
            upper_carry = high_out
            for index in range(position - 1, -1, -1):
                upper_source[index] = (pair_sums[index] + upper_carry) % 10
                upper_carry = _carry(pair_sums[index], upper_carry)
            if upper_carry != phase.port.growth:
                continue

            if phase.port.growth:
                upper_target = [1, *upper_source[:-1]]
                upper_digit = upper_source[-1]
            else:
                upper_target = upper_source
                upper_digit = (pair_sum + right_in) % 10
            if any(
                (lower_source[index], upper_target[index]) != target_outer[index]
                for index in range(position)
            ):
                continue
            output = ((pair_sum + low) % 10, upper_digit)
            if output[0] + output[1] not in target_domain:
                continue
            if exact_target is not None and output != exact_target:
                continue
            from .conditional_pair_ring import RingPairLetter

            letter = RingPairLetter(
                position,
                phase.port.growth,
                pair_sums[-1] if phase.port.growth and position else None,
                low,
                right_in,
            )
            if letter.successor(pair_sum) != sum(output):
                raise AssertionError("ordered-pair transfer disagrees with Q19 law")
            outputs.add(output)
    return tuple(sorted(outputs))


def _phase_matrix(
    phase: CertifiedCarryPhase,
    source_domain: tuple[int, ...],
    target_domain: tuple[int, ...],
) -> BooleanPairMatrix:
    rows = tuple(
        sum(
            1 << pair_index(target)
            for target in _candidate_pairs(phase, source_domain, target_domain, source)
        )
        for source in ALL_PAIRS
    )
    return BooleanPairMatrix(rows)


def _source_guarded_phase_matrix(
    phase: CertifiedCarryPhase,
    source_domain: tuple[int, ...],
    target_domain: tuple[int, ...],
    source_pair: tuple[int, int],
    target_pair: tuple[int, int],
) -> BooleanPairMatrix:
    """Select one owner-joined pair edge before considering matrix rows."""
    source_index = pair_index(source_pair)
    target_index = pair_index(target_pair)
    source_sum = sum(source_pair)
    target_sum = sum(target_pair)
    if source_sum not in source_domain or target_sum not in target_domain:
        raise ValueError("exact source pair path is outside the retained Q19 domains")
    candidates = _candidate_pairs(
        phase,
        (source_sum,),
        (target_sum,),
        source_pair,
        exact_target=target_pair,
    )
    if target_pair not in candidates:
        raise ValueError("exact source child edge is absent from its guarded border")
    rows = [0] * PAIR_COUNT
    rows[source_index] = 1 << target_index
    return BooleanPairMatrix(tuple(rows))


def _window_domains(
    word: CertifiedCarryWord, position: int
) -> tuple[tuple[int, ...], ...]:
    values: list[tuple[int, ...]] = []
    for bank in word.source_banks:
        if position not in bank.positions:
            raise ValueError("carry word has no retained domain at this depth")
        row = bank.phase_pair_domains[bank.positions.index(position)]
        if values and values[-1] != row[0]:
            raise ValueError("adjacent retained ring banks have a Q19 domain seam")
        values.extend(row if not values else row[1:])
    if len(values) != word.duration + 1:
        raise ValueError("retained Q19 domains do not cover the carry word")
    return tuple(values)


@dataclass(frozen=True, slots=True, weakref_slot=True)
class ConditionalQ19DepthWindow:
    """Finite pair relation tied to a retained carry word.

    Exact bank phases and reset/map witnesses constrain each row, but the
    retained coefficient domains are projections.  Without the exact
    punctured source-root assignment, endpoints are not an exact source-root
    fiber. An optional ordered-pair path narrows each phase before composing;
    its source roots remain the caller's responsibility.
    """

    source_word: CertifiedCarryWord = field(repr=False, compare=False)
    position: int
    start_tick: int
    steps: int
    source_domains: tuple[tuple[int, ...], ...]
    target_domains: tuple[tuple[int, ...], ...]
    phase_matrices: tuple[BooleanPairMatrix, ...]
    action: BooleanPairMatrix
    affine_action: Q19AffinePairMatrix
    source_pair_path: tuple[tuple[int, int], ...] | None = None
    physical_repeat_certified: bool = False
    autonomous_source_power_certified: bool = False
    _seal: object = field(default=None, init=False, repr=False, compare=False)
    _binding: tuple[object, ...] = field(
        default=(), init=False, repr=False, compare=False
    )
    _issued_self: ReferenceType[ConditionalQ19DepthWindow] | None = field(
        default=None, init=False, repr=False, compare=False
    )

    def publication_snapshot(self) -> tuple[object, ...]:
        return (
            id(self.source_word),
            _scalar_snapshot(self.position),
            _scalar_snapshot(self.start_tick),
            _scalar_snapshot(self.steps),
            _domain_rows_snapshot(self.source_domains),
            _domain_rows_snapshot(self.target_domains),
            _matrix_rows_snapshot(self.phase_matrices),
            _matrix_snapshot(self.action),
            _affine_matrix_snapshot(self.affine_action),
            _integer_tuple_snapshot(self.source_pair_path)
            if self.source_pair_path is not None
            else (None, None),
            _scalar_snapshot(self.physical_repeat_certified),
            _scalar_snapshot(self.autonomous_source_power_certified),
        )

    def validate(self) -> None:
        """Validate this packet's seal, snapshot, and live source chain once."""
        if self._issued_self is None or self._issued_self() is not self:
            raise ValueError("Q19 depth window was not issued")
        if self._seal is not _ISSUER or self._binding != self.publication_snapshot():
            raise ValueError("Q19 depth window contents changed")
        self.source_word.validate()
        if (
            type(self.source_domains) is not tuple
            or type(self.target_domains) is not tuple
            or type(self.phase_matrices) is not tuple
            or len(self.source_domains) != self.steps
            or len(self.target_domains) != self.steps
            or len(self.phase_matrices) != self.steps
            or any(
                type(domain) is not tuple
                or not domain
                or any(
                    type(value) is not int or not 0 <= value <= 18 for value in domain
                )
                or tuple(sorted(set(domain))) != domain
                for domain in (*self.source_domains, *self.target_domains)
            )
            or any(
                type(matrix) is not BooleanPairMatrix for matrix in self.phase_matrices
            )
            or type(self.action) is not BooleanPairMatrix
            or type(self.affine_action) is not Q19AffinePairMatrix
            or self.affine_action.steps != self.steps
            or self.affine_action.boolean != self.action
            or (
                self.source_pair_path is not None
                and (
                    type(self.source_pair_path) is not tuple
                    or len(self.source_pair_path) != self.steps + 1
                    or any(
                        type(pair) is not tuple
                        or len(pair) != 2
                        or any(
                            type(digit) is not int or not 0 <= digit <= 9
                            for digit in pair
                        )
                        for pair in self.source_pair_path
                    )
                )
            )
        ):
            raise ValueError("invalid Q19 depth-window matrix shape")
        if (
            type(self.position) is not int
            or self.position < 1
            or type(self.start_tick) is not int
            or self.start_tick < 0
            or type(self.steps) is not int
            or self.steps < 1
            or self.start_tick + self.steps > self.source_word.duration
            or self.physical_repeat_certified
            or self.autonomous_source_power_certified
        ):
            raise ValueError("invalid finite Q19 depth-window horizon")
        if self.source_pair_path is not None:
            expected_rows: list[tuple[int, ...]] = []
            for source, target in zip(
                self.source_pair_path[:-1],
                self.source_pair_path[1:],
                strict=True,
            ):
                source_index = pair_index(source)
                target_index = pair_index(target)
                expected_rows.append(
                    tuple(
                        (1 << target_index) if index == source_index else 0
                        for index in range(PAIR_COUNT)
                    )
                )
            if tuple(matrix.rows for matrix in self.phase_matrices) != tuple(
                expected_rows
            ):
                raise ValueError("source pair path was not guarded before composition")
            expected_action, expected_affine = _pointed_path_actions(
                self.source_pair_path
            )
            if self.action.rows != expected_action.rows:
                raise ValueError("pointed relation differs from its issued path")
            if self.affine_action != expected_affine:
                raise ValueError("pointed affine action differs from its issued path")

    @property
    def physical_interval(self) -> tuple[int, int]:
        self.validate()
        first = self.source_word.start + self.start_tick
        return first, first + self.steps

    @property
    def possible_endpoints(self) -> tuple[tuple[int, int], ...]:
        self.validate()
        image = self.action.image((1 << PAIR_COUNT) - 1)
        return tuple(
            ALL_PAIRS[index] for index in range(PAIR_COUNT) if image >> index & 1
        )

    def to_packet(self) -> dict[str, object]:
        """Serialize a conditional matrix after one live-chain validation."""
        self.validate()
        interval_start = self.source_word.start + self.start_tick
        endpoint_bits = self.action.image((1 << PAIR_COUNT) - 1)
        path_guarded = self.source_pair_path is not None
        return {
            "status": "available",
            "mode": (
                "source_pair_path_guarded"
                if path_guarded
                else "projected_source_word_overapproximation"
            ),
            "relation_semantics": (
                "exact_ordered_pair_path_relation"
                if path_guarded
                else "projected_bank_domain_overapproximation"
            ),
            "source_root_assignment_joined": False,
            "source_pair_path_guarded": path_guarded,
            "exact_candidate_set": False,
            "position": self.position,
            "start_tick": self.start_tick,
            "steps": self.steps,
            "physical_interval": [interval_start, interval_start + self.steps],
            "state_encoding": "10 * left_digit + right_digit",
            "source_domains": [list(domain) for domain in self.source_domains],
            "target_domains": [list(domain) for domain in self.target_domains],
            "phase_transition_rows": [
                list(matrix.rows) for matrix in self.phase_matrices
            ],
            "source_pair_path": (
                None
                if self.source_pair_path is None
                else [list(pair) for pair in self.source_pair_path]
            ),
            "transition_rows": list(self.action.rows),
            "affine_relation_semantics": (
                "finite projected-domain paths with offsets correlated by pair state"
            ),
            "affine_transition_rows": [
                [
                    [target, [offset for offset in range(5) if mask & (1 << offset)]]
                    for target, mask in row
                ]
                for row in self.affine_action.rows
            ],
            "possible_endpoints": [
                list(ALL_PAIRS[index])
                for index in range(PAIR_COUNT)
                if endpoint_bits >> index & 1
            ],
            "physical_repeat_certified": False,
            "autonomous_source_power_certified": False,
        }


def conditional_depth_window(
    source_word: CertifiedCarryWord,
    *,
    position: int,
    start_tick: int = 0,
    steps: int | None = None,
    source_pair_path: tuple[tuple[int, int], ...] | None = None,
) -> ConditionalQ19DepthWindow:
    """Compose a finite subword at positive border width ``position``.

    The returned relation respects correlated phase witnesses and retained
    bank domains, but remains an overapproximation until an exact source-root
    punctured-residue join is supplied. When ``source_pair_path`` is given,
    each phase is narrowed to that exact ordered-pair edge before any matrix
    composition; the caller remains responsible for joining the path to its
    source owner's completed roots.
    """
    from .temporal_carry_phase import CertifiedCarryWord as CarryWord

    if type(source_word) is not CarryWord:
        raise TypeError("Q19 depth window requires a CertifiedCarryWord")
    source_word.validate()
    if type(position) is not int or position < 1:
        raise ValueError("Q19 matrix position must be a positive border width")
    if type(start_tick) is not int or start_tick < 0:
        raise ValueError("Q19 depth-window start must be nonnegative")
    if steps is None:
        steps = source_word.duration - start_tick
    if (
        type(steps) is not int
        or steps < 1
        or start_tick + steps > source_word.duration
        or any(
            phase.port.source.k != position
            for phase in source_word.phases[start_tick : start_tick + steps]
        )
    ):
        raise ValueError("requested Q19 depth/time window is outside issued phases")
    domains = _window_domains(source_word, position)[
        start_tick : start_tick + steps + 1
    ]
    phases = source_word.phases[start_tick : start_tick + steps]
    source_domains = tuple(
        tuple(
            sorted(set(domains[index]).intersection(phase.middle_wire.pair_domains[0]))
        )
        for index, phase in enumerate(phases)
    )
    if any(not domain for domain in source_domains):
        raise ValueError("phase carry wire conflicts with its retained Q19 domain")
    if source_pair_path is not None:
        if type(source_pair_path) is not tuple or len(source_pair_path) != steps + 1:
            raise ValueError("source pair path must cover each requested Q19 phase")
        matrices = tuple(
            _source_guarded_phase_matrix(
                phase,
                source_domains[index],
                domains[index + 1],
                source_pair_path[index],
                source_pair_path[index + 1],
            )
            for index, phase in enumerate(phases)
        )
    else:
        # Preserve the unrestricted projected-domain relation as an
        # independent oracle when no exact owner path was supplied.
        matrices = tuple(
            _phase_matrix(phase, source_domains[index], domains[index + 1])
            for index, phase in enumerate(phases)
        )
    if source_pair_path is None:
        action = BooleanPairMatrix.identity()
        affine_action = Q19AffinePairMatrix.identity()
        for matrix in matrices:
            action = action.then(matrix)
            affine_action = affine_action.then(Q19AffinePairMatrix.from_boolean(matrix))
    else:
        action, affine_action = _pointed_path_actions(source_pair_path)
    record = ConditionalQ19DepthWindow(
        source_word,
        position,
        start_tick,
        steps,
        source_domains,
        domains[1:],
        matrices,
        action,
        affine_action,
        source_pair_path,
    )
    issued = issue_q19_record(record, {"_issued_self": ref(record)}, _ISSUER)
    issued.validate()
    return issued


def _pointed_path_actions(
    path: tuple[tuple[int, int], ...],
) -> tuple[BooleanPairMatrix, Q19AffinePairMatrix]:
    """Build the exact relation and affine cocycle for one checked finite path.

    Per-phase source guards are checked before this projection. The result is
    only the finite endpoint action; it carries no authority to repeat the
    path or extend it beyond the supplied roots.
    """
    if type(path) is not tuple or len(path) < 2:
        raise ValueError("pointed Q19 path needs at least one adjacent edge")
    source_index = pair_index(path[0])
    target_index = pair_index(path[-1])
    steps = len(path) - 1
    rows = [0] * PAIR_COUNT
    rows[source_index] = 1 << target_index
    action = BooleanPairMatrix(tuple(rows))

    source_sum = sum(path[0])
    target_sum = sum(path[-1])
    offset = (target_sum - pow(2, steps, 5) * source_sum) % 5
    affine_rows: list[tuple[tuple[int, int], ...]] = [()] * PAIR_COUNT
    affine_rows[source_index] = ((target_index, 1 << offset),)
    affine = Q19AffinePairMatrix(steps, tuple(affine_rows))
    return action, affine


__all__ = [
    "ALL_PAIRS",
    "PAIR_COORDINATE_ORDER",
    "BooleanPairMatrix",
    "ConditionalQ19DepthWindow",
    "Q19AffinePairMatrix",
    "conditional_depth_window",
    "pair_index",
]
